/*
** $Id: lstring.c,v 2.8.1.1 2007/12/27 13:02:25 roberto Exp $
** String table (keeps all strings handled by Lua)
** See Copyright Notice in lua.h
*/


#include <string.h>

#define lstring_c
#define LUA_CORE

#include "lua.h"

#include "lmem.h"
#include "lobject.h"
#include "lstate.h"
#include "lstring.h"


// 对保存string的hash桶进行resize
void luaS_resize (lua_State *L, int newsize) {
  GCObject **newhash;
  stringtable *tb;
  int i;
  // 当前处在清理字符串的 GC 状态时，不能做 resize 操作
  // 直接返回，等待下一次触发即可
  if (G(L)->gcstate == GCSsweepstring)
    return;  /* cannot resize during GC traverse */
  // 申请承载新的哈希桶的数组，大小即为 newsize
  newhash = luaM_newvector(L, newsize, GCObject *);
  tb = &G(L)->strt;
  // 清空新的哈希桶
  for (i=0; i<newsize; i++) newhash[i] = NULL;
  /* rehash */
  // 逐项遍历旧表里的每一个链表与链表上的每一个对象
  for (i=0; i<tb->size; i++) {
    GCObject *p = tb->hash[i];
    while (p) {  /* for each node in the list */
      GCObject *next = p->gch.next;  /* save next */
      unsigned int h = gco2ts(p)->hash;
      // 重新计算hash桶索引，这次需要mod新的hash桶大小
      int h1 = lmod(h, newsize);  /* new position */
      lua_assert(cast_int(h%newsize) == lmod(h, newsize));
      // 链到新表里对应的链表上
      p->gch.next = newhash[h1];  /* chain it */
      newhash[h1] = p;
      p = next;
    }
  }
  // 释放原有哈希桶占用的内存
  luaM_freearray(L, tb->hash, tb->size, TString *);
  tb->size = newsize;
  // 注意：strt 这个结构体仍然不动，仅修改其中的 size 跟 hash 字段
  // 也就是说，nuse 仍保持旧值
  tb->hash = newhash;
}


// 真正创建一个新的字符串实例
static TString *newlstr (lua_State *L, const char *str, size_t l,
                                       unsigned int h) {
  TString *ts;
  stringtable *tb;
  if (l+1 > (MAX_SIZET - sizeof(TString))/sizeof(char))
    luaM_toobig(L);
  // 申请一块新内存用以放置新的字符串对象
  // 此内存的长度为 TString 的大小 + 字符串大小
  // 字符串被紧挨着 TString 结构存放
  ts = cast(TString *, luaM_malloc(L, (l+1)*sizeof(char)+sizeof(TString)));
  ts->tsv.len = l;
  ts->tsv.hash = h;
  // 设置颜色为当前白色，以供 GC 系统跟踪
  ts->tsv.marked = luaC_white(G(L));
  ts->tsv.tt = LUA_TSTRING;
  // 此处创建的都是非保留字符串
  ts->tsv.reserved = 0;
  // 将字符串内容拷贝到新内存中紧挨着 TString 的地方
  memcpy(ts+1, str, l*sizeof(char));
  ((char *)(ts+1))[l] = '\0';  /* ending 0 */
  tb = &G(L)->strt;
  // 找到当前哈希对应的链表
  h = lmod(h, tb->size);
  // 将新字符串对象插到链表头
  ts->tsv.next = tb->hash[h];  /* chain new entry */
  tb->hash[h] = obj2gco(ts);
  tb->nuse++;
  // 在hash桶数组大小小于MAX_INT/2的情况下，
  // 只要字符串数量大于桶数组数量就开始成倍的扩充桶的容量
  if (tb->nuse > cast(lu_int32, tb->size) && tb->size <= MAX_INT/2)
    luaS_resize(L, tb->size*2);  /* too crowded */
  return ts;
}


// 在全局字符串表中查找
// 如果已存在相同的字符串，直接返回已有实例；
// 如果没有，则调用 newlstr 真正进行创建，插入全局字符串表中，并返回此新对象
TString *luaS_newlstr (lua_State *L, const char *str, size_t l) {
  GCObject *o;
  // 字符串长度作为 hash 算法的一部分参与计算
  unsigned int h = cast(unsigned int, l);  /* seed */
  // 计算哈希值过程中使用的步长
  // 当长度小于 64 时，step 为 1，也就是每一个字符都会参与哈希的计算
  // 当长度大于等于 64 时，每 step 个字符之中只有 1 个参与了哈希的计算，减少计算量
  // 虽然有小概率的哈希碰撞的可能，但并不影响功能
  size_t step = (l>>5)+1;  /* if string is too long, don't hash all its chars */
  size_t l1;
  // 每隔 step 取一个字符计算哈希
  for (l1=l; l1>=step; l1-=step)  /* compute hash */
    h = h ^ ((h<<5)+(h>>2)+cast(unsigned char, str[l1-1]));
  // 初始化：计算此哈希对应哪一个链表，取出链表上的首个对象（若有）
  // 条件判断：对象是否为空
  // 迭代方法：往链表的下一个对象移动
  for (o = G(L)->strt.hash[lmod(h, G(L)->strt.size)];
       o != NULL;
       o = o->gch.next) {
    TString *ts = rawgco2ts(o);
    // 判断当前对象是否与正欲创建的字符串相等
    // 条件1：长度相等（可以快速失败）；条件2：字符串内容相等
    if (ts->tsv.len == l && (memcmp(str, getstr(ts), l) == 0)) {
      /* string may be dead */
      // 字符串可能正要被回收，若如此，将其设置为白色，以脱离此轮 GC
      if (isdead(G(L), o)) changewhite(o);
      return ts;
    }
  }
  // 现有的字符串中没有相等的，将真正地创建一个新的字符串
  return newlstr(L, str, l, h);  /* not found */
}


Udata *luaS_newudata (lua_State *L, size_t s, Table *e) {
  Udata *u;
  if (s > MAX_SIZET - sizeof(Udata))
    luaM_toobig(L);
  u = cast(Udata *, luaM_malloc(L, s + sizeof(Udata)));
  u->uv.marked = luaC_white(G(L));  /* is not finalized */
  u->uv.tt = LUA_TUSERDATA;
  u->uv.len = s;
  u->uv.metatable = NULL;
  u->uv.env = e;
  /* chain it on udata list (after main thread) */
  // 这样让udata链接在mainthread之后，一定是整个GC链表的最后
  u->uv.next = G(L)->mainthread->next;
  G(L)->mainthread->next = obj2gco(u);
  return u;
}

