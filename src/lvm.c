/*
** $Id: lvm.c,v 2.63.1.3 2007/12/28 15:32:23 roberto Exp $
** Lua virtual machine
** See Copyright Notice in lua.h
*/


#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define lvm_c
#define LUA_CORE

#include "lua.h"

#include "ldebug.h"
#include "ldo.h"
#include "lfunc.h"
#include "lgc.h"
#include "lobject.h"
#include "lopcodes.h"
#include "lstate.h"
#include "lstring.h"
#include "ltable.h"
#include "ltm.h"
#include "lvm.h"



/* limit for table tag-method chains (to avoid loops) */
#define MAXTAGLOOP	100

// value转换成数字
const TValue *luaV_tonumber (const TValue *obj, TValue *n) {
  lua_Number num;
  if (ttisnumber(obj)) return obj;
  if (ttisstring(obj) && luaO_str2d(svalue(obj), &num)) {
    setnvalue(n, num);
    return n;
  }
  else
    return NULL;
}

// 数字转换成字符串
int luaV_tostring (lua_State *L, StkId obj) {
  if (!ttisnumber(obj))
    return 0;
  else {
    char s[LUAI_MAXNUMBER2STR];
    lua_Number n = nvalue(obj);
    lua_number2str(s, n);
    setsvalue2s(L, obj, luaS_new(L, s));
    return 1;
  }
}

// ????????????
static void traceexec (lua_State *L, const Instruction *pc) {
  lu_byte mask = L->hookmask;
  const Instruction *oldpc = L->savedpc;
  L->savedpc = pc;
  if ((mask & LUA_MASKCOUNT) && L->hookcount == 0) {
    resethookcount(L);
    luaD_callhook(L, LUA_HOOKCOUNT, -1);
  }
  if (mask & LUA_MASKLINE) {
    Proto *p = ci_func(L->ci)->l.p;
    int npc = pcRel(pc, p);
    int newline = getline(p, npc);
    /* call linehook when enter a new function, when jump back (loop),
       or when enter a new line */
    if (npc == 0 || pc <= oldpc || newline != getline(p, pcRel(oldpc, p)))
      luaD_callhook(L, LUA_HOOKLINE, newline);
  }
}

// 调用某函数,最后将结果放在res中
static void callTMres (lua_State *L, StkId res, const TValue *f,
                        const TValue *p1, const TValue *p2) {
  ptrdiff_t result = savestack(L, res);
  setobj2s(L, L->top, f);  /* push function */
  setobj2s(L, L->top+1, p1);  /* 1st argument */
  setobj2s(L, L->top+2, p2);  /* 2nd argument */
  luaD_checkstack(L, 3);
  L->top += 3;
  luaD_call(L, L->top - 3, 1);
  res = restorestack(L, result);
  L->top--;
  setobjs2s(L, res, L->top);
}


// 调用某函数,但是没有结果,这与callTMres不同
static void callTM (lua_State *L, const TValue *f, const TValue *p1,
                    const TValue *p2, const TValue *p3) {
  setobj2s(L, L->top, f);  /* push function */
  setobj2s(L, L->top+1, p1);  /* 1st argument */
  setobj2s(L, L->top+2, p2);  /* 2nd argument */
  setobj2s(L, L->top+3, p3);  /* 3th argument */
  luaD_checkstack(L, 4);
  L->top += 4;
  luaD_call(L, L->top - 4, 0);
}

// 在一个table中查找key对应的值, 找到存放到val中
void luaV_gettable (lua_State *L, const TValue *t, TValue *key, StkId val) {
  int loop;
  // 函数外层以MAXTAGLOOP做为计数,防止死循环
  for (loop = 0; loop < MAXTAGLOOP; loop++) {
    const TValue *tm;
    if (ttistable(t)) {  /* `t' is a table? */
      Table *h = hvalue(t);
      // 首先尝试在表中查找这个key
      const TValue *res = luaH_get(h, key); /* do a primitive get */      
      if (!ttisnil(res) ||  /* result is no nil? */ // 如果结果不是nil
          (tm = fasttm(L, h->metatable, TM_INDEX)) == NULL) { /* or no TM? */ // 在结果为nil的时候如果metable为nil
        setobj2s(L, val, res);
        return;
      }
      /* else will try the tag method */
    }
    // 元表里是否存在 TM_INDEX，如果不存在，报错
    else if (ttisnil(tm = luaT_gettmbyobj(L, t, TM_INDEX)))
      luaG_typeerror(L, t, "index");
    // 如果元表里的 TM_INDEX 是一个函数，调用之
    if (ttisfunction(tm)) {
      callTMres(L, val, tm, t, key);
      return;
    }
    // 否则继续往上层找
    // 因此，元表的 TM_INDEX 可以是另外一个普通的 table，或者其他对象
    t = tm;  /* else repeat with `tm' */
  }
  luaG_runerror(L, "loop in gettable");
}

// 为什么这个操作需要放在lvm也就是虚拟机相关代码的部分呢??
void luaV_settable (lua_State *L, const TValue *t, TValue *key, StkId val) {
  int loop;
  for (loop = 0; loop < MAXTAGLOOP; loop++) {
    const TValue *tm;
    if (ttistable(t)) {  /* `t' is a table? */
      // 首先获取它的hash部分
      Table *h = hvalue(t);
      TValue *oldval = luaH_set(L, h, key); /* do a primitive set */
      if (!ttisnil(oldval) ||  /* result is no nil? */
          (tm = fasttm(L, h->metatable, TM_NEWINDEX)) == NULL) { /* or no TM? */
    	  // 替换原来的旧值
        setobj2t(L, oldval, val);
        luaC_barriert(L, h, val);
        return;
      }
      /* else will try the tag method */
    }
    else if (ttisnil(tm = luaT_gettmbyobj(L, t, TM_NEWINDEX)))
      luaG_typeerror(L, t, "index");
    if (ttisfunction(tm)) {
      callTM(L, tm, t, key, val);
      return;
    }
    t = tm;  /* else repeat with `tm' */ 
  }
  luaG_runerror(L, "loop in settable");
}


static int call_binTM (lua_State *L, const TValue *p1, const TValue *p2,
                       StkId res, TMS event) {
  const TValue *tm = luaT_gettmbyobj(L, p1, event);  /* try first operand */
  if (ttisnil(tm))
    tm = luaT_gettmbyobj(L, p2, event);  /* try second operand */
  if (ttisnil(tm)) return 0;
  callTMres(L, res, tm, p1, p2);
  return 1;
}


static const TValue *get_compTM (lua_State *L, Table *mt1, Table *mt2,
                                  TMS event) {
  const TValue *tm1 = fasttm(L, mt1, event);
  const TValue *tm2;
  if (tm1 == NULL) return NULL;  /* no metamethod */
  if (mt1 == mt2) return tm1;  /* same metatables => same metamethods */
  tm2 = fasttm(L, mt2, event);
  if (tm2 == NULL) return NULL;  /* no metamethod */
  if (luaO_rawequalObj(tm1, tm2))  /* same metamethods? */
    return tm1;
  return NULL;
}


static int call_orderTM (lua_State *L, const TValue *p1, const TValue *p2,
                         TMS event) {
  const TValue *tm1 = luaT_gettmbyobj(L, p1, event);
  const TValue *tm2;
  if (ttisnil(tm1)) return -1;  /* no metamethod? */
  tm2 = luaT_gettmbyobj(L, p2, event);
  if (!luaO_rawequalObj(tm1, tm2))  /* different metamethods? */
    return -1;
  callTMres(L, L->top, tm1, p1, p2);
  return !l_isfalse(L->top);
}


static int l_strcmp (const TString *ls, const TString *rs) {
  const char *l = getstr(ls);
  size_t ll = ls->tsv.len;
  const char *r = getstr(rs);
  size_t lr = rs->tsv.len;
  for (;;) {
    int temp = strcoll(l, r);
    if (temp != 0) return temp;
    else {  /* strings are equal up to a `\0' */
      size_t len = strlen(l);  /* index of first `\0' in both strings */
      if (len == lr)  /* r is finished? */
        return (len == ll) ? 0 : 1;
      else if (len == ll)  /* l is finished? */
        return -1;  /* l is smaller than r (because r is not finished) */
      /* both strings longer than `len'; go on comparing (after the `\0') */
      len++;
      l += len; ll -= len; r += len; lr -= len;
    }
  }
}


int luaV_lessthan (lua_State *L, const TValue *l, const TValue *r) {
  int res;
  if (ttype(l) != ttype(r))
    return luaG_ordererror(L, l, r);
  else if (ttisnumber(l))
    return luai_numlt(nvalue(l), nvalue(r));
  else if (ttisstring(l))
    return l_strcmp(rawtsvalue(l), rawtsvalue(r)) < 0;
  else if ((res = call_orderTM(L, l, r, TM_LT)) != -1)
    return res;
  return luaG_ordererror(L, l, r);
}


static int lessequal (lua_State *L, const TValue *l, const TValue *r) {
  int res;
  if (ttype(l) != ttype(r))
    return luaG_ordererror(L, l, r);
  else if (ttisnumber(l))
    return luai_numle(nvalue(l), nvalue(r));
  else if (ttisstring(l))
    return l_strcmp(rawtsvalue(l), rawtsvalue(r)) <= 0;
  else if ((res = call_orderTM(L, l, r, TM_LE)) != -1)  /* first try `le' */
    return res;
  else if ((res = call_orderTM(L, r, l, TM_LT)) != -1)  /* else try `lt' */
    return !res;
  return luaG_ordererror(L, l, r);
}


int luaV_equalval (lua_State *L, const TValue *t1, const TValue *t2) {
  const TValue *tm;
  lua_assert(ttype(t1) == ttype(t2));
  switch (ttype(t1)) {
    case LUA_TNIL: return 1;
    case LUA_TNUMBER: return luai_numeq(nvalue(t1), nvalue(t2));
    case LUA_TBOOLEAN: return bvalue(t1) == bvalue(t2);  /* true must be 1 !! */
    case LUA_TLIGHTUSERDATA: return pvalue(t1) == pvalue(t2);
    case LUA_TUSERDATA: {
      if (uvalue(t1) == uvalue(t2)) return 1;
      tm = get_compTM(L, uvalue(t1)->metatable, uvalue(t2)->metatable,
                         TM_EQ);
      break;  /* will try TM */
    }
    case LUA_TTABLE: {
      if (hvalue(t1) == hvalue(t2)) return 1;
      tm = get_compTM(L, hvalue(t1)->metatable, hvalue(t2)->metatable, TM_EQ);
      break;  /* will try TM */
    }
    default: return gcvalue(t1) == gcvalue(t2);
  }
  if (tm == NULL) return 0;  /* no TM? */
  callTMres(L, L->top, tm, t1, t2);  /* call TM */
  return !l_isfalse(L->top);
}


// 将以 last 寄存器结尾的 total 个对象，合并到一起，最终结果放置在范围内首个寄存器里
void luaV_concat (lua_State *L, int total, int last) {
  do {
    StkId top = L->base + last + 1;
    // 一次处理两个元素
    // （给下边前两个分支作为默认值，第三个分支其实是一次性把所有字符串都给合并了，里边会覆盖 n 的取值）
    int n = 2;  /* number of elements handled in this pass (at least 2) */
    // 如果三个条件都不满足，可能是一些奇奇怪怪的类型，直接用元表处理
    if (!(ttisstring(top-2) || ttisnumber(top-2)) || !tostring(L, top-1)) {
      if (!call_binTM(L, top-2, top-1, top-2, TM_CONCAT))
        luaG_concaterror(L, top-2, top-1);
    // 如果当前最后一个元素为空字符串，直接将倒数第二个元素转为字符串作为此轮的结果
    } else if (tsvalue(top-1)->len == 0)  /* second op is empty? */
      (void)tostring(L, top - 2);  /* result is first op (as string) */
    else {
      /* at least two string values; get as many as possible */
      size_t tl = tsvalue(top-1)->len;
      char *buffer;
      int i;
      /* collect total length */
      // 从后往前遍历，计算出范围内所有元素（字符串）的长度总和
      for (n = 1; n < total && tostring(L, top-n-1); n++) {
        size_t l = tsvalue(top-n-1)->len;
        // 长度超限报错
        if (l >= MAX_SIZET - tl) luaG_runerror(L, "string length overflow");
        tl += l;
      }
      // 分配一块 tl 长度的内存
      buffer = luaZ_openspace(L, &G(L)->buff, tl);
      tl = 0;
      for (i=n; i>0; i--) {  /* concat all strings */
        size_t l = tsvalue(top-i)->len;
        // 将所有字符串从前往后依次拼接到 buffer 中
        memcpy(buffer+tl, svalue(top-i), l);
        tl += l;
      }
      // 利用 luaS_newlstr 函数创建一个 TString 对象（存入全局字符串表中），并放入第一个字符串对应的寄存器中
      // 详见我的另外一篇解析 Lua 字符串的文章
      setsvalue2s(L, top-n, luaS_newlstr(L, buffer, tl));
    }
    total -= n-1;  /* got `n' strings to create 1 new */
    last -= n-1;
  } while (total > 1);  /* repeat until only 1 result left */
  // 循环的退出条件是只剩一个对象未处理（也就是最终存放结果的那个对象）
}


static void Arith (lua_State *L, StkId ra, const TValue *rb,
                   const TValue *rc, TMS op) {
  TValue tempb, tempc;
  const TValue *b, *c;
  if ((b = luaV_tonumber(rb, &tempb)) != NULL &&
      (c = luaV_tonumber(rc, &tempc)) != NULL) {
    lua_Number nb = nvalue(b), nc = nvalue(c);
    switch (op) {
      case TM_ADD: setnvalue(ra, luai_numadd(nb, nc)); break;
      case TM_SUB: setnvalue(ra, luai_numsub(nb, nc)); break;
      case TM_MUL: setnvalue(ra, luai_nummul(nb, nc)); break;
      case TM_DIV: setnvalue(ra, luai_numdiv(nb, nc)); break;
      case TM_MOD: setnvalue(ra, luai_nummod(nb, nc)); break;
      case TM_POW: setnvalue(ra, luai_numpow(nb, nc)); break;
      case TM_UNM: setnvalue(ra, luai_numunm(nb)); break;
      default: lua_assert(0); break;
    }
  }
  else if (!call_binTM(L, rb, rc, ra, op))
    luaG_aritherror(L, rb, rc);
}



/*
** some macros for common tasks in `luaV_execute'
*/

#define runtime_check(L, c)	{ if (!(c)) break; }

#define RA(i)	(base+GETARG_A(i))
/* to be used after possible stack reallocation */
#define RB(i)	check_exp(getBMode(GET_OPCODE(i)) == OpArgR, base+GETARG_B(i))
#define RC(i)	check_exp(getCMode(GET_OPCODE(i)) == OpArgR, base+GETARG_C(i))
#define RKB(i)	check_exp(getBMode(GET_OPCODE(i)) == OpArgK, \
	ISK(GETARG_B(i)) ? k+INDEXK(GETARG_B(i)) : base+GETARG_B(i))
#define RKC(i)	check_exp(getCMode(GET_OPCODE(i)) == OpArgK, \
	ISK(GETARG_C(i)) ? k+INDEXK(GETARG_C(i)) : base+GETARG_C(i))
#define KBx(i)	check_exp(getBMode(GET_OPCODE(i)) == OpArgK, k+GETARG_Bx(i))


#define dojump(L,pc,i)	{(pc) += (i); luai_threadyield(L);}


#define Protect(x)	{ L->savedpc = pc; {x;}; base = L->base; }


#define arith_op(op,tm) { \
        TValue *rb = RKB(i); \
        TValue *rc = RKC(i); \
        if (ttisnumber(rb) && ttisnumber(rc)) { \
          lua_Number nb = nvalue(rb), nc = nvalue(rc); \
          setnvalue(ra, op(nb, nc)); \
        } \
        else \
          Protect(Arith(L, ra, rb, rc, tm)); \
      }



void luaV_execute (lua_State *L, int nexeccalls) {
  LClosure *cl;
  StkId base;
  TValue *k;
  const Instruction *pc;
 reentry:  /* entry point */
  lua_assert(isLua(L->ci));
  // 当前指令
  // 这个 L->savedpc 在 luaD_precall 中已设置为 p->code，也就是语法解析获得的指令序列，如下：
  //    // 将 pc 指向解析出来的 Proto->code，也就是 opcode 数组
  //    L->savedpc = p->code;  /* starting point */
  pc = L->savedpc;
  // 当前 CallInfo 对应的闭包
  cl = &clvalue(L->ci->func)->l;
  // 栈基
  base = L->base;
  // 常量表，注意到此表随着 closure 一起管理
  k = cl->p->k;
  /* main loop of interpreter */
  for (;;) {
    // 取指令并自增
    const Instruction i = *pc++;
    StkId ra;
    if ((L->hookmask & (LUA_MASKLINE | LUA_MASKCOUNT)) &&
        (--L->hookcount == 0 || L->hookmask & LUA_MASKLINE)) {
      traceexec(L, pc);
      if (L->status == LUA_YIELD) {  /* did hook yield? */
        L->savedpc = pc - 1;
        return;
      }
      base = L->base;
    }
    /* warning!! several calls may realloc the stack and invalidate `ra' */
    ra = RA(i);
    lua_assert(base == L->base && L->base == L->ci->base);
    lua_assert(base <= L->top && L->top <= L->stack + L->stacksize);
    lua_assert(L->top == L->ci->top || luaG_checkopenop(i));
    switch (GET_OPCODE(i)) {
      case OP_MOVE: {
        setobjs2s(L, ra, RB(i));
        continue;
      }
      case OP_LOADK: {
        setobj2s(L, ra, KBx(i));
        continue;
      }
      case OP_LOADBOOL: {
        setbvalue(ra, GETARG_B(i));
        if (GETARG_C(i)) pc++;  /* skip next instruction (if C) */
        continue;
      }
      case OP_LOADNIL: {
        TValue *rb = RB(i);
        do {
          setnilvalue(rb--);
        } while (rb >= ra);
        continue;
      }
      case OP_GETUPVAL: {
        int b = GETARG_B(i);
        setobj2s(L, ra, cl->upvals[b]->v);
        continue;
      }
      case OP_GETGLOBAL: {
        TValue g;
        TValue *rb = KBx(i);
        sethvalue(L, &g, cl->env);
        lua_assert(ttisstring(rb));
        Protect(luaV_gettable(L, &g, rb, ra));
        continue;
      }
      case OP_GETTABLE: {
        Protect(luaV_gettable(L, RB(i), RKC(i), ra));
        continue;
      }
      case OP_SETGLOBAL: {
        TValue g;
        sethvalue(L, &g, cl->env);
        lua_assert(ttisstring(KBx(i)));
        Protect(luaV_settable(L, &g, KBx(i), ra));
        continue;
      }
      case OP_SETUPVAL: {
        UpVal *uv = cl->upvals[GETARG_B(i)];
        setobj(L, uv->v, ra);
        luaC_barrier(L, uv, ra);
        continue;
      }
      case OP_SETTABLE: {
        Protect(luaV_settable(L, ra, RKB(i), RKC(i)));
        continue;
      }
      case OP_NEWTABLE: {
        int b = GETARG_B(i);
        int c = GETARG_C(i);
        sethvalue(L, ra, luaH_new(L, luaO_fb2int(b), luaO_fb2int(c)));
        Protect(luaC_checkGC(L));
        continue;
      }
      case OP_SELF: {
        StkId rb = RB(i);
        setobjs2s(L, ra+1, rb);
        Protect(luaV_gettable(L, rb, RKC(i), ra));
        continue;
      }
      case OP_ADD: {
        arith_op(luai_numadd, TM_ADD);
        continue;
      }
      case OP_SUB: {
        arith_op(luai_numsub, TM_SUB);
        continue;
      }
      case OP_MUL: {
        arith_op(luai_nummul, TM_MUL);
        continue;
      }
      case OP_DIV: {
        arith_op(luai_numdiv, TM_DIV);
        continue;
      }
      case OP_MOD: {
        arith_op(luai_nummod, TM_MOD);
        continue;
      }
      case OP_POW: {
        arith_op(luai_numpow, TM_POW);
        continue;
      }
      case OP_UNM: {
        TValue *rb = RB(i);
        if (ttisnumber(rb)) {
          lua_Number nb = nvalue(rb);
          setnvalue(ra, luai_numunm(nb));
        }
        else {
          Protect(Arith(L, ra, rb, rb, TM_UNM));
        }
        continue;
      }
      case OP_NOT: {
        int res = l_isfalse(RB(i));  /* next assignment may change this value */
        setbvalue(ra, res);
        continue;
      }
      case OP_LEN: {
        const TValue *rb = RB(i);
        switch (ttype(rb)) {
          case LUA_TTABLE: {
            setnvalue(ra, cast_num(luaH_getn(hvalue(rb))));
            break;
          }
          case LUA_TSTRING: {
            setnvalue(ra, cast_num(tsvalue(rb)->len));
            break;
          }
          default: {  /* try metamethod */
            Protect(
              if (!call_binTM(L, rb, luaO_nilobject, ra, TM_LEN))
                luaG_typeerror(L, rb, "get length of");
            )
          }
        }
        continue;
      }
      case OP_CONCAT: {
        int b = GETARG_B(i);
        int c = GETARG_C(i);
        Protect(luaV_concat(L, c-b+1, c); luaC_checkGC(L));
        setobjs2s(L, RA(i), base+b);
        continue;
      }
      case OP_JMP: {
        dojump(L, pc, GETARG_sBx(i));
        continue;
      }
      case OP_EQ: {
        TValue *rb = RKB(i);
        TValue *rc = RKC(i);
        Protect(
          if (equalobj(L, rb, rc) == GETARG_A(i))
            dojump(L, pc, GETARG_sBx(*pc));
        )
        pc++;
        continue;
      }
      case OP_LT: {
        Protect(
          if (luaV_lessthan(L, RKB(i), RKC(i)) == GETARG_A(i))
            dojump(L, pc, GETARG_sBx(*pc));
        )
        pc++;
        continue;
      }
      case OP_LE: {
        Protect(
          if (lessequal(L, RKB(i), RKC(i)) == GETARG_A(i))
            dojump(L, pc, GETARG_sBx(*pc));
        )
        pc++;
        continue;
      }
      case OP_TEST: {
        if (l_isfalse(ra) != GETARG_C(i))
          dojump(L, pc, GETARG_sBx(*pc));
        pc++;
        continue;
      }
      case OP_TESTSET: {
        TValue *rb = RB(i);
        if (l_isfalse(rb) != GETARG_C(i)) {
          setobjs2s(L, ra, rb);
          dojump(L, pc, GETARG_sBx(*pc));
        }
        pc++;
        continue;
      }
      case OP_CALL: {
        // 参数 B 的含义：
        // =0: [ra+1, L->top) 的范围内都是参数
        // >0: (B-1) 为参数个数
        int b = GETARG_B(i);
        // 参数 C 的含义：
        // (C-1) 为返回值个数
        // 所以大多数场景下，C 的典型取值是 2
        int nresults = GETARG_C(i) - 1;
        // 如果参数 B 不是 0，需要调整 top 指针
        // 后续是通过 top 指针来识别参数的
        if (b != 0) L->top = ra+b;  /* else previous instruction set top */
        // 保存当前 pc，这个 pc 在后边 luaD_precall 会被赋值给 L->ci->savedpc
        // 最终在 OP_RETURN 里被用来作为函数退出后跳回的目标地址（指令）
        L->savedpc = pc;
        switch (luaD_precall(L, ra, nresults)) {
          case PCRLUA: {
            // 自增调用栈深度计数器
            nexeccalls++;
            // 如果 ra 这个 closure 是个 Lua 函数，L->savedpc 会被修改为该函数的 proto->code
            // 因此跳回 reentry 之后，重新取的指令就已经是目标函数的了
            // 直到遇到 OP_RETURN 之后，再重新恢复为现有状态，继续被中断执行的“父函数”
            goto reentry;  /* restart luaV_execute over new Lua function */
          }
          case PCRC: {
            // 如果是 C 函数，那么在 luaD_precall 里已经完成调用了
            // 只需要微调一下栈上结构即可，把 top 跟 base 指针恢复一下
            /* it was a C function (`precall' called it); adjust results */
            if (nresults >= 0) L->top = L->ci->top;
            base = L->base;
            continue;
          }
          default: {
            return;  /* yield */
          }
        }
      }
      case OP_TAILCALL: {
        int b = GETARG_B(i);
        // B 参数的含义与 OP_CALL 一致
        if (b != 0) L->top = ra+b;  /* else previous instruction set top */
        L->savedpc = pc;
        lua_assert(GETARG_C(i) - 1 == LUA_MULTRET);
        // LUA_MULTIRET 在 OP_RETURN 中会用到
        switch (luaD_precall(L, ra, LUA_MULTRET)) {
          case PCRLUA: {
            // 如果是 Lua 函数，在 luaD_precall 中已经创建了新 ci
            // 因此此时 L->ci 是新 ci，而 L->ci - 1 则是触发尾调用的这个即将结束的函数的 ci
            // 主要就是把新 ci 的东西搬到调用者的 ci 里，进行偷梁换柱
            /* tail call: put new frame in place of previous one */
            CallInfo *ci = L->ci - 1;  /* previous frame */
            int aux;
            StkId func = ci->func;
            StkId pfunc = (ci+1)->func;  /* previous function index */
            if (L->openupval) luaF_close(L, ci->base);
            L->base = ci->base = ci->func + ((ci+1)->base - pfunc);
            // 将参数一一挪过去
            for (aux = 0; pfunc+aux < L->top; aux++)  /* move frame down */
              setobjs2s(L, func+aux, pfunc+aux);
            // 调整被替代的 ci 里几个重要的指针，top、savedpc 等，base 指针在上边调整过了
            ci->top = L->top = func+aux;  /* correct top */
            lua_assert(L->top == L->base + clvalue(func)->l.p->maxstacksize);
            ci->savedpc = L->savedpc;
            ci->tailcalls++;  /* one more call lost */
            // 「删除」在 luaD_precall 里创建的新 ci
            L->ci--;  /* remove new frame */
            goto reentry;
          }
          case PCRC: {  /* it was a C function (`precall' called it) */
            // 对于 C 函数而言，还是一样没有太多需要做的事情
            base = L->base;
            continue;
          }
          default: {
            return;  /* yield */
          }
        }
      }
      case OP_RETURN: {
        int b = GETARG_B(i);
        // 参数 B 的含义与 OP_CALL 一致 (0代表到top为止都是返回值，>0代表b-1是返回值数量)
        if (b != 0) L->top = ra+b-1;
        // 如果有 upvals，需要关闭
        if (L->openupval) luaF_close(L, base);
        L->savedpc = pc;
        b = luaD_poscall(L, ra);
        // nexeccalls 是外部传入的参数，典型值是 1，在载入 Lua 脚本之后，函数 luaD_call 中发起调用
        // 每当遇到 OP_CALL(而且得是 Lua 函数) 就会 +1，遇到 OP_RETURN 时就会 -1
        // 当最外层函数也完成执行，进入 OP_RETURN 时，这里就会算出 0 值，因此直接让 luaV_execute 退出
        if (--nexeccalls == 0)  /* was previous function running `here'? */
          return;  /* no: return */
        // 而存在函数调用时，nexeccalls 自减完依然非 0
        // 这种情况下，其实是走了 OP_CALL 指令 goto reentry 的逻辑，从 C 调用栈的角度来看，这一次的 luaV_execute 还没退出呢
        // 所以为了恢复到上一次函数调用时刻的状态，也不应该 return 结束掉这一次的 luaV_execute 调用
        // 由于 luaD_poscall 已经做完了相关工作，所以只需要再简单地把 L->top 指针恢复一下即可
        else {  /* yes: continue its execution */
          if (b) L->top = L->ci->top;
          lua_assert(isLua(L->ci));
          lua_assert(GET_OPCODE(*((L->ci)->savedpc - 1)) == OP_CALL);
          goto reentry;
        }
      }
      case OP_FORLOOP: {
        // ra + 0: 初始值（被减过一次步长），循环期间作为计数值使用
        // ra + 1: 极限值（上限/下限）
        // ra + 2: 步长
        lua_Number step = nvalue(ra+2);
        // 先加步长
        // 在第一次循环时抵消掉了 OP_FORPREP 中那次多余的减步长操作
        // 在后续循环中就是正常的循环步增操作了
        lua_Number idx = luai_numadd(nvalue(ra), step); /* increment index */
        lua_Number limit = nvalue(ra+1);
        // 根据步长的正负值来决定条件判断的方向，判断是否已超过了极限值（上限/下限）
        if (luai_numlt(0, step) ? luai_numle(idx, limit)
                                : luai_numle(limit, idx)) {
          // 如果还没超过极限值……
          // 那么往回跳，执行夹在 OP_FORPREP 与 OP_LOOP 之间的循环体
          dojump(L, pc, GETARG_sBx(i));  /* jump back */
          // 更新 ra + 0、ra + 3 这两个计数值
          // 前者供 OP_FORLOOP 这套逻辑使用，后者供循环体使用
          setnvalue(ra, idx);  /* update internal index... */
          setnvalue(ra+3, idx);  /* ...and external index */
        }
        // 如果已超过极限值，不做任何特殊处理，直接正常执行下一条指令即可
        continue;
      }
      case OP_FORPREP: {
        const TValue *init = ra;      // 初始值
        const TValue *plimit = ra+1;  // 极限值（上限/下限）
        const TValue *pstep = ra+2;   // 步长
        L->savedpc = pc;  /* next steps may throw errors */
        // 检查 init, plimit, pstep 三个参数都能转换为数字，并将转换后的结果放在原位置
        if (!tonumber(init, ra))
          luaG_runerror(L, LUA_QL("for") " initial value must be a number");
        else if (!tonumber(plimit, ra+1))
          luaG_runerror(L, LUA_QL("for") " limit must be a number");
        else if (!tonumber(pstep, ra+2))
          luaG_runerror(L, LUA_QL("for") " step must be a number");
        // 先让初始值减去步长，然后根据 sBx 执行跳转（会跳转到 OP_FORLOOP 指令，在其中加上步长，抵消了这一次额外的计算）
        // 这里减完仍然放在 ra + 0 的地方
        setnvalue(ra, luai_numsub(nvalue(ra), nvalue(pstep)));
        dojump(L, pc, GETARG_sBx(i));
        continue;
      }
      case OP_TFORLOOP: {
        // cb = ra + 3 是所谓「call base」
        StkId cb = ra + 3;  /* call base */
        // 将 [ra, ra+3) 范围内的寄存器值，依次搬运到 [cb, cb+3) 中，也就是 [ra+3, ra+6)
        setobjs2s(L, cb+2, ra+2);
        setobjs2s(L, cb+1, ra+1);
        setobjs2s(L, cb, ra);
        L->top = cb+3;  /* func. + 2 args (state and index) */
        Protect(luaD_call(L, cb, GETARG_C(i)));
        L->top = L->ci->top;
        cb = RA(i) + 3;  /* previous call may change the stack */
        if (!ttisnil(cb)) {  /* continue loop? */
          setobjs2s(L, cb-1, cb);  /* save control variable */
          dojump(L, pc, GETARG_sBx(*pc));  /* jump back */
        }
        pc++;
        continue;
      }
      case OP_SETLIST: {
        int n = GETARG_B(i);  // to
        int c = GETARG_C(i);  // from
        int last;
        Table *h;
        if (n == 0) {
          n = cast_int(L->top - ra) - 1;
          L->top = L->ci->top;
        }
        if (c == 0) c = cast_int(*pc++);
        // 确认 A 是一个 table，取出其中 table 部分的数据
        runtime_check(L, ttistable(ra));
        h = hvalue(ra);
        last = ((c-1)*LFIELDS_PER_FLUSH) + n;
        if (last > h->sizearray)  /* needs more space? */
          luaH_resizearray(L, h, last);  /* pre-alloc it at once */
        for (; n > 0; n--) {
          TValue *val = ra+n;
          setobj2t(L, luaH_setnum(L, h, last--), val);
          luaC_barriert(L, h, val);
        }
        continue;
      }
      case OP_CLOSE: {
        luaF_close(L, ra);
        continue;
      }
      case OP_CLOSURE: {
        Proto *p;
        Closure *ncl;
        int nup, j;
        // cl 是当前函数的 closure
        // Bx 是新函数在当前函数的 proto 数组里的下标
        p = cl->p->p[GETARG_Bx(i)];
        // nups 在语法分析期间即已获得，upvals 的数量，被一并存放在 proto 里
        nup = p->nups;
        // 创建一个新的 closure
        ncl = luaF_newLclosure(L, nup, cl->env);
        ncl->l.p = p;
        // 紧接着 OP_CLOSURE 的必须是 nup 条 OP_GETUPVAL 或者 OP_MOVE 指令
        // 注意每次循环都会自增 pc 吃掉下一条指令
        for (j=0; j<nup; j++, pc++) {
          if (GET_OPCODE(*pc) == OP_GETUPVAL)
            // 如果是 OP_GETUPVAL（更上层函数的局部变量）
            // 从当前函数的 upvals 中拷贝到新函数的 upvals 里
            ncl->l.upvals[j] = cl->upvals[GETARG_B(*pc)];
          else {
            // 如果是 OP_MOVE（当前函数的局部变量）
            // 从当前函数的局部变量转换为 UpVal，然后拷贝到新函数的 upvals 里
            lua_assert(GET_OPCODE(*pc) == OP_MOVE);
            ncl->l.upvals[j] = luaF_findupval(L, base + GETARG_B(*pc));
          }
        }
        // 将新创建的 closure 存放到 ra 中
        setclvalue(L, ra, ncl);
        Protect(luaC_checkGC(L));
        continue;
      }
      case OP_VARARG: {
        // b = B - 1 代表需要的参数数量
        // B = 0 为特殊取值，代表无论传多少参数都全要了
        int b = GETARG_B(i) - 1;
        int j;
        CallInfo *ci = L->ci;
        // n 是实际传入的参数数量
        int n = cast_int(ci->base - ci->func) - cl->p->numparams - 1;
        if (b == LUA_MULTRET) {
          // 当 b == -1，也就是 B == 0 时
          // 设置 b(需要的参数数量) = 传入的参数数量
          // 并调整 L->top 指针，在后续 OP_CALL 可能会用到
          Protect(luaD_checkstack(L, n));
          ra = RA(i);  /* previous call may change the stack */
          b = n;
          L->top = ra + n;
        }
        // 遍历，拷贝传入的参数到 ra + xxx 的地方
        // 如果传入的参数数量小于需要的数量，补上 nil
        for (j = 0; j < b; j++) {
          if (j < n) {
            setobjs2s(L, ra + j, ci->base - n + j);
          }
          else {
            setnilvalue(ra + j);
          }
        }
        continue;
      }
    }
  }
}

