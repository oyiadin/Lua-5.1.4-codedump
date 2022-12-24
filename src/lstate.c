/*
** $Id: lstate.c,v 2.36.1.2 2008/01/03 15:20:39 roberto Exp $
** Global State
** See Copyright Notice in lua.h
*/


#include <stddef.h>

#define lstate_c
#define LUA_CORE

#include "lua.h"

#include "ldebug.h"
#include "ldo.h"
#include "lfunc.h"
#include "lgc.h"
#include "llex.h"
#include "lmem.h"
#include "lstate.h"
#include "lstring.h"
#include "ltable.h"
#include "ltm.h"


#define state_size(x)	(sizeof(x) + LUAI_EXTRASPACE)
#define fromstate(l)	(cast(lu_byte *, (l)) - LUAI_EXTRASPACE)
#define tostate(l)   (cast(lua_State *, cast(lu_byte *, l) + LUAI_EXTRASPACE))


/*
** Main thread combines a thread state and the global state
*/
typedef struct LG {
  lua_State l;
  global_State g;
} LG;
  


// 此函数目前存在两处调用点，一处是创建主线程的 f_luaopen 函数中，一处是创建新线程的 luaE_newthread 函数中
// L1 是新的 lua_State，L 是旧的 lua_State
// 当创建主线程时，两个参数指向的都是同一个 lua_State
static void stack_init (lua_State *L1, lua_State *L) {
  /* initialize CallInfo array */
  // 初始化 CallInfo 数组
  L1->base_ci = luaM_newvector(L, BASIC_CI_SIZE, CallInfo);
  L1->ci = L1->base_ci;
  L1->size_ci = BASIC_CI_SIZE;
  L1->end_ci = L1->base_ci + L1->size_ci - 1;
  /* initialize stack array */
  // 初始化堆栈数组
  L1->stack = luaM_newvector(L, BASIC_STACK_SIZE + EXTRA_STACK, TValue);
  L1->stacksize = BASIC_STACK_SIZE + EXTRA_STACK;
  L1->top = L1->stack;
  L1->stack_last = L1->stack+(L1->stacksize - EXTRA_STACK)-1;
  /* initialize first ci */
  // 初始化首个 CallInfo
  // 将 func 指向 L1->top，也就是 L1->stack，也就是栈底首个元素
  L1->ci->func = L1->top;
  // 将刚才 func 指向的区域给置为 nil，并自增 top
  setnilvalue(L1->top++);  /* `function' entry for this `ci' */
  // 执行这句调用之后, base = top = stack + 1
  // 此时栈上的结构
  //              ???   -+
  //              ...    |  LUA_MINSTACK (20)
  // top, base -> ???   -+
  // ci->func  -> nil
  L1->base = L1->ci->base = L1->top;
  // 这里的意思是,每个lua函数最开始预留LUA_MINSTACK个栈位置,不够的时候再增加,见luaD_checkstack函数
  L1->ci->top = L1->top + LUA_MINSTACK;
}


static void freestack (lua_State *L, lua_State *L1) {
  luaM_freearray(L, L1->base_ci, L1->size_ci, CallInfo);
  luaM_freearray(L, L1->stack, L1->stacksize, TValue);
}


/*
** open parts that may cause memory-allocation errors
*/
// 仅存在一处调用，发生在 lua_newstate 函数中
static void f_luaopen (lua_State *L, void *ud) {
  global_State *g = G(L);
  UNUSED(ud);
  // 初始化堆栈
  stack_init(L, L);  /* init stack */
  // 初始化全局表
  sethvalue(L, gt(L), luaH_new(L, 0, 2));  /* table of globals */
  // 初始化寄存器 TODO
  sethvalue(L, registry(L), luaH_new(L, 0, 2));  /* registry */
  // 初始化字符串表
  luaS_resize(L, MINSTRTABSIZE);  /* initial size of string table */
  // 初始化 tag method 名称列表
  luaT_init(L);
  // 初始化关键字字符串，标记为 reserved
  luaX_init(L);
  // 初始化not enough memory这个字符串并且标记为不可回收
  luaS_fix(luaS_newliteral(L, MEMERRMSG));
  g->GCthreshold = 4*g->totalbytes;
}


static void preinit_state (lua_State *L, global_State *g) {
  // 将 L 里的 l_G 指针置为 g
  G(L) = g;
  // 主要清空各种与栈相关的字段
  L->stack = NULL;
  L->stacksize = 0;
  L->errorJmp = NULL;
  L->hook = NULL;
  L->hookmask = 0;
  L->basehookcount = 0;
  L->allowhook = 1;
  resethookcount(L);
  L->openupval = NULL;
  L->size_ci = 0;
  L->nCcalls = L->baseCcalls = 0;
  L->status = 0;
  L->base_ci = L->ci = NULL;
  L->savedpc = NULL;
  L->errfunc = 0;
  // 清空 global table
  setnilvalue(gt(L));
}


static void close_state (lua_State *L) {
  global_State *g = G(L);
  luaF_close(L, L->stack);  /* close all upvalues for this thread */
  luaC_freeall(L);  /* collect all objects */
  lua_assert(g->rootgc == obj2gco(L));
  lua_assert(g->strt.nuse == 0);
  luaM_freearray(L, G(L)->strt.hash, G(L)->strt.size, TString *);
  luaZ_freebuffer(L, &g->buff);
  freestack(L, L);
  lua_assert(g->totalbytes == sizeof(LG));
  (*g->frealloc)(g->ud, fromstate(L), state_size(LG), 0);
}


lua_State *luaE_newthread (lua_State *L) {
  lua_State *L1 = tostate(luaM_malloc(L, state_size(lua_State)));
  luaC_link(L, obj2gco(L1), LUA_TTHREAD);
  preinit_state(L1, G(L));
  stack_init(L1, L);  /* init stack */
  setobj2n(L, gt(L1), gt(L));  /* share table of globals */
  L1->hookmask = L->hookmask;
  L1->basehookcount = L->basehookcount;
  L1->hook = L->hook;
  resethookcount(L1);
  lua_assert(iswhite(obj2gco(L1)));
  return L1;
}


void luaE_freethread (lua_State *L, lua_State *L1) {
  luaF_close(L1, L1->stack);  /* close all upvalues for this thread */
  lua_assert(L1->openupval == NULL);
  luai_userstatefree(L1);
  freestack(L, L1);
  luaM_freemem(L, fromstate(L1), state_size(lua_State));
}


// 创建并初始化一个新的 lua_State 对象（以及 global_State 对象）
// 用于创建主线程时一起创建 lua_State 与 global_State
LUA_API lua_State *lua_newstate (lua_Alloc f, void *ud) {
  int i;
  lua_State *L;
  global_State *g;
  // 用传入的 lua_Alloc 函数创建一块内存用以放置 lua_State 跟 global_State
  // state_size 展开来是 (sizeof(LG) + LUAI_EXTRASPACE)
  // LG 是一个仅包含了 lua_State 跟 global_State 的结构体
  // LUAI_EXTRASPACE 是一个用户可以指定的常量，默认为 0，作用是定制 Lua 解释器时可以借助这个宏在 lua_State 里扩充自己的字段
  void *l = (*f)(ud, NULL, 0, state_size(LG));
  // 这里创建出来是 lua_State + global_State + LUAI_EXTRASPACE(默认为0) 的大小
  // 当另开新线程时，使用的是 lua_newthread，仅创建 lua_State，与已有的线程共享 global_State
  if (l == NULL) return NULL;
  L = tostate(l);
  g = &((LG *)L)->g;
  // 清空、初始化 L 跟 g 的各种字段
  // GC 部分，标记为白色，等后边研究 GC 再讨论
  L->next = NULL;
  L->tt = LUA_TTHREAD;
  g->currentwhite = bit2mask(WHITE0BIT, FIXEDBIT);
  L->marked = luaC_white(g);
  // 标记刚创建的 lua_State 对象为不可回收
  set2bits(L->marked, FIXEDBIT, SFIXEDBIT);
  // 主要初始化一些栈相关的字段
  preinit_state(L, g);
  g->frealloc = f;
  g->ud = ud;
  // 全局状态结构体里，主线程置为当前 lua_State
  g->mainthread = L;
  g->uvhead.u.l.prev = &g->uvhead;
  g->uvhead.u.l.next = &g->uvhead;
  g->GCthreshold = 0;  /* mark it as unfinished state */
  // 全局字符串表，Lua 里的字符串都是「内化」（interned）的
  // 所有相同取值的字符串有且仅有一个实例，被记录在 strt 全局字符串表中
  g->strt.size = 0;
  g->strt.nuse = 0;
  g->strt.hash = NULL;
  setnilvalue(registry(L));
  luaZ_initbuffer(L, &g->buff);
  g->panic = NULL;
  // GC 相关的字段
  g->gcstate = GCSpause;
  g->rootgc = obj2gco(L);
  g->sweepstrgc = 0;
  g->sweepgc = &g->rootgc;
  g->gray = NULL;
  g->grayagain = NULL;
  g->weak = NULL;
  g->tmudata = NULL;
  g->totalbytes = sizeof(LG);
  g->gcpause = LUAI_GCPAUSE;
  g->gcstepmul = LUAI_GCMUL;
  g->gcdept = 0;
  // 清空全局元表
  // g->mt 的元素与各个类型一一对应，如 LUA_TNUMBER、LUA_TSTRING 等
  for (i=0; i<NUM_TAGS; i++) g->mt[i] = NULL;
  if (luaD_rawrunprotected(L, f_luaopen, NULL) != 0) {
    /* memory allocation error: free partial state */
    close_state(L);
    L = NULL;
  }
  else
    luai_userstateopen(L);
  return L;
}


static void callallgcTM (lua_State *L, void *ud) {
  UNUSED(ud);
  luaC_callGCTM(L);  /* call GC metamethods for all udata */
}


LUA_API void lua_close (lua_State *L) {
  L = G(L)->mainthread;  /* only the main thread can be closed */
  lua_lock(L);
  luaF_close(L, L->stack);  /* close all upvalues for this thread */
  luaC_separateudata(L, 1);  /* separate udata that have GC metamethods */
  L->errfunc = 0;  /* no error function during GC metamethods */
  do {  /* repeat until no more errors */
    L->ci = L->base_ci;
    L->base = L->top = L->ci->base;
    L->nCcalls = L->baseCcalls = 0;
  } while (luaD_rawrunprotected(L, callallgcTM, NULL) != 0);
  lua_assert(G(L)->tmudata == NULL);
  luai_userstateclose(L);
  close_state(L);
}

