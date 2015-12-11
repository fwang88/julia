/*
  femtoLisp

  a compact interpreter for a minimal lisp/scheme dialect

  characteristics:
  * lexical scope, lisp-1
  * unrestricted macros
  * data types: 30-bit integer, symbol, pair, vector, char, string, table
      iostream, procedure, low-level data types
  * case-sensitive
  * simple compacting copying garbage collector
  * Scheme-style varargs (dotted formal argument lists)
  * "human-readable" bytecode with self-hosted compiler

  extra features:
  * circular structure can be printed and read
  * #. read macro for eval-when-read and readably printing builtins
  * read macros for backquote
  * symbol character-escaping printer
  * exceptions
  * gensyms (can be usefully read back in, too)
  * #| multiline comments |#, lots of other lexical syntax
  * generic compare function, cyclic equal
  * cvalues system providing C data types and a C FFI
  * constructor notation for nicely printing arbitrary values

  by Jeff Bezanson (C) 2009
  Distributed under the BSD License
*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <setjmp.h>
#include <stdint.h>
#include <stdarg.h>
#include <assert.h>
#include <ctype.h>
#include <wctype.h>
#include <sys/types.h>
#include <locale.h>
#include <limits.h>
#include <errno.h>

#include "platform.h"
#include "libsupport.h"
#include "flisp.h"
#include "opcodes.h"

#ifdef __cplusplus
extern "C" {
#endif

#if defined(_OS_WINDOWS_) && !defined(_COMPILER_MINGW_)
#include <malloc.h>
JL_DLLEXPORT char * dirname(char *);
#else
#include <libgen.h>
#endif

static char *const builtin_names[] =
    { NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
      NULL, NULL, NULL, NULL,
      // predicates
      "eq?", "eqv?", "equal?", "atom?", "not", "null?", "boolean?", "symbol?",
      "number?", "bound?", "pair?", "builtin?", "vector?", "fixnum?",
      "function?",

      // lists
      "cons", "list", "car", "cdr", "set-car!", "set-cdr!",

      // execution
      "apply",

      // arithmetic
      "+", "-", "*", "/", "div0", "=", "<", "compare",

      // sequences
      "vector", "aref", "aset!",
      "", "", "" };

#define ANYARGS -10000

static const short builtin_arg_counts[] =
    { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      2, ANYARGS, 1, 1, 2, 2,
      -2,
      ANYARGS, -1, ANYARGS, -1, 2,  2, 2, 2,
      ANYARGS, 2, 3 };

#define FL_N_STACK fl_global_ctx->N_STACK
#define fl_Stack fl_global_ctx->Stack
#define FL_SP fl_global_ctx->SP
#define fl_curr_frame fl_global_ctx->curr_frame
#define PUSH(v) (fl_Stack[FL_SP++] = (v))
#define POP()   (fl_Stack[--FL_SP])
#define POPN(n) (FL_SP-=(n))

#define fl_GCHandleStack fl_global_ctx->GCHandleStack
#define FL_N_GCHND fl_global_ctx->N_GCHND

#define FL_LAMBDA fl_global_ctx->LAMBDA
#define FL_IF fl_global_ctx->IF
#define FL_TRYCATCH fl_global_ctx->TRYCATCH
#define FL_BACKQUOTE fl_global_ctx->BACKQUOTE
#define FL_COMMA fl_global_ctx->COMMA
#define FL_COMMAAT fl_global_ctx->COMMAAT
#define FL_COMMADOT fl_global_ctx->COMMADOT
#define FL_FUNCTION fl_global_ctx->FUNCTION

#define fl_pairsym fl_global_ctx->pairsym
#define fl_symbolsym fl_global_ctx->symbolsym
#define fl_fixnumsym fl_global_ctx->fixnumsym
#define fl_vectorsym fl_global_ctx->vectorsym
#define fl_builtinsym fl_global_ctx->builtinsym
#define fl_vu8sym fl_global_ctx->vu8sym
#define fl_definesym fl_global_ctx->definesym
#define fl_defmacrosym fl_global_ctx->defmacrosym
#define fl_forsym fl_global_ctx->forsym
#define fl_setqsym fl_global_ctx->setqsym
#define fl_tsym fl_global_ctx->tsym
#define fl_Tsym fl_global_ctx->Tsym
#define fl_fsym fl_global_ctx->fsym
#define fl_Fsym fl_global_ctx->Fsym
#define fl_booleansym fl_global_ctx->booleansym
#define fl_nullsym fl_global_ctx->nullsym
#define fl_evalsym fl_global_ctx->evalsym
#define fl_fnsym fl_global_ctx->fnsym
#define fl_nulsym fl_global_ctx->nulsym
#define fl_alarmsym fl_global_ctx->alarmsym
#define fl_backspacesym fl_global_ctx->backspacesym
#define fl_tabsym fl_global_ctx->tabsym
#define fl_linefeedsym fl_global_ctx->linefeedsym
#define fl_newlinesym fl_global_ctx->newlinesym
#define fl_vtabsym fl_global_ctx->vtabsym
#define fl_pagesym fl_global_ctx->pagesym
#define fl_returnsym fl_global_ctx->returnsym
#define fl_escsym fl_global_ctx->escsym
#define fl_spacesym fl_global_ctx->spacesym
#define fl_deletesym fl_global_ctx->deletesym

static value_t apply_cl(uint32_t nargs);
static value_t apply_cl_ctx(fl_global_context_t *global_ctx, uint32_t nargs);
static value_t *alloc_words(int n);
static value_t relocate(value_t v);

typedef struct _fl_readstate_t {
    htable_t backrefs;
    htable_t gensyms;
    value_t source;
    struct _fl_readstate_t *prev;
} fl_readstate_t;

#define fl_readstate fl_global_ctx->readstate

static void free_readstate(fl_readstate_t *rs)
{
    htable_free(&rs->backrefs);
    htable_free(&rs->gensyms);
}

#define fl_fromspace fl_global_ctx->fromspace
#define fl_tospace fl_global_ctx->tospace
#define fl_curheap fl_global_ctx->curheap
#define fl_lim fl_global_ctx->lim
#define fl_heapsize fl_global_ctx->heapsize    //bytes
#define fl_consflags fl_global_ctx->consflags

// error utilities ------------------------------------------------------------

#define FL_TRY \
  fl_exception_context_t _ctx; int l__tr, l__ca; \
  _ctx.sp=FL_SP; _ctx.frame=fl_curr_frame; _ctx.rdst=fl_readstate; _ctx.prev=fl_ctx; \
  _ctx.ngchnd = FL_N_GCHND; fl_ctx = &_ctx;                                    \
  if (!setjmp(_ctx.buf)) \
    for (l__tr=1; l__tr; l__tr=0, (void)(fl_ctx=fl_ctx->prev))

#define FL_CATCH \
  else \
    for(l__ca=1; l__ca; l__ca=0, \
      fl_lasterror=FL_NIL,fl_throwing_frame=0,FL_SP=_ctx.sp,fl_curr_frame=_ctx.frame)

void fl_savestate(fl_exception_context_t *_ctx)
{
    _ctx->sp = FL_SP;
    _ctx->frame = fl_curr_frame;
    _ctx->rdst = fl_readstate;
    _ctx->prev = fl_ctx;
    _ctx->ngchnd = FL_N_GCHND;
}

void fl_restorestate(fl_exception_context_t *_ctx)
{
    fl_lasterror = FL_NIL;
    fl_throwing_frame = 0;
    FL_SP = _ctx->sp;
    fl_curr_frame = _ctx->frame;
}

void fl_raise(value_t e)
{
    fl_lasterror = e;
    // unwind read state
    while (fl_readstate != (fl_readstate_t*)fl_ctx->rdst) {
        free_readstate(fl_readstate);
        fl_readstate = fl_readstate->prev;
    }
    if (fl_throwing_frame == 0)
        fl_throwing_frame = fl_curr_frame;
    FL_N_GCHND = fl_ctx->ngchnd;
    fl_exception_context_t *thisctx = fl_ctx;
    if (fl_ctx->prev)   // don't throw past toplevel
        fl_ctx = fl_ctx->prev;
    longjmp(thisctx->buf, 1);
}

static value_t make_error_msg(char *format, va_list args)
{
    char msgbuf[512];
    vsnprintf(msgbuf, sizeof(msgbuf), format, args);
    return string_from_cstr(msgbuf);
}

void lerrorf(value_t e, char *format, ...)
{
    va_list args;
    PUSH(e);
    va_start(args, format);
    value_t msg = make_error_msg(format, args);
    va_end(args);

    e = POP();
    fl_raise(fl_list2(e, msg));
}

void lerror(value_t e, const char *msg)
{
    PUSH(e);
    value_t m = cvalue_static_cstring(msg);
    e = POP();
    fl_raise(fl_list2(e, m));
}

void type_error(char *fname, char *expected, value_t got)
{
    fl_raise(fl_listn(4, fl_TypeError, symbol(fname), symbol(expected), got));
}

void bounds_error(char *fname, value_t arr, value_t ind)
{
    fl_raise(fl_listn(4, fl_BoundsError, symbol(fname), arr, ind));
}

// safe cast operators --------------------------------------------------------

#define isstring fl_isstring
#define SAFECAST_OP(type,ctype,cnvt)                                          \
ctype to##type(value_t v, char *fname)                                        \
{                                                                             \
    if (is##type(v))                                                          \
        return (ctype)cnvt(v);                                                \
    type_error(fname, #type, v);                                              \
}
SAFECAST_OP(cons,  cons_t*,  ptr)
SAFECAST_OP(symbol,symbol_t*,ptr)
SAFECAST_OP(fixnum,fixnum_t, numval)
SAFECAST_OP(cvalue,cvalue_t*,ptr)
SAFECAST_OP(string,char*,    cvalue_data)
#undef isstring

// symbol table ---------------------------------------------------------------

JL_DLLEXPORT fl_global_context_t *pfl_global_ctx = NULL;

int fl_is_keyword_name(const char *str, size_t len)
{
    return len>1 && ((str[0] == ':' || str[len-1] == ':') && str[1] != '\0');
}

#define CHECK_ALIGN8(p) assert((((uptrint_t)(p))&0x7)==0 && "flisp requires malloc to return 8-aligned pointers")

static symbol_t *mk_symbol(const char *str)
{
    symbol_t *sym;
    size_t len = strlen(str);

    sym = (symbol_t*)malloc((offsetof(symbol_t,name)+len+1+7)&-8);
    CHECK_ALIGN8(sym);
    sym->left = sym->right = NULL;
    sym->flags = 0;
    if (fl_is_keyword_name(str, len)) {
        value_t s = tagptr(sym, TAG_SYM);
        setc(s, s);
        sym->flags |= 0x2;
    }
    else {
        sym->binding = UNBOUND;
    }
    sym->type = NULL;
    sym->dlcache = NULL;
    sym->hash = memhash32(str, len)^0xAAAAAAAA;
    strcpy(&sym->name[0], str);
    return sym;
}

static symbol_t **symtab_lookup(symbol_t **ptree, const char *str)
{
    int x;

    while (*ptree != NULL) {
        x = strcmp(str, (*ptree)->name);
        if (x == 0)
            return ptree;
        if (x < 0)
            ptree = &(*ptree)->left;
        else
            ptree = &(*ptree)->right;
    }
    return ptree;
}

value_t symbol(char *str)
{
    symbol_t **pnode = symtab_lookup(&fl_symtab, str);
    if (*pnode == NULL)
        *pnode = mk_symbol(str);
    return tagptr(*pnode, TAG_SYM);
}

#define fl_gensym_ctr fl_global_ctx->gensym_ctr
#define fl_gsname fl_global_ctx->gsname
#define fl_gsnameno fl_global_ctx->gsnameno
value_t fl_gensym(value_t *args, uint32_t nargs)
{
#ifdef MEMDEBUG2
    fl_gsnameno = 1-fl_gsnameno;
    char *n = uint2str(fl_gsname[fl_gsnameno]+1, sizeof(fl_gsname[0])-1, fl_gensym_ctr++, 10);
    *(--n) = 'g';
    return tagptr(mk_symbol(n), TAG_SYM);
#else
    argcount("gensym", nargs, 0);
    (void)args;
    gensym_t *gs = (gensym_t*)alloc_words(sizeof(gensym_t)/sizeof(void*));
    gs->id = fl_gensym_ctr++;
    gs->binding = UNBOUND;
    gs->isconst = 0;
    gs->type = NULL;
    return tagptr(gs, TAG_SYM);
#endif
}

int fl_isgensym(value_t v)
{
    return isgensym(v);
}

static value_t fl_gensymp(value_t *args, u_int32_t nargs)
{
    argcount("gensym?", nargs, 1);
    return isgensym(args[0]) ? FL_T : FL_F;
}

char *symbol_name(value_t v)
{
#ifndef MEMDEBUG2
    if (ismanaged(v)) {
        gensym_t *gs = (gensym_t*)ptr(v);
        fl_gsnameno = 1-fl_gsnameno;
        char *n = uint2str(fl_gsname[fl_gsnameno]+1, sizeof(fl_gsname[0])-1, gs->id, 10);
        *(--n) = 'g';
        return n;
    }
#endif
    return ((symbol_t*)ptr(v))->name;
}

// conses ---------------------------------------------------------------------

#ifdef MEMDEBUG2
#define fl_tochain fl_global_ctx->tochain
#define fl_n_allocd fl_global_ctx->n_allocd
#define GC_INTERVAL 100000
#endif

void gc(int mustgrow);

static value_t mk_cons(void)
{
    cons_t *c;

#ifdef MEMDEBUG2
    if (fl_n_allocd > GC_INTERVAL)
        gc(0);
    c = (cons_t*)((void**)malloc(3*sizeof(void*)) + 1);
    CHECK_ALIGN8(c);
    ((void**)c)[-1] = fl_tochain;
    fl_tochain = c;
    fl_n_allocd += sizeof(cons_t);
#else
    if (__unlikely(fl_curheap > fl_lim))
        gc(0);
    c = (cons_t*)fl_curheap;
    fl_curheap += sizeof(cons_t);
#endif
    return tagptr(c, TAG_CONS);
}

static value_t *alloc_words(int n)
{
    value_t *first;

    assert(n > 0);
    n = LLT_ALIGN(n, 2);   // only allocate multiples of 2 words
#ifdef MEMDEBUG2
    if (fl_n_allocd > GC_INTERVAL)
        gc(0);
    first = (value_t*)malloc((n+1)*sizeof(value_t)) + 1;
    CHECK_ALIGN8(first);
    first[-1] = (value_t)fl_tochain;
    fl_tochain = first;
    fl_n_allocd += (n*sizeof(value_t));
#else
    if (__unlikely((value_t*)fl_curheap > ((value_t*)fl_lim)+2-n)) {
        gc(0);
        while ((value_t*)fl_curheap > ((value_t*)fl_lim)+2-n) {
            gc(1);
        }
    }
    first = (value_t*)fl_curheap;
    fl_curheap += (n*sizeof(value_t));
#endif
    return first;
}

// allocate n consecutive conses
#ifndef MEMDEBUG2
#define cons_reserve(n) tagptr(alloc_words((n)*2), TAG_CONS)
#endif

#ifndef MEMDEBUG2
#define cons_index(c)  (((cons_t*)ptr(c))-((cons_t*)fl_fromspace))
#endif

#ifdef MEMDEBUG2
#define ismarked(c)    ((((value_t*)ptr(c))[-1]&1) != 0)
#define mark_cons(c)   ((((value_t*)ptr(c))[-1]) |= 1)
#define unmark_cons(c) ((((value_t*)ptr(c))[-1]) &= (~(value_t)1))
#else
#define ismarked(c)    bitvector_get(fl_consflags, cons_index(c))
#define mark_cons(c)   bitvector_set(fl_consflags, cons_index(c), 1)
#define unmark_cons(c) bitvector_set(fl_consflags, cons_index(c), 0)
#endif

#define fl_the_empty_vector fl_global_ctx->the_empty_vector

value_t alloc_vector(size_t n, int init)
{
    if (n == 0) return fl_the_empty_vector;
    value_t *c = alloc_words(n+1);
    value_t v = tagptr(c, TAG_VECTOR);
    vector_setsize(v, n);
    if (init) {
        unsigned int i;
        for(i=0; i < n; i++)
            vector_elt(v, i) = FL_UNSPECIFIED;
    }
    return v;
}

// cvalues --------------------------------------------------------------------

#include "cvalues.c"
#include "types.c"

// print ----------------------------------------------------------------------

static int isnumtok(char *tok, value_t *pval);
static inline int symchar(char c);

#include "print.c"

// collector ------------------------------------------------------------------

void fl_gc_handle(value_t *pv)
{
    if (FL_N_GCHND >= FL_N_GC_HANDLES)
        lerror(fl_OutOfMemoryError, "out of gc handles");
    fl_GCHandleStack[FL_N_GCHND++] = pv;
}

void fl_free_gc_handles(uint32_t n)
{
    assert(FL_N_GCHND >= n);
    FL_N_GCHND -= n;
}

value_t relocate_lispvalue(value_t v)
{
    return relocate(v);
}

static void trace_globals(symbol_t *root)
{
    while (root != NULL) {
        if (root->binding != UNBOUND)
            root->binding = relocate(root->binding);
        trace_globals(root->left);
        root = root->right;
    }
}

#undef fl_global_ctx
#define fl_global_ctx global_ctx

static value_t relocate(value_t v)
{
    fl_global_context_t *global_ctx = pfl_global_ctx;
    value_t a, d, nc, first, *pcdr;
    uptrint_t t = tag(v);

    if (t == TAG_CONS) {
        // iterative implementation allows arbitrarily long cons chains
        pcdr = &first;
        do {
            if ((a=car_(v)) == TAG_FWD) {
                *pcdr = cdr_(v);
                return first;
            }
#ifdef MEMDEBUG2
            *pcdr = nc = mk_cons();
#else
            *pcdr = nc = tagptr((cons_t*)fl_curheap, TAG_CONS);
            fl_curheap += sizeof(cons_t);
#endif
            d = cdr_(v);
            car_(v) = TAG_FWD; cdr_(v) = nc;
            if ((tag(a)&3) == 0 || !ismanaged(a))
                car_(nc) = a;
            else
                car_(nc) = relocate(a);
            pcdr = &cdr_(nc);
            v = d;
        } while (iscons(v));
        *pcdr = (d==FL_NIL) ? FL_NIL : relocate(d);
        return first;
    }

    if ((t&3) == 0 || !ismanaged(v)) return v;
    if (isforwarded(v)) return forwardloc(v);

    if (t == TAG_VECTOR) {
        // N.B.: 0-length vectors secretly have space for a first element
        size_t i, sz = vector_size(v);
        if (vector_elt(v,-1) & 0x1) {
            // grown vector
            nc = relocate(vector_elt(v,0));
            forward(v, nc);
        }
        else {
            nc = tagptr(alloc_words(sz+1), TAG_VECTOR);
            vector_setsize(nc, sz);
            a = vector_elt(v,0);
            forward(v, nc);
            if (sz > 0) {
                vector_elt(nc,0) = relocate(a);
                for(i=1; i < sz; i++) {
                    a = vector_elt(v,i);
                    if ((tag(a)&3) == 0 || !ismanaged(a))
                        vector_elt(nc,i) = a;
                    else
                        vector_elt(nc,i) = relocate(a);
                }
            }
        }
        return nc;
    }
    else if (t == TAG_CPRIM) {
        cprim_t *pcp = (cprim_t*)ptr(v);
        size_t nw = CPRIM_NWORDS-1+NWORDS(cp_class(pcp)->size);
        cprim_t *ncp = (cprim_t*)alloc_words(nw);
        while (nw--)
            ((value_t*)ncp)[nw] = ((value_t*)pcp)[nw];
        nc = tagptr(ncp, TAG_CPRIM);
        forward(v, nc);
        return nc;
    }
    else if (t == TAG_CVALUE) {
        return cvalue_relocate(v);
    }
    else if (t == TAG_FUNCTION) {
        function_t *fn = (function_t*)ptr(v);
        function_t *nfn = (function_t*)alloc_words(4);
        nfn->bcode = fn->bcode;
        nfn->vals = fn->vals;
        nc = tagptr(nfn, TAG_FUNCTION);
        forward(v, nc);
        nfn->env = relocate(fn->env);
        nfn->vals = relocate(nfn->vals);
        nfn->bcode = relocate(nfn->bcode);
        nfn->name = fn->name;
        return nc;
    }
    else if (t == TAG_SYM) {
        gensym_t *gs = (gensym_t*)ptr(v);
        gensym_t *ng = (gensym_t*)alloc_words(sizeof(gensym_t)/sizeof(void*));
        ng->id = gs->id;
        ng->binding = gs->binding;
        ng->isconst = 0;
        nc = tagptr(ng, TAG_SYM);
        forward(v, nc);
        if (ng->binding != UNBOUND)
            ng->binding = relocate(ng->binding);
        return nc;
    }
    return v;
}

#define fl_memory_exception_value fl_global_ctx->memory_exception_value
#define fl_gc_grew fl_global_ctx->gc_grew

void gc(int mustgrow)
{
    fl_global_context_t *global_ctx = pfl_global_ctx;
    void *temp;
    uint32_t i, f, top;
    fl_readstate_t *rs;
#ifdef MEMDEBUG2
    temp = fl_tochain;
    fl_tochain = NULL;
    fl_n_allocd = -100000000000LL;
#else
    size_t hsz = fl_gc_grew ? fl_heapsize*2 : fl_heapsize;
#ifdef MEMDEBUG
    fl_tospace = LLT_ALLOC(hsz);
#endif
    fl_curheap = fl_tospace;
    fl_lim = fl_curheap + hsz - sizeof(cons_t);
#endif

    if (fl_throwing_frame > fl_curr_frame) {
        top = fl_throwing_frame - 3;
        f = fl_Stack[fl_throwing_frame-3];
    }
    else {
        top = FL_SP;
        f = fl_curr_frame;
    }
    while (1) {
        for (i=f; i < top; i++)
            fl_Stack[i] = relocate(fl_Stack[i]);
        if (f == 0) break;
        top = f - 3;
        f = fl_Stack[f-3];
    }
    for (i=0; i < FL_N_GCHND; i++)
        *fl_GCHandleStack[i] = relocate(*fl_GCHandleStack[i]);
    trace_globals(fl_symtab);
    relocate_typetable();
    rs = fl_readstate;
    while (rs) {
        for(i=0; i < rs->backrefs.size; i++)
            rs->backrefs.table[i] = (void*)relocate((value_t)rs->backrefs.table[i]);
        for(i=0; i < rs->gensyms.size; i++)
            rs->gensyms.table[i] = (void*)relocate((value_t)rs->gensyms.table[i]);
        rs->source = relocate(rs->source);
        rs = rs->prev;
    }
    fl_lasterror = relocate(fl_lasterror);
    fl_memory_exception_value = relocate(fl_memory_exception_value);
    fl_the_empty_vector = relocate(fl_the_empty_vector);

    sweep_finalizers();

#ifdef MEMDEBUG2
    while (temp != NULL) {
        void *next = ((void**)temp)[-1];
        free(&((void**)temp)[-1]);
        temp = next;
    }
    fl_n_allocd = 0;
#else
#ifdef VERBOSEGC
    printf("GC: found %d/%d live conses\n",
           (fl_curheap-fl_tospace)/sizeof(cons_t), fl_heapsize/sizeof(cons_t));
#endif

    temp = fl_tospace;
    fl_tospace = fl_fromspace;
    fl_fromspace = (unsigned char*)temp;

    // if we're using > 80% of the space, resize tospace so we have
    // more space to fill next time. if we grew tospace last time,
    // grow the other half of the heap this time to catch up.
    if (fl_gc_grew || mustgrow
#ifdef MEMDEBUG
        // GC more often
        || ((fl_lim-fl_curheap) < (int)(fl_heapsize/128))
#else
        || ((fl_lim-fl_curheap) < (int)(fl_heapsize/5))
#endif
        ) {
        temp = LLT_REALLOC(fl_tospace, fl_heapsize*2);
        if (temp == NULL)
            fl_raise(fl_memory_exception_value);
        fl_tospace = (unsigned char*)temp;
        if (fl_gc_grew) {
            fl_heapsize*=2;
            temp = bitvector_resize(fl_consflags, 0, fl_heapsize/sizeof(cons_t), 1);
            if (temp == NULL)
                fl_raise(fl_memory_exception_value);
            fl_consflags = (uint32_t*)temp;
        }
        fl_gc_grew = !fl_gc_grew;
    }
#ifdef MEMDEBUG
    LLT_FREE(fl_tospace);
#endif
    if ((value_t*)fl_curheap > ((value_t*)fl_lim)-2) {
        // all data was live; gc again and grow heap.
        // but also always leave at least 4 words available, so a closure
        // can be allocated without an extra check.
        gc(0);
    }
#endif
}

static void grow_stack(fl_global_context_t *global_ctx)
{
    size_t newsz = FL_N_STACK + (FL_N_STACK>>1);
    value_t *ns = (value_t*)realloc(fl_Stack, newsz*sizeof(value_t));
    if (ns == NULL)
        lerror(fl_OutOfMemoryError, "stack overflow");
    fl_Stack = ns;
    FL_N_STACK = newsz;
}

// utils ----------------------------------------------------------------------

// apply function with n args on the stack
static value_t _applyn(fl_global_context_t *global_ctx, uint32_t n)
{
    value_t f = fl_Stack[FL_SP-n-1];
    uint32_t saveSP = FL_SP;
    value_t v;
    if (iscbuiltin(f)) {
        v = ((builtin_t*)ptr(f))[3](&fl_Stack[FL_SP-n], n);
    }
    else if (isfunction(f)) {
        v = apply_cl(n);
    }
    else if (isbuiltin(f)) {
        value_t tab = symbol_value(fl_builtins_table_sym);
        fl_Stack[FL_SP-n-1] = vector_elt(tab, uintval(f));
        v = apply_cl(n);
    }
    else {
        type_error("apply", "function", f);
    }
    FL_SP = saveSP;
    return v;
}

value_t fl_apply(value_t f, value_t l)
{
    fl_global_context_t *global_ctx = pfl_global_ctx;
    value_t v = l;
    uint32_t n = FL_SP;

    PUSH(f);
    while (iscons(v)) {
        if (FL_SP >= FL_N_STACK)
            grow_stack(global_ctx);
        PUSH(car_(v));
        v = cdr_(v);
    }
    n = FL_SP - n - 1;
    v = _applyn(global_ctx, n);
    POPN(n+1);
    return v;
}

value_t fl_applyn(uint32_t n, value_t f, ...)
{
    fl_global_context_t *global_ctx = pfl_global_ctx;
    va_list ap;
    va_start(ap, f);
    size_t i;

    PUSH(f);
    while (FL_SP+n > FL_N_STACK)
        grow_stack(global_ctx);
    for(i=0; i < n; i++) {
        value_t a = va_arg(ap, value_t);
        PUSH(a);
    }
    value_t v = _applyn(global_ctx, n);
    POPN(n+1);
    va_end(ap);
    return v;
}

value_t fl_listn(size_t n, ...)
{
    fl_global_context_t *global_ctx = pfl_global_ctx;
    va_list ap;
    va_start(ap, n);
    uint32_t si = FL_SP;
    size_t i;

    while (FL_SP+n > FL_N_STACK)
        grow_stack(global_ctx);
    for(i=0; i < n; i++) {
        value_t a = va_arg(ap, value_t);
        PUSH(a);
    }
#ifdef MEMDEBUG2
    si = FL_SP-1;
    value_t l = FL_NIL;
    for(i=0; i < n; i++) {
        l = fl_cons(fl_Stack[si--], l);
    }
    POPN(n);
    va_end(ap);
    return l;
#else
    cons_t *c = (cons_t*)alloc_words(n*2);
    cons_t *l = c;
    for(i=0; i < n; i++) {
        c->car = fl_Stack[si++];
        c->cdr = tagptr(c+1, TAG_CONS);
        c++;
    }
    (c-1)->cdr = FL_NIL;
    POPN(n);
    va_end(ap);
    return tagptr(l, TAG_CONS);
#endif
}

value_t fl_list2(value_t a, value_t b)
{
    fl_global_context_t *global_ctx = pfl_global_ctx;
    PUSH(a);
    PUSH(b);
#ifdef MEMDEBUG2
    fl_Stack[FL_SP-1] = fl_cons(b, FL_NIL);
    a = fl_cons(fl_Stack[FL_SP-2], fl_Stack[FL_SP-1]);
    POPN(2);
    return a;
#else
    cons_t *c = (cons_t*)alloc_words(4);
    b = POP();
    a = POP();
    c[0].car = a;
    c[0].cdr = tagptr(c+1, TAG_CONS);
    c[1].car = b;
    c[1].cdr = FL_NIL;
    return tagptr(c, TAG_CONS);
#endif
}

value_t fl_cons(value_t a, value_t b)
{
    fl_global_context_t *global_ctx = pfl_global_ctx;
    PUSH(a);
    PUSH(b);
    value_t c = mk_cons();
    cdr_(c) = POP();
    car_(c) = POP();
    return c;
}

int fl_isnumber(value_t v)
{
    fl_global_context_t *global_ctx = pfl_global_ctx;
    if (isfixnum(v)) return 1;
    if (iscprim(v)) {
        cprim_t *c = (cprim_t*)ptr(v);
        return c->type != fl_wchartype;
    }
    return 0;
}
#undef fl_global_ctx
#define fl_global_ctx (pfl_global_ctx)

// read -----------------------------------------------------------------------

#include "read.c"

// equal ----------------------------------------------------------------------

#include "equal.c"

// eval -----------------------------------------------------------------------

#define list(a,n) _list((a),(n),0)

static value_t _list(value_t *args, uint32_t nargs, int star)
{
    cons_t *c;
    int i;
    value_t v;
#ifdef MEMDEBUG2
    value_t n;
    i = nargs-1;
    if (star) {
        n = mk_cons();
        c = (cons_t*)ptr(n);
        c->car = args[i-1];
        c->cdr = args[i];
        i -= 2;
        v = n;
    }
    else {
        v = FL_NIL;
    }
    PUSH(v);
    for(; i >= 0; i--) {
        n = mk_cons();
        c = (cons_t*)ptr(n);
        c->car = args[i];
        c->cdr = fl_Stack[FL_SP-1];
        fl_Stack[FL_SP-1] = n;
    }
    v = POP();
#else
    v = cons_reserve(nargs);
    c = (cons_t*)ptr(v);
    for(i=0; i < nargs; i++) {
        c->car = args[i];
        c->cdr = tagptr(c+1, TAG_CONS);
        c++;
    }
    if (star)
        (c-2)->cdr = (c-1)->car;
    else
        (c-1)->cdr = FL_NIL;
#endif
    return v;
}

static value_t copy_list(value_t L)
{
    if (!iscons(L))
        return FL_NIL;
    PUSH(FL_NIL);
    PUSH(L);
    value_t *plcons = &fl_Stack[FL_SP-2];
    value_t *pL = &fl_Stack[FL_SP-1];
    value_t c;
    c = mk_cons(); PUSH(c);  // save first cons
    car_(c) = car_(*pL);
    cdr_(c) = FL_NIL;
    *plcons = c;
    *pL = cdr_(*pL);
    while (iscons(*pL)) {
        c = mk_cons();
        car_(c) = car_(*pL);
        cdr_(c) = FL_NIL;
        cdr_(*plcons) = c;
        *plcons = c;
        *pL = cdr_(*pL);
    }
    c = POP();  // first cons
    POPN(2);
    return c;
}

#undef fl_global_ctx
#define fl_global_ctx global_ctx
static value_t do_trycatch(fl_global_context_t *global_ctx)
{
    uint32_t saveSP = FL_SP;
    value_t v;
    value_t thunk = fl_Stack[FL_SP-2];
    fl_Stack[FL_SP-2] = fl_Stack[FL_SP-1];
    fl_Stack[FL_SP-1] = thunk;

    FL_TRY {
        v = apply_cl_ctx(global_ctx, 0);
    }
    FL_CATCH {
        v = fl_Stack[saveSP-2];
        PUSH(v);
        PUSH(fl_lasterror);
        v = apply_cl_ctx(global_ctx, 1);
    }
    FL_SP = saveSP;
    return v;
}

/*
  argument layout on stack is
  |--required args--|--opt args--|--kw args--|--rest args...
*/
static uint32_t process_keys(fl_global_context_t *global_ctx, value_t kwtable,
                             uint32_t nreq, uint32_t nkw, uint32_t nopt,
                             uint32_t bp, uint32_t nargs, int va)
{
    uptrint_t n;
    uint32_t extr = nopt+nkw;
    uint32_t ntot = nreq+extr;
    value_t *args = (value_t*)alloca(extr*sizeof(value_t));
    value_t v;
    uint32_t i, a = 0, nrestargs;
    value_t s1 = fl_Stack[FL_SP-1];
    value_t s3 = fl_Stack[FL_SP-3];
    value_t s4 = fl_Stack[FL_SP-4];
    if (nargs < nreq)
        lerror(fl_ArgError, "apply: too few arguments");
    for (i=0; i < extr; i++) args[i] = UNBOUND;
    for (i=nreq; i < nargs; i++) {
        v = fl_Stack[bp+i];
        if (issymbol(v) && iskeyword((symbol_t*)ptr(v)))
            break;
        if (a >= nopt)
            goto no_kw;
        args[a++] = v;
    }
    if (i >= nargs) goto no_kw;
    // now process keywords
    n = vector_size(kwtable)/2;
    do {
        i++;
        if (i >= nargs)
            lerrorf(fl_ArgError, "keyword %s requires an argument",
                    symbol_name(v));
        value_t hv = fixnum(((symbol_t*)ptr(v))->hash);
        uptrint_t x = 2*(labs(numval(hv)) % n);
        if (vector_elt(kwtable, x) == v) {
            uptrint_t idx = numval(vector_elt(kwtable, x+1));
            assert(idx < nkw);
            idx += nopt;
            if (args[idx] == UNBOUND) {
                // if duplicate key, keep first value
                args[idx] = fl_Stack[bp+i];
            }
        }
        else {
            lerrorf(fl_ArgError, "unsupported keyword %s", symbol_name(v));
        }
        i++;
        if (i >= nargs) break;
        v = fl_Stack[bp+i];
    } while (issymbol(v) && iskeyword((symbol_t*)ptr(v)));
 no_kw:
    nrestargs = nargs - i;
    if (!va && nrestargs > 0)
        lerror(fl_ArgError, "apply: too many arguments");
    nargs = ntot + nrestargs;
    if (nrestargs)
        memmove(&fl_Stack[bp+ntot], &fl_Stack[bp+i], nrestargs*sizeof(value_t));
    memcpy(&fl_Stack[bp+nreq], args, extr*sizeof(value_t));
    FL_SP = bp + nargs;
    assert(FL_SP < FL_N_STACK-4);
    PUSH(s4);
    PUSH(s3);
    PUSH(nargs);
    PUSH(s1);
    fl_curr_frame = FL_SP;
    return nargs;
}

#if BYTE_ORDER == BIG_ENDIAN
#define GET_INT32(a)                            \
    ((int32_t)                                  \
    ((((int32_t)a[0])<<0)  |                    \
     (((int32_t)a[1])<<8)  |                    \
     (((int32_t)a[2])<<16) |                    \
     (((int32_t)a[3])<<24)))
#define GET_INT16(a)                            \
    ((int16_t)                                  \
    ((((int16_t)a[0])<<0)  |                    \
     (((int16_t)a[1])<<8)))
#define PUT_INT32(a,i) (*(int32_t*)(a) = bswap_32((int32_t)(i)))
#else
#define GET_INT32(a) (*(int32_t*)a)
#define GET_INT16(a) (*(int16_t*)a)
#define PUT_INT32(a,i) (*(int32_t*)(a) = (int32_t)(i))
#endif
#define SWAP_INT32(a) (*(int32_t*)(a) = bswap_32(*(int32_t*)(a)))
#define SWAP_INT16(a) (*(int16_t*)(a) = bswap_16(*(int16_t*)(a)))

#ifdef USE_COMPUTED_GOTO
#define OP(x) L_##x:
#define NEXT_OP goto *vm_labels[*ip++]
#else
#define OP(x) case x:
#define NEXT_OP goto next_op
#endif

/*
  stack on entry: <func>  <nargs args...>
  caller's responsibility:
  - put the stack in this state
  - provide arg count
  - respect tail position
  - restore FL_SP

  callee's responsibility:
  - check arg counts
  - allocate vararg array
  - push closed env, set up new environment
*/
static value_t apply_cl_ctx(fl_global_context_t *global_ctx, uint32_t nargs)
{
    VM_LABELS;
    VM_APPLY_LABELS;
    uint32_t top_frame = fl_curr_frame;
    // frame variables
    uint32_t n=0;
    uint32_t bp;
    const uint8_t *ip;
    fixnum_t s, hi;

    // temporary variables (not necessary to preserve across calls)
#ifndef USE_COMPUTED_GOTO
    uint32_t op;
#endif
    uint32_t i;
    symbol_t *sym;
#define fl_apply_c global_ctx->apply_c
#define fl_apply_pv global_ctx->apply_pv
#define fl_apply_accum global_ctx->apply_accum
#define fl_apply_func global_ctx->apply_func
#define fl_apply_v global_ctx->apply_v
#define fl_apply_e global_ctx->apply_e

 apply_cl_top:
    fl_apply_func = fl_Stack[FL_SP-nargs-1];
    ip = (uint8_t*)cv_data((cvalue_t*)ptr(fn_bcode(fl_apply_func)));
#ifndef MEMDEBUG2
    assert(!ismanaged((uptrint_t)ip));
#endif
    while (FL_SP+GET_INT32(ip) > FL_N_STACK) {
        grow_stack(global_ctx);
    }
    ip += 4;

    bp = FL_SP-nargs;
    PUSH(fn_env(fl_apply_func));
    PUSH(fl_curr_frame);
    PUSH(nargs);
    FL_SP++;//PUSH(0); //ip
    fl_curr_frame = FL_SP;

    {
#ifdef USE_COMPUTED_GOTO
    {
        NEXT_OP;
#else
    next_op:
        op = *ip++;
    dispatch:
        switch (op) {
#endif
        OP(OP_ARGC)
            n = *ip++;
        do_argc:
            if (nargs != n) {
                if (nargs > n)
                    lerror(fl_ArgError, "apply: too many arguments");
                else
                    lerror(fl_ArgError, "apply: too few arguments");
            }
            NEXT_OP;
        OP(OP_VARGC)
            i = *ip++;
        do_vargc:
            s = (fixnum_t)nargs - (fixnum_t)i;
            if (s > 0) {
                fl_apply_v = list(&fl_Stack[bp+i], s);
                fl_Stack[bp+i] = fl_apply_v;
                if (s > 1) {
                    fl_Stack[bp+i+1] = fl_Stack[bp+nargs+0];
                    fl_Stack[bp+i+2] = fl_Stack[bp+nargs+1];
                    fl_Stack[bp+i+3] = i+1;
                    fl_Stack[bp+i+4] = 0;
                    FL_SP =  bp+i+5;
                    fl_curr_frame = FL_SP;
                }
            }
            else if (s < 0) {
                lerror(fl_ArgError, "apply: too few arguments");
            }
            else {
                FL_SP++;
                fl_Stack[FL_SP-2] = i+1;
                fl_Stack[FL_SP-3] = fl_Stack[FL_SP-4];
                fl_Stack[FL_SP-4] = fl_Stack[FL_SP-5];
                fl_Stack[FL_SP-5] = FL_NIL;
                fl_curr_frame = FL_SP;
            }
            nargs = i+1;
            NEXT_OP;
        OP(OP_LARGC)
            n = GET_INT32(ip); ip+=4;
            goto do_argc;
        OP(OP_LVARGC)
            i = GET_INT32(ip); ip+=4;
            goto do_vargc;
        OP(OP_BRBOUND)
            i = GET_INT32(ip); ip+=4;
            fl_apply_v = fl_Stack[bp+i];
            if (fl_apply_v != UNBOUND) PUSH(FL_T);
            else PUSH(FL_F);
            NEXT_OP;
        OP(OP_DUP) FL_SP++; fl_Stack[FL_SP-1] = fl_Stack[FL_SP-2]; NEXT_OP;
        OP(OP_POP) POPN(1); NEXT_OP;
        OP(OP_TCALL)
            n = *ip++;  // nargs
        do_tcall:
            fl_apply_func = fl_Stack[FL_SP-n-1];
            if (tag(fl_apply_func) == TAG_FUNCTION) {
                if (fl_apply_func > (N_BUILTINS<<3)) {
                    fl_curr_frame = fl_Stack[fl_curr_frame-3];
                    for(s=-1; s < (fixnum_t)n; s++)
                        fl_Stack[bp+s] = fl_Stack[FL_SP-n+s];
                    FL_SP = bp+n;
                    nargs = n;
                    goto apply_cl_top;
                }
                else {
                    i = uintval(fl_apply_func);
                    if (i <= OP_ASET) {
                        s = builtin_arg_counts[i];
                        if (s >= 0)
                            argcount(builtin_names[i], n, s);
                        else if (s != ANYARGS && (signed)n < -s)
                            argcount(builtin_names[i], n, -s);
                        // remove function arg
                        for(s=FL_SP-n-1; s < (int)FL_SP-1; s++)
                            fl_Stack[s] = fl_Stack[s+1];
                        FL_SP--;
#ifdef USE_COMPUTED_GOTO
                        if (i == OP_APPLY)
                            goto apply_tapply;
                        goto *vm_apply_labels[i];
#else
                        switch (i) {
                        case OP_LIST:   goto apply_list;
                        case OP_VECTOR: goto apply_vector;
                        case OP_APPLY:  goto apply_tapply;
                        case OP_ADD:    goto apply_add;
                        case OP_SUB:    goto apply_sub;
                        case OP_MUL:    goto apply_mul;
                        case OP_DIV:    goto apply_div;
                        default:
                            op = (uint8_t)i;
                            goto dispatch;
                        }
#endif
                    }
                }
            }
            else if (iscbuiltin(fl_apply_func)) {
                s = FL_SP;
                fl_apply_v = ((builtin_t)(((void**)ptr(fl_apply_func))[3]))(&fl_Stack[FL_SP-n], n);
                FL_SP = s-n;
                fl_Stack[FL_SP-1] = fl_apply_v;
                NEXT_OP;
            }
            type_error("apply", "function", fl_apply_func);
        // WARNING: repeated code ahead
        OP(OP_CALL)
            n = *ip++;  // nargs
        do_call:
            fl_apply_func = fl_Stack[FL_SP-n-1];
            if (tag(fl_apply_func) == TAG_FUNCTION) {
                if (fl_apply_func > (N_BUILTINS<<3)) {
                    fl_Stack[fl_curr_frame-1] = (uptrint_t)ip;
                    nargs = n;
                    goto apply_cl_top;
                }
                else {
                    i = uintval(fl_apply_func);
                    if (i <= OP_ASET) {
                        s = builtin_arg_counts[i];
                        if (s >= 0)
                            argcount(builtin_names[i], n, s);
                        else if (s != ANYARGS && (signed)n < -s)
                            argcount(builtin_names[i], n, -s);
                        // remove function arg
                        for(s=FL_SP-n-1; s < (int)FL_SP-1; s++)
                            fl_Stack[s] = fl_Stack[s+1];
                        FL_SP--;
#ifdef USE_COMPUTED_GOTO
                        goto *vm_apply_labels[i];
#else
                        switch (i) {
                        case OP_LIST:   goto apply_list;
                        case OP_VECTOR: goto apply_vector;
                        case OP_APPLY:  goto apply_apply;
                        case OP_ADD:    goto apply_add;
                        case OP_SUB:    goto apply_sub;
                        case OP_MUL:    goto apply_mul;
                        case OP_DIV:    goto apply_div;
                        default:
                            op = (uint8_t)i;
                            goto dispatch;
                        }
#endif
                    }
                }
            }
            else if (iscbuiltin(fl_apply_func)) {
                s = FL_SP;
                fl_apply_v = ((builtin_t)(((void**)ptr(fl_apply_func))[3]))(&fl_Stack[FL_SP-n], n);
                FL_SP = s-n;
                fl_Stack[FL_SP-1] = fl_apply_v;
                NEXT_OP;
            }
            type_error("apply", "function", fl_apply_func);
        OP(OP_TCALLL) n = GET_INT32(ip); ip+=4; goto do_tcall;
        OP(OP_CALLL)  n = GET_INT32(ip); ip+=4; goto do_call;
        OP(OP_JMP) ip += (ptrint_t)GET_INT16(ip); NEXT_OP;
        OP(OP_BRF)
            fl_apply_v = POP();
            if (fl_apply_v == FL_F) ip += (ptrint_t)GET_INT16(ip);
            else ip += 2;
            NEXT_OP;
        OP(OP_BRT)
            fl_apply_v = POP();
            if (fl_apply_v != FL_F) ip += (ptrint_t)GET_INT16(ip);
            else ip += 2;
            NEXT_OP;
        OP(OP_JMPL) ip += (ptrint_t)GET_INT32(ip); NEXT_OP;
        OP(OP_BRFL)
            fl_apply_v = POP();
            if (fl_apply_v == FL_F) ip += (ptrint_t)GET_INT32(ip);
            else ip += 4;
            NEXT_OP;
        OP(OP_BRTL)
            fl_apply_v = POP();
            if (fl_apply_v != FL_F) ip += (ptrint_t)GET_INT32(ip);
            else ip += 4;
            NEXT_OP;
        OP(OP_BRNE)
            if (fl_Stack[FL_SP-2] != fl_Stack[FL_SP-1]) ip += (ptrint_t)GET_INT16(ip);
            else ip += 2;
            POPN(2);
            NEXT_OP;
        OP(OP_BRNEL)
            if (fl_Stack[FL_SP-2] != fl_Stack[FL_SP-1]) ip += (ptrint_t)GET_INT32(ip);
            else ip += 4;
            POPN(2);
            NEXT_OP;
        OP(OP_BRNN)
            fl_apply_v = POP();
            if (fl_apply_v != FL_NIL) ip += (ptrint_t)GET_INT16(ip);
            else ip += 2;
            NEXT_OP;
        OP(OP_BRNNL)
            fl_apply_v = POP();
            if (fl_apply_v != FL_NIL) ip += (ptrint_t)GET_INT32(ip);
            else ip += 4;
            NEXT_OP;
        OP(OP_BRN)
            fl_apply_v = POP();
            if (fl_apply_v == FL_NIL) ip += (ptrint_t)GET_INT16(ip);
            else ip += 2;
            NEXT_OP;
        OP(OP_BRNL)
            fl_apply_v = POP();
            if (fl_apply_v == FL_NIL) ip += (ptrint_t)GET_INT32(ip);
            else ip += 4;
            NEXT_OP;
        OP(OP_RET)
            fl_apply_v = POP();
            FL_SP = fl_curr_frame;
            fl_curr_frame = fl_Stack[FL_SP-3];
            if (fl_curr_frame == top_frame) return fl_apply_v;
            FL_SP -= (4+nargs);
            ip = (uint8_t*)fl_Stack[fl_curr_frame-1];
            nargs        = fl_Stack[fl_curr_frame-2];
            bp           = fl_curr_frame - 4 - nargs;
            fl_Stack[FL_SP-1] = fl_apply_v;
            NEXT_OP;

        OP(OP_EQ)
            fl_Stack[FL_SP-2] = ((fl_Stack[FL_SP-2] == fl_Stack[FL_SP-1]) ? FL_T : FL_F);
            POPN(1); NEXT_OP;
        OP(OP_EQV)
            if (fl_Stack[FL_SP-2] == fl_Stack[FL_SP-1]) {
                fl_apply_v = FL_T;
            }
            else if (!leafp(fl_Stack[FL_SP-2]) || !leafp(fl_Stack[FL_SP-1])) {
                fl_apply_v = FL_F;
            }
            else {
                fl_apply_v = (compare_(fl_Stack[FL_SP-2], fl_Stack[FL_SP-1], 1)==0 ? FL_T : FL_F);
            }
            fl_Stack[FL_SP-2] = fl_apply_v; POPN(1);
            NEXT_OP;
        OP(OP_EQUAL)
            if (fl_Stack[FL_SP-2] == fl_Stack[FL_SP-1]) {
                fl_apply_v = FL_T;
            }
            else {
                fl_apply_v = (compare_(fl_Stack[FL_SP-2], fl_Stack[FL_SP-1], 1)==0 ? FL_T : FL_F);
            }
            fl_Stack[FL_SP-2] = fl_apply_v; POPN(1);
            NEXT_OP;
        OP(OP_PAIRP)
            fl_Stack[FL_SP-1] = (iscons(fl_Stack[FL_SP-1]) ? FL_T : FL_F); NEXT_OP;
        OP(OP_ATOMP)
            fl_Stack[FL_SP-1] = (iscons(fl_Stack[FL_SP-1]) ? FL_F : FL_T); NEXT_OP;
        OP(OP_NOT)
            fl_Stack[FL_SP-1] = ((fl_Stack[FL_SP-1]==FL_F) ? FL_T : FL_F); NEXT_OP;
        OP(OP_NULLP)
            fl_Stack[FL_SP-1] = ((fl_Stack[FL_SP-1]==FL_NIL) ? FL_T : FL_F); NEXT_OP;
        OP(OP_BOOLEANP)
            fl_apply_v = fl_Stack[FL_SP-1];
            fl_Stack[FL_SP-1] = ((fl_apply_v == FL_T || fl_apply_v == FL_F) ? FL_T:FL_F); NEXT_OP;
        OP(OP_SYMBOLP)
            fl_Stack[FL_SP-1] = (issymbol(fl_Stack[FL_SP-1]) ? FL_T : FL_F); NEXT_OP;
        OP(OP_NUMBERP)
            fl_apply_v = fl_Stack[FL_SP-1];
            fl_Stack[FL_SP-1] = (fl_isnumber(fl_apply_v) ? FL_T:FL_F); NEXT_OP;
        OP(OP_FIXNUMP)
            fl_Stack[FL_SP-1] = (isfixnum(fl_Stack[FL_SP-1]) ? FL_T : FL_F); NEXT_OP;
        OP(OP_BOUNDP)
            sym = tosymbol(fl_Stack[FL_SP-1], "bound?");
            fl_Stack[FL_SP-1] = ((sym->binding == UNBOUND) ? FL_F : FL_T);
            NEXT_OP;
        OP(OP_BUILTINP)
            fl_apply_v = fl_Stack[FL_SP-1];
            fl_Stack[FL_SP-1] = (isbuiltin(fl_apply_v) || iscbuiltin(fl_apply_v)) ? FL_T : FL_F;
            NEXT_OP;
        OP(OP_FUNCTIONP)
            fl_apply_v = fl_Stack[FL_SP-1];
            fl_Stack[FL_SP-1] = ((tag(fl_apply_v)==TAG_FUNCTION &&
                            (uintval(fl_apply_v)<=OP_ASET || fl_apply_v>(N_BUILTINS<<3))) ||
                           iscbuiltin(fl_apply_v)) ? FL_T : FL_F;
            NEXT_OP;
        OP(OP_VECTORP)
            fl_Stack[FL_SP-1] = (isvector(fl_Stack[FL_SP-1]) ? FL_T : FL_F); NEXT_OP;

        OP(OP_CONS)
#ifdef MEMDEBUG2
            fl_apply_c = (cons_t*)ptr(mk_cons());
#else
            if (fl_curheap > fl_lim)
                gc(0);
            fl_apply_c = (cons_t*)fl_curheap;
            fl_curheap += sizeof(cons_t);
#endif
            fl_apply_c->car = fl_Stack[FL_SP-2];
            fl_apply_c->cdr = fl_Stack[FL_SP-1];
            fl_Stack[FL_SP-2] = tagptr(fl_apply_c, TAG_CONS);
            POPN(1); NEXT_OP;
        OP(OP_CAR)
            fl_apply_v = fl_Stack[FL_SP-1];
            if (!iscons(fl_apply_v)) type_error("car", "cons", fl_apply_v);
            fl_Stack[FL_SP-1] = car_(fl_apply_v);
            NEXT_OP;
        OP(OP_CDR)
            fl_apply_v = fl_Stack[FL_SP-1];
            if (!iscons(fl_apply_v)) type_error("cdr", "cons", fl_apply_v);
            fl_Stack[FL_SP-1] = cdr_(fl_apply_v);
            NEXT_OP;
        OP(OP_CADR)
            fl_apply_v = fl_Stack[FL_SP-1];
            if (!iscons(fl_apply_v)) type_error("cdr", "cons", fl_apply_v);
            fl_apply_v = cdr_(fl_apply_v);
            if (!iscons(fl_apply_v)) type_error("car", "cons", fl_apply_v);
            fl_Stack[FL_SP-1] = car_(fl_apply_v);
            NEXT_OP;
        OP(OP_SETCAR)
            car(fl_Stack[FL_SP-2]) = fl_Stack[FL_SP-1];
            POPN(1); NEXT_OP;
        OP(OP_SETCDR)
            cdr(fl_Stack[FL_SP-2]) = fl_Stack[FL_SP-1];
            POPN(1); NEXT_OP;
        OP(OP_LIST)
            n = *ip++;
        apply_list:
            if (n > 0) {
                fl_apply_v = list(&fl_Stack[FL_SP-n], n);
                POPN(n);
                PUSH(fl_apply_v);
            }
            else {
                PUSH(FL_NIL);
            }
            NEXT_OP;

        OP(OP_TAPPLY)
            n = *ip++;
        apply_tapply:
            fl_apply_v = POP();     // arglist
            n = FL_SP-(n-2);  // n-2 == # leading arguments not in the list
            while (iscons(fl_apply_v)) {
                if (FL_SP >= FL_N_STACK)
                    grow_stack(global_ctx);
                PUSH(car_(fl_apply_v));
                fl_apply_v = cdr_(fl_apply_v);
            }
            n = FL_SP-n;
            goto do_tcall;
        OP(OP_APPLY)
            n = *ip++;
        apply_apply:
            fl_apply_v = POP();     // arglist
            n = FL_SP-(n-2);  // n-2 == # leading arguments not in the list
            while (iscons(fl_apply_v)) {
                if (FL_SP >= FL_N_STACK)
                    grow_stack(global_ctx);
                PUSH(car_(fl_apply_v));
                fl_apply_v = cdr_(fl_apply_v);
            }
            n = FL_SP-n;
            goto do_call;

        OP(OP_ADD)
            n = *ip++;
        apply_add:
            s = 0;
            i = FL_SP-n;
            for (; i < FL_SP; i++) {
                if (isfixnum(fl_Stack[i])) {
                    s += numval(fl_Stack[i]);
                    if (!fits_fixnum(s)) {
                        i++;
                        goto add_ovf;
                    }
                }
                else {
                add_ovf:
                    fl_apply_v = fl_add_any(&fl_Stack[i], FL_SP-i, s);
                    break;
                }
            }
            if (i==FL_SP)
                fl_apply_v = fixnum(s);
            POPN(n);
            PUSH(fl_apply_v);
            NEXT_OP;
        OP(OP_ADD2)
            if (bothfixnums(fl_Stack[FL_SP-1], fl_Stack[FL_SP-2])) {
                s = numval(fl_Stack[FL_SP-1]) + numval(fl_Stack[FL_SP-2]);
                if (fits_fixnum(s))
                    fl_apply_v = fixnum(s);
                else
                    fl_apply_v = mk_ptrdiff(s);
            }
            else {
                fl_apply_v = fl_add_any(&fl_Stack[FL_SP-2], 2, 0);
            }
            POPN(1);
            fl_Stack[FL_SP-1] = fl_apply_v;
            NEXT_OP;
        OP(OP_SUB)
            n = *ip++;
        apply_sub:
            if (n == 2) goto do_sub2;
            if (n == 1) goto do_neg;
            i = FL_SP-n;
            // we need to pass the full arglist on to fl_add_any
            // so it can handle rest args properly
            PUSH(fl_Stack[i]);
            fl_Stack[i] = fixnum(0);
            fl_Stack[i+1] = fl_neg(fl_add_any(&fl_Stack[i], n, 0));
            fl_Stack[i] = POP();
            fl_apply_v = fl_add_any(&fl_Stack[i], 2, 0);
            POPN(n);
            PUSH(fl_apply_v);
            NEXT_OP;
        OP(OP_NEG)
        do_neg:
            if (isfixnum(fl_Stack[FL_SP-1]))
                fl_Stack[FL_SP-1] = fixnum(-numval(fl_Stack[FL_SP-1]));
            else
                fl_Stack[FL_SP-1] = fl_neg(fl_Stack[FL_SP-1]);
            NEXT_OP;
        OP(OP_SUB2)
        do_sub2:
            if (bothfixnums(fl_Stack[FL_SP-2], fl_Stack[FL_SP-1])) {
                s = numval(fl_Stack[FL_SP-2]) - numval(fl_Stack[FL_SP-1]);
                if (fits_fixnum(s))
                    fl_apply_v = fixnum(s);
                else
                    fl_apply_v = mk_ptrdiff(s);
            }
            else {
                fl_Stack[FL_SP-1] = fl_neg(fl_Stack[FL_SP-1]);
                fl_apply_v = fl_add_any(&fl_Stack[FL_SP-2], 2, 0);
            }
            POPN(1);
            fl_Stack[FL_SP-1] = fl_apply_v;
            NEXT_OP;
        OP(OP_MUL)
            n = *ip++;
        apply_mul:
            fl_apply_accum = 1;
            i = FL_SP-n;
            for (; i < FL_SP; i++) {
                if (isfixnum(fl_Stack[i])) {
                    fl_apply_accum *= numval(fl_Stack[i]);
                }
                else {
                    fl_apply_v = fl_mul_any(&fl_Stack[i], FL_SP-i, fl_apply_accum);
                    break;
                }
            }
            if (i == FL_SP) {
                if (fits_fixnum(fl_apply_accum))
                    fl_apply_v = fixnum(fl_apply_accum);
                else
                    fl_apply_v = return_from_int64(fl_apply_accum);
            }
            POPN(n);
            PUSH(fl_apply_v);
            NEXT_OP;
        OP(OP_DIV)
            n = *ip++;
        apply_div:
            i = FL_SP-n;
            if (n == 1) {
                fl_Stack[FL_SP-1] = fl_div2(fixnum(1), fl_Stack[i]);
            }
            else {
                if (n > 2) {
                    PUSH(fl_Stack[i]);
                    fl_Stack[i] = fixnum(1);
                    fl_Stack[i+1] = fl_mul_any(&fl_Stack[i], n, 1);
                    fl_Stack[i] = POP();
                }
                fl_apply_v = fl_div2(fl_Stack[i], fl_Stack[i+1]);
                POPN(n);
                PUSH(fl_apply_v);
            }
            NEXT_OP;
        OP(OP_IDIV)
            fl_apply_v = fl_Stack[FL_SP-2]; fl_apply_e = fl_Stack[FL_SP-1];
            if (bothfixnums(fl_apply_v, fl_apply_e)) {
                if (fl_apply_e==0) DivideByZeroError();
                fl_apply_v = fixnum(numval(fl_apply_v) / numval(fl_apply_e));
            }
            else
                fl_apply_v = fl_idiv2(fl_apply_v, fl_apply_e);
            POPN(1);
            fl_Stack[FL_SP-1] = fl_apply_v;
            NEXT_OP;
        OP(OP_NUMEQ)
            fl_apply_v = fl_Stack[FL_SP-2]; fl_apply_e = fl_Stack[FL_SP-1];
            if (bothfixnums(fl_apply_v, fl_apply_e))
                fl_apply_v = (fl_apply_v == fl_apply_e) ? FL_T : FL_F;
            else
                fl_apply_v = (!numeric_compare(fl_apply_v,fl_apply_e,1,0,"=")) ? FL_T : FL_F;
            POPN(1);
            fl_Stack[FL_SP-1] = fl_apply_v;
            NEXT_OP;
        OP(OP_LT)
            if (bothfixnums(fl_Stack[FL_SP-2], fl_Stack[FL_SP-1])) {
                fl_apply_v = (numval(fl_Stack[FL_SP-2]) < numval(fl_Stack[FL_SP-1])) ? FL_T : FL_F;
            }
            else {
                fl_apply_v = (numval(fl_compare(fl_Stack[FL_SP-2], fl_Stack[FL_SP-1])) < 0) ?
                    FL_T : FL_F;
            }
            POPN(1);
            fl_Stack[FL_SP-1] = fl_apply_v;
            NEXT_OP;
        OP(OP_COMPARE)
            fl_Stack[FL_SP-2] = compare_(fl_Stack[FL_SP-2], fl_Stack[FL_SP-1], 0);
            POPN(1);
            NEXT_OP;

        OP(OP_VECTOR)
            n = *ip++;
        apply_vector:
            fl_apply_v = alloc_vector(n, 0);
            if (n) {
                memcpy(&vector_elt(fl_apply_v,0), &fl_Stack[FL_SP-n], n*sizeof(value_t));
                POPN(n);
            }
            PUSH(fl_apply_v);
            NEXT_OP;

        OP(OP_AREF)
            fl_apply_v = fl_Stack[FL_SP-2];
            if (isvector(fl_apply_v)) {
                fl_apply_e = fl_Stack[FL_SP-1];
                if (isfixnum(fl_apply_e))
                    i = numval(fl_apply_e);
                else
                    i = (uint32_t)tosize(fl_apply_e, "aref");
                if ((unsigned)i >= vector_size(fl_apply_v))
                    bounds_error("aref", fl_apply_v, fl_apply_e);
                fl_apply_v = vector_elt(fl_apply_v, i);
            }
            else if (isarray(fl_apply_v)) {
                fl_apply_v = cvalue_array_aref(&fl_Stack[FL_SP-2]);
            }
            else {
                type_error("aref", "sequence", fl_apply_v);
            }
            POPN(1);
            fl_Stack[FL_SP-1] = fl_apply_v;
            NEXT_OP;
        OP(OP_ASET)
            fl_apply_e = fl_Stack[FL_SP-3];
            if (isvector(fl_apply_e)) {
                i = tofixnum(fl_Stack[FL_SP-2], "aset!");
                if ((unsigned)i >= vector_size(fl_apply_e))
                    bounds_error("aset!", fl_apply_v, fl_Stack[FL_SP-1]);
                vector_elt(fl_apply_e, i) = (fl_apply_v=fl_Stack[FL_SP-1]);
            }
            else if (isarray(fl_apply_e)) {
                fl_apply_v = cvalue_array_aset(&fl_Stack[FL_SP-3]);
            }
            else {
                type_error("aset!", "sequence", fl_apply_e);
            }
            POPN(2);
            fl_Stack[FL_SP-1] = fl_apply_v;
            NEXT_OP;
        OP(OP_FOR)
            s  = tofixnum(fl_Stack[FL_SP-3], "for");
            hi = tofixnum(fl_Stack[FL_SP-2], "for");
            //f = fl_Stack[FL_SP-1];
            fl_apply_v = FL_UNSPECIFIED;
            FL_SP += 2;
            n = FL_SP;
            for(; s <= hi; s++) {
                fl_Stack[FL_SP-2] = fl_Stack[FL_SP-3];
                fl_Stack[FL_SP-1] = fixnum(s);
                fl_apply_v = apply_cl_ctx(global_ctx, 1);
                FL_SP = n;
            }
            POPN(4);
            fl_Stack[FL_SP-1] = fl_apply_v;
            NEXT_OP;

        OP(OP_LOADT) PUSH(FL_T); NEXT_OP;
        OP(OP_LOADF) PUSH(FL_F); NEXT_OP;
        OP(OP_LOADNIL) PUSH(FL_NIL); NEXT_OP;
        OP(OP_LOAD0) PUSH(fixnum(0)); NEXT_OP;
        OP(OP_LOAD1) PUSH(fixnum(1)); NEXT_OP;
        OP(OP_LOADI8) s = (int8_t)*ip++; PUSH(fixnum(s)); NEXT_OP;
        OP(OP_LOADV)
            fl_apply_v = fn_vals(fl_Stack[bp-1]);
            assert(*ip < vector_size(fl_apply_v));
            fl_apply_v = vector_elt(fl_apply_v, *ip); ip++;
            PUSH(fl_apply_v);
            NEXT_OP;
        OP(OP_LOADVL)
            fl_apply_v = fn_vals(fl_Stack[bp-1]);
            fl_apply_v = vector_elt(fl_apply_v, GET_INT32(ip)); ip+=4;
            PUSH(fl_apply_v);
            NEXT_OP;
        OP(OP_LOADGL)
            fl_apply_v = fn_vals(fl_Stack[bp-1]);
            fl_apply_v = vector_elt(fl_apply_v, GET_INT32(ip)); ip+=4;
            goto do_loadg;
        OP(OP_LOADG)
            fl_apply_v = fn_vals(fl_Stack[bp-1]);
            assert(*ip < vector_size(fl_apply_v));
            fl_apply_v = vector_elt(fl_apply_v, *ip); ip++;
        do_loadg:
            assert(issymbol(fl_apply_v));
            sym = (symbol_t*)ptr(fl_apply_v);
            if (sym->binding == UNBOUND)
                fl_raise(fl_list2(fl_UnboundError, fl_apply_v));
            PUSH(sym->binding);
            NEXT_OP;

        OP(OP_SETGL)
            fl_apply_v = fn_vals(fl_Stack[bp-1]);
            fl_apply_v = vector_elt(fl_apply_v, GET_INT32(ip)); ip+=4;
            goto do_setg;
        OP(OP_SETG)
            fl_apply_v = fn_vals(fl_Stack[bp-1]);
            assert(*ip < vector_size(fl_apply_v));
            fl_apply_v = vector_elt(fl_apply_v, *ip); ip++;
        do_setg:
            assert(issymbol(fl_apply_v));
            sym = (symbol_t*)ptr(fl_apply_v);
            fl_apply_v = fl_Stack[FL_SP-1];
            if (!isconstant(sym))
                sym->binding = fl_apply_v;
            NEXT_OP;

        OP(OP_LOADA)
            i = *ip++;
            fl_apply_v = fl_Stack[bp+i];
            PUSH(fl_apply_v);
            NEXT_OP;
        OP(OP_LOADA0)
            fl_apply_v = fl_Stack[bp];
            PUSH(fl_apply_v);
            NEXT_OP;
        OP(OP_LOADA1)
            fl_apply_v = fl_Stack[bp+1];
            PUSH(fl_apply_v);
            NEXT_OP;
        OP(OP_LOADAL)
            i = GET_INT32(ip); ip+=4;
            fl_apply_v = fl_Stack[bp+i];
            PUSH(fl_apply_v);
            NEXT_OP;
        OP(OP_SETA)
            fl_apply_v = fl_Stack[FL_SP-1];
            i = *ip++;
            fl_Stack[bp+i] = fl_apply_v;
            NEXT_OP;
        OP(OP_SETAL)
            fl_apply_v = fl_Stack[FL_SP-1];
            i = GET_INT32(ip); ip+=4;
            fl_Stack[bp+i] = fl_apply_v;
            NEXT_OP;

        OP(OP_BOX)
            i = *ip++;
            fl_apply_v = mk_cons();
            car_(fl_apply_v) = fl_Stack[bp+i];
            cdr_(fl_apply_v) = FL_NIL;
            fl_Stack[bp+i] = fl_apply_v;
            NEXT_OP;
        OP(OP_BOXL)
            i = GET_INT32(ip); ip+=4;
            fl_apply_v = mk_cons();
            car_(fl_apply_v) = fl_Stack[bp+i];
            cdr_(fl_apply_v) = FL_NIL;
            fl_Stack[bp+i] = fl_apply_v;
            NEXT_OP;

        OP(OP_SHIFT)
            i = *ip++;
            fl_Stack[FL_SP-1-i] = fl_Stack[FL_SP-1];
            FL_SP -= i;
            NEXT_OP;

        OP(OP_LOADC)
            i = *ip++;
            fl_apply_v = fl_Stack[bp+nargs];
            assert(isvector(fl_apply_v));
            assert(i < vector_size(fl_apply_v));
            PUSH(vector_elt(fl_apply_v, i));
            NEXT_OP;

        OP(OP_LOADC0)
            PUSH(vector_elt(fl_Stack[bp+nargs], 0));
            NEXT_OP;
        OP(OP_LOADC1)
            PUSH(vector_elt(fl_Stack[bp+nargs], 1));
            NEXT_OP;

        OP(OP_LOADCL)
            i = GET_INT32(ip); ip+=4;
            fl_apply_v = fl_Stack[bp+nargs];
            PUSH(vector_elt(fl_apply_v, i));
            NEXT_OP;

        OP(OP_CLOSURE)
            n = *ip++;
            assert(n > 0);
            fl_apply_pv = alloc_words(n + 1);
            fl_apply_v = tagptr(fl_apply_pv, TAG_VECTOR);
            fl_apply_pv[0] = fixnum(n);
            i = 1;
            do {
                fl_apply_pv[i] = fl_Stack[FL_SP-n + i-1];
                i++;
            } while (i<=n);
            POPN(n);
            PUSH(fl_apply_v);
#ifdef MEMDEBUG2
            fl_apply_pv = alloc_words(4);
#else
            if ((value_t*)fl_curheap > ((value_t*)fl_lim)-2)
                gc(0);
            fl_apply_pv = (value_t*)fl_curheap;
            fl_curheap += (4*sizeof(value_t));
#endif
            fl_apply_e = fl_Stack[FL_SP-2];  // closure to copy
            assert(isfunction(fl_apply_e));
            fl_apply_pv[0] = ((value_t*)ptr(fl_apply_e))[0];
            fl_apply_pv[1] = ((value_t*)ptr(fl_apply_e))[1];
            fl_apply_pv[2] = fl_Stack[FL_SP-1];  // env
            fl_apply_pv[3] = ((value_t*)ptr(fl_apply_e))[3];
            POPN(1);
            fl_Stack[FL_SP-1] = tagptr(fl_apply_pv, TAG_FUNCTION);
            NEXT_OP;

        OP(OP_TRYCATCH)
            fl_apply_v = do_trycatch(global_ctx);
            POPN(1);
            fl_Stack[FL_SP-1] = fl_apply_v;
            NEXT_OP;

        OP(OP_OPTARGS)
            i = GET_INT32(ip); ip+=4;
            n = GET_INT32(ip); ip+=4;
            if (nargs < i)
                lerror(fl_ArgError, "apply: too few arguments");
            if ((int32_t)n > 0) {
                if (nargs > n)
                    lerror(fl_ArgError, "apply: too many arguments");
            }
            else n = -n;
            if (n > nargs) {
                n -= nargs;
                FL_SP += n;
                fl_Stack[FL_SP-1] = fl_Stack[FL_SP-n-1];
                fl_Stack[FL_SP-2] = nargs+n;
                fl_Stack[FL_SP-3] = fl_Stack[FL_SP-n-3];
                fl_Stack[FL_SP-4] = fl_Stack[FL_SP-n-4];
                fl_curr_frame = FL_SP;
                for(i=0; i < n; i++) {
                    fl_Stack[bp+nargs+i] = UNBOUND;
                }
                nargs += n;
            }
            NEXT_OP;
        OP(OP_KEYARGS)
            fl_apply_v = fn_vals(fl_Stack[bp-1]);
            fl_apply_v = vector_elt(fl_apply_v, 0);
            i = GET_INT32(ip); ip+=4;
            n = GET_INT32(ip); ip+=4;
            s = GET_INT32(ip); ip+=4;
            nargs = process_keys(global_ctx, fl_apply_v, i, n, llabs(s)-(i+n), bp, nargs, s<0);
            NEXT_OP;

#ifndef USE_COMPUTED_GOTO
        default:
            goto dispatch;
#endif
        }
    }
#ifdef USE_COMPUTED_GOTO
    return UNBOUND;  // not reached
#else
    goto dispatch;
#endif
}

static value_t apply_cl(uint32_t nargs)
{
    return apply_cl_ctx(pfl_global_ctx, nargs);
}
#undef fl_global_ctx
#define fl_global_ctx (pfl_global_ctx)

static uint32_t compute_maxstack(uint8_t *code, size_t len, int bswap)
{
    uint8_t *ip = code+4, *end = code+len;
    uint8_t op;
    uint32_t i, n, sp = 0, maxsp = 0;

    while (1) {
        if ((int32_t)sp > (int32_t)maxsp) maxsp = sp;
        if (ip >= end) break;
        op = *ip++;
        switch (op) {
        case OP_ARGC:
            n = *ip++;
            break;
        case OP_VARGC:
            n = *ip++;
            sp += (n+2);
            break;
        case OP_LARGC:
            if (bswap) SWAP_INT32(ip);
            n = GET_INT32(ip); ip+=4;
            break;
        case OP_LVARGC:
            if (bswap) SWAP_INT32(ip);
            n = GET_INT32(ip); ip+=4;
            sp += (n+2);
            break;
        case OP_OPTARGS:
            if (bswap) SWAP_INT32(ip);
            i = GET_INT32(ip); ip+=4;
            if (bswap) SWAP_INT32(ip);
            n = abs(GET_INT32(ip)); ip+=4;
            sp += (n-i);
            break;
        case OP_KEYARGS:
            if (bswap) SWAP_INT32(ip);
            i = GET_INT32(ip); ip+=4;
            if (bswap) SWAP_INT32(ip);
            n = GET_INT32(ip); ip+=4;
            if (bswap) SWAP_INT32(ip);
            n = abs(GET_INT32(ip)); ip+=4;
            sp += (n-i);
            break;
        case OP_BRBOUND:
            if (bswap) SWAP_INT32(ip);
            ip+=4;
            sp++;
            break;

        case OP_TCALL: case OP_CALL:
            n = *ip++;  // nargs
            sp -= n;
            break;
        case OP_TCALLL: case OP_CALLL:
            if (bswap) SWAP_INT32(ip);
            n = GET_INT32(ip); ip+=4;
            sp -= n;
            break;
        case OP_JMP:
            if (bswap) SWAP_INT16(ip);
            ip += 2; break;
        case OP_JMPL:
            if (bswap) SWAP_INT32(ip);
            ip += 4; break;
        case OP_BRF: case OP_BRT:
            if (bswap) SWAP_INT16(ip);
            ip+=2;
            sp--;
            break;
        case OP_BRFL: case OP_BRTL:
            if (bswap) SWAP_INT32(ip);
            ip += 4;
            sp--;
            break;
        case OP_BRNE:
            if (bswap) SWAP_INT16(ip);
            ip += 2;
            sp -= 2;
            break;
        case OP_BRNEL:
            if (bswap) SWAP_INT32(ip);
            ip += 4;
            sp -= 2;
            break;
        case OP_BRNN: case OP_BRN:
            if (bswap) SWAP_INT16(ip);
            ip += 2;
            sp--;
            break;
        case OP_BRNNL: case OP_BRNL:
            if (bswap) SWAP_INT32(ip);
            ip += 4;
            sp--;
            break;
        case OP_RET: sp--; break;

        case OP_CONS: case OP_SETCAR: case OP_SETCDR: case OP_POP:
        case OP_EQ: case OP_EQV: case OP_EQUAL: case OP_ADD2: case OP_SUB2:
        case OP_IDIV: case OP_NUMEQ: case OP_LT: case OP_COMPARE:
        case OP_AREF: case OP_TRYCATCH:
            sp--;
            break;

        case OP_PAIRP: case OP_ATOMP: case OP_NOT: case OP_NULLP:
        case OP_BOOLEANP: case OP_SYMBOLP: case OP_NUMBERP: case OP_FIXNUMP:
        case OP_BOUNDP: case OP_BUILTINP: case OP_FUNCTIONP: case OP_VECTORP:
        case OP_NOP: case OP_CAR: case OP_CDR: case OP_NEG:
            break;

        case OP_TAPPLY: case OP_APPLY:
            n = *ip++;
            sp -= (n-1);
            break;

        case OP_LIST: case OP_ADD: case OP_SUB: case OP_MUL: case OP_DIV:
        case OP_VECTOR:
            n = *ip++;
            sp -= (n-1);
            break;
        case OP_CLOSURE:
            n = *ip++;
            sp -= n;
            break;
        case OP_SHIFT:
            n = *ip++;
            sp -= n;
            break;

        case OP_ASET:
            sp -= 2;
            break;
        case OP_FOR:
            if (sp+2 > maxsp) maxsp = sp+2;
            sp -=2;
            break;

        case OP_LOADT: case OP_LOADF: case OP_LOADNIL: case OP_LOAD0:
        case OP_LOAD1: case OP_LOADA0: case OP_LOADA1: case OP_DUP:
        case OP_LOADC0: case OP_LOADC1:
            sp++;
            break;

        case OP_LOADI8: case OP_LOADV: case OP_LOADG: case OP_LOADA:
            ip++;
            sp++;
            break;
        case OP_LOADVL: case OP_LOADGL: case OP_LOADAL:
            if (bswap) SWAP_INT32(ip);
            ip+=4;
            sp++;
            break;

        case OP_SETG: case OP_SETA: case OP_BOX:
            ip++;
            break;
        case OP_SETGL: case OP_SETAL: case OP_BOXL:
            if (bswap) SWAP_INT32(ip);
            ip+=4;
            break;

        case OP_LOADC: ip+=1; sp++; break;
        case OP_LOADCL:
            if (bswap) SWAP_INT32(ip);
            ip+=4;
            sp++; break;
        }
    }
    return maxsp+4;
}

// top = top frame pointer to start at
static value_t _stacktrace(uint32_t top)
{
    uint32_t bp, sz;
    value_t v, lst = FL_NIL;
    fl_gc_handle(&lst);
    while (top > 0) {
        sz = fl_Stack[top-2]+1;
        bp = top-4-sz;
        v = alloc_vector(sz, 0);
        memcpy(&vector_elt(v,0), &fl_Stack[bp], sz*sizeof(value_t));
        lst = fl_cons(v, lst);
        top = fl_Stack[top-3];
    }
    fl_free_gc_handles(1);
    return lst;
}

// builtins -------------------------------------------------------------------

void assign_global_builtins(const builtinspec_t *b)
{
    while (b->name != NULL) {
        setc(symbol(b->name), cbuiltin(b->name, b->fptr));
        b++;
    }
}

static value_t fl_function(value_t *args, uint32_t nargs)
{
    if (nargs == 1 && issymbol(args[0]))
        return fl_builtin(args, nargs);
    if (nargs < 2 || nargs > 4)
        argcount("function", nargs, 2);
    if (!fl_isstring(args[0]))
        type_error("function", "string", args[0]);
    if (!isvector(args[1]))
        type_error("function", "vector", args[1]);
    cvalue_t *arr = (cvalue_t*)ptr(args[0]);
    cv_pin(arr);
    char *data = (char*)cv_data(arr);
    int swap = 0;
    if ((uint8_t)data[4] >= N_OPCODES) {
        // read syntax, shifted 48 for compact text representation
        size_t i, sz = cv_len(arr);
        for(i=0; i < sz; i++)
            data[i] -= 48;
    }
    else {
#if BYTE_ORDER == BIG_ENDIAN
        swap = 1;
#endif
    }
    uint32_t ms = compute_maxstack((uint8_t*)data, cv_len(arr), swap);
    PUT_INT32(data, ms);
    function_t *fn = (function_t*)alloc_words(4);
    value_t fv = tagptr(fn, TAG_FUNCTION);
    fn->bcode = args[0];
    fn->vals = args[1];
    fn->env = FL_NIL;
    fn->name = FL_LAMBDA;
    if (nargs > 2) {
        if (issymbol(args[2])) {
            fn->name = args[2];
            if (nargs > 3)
                fn->env = args[3];
        }
        else {
            fn->env = args[2];
            if (nargs > 3) {
                if (!issymbol(args[3]))
                    type_error("function", "symbol", args[3]);
                fn->name = args[3];
            }
        }
        if (isgensym(fn->name))
            lerror(fl_ArgError, "function: name should not be a gensym");
    }
    return fv;
}

static value_t fl_function_code(value_t *args, uint32_t nargs)
{
    argcount("function:code", nargs, 1);
    value_t v = args[0];
    if (!isclosure(v)) type_error("function:code", "function", v);
    return fn_bcode(v);
}
static value_t fl_function_vals(value_t *args, uint32_t nargs)
{
    argcount("function:vals", nargs, 1);
    value_t v = args[0];
    if (!isclosure(v)) type_error("function:vals", "function", v);
    return fn_vals(v);
}
static value_t fl_function_env(value_t *args, uint32_t nargs)
{
    argcount("function:env", nargs, 1);
    value_t v = args[0];
    if (!isclosure(v)) type_error("function:env", "function", v);
    return fn_env(v);
}
static value_t fl_function_name(value_t *args, uint32_t nargs)
{
    argcount("function:name", nargs, 1);
    value_t v = args[0];
    if (!isclosure(v)) type_error("function:name", "function", v);
    return fn_name(v);
}

value_t fl_copylist(value_t *args, u_int32_t nargs)
{
    argcount("copy-list", nargs, 1);
    return copy_list(args[0]);
}

value_t fl_append(value_t *args, u_int32_t nargs)
{
    if (nargs == 0)
        return FL_NIL;
    value_t first=FL_NIL, lst, lastcons=FL_NIL;
    fl_gc_handle(&first);
    fl_gc_handle(&lastcons);
    uint32_t i=0;
    while (1) {
        lst = args[i++];
        if (i >= nargs) break;
        if (iscons(lst)) {
            lst = copy_list(lst);
            if (first == FL_NIL)
                first = lst;
            else
                cdr_(lastcons) = lst;
#ifdef MEMDEBUG2
            lastcons = lst;
            while (cdr_(lastcons) != FL_NIL)
                lastcons = cdr_(lastcons);
#else
            lastcons = tagptr((((cons_t*)fl_curheap)-1), TAG_CONS);
#endif
        }
        else if (lst != FL_NIL) {
            type_error("append", "cons", lst);
        }
    }
    if (first == FL_NIL)
        first = lst;
    else
        cdr_(lastcons) = lst;
    fl_free_gc_handles(2);
    return first;
}

value_t fl_liststar(value_t *args, u_int32_t nargs)
{
    if (nargs == 1) return args[0];
    else if (nargs == 0) argcount("list*", nargs, 1);
    return _list(args, nargs, 1);
}

value_t fl_stacktrace(value_t *args, u_int32_t nargs)
{
    (void)args;
    argcount("stacktrace", nargs, 0);
    return _stacktrace(fl_throwing_frame ? fl_throwing_frame : fl_curr_frame);
}

#undef fl_global_ctx
#define fl_global_ctx global_ctx
value_t fl_map1(value_t *args, u_int32_t nargs)
{
    fl_global_context_t *global_ctx = pfl_global_ctx;
    if (nargs < 2)
        lerror(fl_ArgError, "map: too few arguments");
    if (!iscons(args[1])) return FL_NIL;
    value_t v;
    uint32_t first, last, argSP = args-fl_Stack;
    assert(args >= fl_Stack && argSP < FL_N_STACK);
    if (nargs == 2) {
        if (FL_SP+4 > FL_N_STACK) grow_stack(global_ctx);
        PUSH(fl_Stack[argSP]);
        PUSH(car_(fl_Stack[argSP+1]));
        v = _applyn(global_ctx, 1);
        POPN(2);
        PUSH(v);
        v = mk_cons();
        car_(v) = POP(); cdr_(v) = FL_NIL;
        PUSH(v);
        PUSH(v);
        first = FL_SP-2;
        last = FL_SP-1;
        fl_Stack[argSP+1] = cdr_(fl_Stack[argSP+1]);
        while (iscons(fl_Stack[argSP+1])) {
            PUSH(fl_Stack[argSP]);
            PUSH(car_(fl_Stack[argSP+1]));
            v = _applyn(global_ctx, 1);
            POPN(2);
            PUSH(v);
            v = mk_cons();
            car_(v) = POP(); cdr_(v) = FL_NIL;
            cdr_(fl_Stack[last]) = v;
            fl_Stack[last] = v;
            fl_Stack[argSP+1] = cdr_(fl_Stack[argSP+1]);
        }
        POPN(2);
    }
    else {
        size_t i;
        while (FL_SP+nargs+1 > FL_N_STACK) grow_stack(global_ctx);
        PUSH(fl_Stack[argSP]);
        for(i=1; i < nargs; i++) {
            PUSH(car(fl_Stack[argSP+i]));
            fl_Stack[argSP+i] = cdr_(fl_Stack[argSP+i]);
        }
        v = _applyn(global_ctx, nargs-1);
        POPN(nargs);
        PUSH(v);
        v = mk_cons();
        car_(v) = POP(); cdr_(v) = FL_NIL;
        PUSH(v);
        PUSH(v);
        first = FL_SP-2;
        last = FL_SP-1;
        while (iscons(fl_Stack[argSP+1])) {
            PUSH(fl_Stack[argSP]);
            for(i=1; i < nargs; i++) {
                PUSH(car(fl_Stack[argSP+i]));
                fl_Stack[argSP+i] = cdr_(fl_Stack[argSP+i]);
            }
            v = _applyn(global_ctx, nargs-1);
            POPN(nargs);
            PUSH(v);
            v = mk_cons();
            car_(v) = POP(); cdr_(v) = FL_NIL;
            cdr_(fl_Stack[last]) = v;
            fl_Stack[last] = v;
        }
        POPN(2);
    }
    return fl_Stack[first];
}
#undef fl_global_ctx
#define fl_global_ctx (pfl_global_ctx)

static const builtinspec_t core_builtin_info[] = {
    { "function", fl_function },
    { "function:code", fl_function_code },
    { "function:vals", fl_function_vals },
    { "function:env", fl_function_env },
    { "function:name", fl_function_name },
    { "stacktrace", fl_stacktrace },
    { "gensym", fl_gensym },
    { "gensym?", fl_gensymp },
    { "hash", fl_hash },
    { "copy-list", fl_copylist },
    { "append", fl_append },
    { "list*", fl_liststar },
    { "map", fl_map1 },
    { NULL, NULL }
};

// initialization -------------------------------------------------------------

extern void builtins_init(void);
extern void comparehash_init(void);

static void lisp_init(size_t initial_heapsize)
{
    int i;

    libsupport_init();

    FL_SP = 0;
    fl_curr_frame = 0;
    FL_N_GCHND = 0;
    fl_readstate = NULL;
    fl_gensym_ctr = 0;
    fl_gsnameno = 0;

#ifdef MEMDEBUG2
    fl_tochain = NULL;
    fl_n_allocd = 0;
#endif

    fl_heapsize = initial_heapsize;

    fl_fromspace = (unsigned char*)LLT_ALLOC(fl_heapsize);
#ifdef MEMDEBUG
    fl_tospace   = NULL;
#else
    fl_tospace   = (unsigned char*)LLT_ALLOC(fl_heapsize);
#endif
    fl_curheap = fl_fromspace;
    fl_lim = fl_curheap+fl_heapsize-sizeof(cons_t);
    fl_consflags = bitvector_new(fl_heapsize/sizeof(cons_t), 1);
    fl_print_init();
    comparehash_init();
    FL_N_STACK = 262144;
    fl_Stack = (value_t*)malloc(FL_N_STACK*sizeof(value_t));
    CHECK_ALIGN8(fl_Stack);

    FL_NIL = builtin(OP_THE_EMPTY_LIST);
    FL_T = builtin(OP_BOOL_CONST_T);
    FL_F = builtin(OP_BOOL_CONST_F);
    FL_EOF = builtin(OP_EOF_OBJECT);
    FL_LAMBDA = symbol("lambda");        FL_FUNCTION = symbol("function");
    FL_QUOTE = symbol("quote");          FL_TRYCATCH = symbol("trycatch");
    FL_BACKQUOTE = symbol("quasiquote");       FL_COMMA = symbol("unquote");
    FL_COMMAAT = symbol("unquote-splicing");   FL_COMMADOT = symbol("unquote-nsplicing");
    fl_IOError = symbol("io-error");     fl_ParseError = symbol("parse-error");
    fl_TypeError = symbol("type-error"); fl_ArgError = symbol("arg-error");
    fl_UnboundError = symbol("unbound-error");
    fl_KeyError = symbol("key-error");   fl_OutOfMemoryError = symbol("memory-error");
    fl_BoundsError = symbol("bounds-error");
    fl_DivideError = symbol("divide-error");
    fl_EnumerationError = symbol("enumeration-error");
    fl_pairsym = symbol("pair");
    fl_symbolsym = symbol("symbol");     fl_fixnumsym = symbol("fixnum");
    fl_vectorsym = symbol("vector");     fl_builtinsym = symbol("builtin");
    fl_booleansym = symbol("boolean");   fl_nullsym = symbol("null");
    fl_definesym = symbol("define");     fl_defmacrosym = symbol("define-macro");
    fl_forsym = symbol("for");
    fl_setqsym = symbol("set!");         fl_evalsym = symbol("eval");
    fl_vu8sym = symbol("vu8");           fl_fnsym = symbol("fn");
    fl_nulsym = symbol("nul");           fl_alarmsym = symbol("alarm");
    fl_backspacesym = symbol("backspace"); fl_tabsym = symbol("tab");
    fl_linefeedsym = symbol("linefeed"); fl_vtabsym = symbol("vtab");
    fl_pagesym = symbol("page");         fl_returnsym = symbol("return");
    fl_escsym = symbol("esc");           fl_spacesym = symbol("space");
    fl_deletesym = symbol("delete");     fl_newlinesym = symbol("newline");
    fl_tsym = symbol("t"); fl_Tsym = symbol("T");
    fl_fsym = symbol("f"); fl_Fsym = symbol("F");
    set(fl_printprettysym=symbol("*print-pretty*"), FL_T);
    set(fl_printreadablysym=symbol("*print-readably*"), FL_T);
    set(fl_printwidthsym=symbol("*print-width*"), fixnum(FL_SCR_WIDTH));
    set(fl_printlengthsym=symbol("*print-length*"), FL_F);
    set(fl_printlevelsym=symbol("*print-level*"), FL_F);
    fl_builtins_table_sym = symbol("*builtins*");
    fl_lasterror = FL_NIL;
    i = 0;
    for (i=OP_EQ; i <= OP_ASET; i++) {
        setc(symbol(builtin_names[i]), builtin(i));
    }
    setc(symbol("eq"), builtin(OP_EQ));
    setc(symbol("procedure?"), builtin(OP_FUNCTIONP));
    setc(symbol("top-level-bound?"), builtin(OP_BOUNDP));

#if defined(_OS_LINUX_)
    set(symbol("*os-name*"), symbol("linux"));
#elif defined(_OS_WINDOWS_)
    set(symbol("*os-name*"), symbol("win32"));
#elif defined(_OS_DARWIN_)
    set(symbol("*os-name*"), symbol("macos"));
#else
    set(symbol("*os-name*"), symbol("unknown"));
#endif

    fl_jl_sym = symbol("julia_value");

    fl_the_empty_vector = tagptr(alloc_words(1), TAG_VECTOR);
    vector_setsize(fl_the_empty_vector, 0);

    cvalues_init();

    char exename[1024];
    size_t exe_size = sizeof(exename) / sizeof(exename[0]);
    if ( uv_exepath(exename, &exe_size) == 0 ) {
        setc(symbol("*install-dir*"), cvalue_static_cstring(strdup(dirname(exename))));
    }

    fl_memory_exception_value = fl_list2(fl_OutOfMemoryError,
                                         cvalue_static_cstring("out of memory"));

    assign_global_builtins(core_builtin_info);

    fl_read_init();

    builtins_init();
}

// top level ------------------------------------------------------------------

value_t fl_toplevel_eval(value_t expr)
{
    return fl_applyn(1, symbol_value(fl_evalsym), expr);
}

extern void fl_init_julia_extensions(void);

void fl_init(size_t initial_heapsize)
{
    lisp_init(initial_heapsize);
    fl_init_julia_extensions();
}

int fl_load_system_image_str(char *str, size_t len)
{
    value_t img = cvalue(fl_iostreamtype, sizeof(ios_t));
    ios_t *pi = value2c(ios_t*, img);
    ios_static_buffer(pi, str, len);

    return fl_load_system_image(img);
}

#undef fl_global_ctx
#define fl_global_ctx global_ctx
int fl_load_system_image(value_t sys_image_iostream)
{
    fl_global_context_t *global_ctx = pfl_global_ctx;
    value_t e;
    int saveSP;
    symbol_t *sym;

    PUSH(sys_image_iostream);
    saveSP = FL_SP;
    FL_TRY {
        while (1) {
            e = fl_read_sexpr(fl_Stack[FL_SP-1]);
            if (ios_eof(value2c(ios_t*,fl_Stack[FL_SP-1]))) break;
            if (isfunction(e)) {
                // stage 0 format: series of thunks
                PUSH(e);
                (void)_applyn(global_ctx, 0);
                FL_SP = saveSP;
            }
            else {
                // stage 1 format: list alternating symbol/value
                while (iscons(e)) {
                    sym = tosymbol(car_(e), "bootstrap");
                    e = cdr_(e);
                    (void)tocons(e, "bootstrap");
                    sym->binding = car_(e);
                    e = cdr_(e);
                }
                break;
            }
        }
    }
    FL_CATCH {
        ios_puts("fatal error during bootstrap:\n", ios_stderr);
        fl_print(ios_stderr, fl_lasterror);
        ios_putc('\n', ios_stderr);
        return 1;
    }
    ios_close(value2c(ios_t*,fl_Stack[FL_SP-1]));
    POPN(1);
    return 0;
}
#undef fl_global_ctx
#define fl_global_ctx (pfl_global_ctx)

#ifdef __cplusplus
}
#endif
