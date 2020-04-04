static const char version[] = "dadalisp version 0.0";

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef enum { false=0, true=1 } Flag;

#define array_size(array)	( sizeof(array) / sizeof((array)[0]) )

/* --- Error handling

 Make error() separate, with an initial Cell argument.
 Have it save the interpreter state in a list somewhere,
 along with a symbol representing next_action -- though
 what we really want is meta-access to the stacks, that
 can come later.  Actually, instead of saving it in a 
 list I think you should create a special stack frame.
 Be careful about stack- or memory-exhaustion, though.

 Another idea is to create a continuation object for each
 break-level.  The break loop can retry the last next_action
 call by simply returning, or substitute a value for whatever
 that action was supposed to compute by calling the current
 break-continuation, or abort by calling a higher-level continuation.
*/

#define unreachable 0
#define UNREACHABLE assert(unreachable)

static void fatal_error(const char *message, ...)
{
    va_list args;
    fprintf(stderr, "\n");
    va_start(args, message);
    vfprintf(stderr, message, args);
    va_end(args);
    fprintf(stderr, "\n");
    exit(1);
}

#define error fatal_error

/* --- Misc */

static void *allot(size_t size)
{
    void *result = malloc(size);
    if (!result)	/* I assume size != 0 */
        fatal_error("Out of memory");	/** should try a gc before giving up */
    return result;
}

static int stricmp(const unsigned char *s1, const unsigned char *s2)
{
  for (; *s1 && *s2 && tolower(*s1) == tolower(*s2); ++s1, ++s2)
    ;
  return tolower(*s1) - tolower(*s2);
}

/* --- Ports */

/** Only handle input Ports for now. */
typedef struct Port {
    Flag char_is_in_buffer;
    int buffered_char;
    void *data;
    int (*get_char)(void *data);
    void (*put_char)(char c, void *data);
    void (*close)(void *data);
    /*	void (*gc_mark)(void *data);	is this necessary? Could be.*/
} Port;

static int peek_char(Port *port)
{
    if (port->char_is_in_buffer)
        return port->buffered_char;
    if (!port->get_char)
        error("Port isn't readable");
    port->buffered_char = port->get_char(port->data);
    port->char_is_in_buffer = true;
    return port->buffered_char;
}

static int read_char(Port *port)
{
    if (port->char_is_in_buffer) {
        port->char_is_in_buffer = false;
        return port->buffered_char;
    }
    if (!port->get_char)
        error("Port isn't readable");
    return port->get_char(port->data);
}

static void write_char(Port *port, char c)
{
    if (!port->put_char)
        error("Port isn't writable");
    port->put_char(c, port->data);
}

/* There's a little problem here with interactive input:
 you have to hit ^Z twice to terminate the program.
 Maybe you could change the reader to fix that? */
static Flag at_eof(Port *port)		{ return peek_char(port) == EOF; }

static void close_port(Port *port)
{
    port->close(port->data);
    free(port);
}

static Port *open_file(const char *filename, const char *mode)
{
    Port *port = allot(sizeof(Port));
    port->char_is_in_buffer = false;
    port->close = (void (*)(void *)) fclose;	/* is that okay? Probably not. */

    port->get_char = NULL;
    port->put_char = NULL;
    if (mode[0] == 'r')
        port->get_char = (int (*)(void *)) fgetc;
    else if (mode[0] == 'w')
        port->put_char = (void (*)(char, void *)) fputc;
    else
        error("Unknown file-open mode: %s", mode);

    if (strcmp(filename, "-") == 0) {
        port->data = mode[0] == 'w' ? stdout : stdin;
    } else {
        port->data = fopen(filename, mode);
        if (!port->data)
            error("%s: %s", filename, strerror(errno));
    }

    return port;
}

/* --- Representation of Lisp data */

typedef float Number;
/* typedef double Number; */

typedef enum { 
    a_number, a_symbol, a_pair, a_nil, a_port, a_primitive, a_closure, a_cont
} Type;

static const char * const type_name[] = { 
    "number", "symbol", "pair", "()", "port", "primitive", "closure", "continuation"
};

typedef struct Cell *Cell;

typedef void Action(void);

typedef union {
    Cell *cell_ptr;
    Action *action;
} RStackEntry;

struct Cell {
    Type cell_type;
    union {
        Number number;
        struct {
            const char *name;
            Cell value;
        } symbol;
        struct {
            Cell pair_car, pair_cdr;
        } pair;
        Port *port;		/* this must be the -only- pointer to the port, since gc will close it.  That suggests we should pass the Cell around, instead of the Port *. */
        struct {
            unsigned char min_args, arg_count_range;
            void (*handler)(void);
        } primitive;
        struct {
            Cell *stack_ptr;	        /** these will have to be offsets */
            RStackEntry *rstack_ptr;	/** if we allow the stacks to grow */
        } cont;
    } data;
    Flag marked;
};

static Cell nil, t, keyword_quote;
static Cell the_eof_object;
static Cell uninitialized;
static Cell current_input_port;

#define type(cell)		( (cell)->cell_type )

#define num_value(num)		( (num)->data.number )
#define numeric_value(num)	num_value(must_be(a_number, (num)))

#define printname(sym)		( (sym)->data.symbol.name )
#define global_value(sym)	( (sym)->data.symbol.value )
#define is_bound(sym)		( !eq(global_value(sym), uninitialized) )	/** take this out */
#define set_global_value(symbol, value)	( global_value(symbol) = (value) )

#define fast_car(pear)		( (pear)->data.pair.pair_car )
#define fast_cdr(pear)		( (pear)->data.pair.pair_cdr )

#define car(cell)		fast_car(must_be(a_pair, (cell)))
#define cdr(cell)		fast_cdr(must_be(a_pair, (cell)))

#define first(list)		car(list)
#define second(list)		car(cdr(list))
#define third(list)		car(cdr(cdr(list)))

#define rest(list)		cdr(list)

#define cell_port(cell)		( (cell)->data.port )

#define proc_formals(closure)	fast_car(fast_cdr(fast_car(closure)))
#define proc_body(closure)	fast_cdr(fast_cdr(fast_car(closure)))
#define proc_env(closure)	fast_cdr(closure)

#define cont_stack(k)		( (k)->data.cont.stack_ptr )
#define cont_rstack(k)		( (k)->data.cont.rstack_ptr )

static Cell must_be(Type a_type, Cell cell)	
{ 
    if (type(cell) != a_type) 
        error("Expected a %s, not a %s", 
              type_name[a_type], type_name[type(cell)]);
    return cell;
}

#define is_number(cell)		( type(cell) == a_number )
#define is_symbol(cell)		( type(cell) == a_symbol )
#define is_pair(cell)		( type(cell) == a_pair )
#define is_port(cell)		( type(cell) == a_port )
#define is_primitive(cell)	( type(cell) == a_primitive )
#define is_closure(cell)	( type(cell) == a_closure )
#define is_cont(cell)		( type(cell) == a_cont )

#define is_atom(cell)		( type(cell) != a_pair )

#define eq(cell1, cell2)	( (cell1) == (cell2) )
#define is_nil(cell)		eq(cell, nil)

/* --- Garbage collection */

static const size_t store_size = 32767 / sizeof(struct Cell);

static Cell free_list;

static struct Cell *the_store;

static Cell stack[1000];
static Cell *stack_ptr = stack;

/* Interpreter state variables */
static Cell value, expr, env, proc, rands, exprs;

static Cell symbol_table[23];

static Cell hash_table[101];

static Cell push(Cell cell)
{
    if (stack + array_size(stack) <= stack_ptr)
        fatal_error("Stack overflow");		/** have to find a way to make this non-fatal */
    return *stack_ptr++ = cell;
}

static Cell pop(void)
{
    if (stack_ptr <= stack)
        fatal_error("BUG: stack underflow");
    return *--stack_ptr;
}

static void mark(Cell cell)
{
    while (!cell->marked) {
        cell->marked = true;
        if (is_atom(cell) && !is_closure(cell)) {	/** a switch() might be faster */
            if (is_symbol(cell)) {
                cell = global_value(cell);
                continue;
            }			
            break;
        }
        mark(fast_car(cell));	/* this works for both lists and closures */
        cell = fast_cdr(cell);
    }
}

static void sweep(void)
{
    Cell p;
    free_list = nil;
    for (p = the_store; p < the_store + store_size; ++p)
        if (p->marked)
            p->marked = false;
        else {
            if (is_symbol(p))
                free((char *)printname(p));		/** make sure this gets tested */
            else if (is_port(p))
                close_port(cell_port(p));	/** we need to make sure this won't harm anything if the user closes it explicitly */
            fast_cdr(p) = free_list;
            free_list = p;
        }
}

static void gc(Cell car, Cell cdr)
{
    Cell *root;
    mark(car); 
    mark(cdr);
    mark(value);
    mark(expr);
    mark(env);
    mark(proc);
    mark(rands);
    mark(exprs);
    mark(current_input_port);
    mark(nil);
    for (root = symbol_table; root < symbol_table + array_size(symbol_table); ++root)
        mark(*root);
    for (root = stack; root < stack_ptr; ++root)
        mark(*root);
    for (root = hash_table; root < hash_table + array_size(hash_table); ++root)
        mark(*root);

    sweep();
    if (is_nil(free_list))
        fatal_error("Out of heap space");	/** maybe have a 'reserve tank' for shutdown */
}

/** make a macro out of this */
static Cell new_cell(Type cell_type, Cell foo, Cell bar)
{
    if (is_nil(free_list))
        gc(foo, bar);
    {
        Cell result = free_list;
        free_list = fast_cdr(free_list);
        type(result) = cell_type;
        return result;
    }
}

/* --- Constructors */

static Cell make_number(Number n)
{ 
    Cell result = new_cell(a_number, nil, nil);
    num_value(result) = n;
    return result;
}

static Cell string_to_uninterned_symbol(const char *string)
{
    Cell result = new_cell(a_symbol, nil, nil);
    printname(result) = allot(strlen(string) + 1);
    strcpy((char*)printname(result), string);
    global_value(result) = uninitialized;
    return result;
}

/* Make a new pair. */
static Cell cons(Cell car, Cell cdr)
{
    Cell result = new_cell(a_pair, car, cdr);
    fast_car(result) = car;
    fast_cdr(result) = cdr;
    return result;
}

static Cell make_port(Port *port)
{
    Cell result = new_cell(a_port, nil, nil);
    cell_port(result) = port;
    return result;
}

static Cell make_primitive(
  unsigned char min_args, unsigned char max_args, void (*handler)(void))
{
    Cell result = new_cell(a_primitive, nil, nil);
    result->data.primitive.min_args = min_args;
    result->data.primitive.arg_count_range = max_args - min_args;
    result->data.primitive.handler = handler;
    return result;
}

static Cell make_closure(Cell lambda_exp, Cell env)
{
    Cell result = new_cell(a_closure, lambda_exp, env);
    fast_car(result) = lambda_exp;
    fast_cdr(result) = env;
    return result;
}

static Cell make_cont(Cell *stack_ptr, RStackEntry *rstack_ptr)
{
    Cell result = new_cell(a_cont, nil, nil);
    cont_stack(result) = stack_ptr;
    cont_rstack(result) = rstack_ptr;
    return result;
}

/* --- The symbol table */

static size_t hash(const char *string)
{
    size_t result = 0;
    for (; *string; ++string)
        result = (result << 5) - result + *string;
    return result;
}

static void setup_symbol_table(void)
{
    unsigned i;
    for (i = 0; i < array_size(symbol_table); ++i)
        symbol_table[i] = nil;
}

/* Convert a string to the symbol it names. */
static Cell string_to_symbol(const char *string)
{
    Cell *bucket = symbol_table + hash(string) % array_size(symbol_table);
    Cell symbols = *bucket;
    for (; !is_nil(symbols); symbols = fast_cdr(symbols))
        if (stricmp(printname(fast_car(symbols)), string) == 0)
            return fast_car(symbols);
    {
        Cell result = string_to_uninterned_symbol(string);
        *bucket = cons(result, *bucket);
        return result;
    }
}

/* --- The get/put hash table */

static void setup_hash_table(void)
{
    unsigned i;
    for (i = 0; i < array_size(hash_table); ++i)
        hash_table[i] = nil;
}

/** check whether this hasher is any good */
static size_t hash_cells(Cell key1, Cell key2)
{
    return (key1 - the_store) * (key2 - the_store);
}

/* Pre: if store_it, then arguments are protected from gc. */
static Cell hash_lookup(Cell key1, Cell key2, Cell value, Flag store_it)
{
    Cell *bucket = hash_table + hash_cells(key1, key2) % array_size(hash_table);
    Cell list = *bucket;
    for (; !is_nil(list); list = fast_cdr(fast_cdr(list)))
        if (eq(fast_car(fast_car(list)), key1)
           && eq(fast_cdr(fast_car(list)), key2)) {
            if (store_it)
                fast_car(fast_cdr(list)) = value;
            return fast_car(fast_cdr(list));
        }
    if (store_it) {		/** maybe should delete the entry if value = nil? */
        *bucket = cons(value, *bucket);		/* we cons the keys and value in 2 stages so the garbage collector always knows what's what */
        *bucket = cons(cons(key1, key2), *bucket);
        return value;
    } else
        return nil;
}

static Cell get(Cell key1, Cell key2)
{
    return hash_lookup(key1, key2, nil, false);
}

/* Pre: arguments are protected from gc. */
static void put(Cell key1, Cell key2, Cell value)
{
    hash_lookup(key1, key2, value, true);
}

/* --- Initialization */

static Cell keyword_if, keyword_lambda, keyword_setq, keyword_define, 
            keyword_begin;

static Cell clobbered_cont;
static Cell user_initial_env;

static void setup_memory(void)
{
    the_store = allot(store_size * sizeof(struct Cell));

    nil = the_store;
    type(nil) = a_nil;
        
    {
        Cell p;
        free_list = nil;
        for (p = the_store + 1; p < the_store + store_size; ++p) {
            p->marked = false;
            fast_cdr(p) = free_list;
            free_list = p;
        }
    }

    value = expr = env = proc = rands = exprs = nil;
    current_input_port = nil;

    uninitialized = string_to_uninterned_symbol("#uninitialized");
    set_global_value(uninitialized, uninitialized);

    setup_symbol_table();
    setup_hash_table();

    the_eof_object = string_to_uninterned_symbol("#eof");
    set_global_value(string_to_symbol("the-eof-object"), the_eof_object);
    t = string_to_symbol("t");
    set_global_value(t, t);
    set_global_value(string_to_symbol("nil"), nil);

    keyword_quote 	= string_to_symbol("quote");
    keyword_if 		= string_to_symbol("if");
    keyword_lambda	= string_to_symbol("lambda");
    keyword_setq	= string_to_symbol("set!");
    keyword_define	= string_to_symbol("define");
    keyword_begin	= string_to_symbol("begin");
    
    clobbered_cont = string_to_symbol("#dead-continuation");
    
    user_initial_env = nil;
    set_global_value(string_to_symbol("user-initial-environment"), user_initial_env);
}

/*  --- From this point on in the program, as a rule all procedures that take
     a Cell as a parameter have the precondition that the cell is protected
     against garbage collection.  (An exception might be procedures that
     you'd never expect to need to allocate memory -- predicates, for instance.)
*/

/* --- List operations */

/* Destructively reverse a proper list. */
static Cell nreverse(Cell list)
{
    Cell reversed_head = nil;
    while (is_pair(list)) {
        Cell tail = fast_cdr(list);
        fast_cdr(list) = reversed_head;
        reversed_head = list;
        list = tail;
    }
    if (!is_nil(list))
        error("Not a proper list - reverse!");
    return reversed_head;
}

/* Equality of atoms. */
static Flag eqv(Cell cell1, Cell cell2)
{
    if (type(cell1) != type(cell2))
        return false;
    if (is_number(cell1))
        return num_value(cell1) == num_value(cell2);
    return eq(cell1, cell2);
}

/* Equality of atoms and noncircular list structures. */
static Flag equal(Cell cell1, Cell cell2)
{
  recurse:
    if (type(cell1) != type(cell2))
        return false;
    if (is_atom(cell1))
        return eqv(cell1, cell2);	/* slightly inefficient... */
    if (!equal(fast_car(cell1), fast_car(cell2)))
        return false;
    cell1 = fast_cdr(cell1), cell2 = fast_cdr(cell2);
    goto recurse;
}

/* Length of a proper list. */
static unsigned length(Cell list)
{
    unsigned result = 0;
    for (; is_pair(list); list = fast_cdr(list))
        ++result;
    if (!is_nil(list))
        error("Not a proper list - length");
    return result;
}

/* --- Output */

static void write_expr(Cell expr)
{
    switch (type(expr)) {
        case a_number:		printf("%g", num_value(expr)); break;
        case a_symbol:		printf("%s", printname(expr)); break;
        case a_nil:		printf("()"); break;
        case a_port:
        case a_primitive:
        case a_closure:
        case a_cont:		
            printf("#<%s: %p>", type_name[type(expr)], expr); 
            break;
        case a_pair:
            printf("(");
            for (;;) {
                write_expr(fast_car(expr));
                expr = fast_cdr(expr);
                if (is_atom(expr))
                    break;
                printf(" ");
            }
            if (!is_nil(expr)) {
                printf(" . ");
                write_expr(expr);
            }
            printf(")");
            break;
        default: UNREACHABLE;
    }
}

static void print_expr(Cell expr)
{
    write_expr(expr);
    printf("\n");
}

/* --- Input */

static void skip_blanks(Port *port)
{
  recurse:
    while (isspace(peek_char(port)))
        read_char(port);
    if (peek_char(port) == ';') {		/* skip comments, too */
        int c;
        do {
            c = read_char(port);
        } while (c != EOF && c != '\n');
        goto recurse;
    }
}

static Cell read(Port *port);

static Flag is_symbol_terminator(int c)
{
    return c == EOF || strchr("();\" \t\n", c);
}

/* Read a symbol or number. */
static Cell read_atom(Port *port, int c)
{
    char token[100];
    char *scan = token;
    *scan++ = (char) c;
    while (!is_symbol_terminator(peek_char(port))) {
        if (token + sizeof token <= scan + 1)
            error("Token too long");
        *scan++ = (char) read_char(port);
    }
    *scan = '\0';
    {	/* try to convert it to a number */
        char *end;
        Number number = strtod(token, &end);
        return end == scan ? make_number(number) : string_to_symbol(token);
        /** I'm afraid that test isn't sufficient. */
    }
}

/*
 A list has the syntax:
           list ::= '(' ( ')' | rest-of-list )
   rest-of-list ::= expr+ ( ')' | '.' expr ')' )
 */
static Cell rest_of_list(Port *port)
{
    Cell head = read(port);
    skip_blanks(port);
    {
        int c = peek_char(port);
        if (c == EOF) {
            error("Unexpected EOF in list");
            return nil;
        } else if (c == ')') {
            read_char(port);
            return cons(head, nil);
        } else {
            Cell tail;
            push(head);
            if (c != '.')
                tail = rest_of_list(port);
            else {
                read_char(port);
                if (!is_symbol_terminator(peek_char(port))) {
                    tail = cons(push(read_atom(port, c)), rest_of_list(port));
                    pop();
                } else {
                    tail = read(port);
                    skip_blanks(port);
                    if (read_char(port) != ')')
                        error("Expected a ')'");
                }
            }
            pop();
            return cons(head, tail);
        }
    }
}

static Cell read_list(Port *port, int c)
{
    skip_blanks(port);
    c = peek_char(port);
    if (c == EOF) {
        error("Unexpected EOF in list");
        return nil;
    } else if (c == ')') {
        read_char(port);
        return nil;
    } else
        return rest_of_list(port);
}

static Cell read(Port *port)
{
    int c;
    skip_blanks(port);
    c = read_char(port);
    if (c == EOF)
        return the_eof_object;
    switch (c) {
        case '\'':	return cons(keyword_quote, cons(read(port), nil));
        case '(':	return read_list(port, c);
        case ')':	error("')' without matching '('"); return nil;
        case '.':
            if (is_symbol_terminator(peek_char(port)))
                error("Lone '.'");
            return read_atom(port, c);
        default:
            if (strchr("\"#[]{}", c)) {
                error("Character '%c' reserved for future extensions", c);
                return nil;
            }
            return read_atom(port, c);
    }
}

/* --- The environment */

static Cell *frame_ptr = stack;

static Cell extend_env(Cell variables, Cell env)
{
    Cell values = nil, vars = variables;
    Cell *p = stack_ptr - 1;
    for (; is_pair(vars); vars = fast_cdr(vars), --p) {
        if (p == frame_ptr)
            error("Not enough arguments to procedure");
        else if (!is_symbol(first(vars)))
            error("Formal parameter is not a symbol");
        else
            values = cons(*p, values);
    }
    if (!is_nil(vars)) {
        if (!is_symbol(vars))
            error("Formal parameter is not a symbol");
        for (; p != frame_ptr; --p)
            values = cons(*p, values);
    } else
        if (p != frame_ptr)
            error("Too many arguments to procedure");
    return cons(cons(variables, values), env);
}

static Cell *lookup_var(Cell variable, Cell env)
{
    for (; is_pair(env); env = fast_cdr(env)) {
        Cell vals_ptr = fast_car(env);
        Cell vars = fast_car(vals_ptr);
        for (; is_pair(vars); vars = fast_cdr(vars)) {
            vals_ptr = fast_cdr(vals_ptr);
            if (eq(fast_car(vars), variable))
                return &fast_car(vals_ptr);
        }
        if (eq(vars, variable))
            return &fast_cdr(vals_ptr);
    }
    if (eq(global_value(variable), uninitialized))
        error("Unbound variable: %s", printname(variable));
    return &global_value(variable);
}

#define var_value(var, env)		( *lookup_var((var), (env)) )
#define set_var_value(var, value, env)	( *lookup_var((var), (env)) = (value) )

static void define_var_value(Cell variable, Cell value, Cell env)
{
    if (is_nil(env))
        global_value(variable) = value;
    else {
        Cell frame = fast_car(env);
        fast_car(frame) = cons(variable, fast_car(frame));
        fast_cdr(frame) = cons(value, fast_cdr(frame));
    }
}

/** this doesn't really belong in the env section... */
static Cell frame_to_list(void)
{
    Cell *p;
    Cell result = nil;
    for (p = stack_ptr - 1; frame_ptr < p; --p)
        result = cons(*p, result);
    return result;
}

/* --- The return stack */

static RStackEntry rstack[1000];
static RStackEntry *rstack_ptr = rstack;

static void push_frame(Cell *frame)
{
    if (rstack + array_size(rstack) <= rstack_ptr)
        fatal_error("rstack overflow");
    (rstack_ptr++)->cell_ptr = frame;
}

static Cell *pop_frame(void)
{
    if (rstack_ptr <= rstack)
        fatal_error("BUG: rstack underflow");
    return (--rstack_ptr)->cell_ptr;
}

static void push_action(Action *action)
{
    if (rstack + array_size(rstack) <= rstack_ptr)
        fatal_error("rstack overflow");
    (rstack_ptr++)->action = action;
}

static Action *pop_action(void)
{
    if (rstack_ptr <= rstack)
        fatal_error("BUG: rstack underflow");
    return (--rstack_ptr)->action;
}

/* --- The interpreter */

#define is_true(value)		( !eq(value, nil) )
#define make_flag(flag)		( (flag) ? t : nil )

static jmp_buf error_k;

static Action *next_action;

static Action handle_error;		/** need to fill this in */
static Action apply;

static void enter_interpreter(Action action)
{
    push_action(NULL);
    next_action = action;

    /*
  restart:
    if (setjmp(error_k) != 0) {
        ** here save an explicit continuation
        
        push_action(next_action);	 note this means stack overflow has to be a fatal error, until you fix this
        push(handle_error);		 probably this should be a lookup
        push(value);
        push(expr);
        push(env);
        push(proc);
        push(rands);
        push(exprs);
        
        next_action = apply;	** no: won't restore state on returning!
        goto restart;
    }
    */
    
    while (next_action)
        next_action();
}

#define jump(action)	do { next_action = (action); return; } while(0)

#define define_action(name)	static void name(void)

static Action eval, eval_begin_loop;

define_action(eval_begin) {
    expr = first(exprs);
    exprs = fast_cdr(exprs);
    if (!is_nil(exprs)) {
        push(exprs);
        push(env);
        push_action(eval_begin_loop);
    }
    jump(eval);
}

define_action(eval_begin_loop) {
    env = pop();
    exprs = pop();
    jump(eval_begin);
}

/*
 Pre:	frame_ptr[0] is the procedure to apply.
        frame_ptr[1..stack_ptr - frame_ptr) are the arguments.
        The old frame_ptr is on top of the return stack.
*/
define_action(apply) {
    proc = frame_ptr[0];	/* proc doesn't have to be global, does it? */
    if (is_primitive(proc)) {	/** use a switch() instead? */
        if (proc->data.primitive.arg_count_range <
               (unsigned)(stack_ptr - frame_ptr - 1) - 
                 proc->data.primitive.min_args)
            error("Wrong number of arguments to primitive");
        proc->data.primitive.handler();
        stack_ptr = frame_ptr;	/** maybe move this into pop_frame() */
        jump(pop_action());
    } else if (is_closure(proc)) {
        exprs = proc_body(proc);
        env = extend_env(proc_formals(proc), proc_env(proc));
        stack_ptr = frame_ptr;
        jump(eval_begin);
    } else if (is_cont(proc)) {
        stack_ptr = cont_stack(proc);
        rstack_ptr = cont_rstack(proc);
        jump(pop_action());
    } else {
        error("Unknown procedure type -- apply");
        stack_ptr = frame_ptr;
        jump(pop_action());
    }
}

static Action if_decide, setq_action, define_action, eval_rands, apply_no_args;

define_action(eval) {
  eval_again:
    switch (type(expr)) {
        case a_number:
        case a_closure:	
        case a_nil:
            value = expr;
            jump(pop_action());
            break;
        case a_symbol:	
            value = var_value(expr, env);
            jump(pop_action());
            break;
        case a_pair: {
            Cell rator = fast_car(expr);
            rands = fast_cdr(expr);
            if (eq(rator, keyword_quote)) {
                value = first(rands);
                jump(pop_action());
            } else if (eq(rator, keyword_lambda)) {
                value = make_closure(expr, env);
                jump(pop_action());
            } else if (eq(rator, keyword_if)) {
                expr = first(rands);
                push(fast_cdr(rands));
                push(env);
                push_action(if_decide);
                goto eval_again;
            } else if (eq(rator, keyword_begin)) {
                exprs = rands;
                jump(eval_begin);
            } else if (eq(rator, keyword_setq)) {
                push(rands);
                push(env);
                push_action(setq_action);
                expr = second(rands);
                goto eval_again;
            } else if (eq(rator, keyword_define)) {
                push(rands);
                push(env);
                push_action(define_action);
                expr = second(rands);
                goto eval_again;
            } else {		/* Evaluate a procedure application */
                if (is_nil(rands)) 
                    push_action(apply_no_args);
                else {
                    push_frame(stack_ptr);
                    push_action(eval_rands);
                    push(rands);
                    push(env);
                }
                expr = rator;	/* Evaluate the operator */
                goto eval_again;
            }
        }
        default: UNREACHABLE;
    }
}

define_action(apply_no_args) {
    frame_ptr = stack_ptr;
    push(value);
    jump(apply);
}

define_action(apply_args) {
    frame_ptr = pop_frame();
    push(value);
    jump(apply);
}

define_action(eval_rands) {
    env = pop();
    rands = pop();
    push(value);		/* accumulate the proc or arg onto the stack */
    expr = first(rands);
    rands = fast_cdr(rands);
    if (is_nil(rands)) {
        push_action(apply_args);
    } else {
        push(rands);
        push(env);
        push_action(eval_rands);
    }
    jump(eval);
}

define_action(if_decide) {
    env = pop();
    rands = pop();
    expr = is_true(value) 
             ? first(rands)
             : is_nil(rest(rands)) ? nil : second(rands);
    jump(eval);
}

define_action(setq_action) {
    env = pop();
    rands = pop();
    value = set_var_value(first(rands), value, env);
    jump(pop_action());
}

define_action(define_action) {		/** !!! */
    env = pop();
    rands = pop();
    define_var_value(first(rands), value, env);
    value = fast_car(rands);
    jump(pop_action());
}

/* --- Primitive procedures */

#define arg(arg_num)		frame_ptr[(arg_num) + 1]

static Cell opt_arg(int arg_num, Cell default_value)
{
    return stack_ptr - frame_ptr - 1 <= arg_num 
             ? default_value : arg(arg_num);
}

#define define_prim(name) static void name(void)

define_prim(add)	/** what about FP exceptions? */
{ value = make_number(numeric_value(arg(0)) + numeric_value(arg(1))); }

define_prim(sub)
{ value = make_number(numeric_value(arg(0)) - numeric_value(arg(1))); }

define_prim(mul)
{ value = make_number(numeric_value(arg(0)) * numeric_value(arg(1))); }

define_prim(divide)
{ 
    Number denom = numeric_value(arg(1));
    if (denom == 0)
        error("Division by zero");
    value = make_number(numeric_value(arg(0)) / denom); 
}

define_prim(quotient)
{ 
    long numer = (long)numeric_value(arg(0));
    long denom = (long)numeric_value(arg(1));
    if ((Number)numer != num_value(arg(0))
     || (Number)denom != num_value(arg(1)))
        error("Non-integer argument");
    if (denom == 0)
        error("Division by zero");
    value = make_number(numer / denom); 
}

define_prim(remainder)
{ 
    long numer = (long)numeric_value(arg(0));
    long denom = (long)numeric_value(arg(1));
    if ((Number)numer != num_value(arg(0))
     || (Number)denom != num_value(arg(1)))
        error("Non-integer argument");
    if (denom == 0)
        error("Division by zero");
    value = make_number(numer % denom);
}

define_prim(less_than)
{ value = make_flag(numeric_value(arg(0)) < numeric_value(arg(1))); }

define_prim(num_equal)
{ value = make_flag(numeric_value(arg(0)) == numeric_value(arg(1))); }

define_prim(prim_eq)		{ value = make_flag(eq(arg(0), arg(1))); }
define_prim(prim_eqv)		{ value = make_flag(eqv(arg(0), arg(1))); }
define_prim(prim_equal)		{ value = make_flag(equal(arg(0), arg(1))); }

define_prim(prim_null)		{ value = make_flag(is_nil(arg(0))); }
define_prim(prim_cons)		{ value = cons(arg(0), arg(1)); }
define_prim(prim_car)		{ value = car(arg(0)); }
define_prim(prim_cdr)		{ value = cdr(arg(0)); }
define_prim(prim_caar)		{ value = car(car(arg(0))); }
define_prim(prim_cdar)		{ value = cdr(car(arg(0))); }
define_prim(prim_cadr)		{ value = car(cdr(arg(0))); }
define_prim(prim_cddr)		{ value = cdr(cdr(arg(0))); }
define_prim(prim_caddr)		{ value = car(cdr(cdr(arg(0)))); }
define_prim(prim_length)	{ value = make_number(length(arg(0))); }

define_prim(prim_set_car)	{ value = car(arg(0)) = arg(1); }
define_prim(prim_set_cdr)	{ value = cdr(arg(0)) = arg(1); }

define_prim(prim_nreverse)	{ value = nreverse(arg(0)); }

define_prim(prim_open_input_file)
{ value = make_port(open_file(printname(must_be(a_symbol, arg(0))), "r")); }

define_prim(prim_read)
{ value = read(cell_port(must_be(a_port, opt_arg(0, current_input_port)))); }

define_prim(prim_write)		{ write_expr(arg(0)); printf(" "); value = nil; }
define_prim(prim_print)		{ print_expr(arg(0)); value = nil; }
define_prim(prim_newline)	{ printf("\n"); value = nil; }

define_prim(prim_atomp)		{ value = make_flag(is_atom(arg(0))); }
define_prim(prim_numberp)	{ value = make_flag(is_number(arg(0))); }
define_prim(prim_symbolp)	{ value = make_flag(is_symbol(arg(0))); }
define_prim(prim_pairp)		{ value = make_flag(is_pair(arg(0))); }
define_prim(prim_portp)		{ value = make_flag(is_port(arg(0))); }
define_prim(prim_closurep)	{ value = make_flag(is_closure(arg(0))); }
define_prim(prim_primitivep)	{ value = make_flag(is_primitive(arg(0))); }

define_prim(prim_gensym)
{
    static unsigned counter = 0;
    char buffer[15];
    sprintf(buffer, "G%u", ++counter);
    value = string_to_uninterned_symbol(buffer);
}

define_prim(prim_list)		{ value = frame_to_list(); }

define_prim(prim_eval)
{
    expr = arg(0);
    env = arg(1);
    push_action(eval);
}

define_action(do_apply) {
    frame_ptr = stack_ptr;
    push(proc);
    for (; is_pair(rands); rands = fast_cdr(rands))	/* Push the arg list */
        push(fast_car(rands));
    if (!is_nil(rands))
        error("Bad argument to APPLY: not a proper list");
    jump(apply);
}

define_prim(prim_apply)
{
    proc = arg(0);
    rands = arg(1);
    push_action(do_apply);
}

define_action(clobber_cont) {
    *pop() = *clobbered_cont;
    jump(pop_action());
}

define_action(do_callcc) {
    push_action(clobber_cont);
    value = make_cont(stack_ptr+1, rstack_ptr);
    push(value);
    frame_ptr = stack_ptr;
    push(proc);
    push(value);
    jump(apply);
}

define_prim(prim_callcc)
{
    proc = arg(0);
    push_action(do_callcc);
}

define_prim(prim_random)
{
    value = make_number(rand() % (unsigned) numeric_value(arg(0)));	/** should convert explicitly, with checking, to int */
}

define_prim(prim_get)	{ value = get(arg(0), arg(1)); }
define_prim(prim_put)	{ put(arg(0), arg(1), arg(2)); value = arg(2); }

define_prim(prim_error)
{
    printf("Error!\n");
    print_expr(frame_to_list());
    exit(1);
}

define_prim(prim_exit)	      { exit(0); }

define_prim(prim_clobber)     { *arg(0) = *arg(1); value = arg(0); }

define_prim(prim_the_environment) { value = env; }

define_prim(prim_proc_body)   { value = proc_body(must_be(a_closure, arg(0))); }
define_prim(prim_proc_env)    { value = proc_env(must_be(a_closure, arg(0))); }
define_prim(prim_proc_formals){ value = proc_formals(must_be(a_closure, arg(0))); }

static void install_primitives(void)
{
    static const struct {
        char *name;
        int min_args, max_args;
        void (*action)(void);
    } primitives[] = {
        { "*",			2, 2, mul },
        { "+",			2, 2, add },
        { "-",			2, 2, sub },
        { "/",			2, 2, divide },
        { "<",			2, 2, less_than },
        { "=",			2, 2, num_equal },
        { "apply",		2, 2, prim_apply },
        { "atom?",		1, 1, prim_atomp },
        { "caar",		1, 1, prim_caar },
        { "caddr",		1, 1, prim_caddr },
        { "cadr",		1, 1, prim_cadr },
        { "call/cc",		1, 1, prim_callcc },
        { "car",		1, 1, prim_car },
        { "cdar",		1, 1, prim_cdar },
        { "cddr",		1, 1, prim_cddr },
        { "cdr",		1, 1, prim_cdr },
        { "clobber!",		2, 2, prim_clobber },
        { "closure?",		1, 1, prim_closurep },
        { "closure-body",	1, 1, prim_proc_body },
        { "closure-environment",1, 1, prim_proc_env },
        { "closure-formals",	1, 1, prim_proc_formals },
        { "cons",		2, 2, prim_cons },
        { "eq?",		2, 2, prim_eq },
        { "equal?",		2, 2, prim_equal },
        { "eqv?",		2, 2, prim_eqv },
        { "error",	       0,255, prim_error },
        { "exit",		0, 0, prim_exit },
        { "fast-eval",		2, 2, prim_eval },
        { "gensym",		0, 0, prim_gensym },
        { "get",		2, 2, prim_get },
        { "length",		1, 1, prim_length },
        { "list",	       0,255, prim_list },
        { "newline",		0, 0, prim_newline },
        { "null?",		1, 1, prim_null },
        { "number?",		1, 1, prim_numberp },
        { "open-input-file",	1, 1, prim_open_input_file },
        { "pair?",		1, 1, prim_pairp },
        { "port?",		1, 1, prim_portp },
        { "primitive?",		1, 1, prim_primitivep },
        { "print",		1, 1, prim_print },
        { "put",		3, 3, prim_put },
        { "quotient",		2, 2, quotient },
        { "random",		1, 1, prim_random },
        { "read",		0, 1, prim_read },
        { "remainder",		2, 2, remainder },
        { "reverse!",		1, 1, prim_nreverse },
        { "set-car!",		2, 2, prim_set_car },
        { "set-cdr!",		2, 2, prim_set_cdr },
        { "symbol?",		1, 1, prim_symbolp },
        { "the-environment",	0, 0, prim_the_environment },
        { "write",		1, 1, prim_write },
    };
    
    unsigned i;
    for (i = 0; i < array_size(primitives); ++i)
        set_global_value(string_to_symbol(primitives[i].name), 
            make_primitive(primitives[i].min_args, 
                           primitives[i].max_args, 
                           primitives[i].action));
}

/* --- Main program */

static void driver_loop(const char *filename)
{
    Cell symbol_driver = string_to_symbol("top-level-driver");
    current_input_port = make_port(open_file(filename, "r"));
    while (!at_eof(cell_port(current_input_port)))
        if (is_bound(symbol_driver) && is_true(global_value(symbol_driver))) {
            frame_ptr = stack_ptr;
            push(global_value(symbol_driver));
            enter_interpreter(apply);
        } else {
            expr = read(cell_port(current_input_port));
            if (eq(expr, the_eof_object))
                break;
            env = user_initial_env;
            enter_interpreter(eval);
            print_expr(value);
        }
/*	close_port(cell_port(current_input_port)); */
}

int main(int argc, char **argv)
{
    srand(time(NULL));
    setup_memory();
    install_primitives();
    if (argc == 1)
        driver_loop("-");
    else {
        int i;
        for (i = 1; i < argc; ++i)
            driver_loop(argv[i]);
    }
    return 0;
}
