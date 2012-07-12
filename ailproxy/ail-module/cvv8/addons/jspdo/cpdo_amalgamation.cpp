#include "cpdo_amalgamation.hpp"
#if CPDO_ENABLE_SQLITE3
namespace {
    static const int registration_sq3 = cpdo_driver_sqlite3_register();
}
#endif /*CPDO_ENABLE_SQLITE3*/
#if CPDO_ENABLE_MYSQL5
namespace {
    static const int registration_my5 = cpdo_driver_mysql5_register();
}
#endif /*CPDO_ENABLE_MYSQL5*/
/* start of file cpdo_amalgamation.c */
#if !defined(__STDC_FORMAT_MACROS) /* required for PRIi32 and friends.*/
#  define __STDC_FORMAT_MACROS
#endif
/* start of file cpdo.c */
#include <assert.h>
#include <string.h> /* strcmp() */
#include <stdlib.h> /* atexit(), malloc() and friends. */

#include <stdio.h> /* only for debuggering */
#include <inttypes.h> /* only used for debuggering */
#define MARKER if(1) printf("MARKER: %s:%d:%s():\t",__FILE__,__LINE__,__func__); if(1) printf

#if defined(__cplusplus)
extern "C" {
#endif

const cpdo_stmt cpdo_stmt_empty = cpdo_stmt_empty_m;
const cpdo_connect_opt cpdo_connect_opt_empty = cpdo_connect_opt_empty_m;
const cpdo_driver_details cpdo_driver_details_empty = cpdo_driver_details_empty_m;
const cpdo_bind_val cpdo_bind_val_empty = cpdo_bind_val_empty_m;

char const * cpdo_rc_string(int rc)
{
    if(0 == rc) return "OK";
#define CHECK(N) else if(cpdo_rc.N == rc ) return #N
    CHECK(OK);
    CHECK(ArgError);
    CHECK(RangeError);
    CHECK(TypeError);
    CHECK(IOError);
    CHECK(AllocError);
    CHECK(NYIError);
    CHECK(InternalError);
    CHECK(UnsupportedError);
    CHECK(NotFoundError);
    CHECK(UnknownError);
    CHECK(CheckDbError);
    CHECK(ConnectionError);
    CHECK(AccessError);
    CHECK(UsageError);
    else return "UnknownError";
#undef CHECK
}


int cpdo_split_dsn( char const * dsn,
                    char * out, uint32_t outLen,
                    char const ** paramPos )
{
    size_t const slen = dsn ? strlen(dsn) : 0;
    if( !outLen || (slen<2) || (slen >= outLen) ) return cpdo_rc.RangeError;
    else
    {
        char * pos = out;
        uint32_t at = 0;
        memcpy(out, dsn, slen );
        memset(out+slen, 0, outLen-slen);
        for( ; *pos && (at<outLen) ; ++pos, ++at )
        {
            if( ':' == *pos )
            {
                *pos = 0;
                ++pos;
                break;
            }
        }
        if( !*pos ) return cpdo_rc.RangeError;
        if( paramPos ) *paramPos = pos;
        return (at == outLen) ? cpdo_rc.RangeError : 0;
    }
}


enum {
/**
    Max length, including NUL terminator, of a driver's  name.
    */
CPDO_DRIVER_MAX_NAME_LENGTH = 33,
/** Number of slots of driver registration.
    The API docs guaranty at least 20 slots.
*/
CPDO_DRIVER_LIST_LENGTH = 20
};
typedef struct cpdo_driver_reg cpdo_driver_reg;
struct cpdo_driver_reg
{
    char name[CPDO_DRIVER_MAX_NAME_LENGTH];
    int (*factory)( cpdo_driver ** );
};
#define cpdo_driver_reg_empty_m {{0},NULL}
/**
    The list used by cpdo_driver_register() and cpdo_driver_search().
*/
static cpdo_driver_reg CPDO_DRIVER_LIST[CPDO_DRIVER_LIST_LENGTH] =
{
#define X cpdo_driver_reg_empty_m
X,X,X,X,X,
X,X,X,X,X,
X,X,X,X,X,
X,X,X,X,X
#undef X
};

/**
   Searches for a registered driver with the given name. If one is
   found, 0 is returned and if slot is not NULL then *slot is assigned
   to the registration entry. Returns cpdo_rc.NotFoundError if not
   entry is found.
*/
static int cpdo_driver_search( char const * name, cpdo_driver_reg ** slot );


int cpdo_driver_new( cpdo_driver ** tgt,
                     char const * driver,
                     char const * opt )
{
    cpdo_driver_reg * reg = NULL;
    int rc;
    if( ! driver || !tgt ) return cpdo_rc.ArgError;
    /**
       FIXME: put these in a registration table.
    */
    rc = cpdo_driver_search( driver, &reg );
    if( rc ) return cpdo_rc.NotFoundError;
    assert( reg );
    return reg->factory(tgt);
}

int cpdo_driver_new_connect( cpdo_driver ** tgt, char const * dsn,
                             char const * user, char const * passwd )
{
    if( ! dsn || !tgt ) return cpdo_rc.ArgError;
    else
    {
        enum { BufSize = 256U };
        char buf[BufSize];
        cpdo_driver * drv = NULL;
        char const * params = NULL;
        int rc = cpdo_split_dsn( dsn, buf, BufSize, &params );
        if( rc ) return rc;
        rc = cpdo_driver_new( &drv, buf, params );
        if( rc ) return rc;
        else
        {
            cpdo_connect_opt copt = cpdo_connect_opt_empty;
            copt.dsn = dsn;
            copt.user_name = user;
            copt.password = passwd;
            rc = drv->api->connect( drv, &copt );
            *tgt = drv;
            return rc;
        }
    }
}

int cpdo_sql_escape( char const * sql, uint32_t * len, char ** dest,
                     char quoteChar, char escapeChar, char addQuotes )
{
    if( !dest || !len ) return cpdo_rc.ArgError;
    else if( !sql )
    {
        char * tmp = (char *)malloc(5);
        if( ! tmp ) return cpdo_rc.AllocError;
        strcpy( tmp, "NULL" );
        *dest = tmp;
        *len = 4;
        return 0;
    }
    else
    {
        uint32_t sz = (addQuotes ? 2 /* open/closing quotes */ : 0)
            + 1 /* NUL pad */
            ;
        char * esc = NULL;
        char * escStart = NULL;
        char const * pos = sql;
        uint32_t const slen = *len;
        /* count the number of single-quotes and base our malloc() off
           of that.
        */
        for( ; *pos && (pos<(sql+slen)); ++pos, ++sz )
        {
            if( quoteChar == *pos ) ++sz;
        }
        esc = (char *)calloc(1,sz);
        if( ! esc ) return cpdo_rc.AllocError;
        escStart = esc;
        pos = sql;
        if( addQuotes ) *(esc++) = quoteChar;
        for( ; *pos && (pos<(sql+slen)); ++pos )
        {
            if( quoteChar == *pos )
            {
                *(esc++) = escapeChar;
            }
            *(esc++) = *pos;
        }
        if( addQuotes ) *(esc++) = quoteChar;
        *len = esc - escStart;
        *dest = escStart;
        return 0;
    }
}

int cpdo_exec( cpdo_driver * drv, char const * sql, uint32_t len )
{
    if( !drv || !sql || !len || !*sql ) return cpdo_rc.ArgError;
    else if( !drv->api->is_connected(drv) ) return cpdo_rc.ConnectionError;
    else
    {
        cpdo_stmt * st = NULL;
        int rc = drv->api->prepare( drv, &st, sql, len );
        if( 0 == rc )
        {
            rc = st->api->step(st);
            st->api->finalize(st);
            if( rc != CPDO_STEP_ERROR ) rc = 0;
        }
        return rc;
    }
}

static int cpdo_driver_search( char const * name, cpdo_driver_reg ** slot )
{
    size_t nlen = 0;
    if( ! name ) return cpdo_rc.ArgError;
    else if( !*name ) return cpdo_rc.RangeError;
    else if( CPDO_DRIVER_MAX_NAME_LENGTH <= (nlen=strlen(name)) ) return cpdo_rc.RangeError;    
    else
    {
        cpdo_driver_reg * r = NULL;
        int i = 0;
        for( r = &CPDO_DRIVER_LIST[0];
             i < CPDO_DRIVER_LIST_LENGTH;
             ++i, r = &CPDO_DRIVER_LIST[i] )
        {
            if( ! *r->name )
            {
                continue;
            }
            else if( 0 == strcmp(r->name,name) )
            {
                if( slot ) *slot = r;
                return 0;
            }
        }
        return cpdo_rc.NotFoundError;
    }
}

int cpdo_driver_register( char const * name, cpdo_driver_factory_f factory )
{

    size_t nlen = 0;
    if( ! name || !factory ) return cpdo_rc.ArgError;
    else if( !*name ) return cpdo_rc.RangeError;
    else if( CPDO_DRIVER_MAX_NAME_LENGTH <= (nlen=strlen(name)) ) return cpdo_rc.RangeError;    
    else
    {
        cpdo_driver_reg * r = NULL;
        int i = 0;
        for( r = &CPDO_DRIVER_LIST[0];
             i < CPDO_DRIVER_LIST_LENGTH;
             ++i, r = &CPDO_DRIVER_LIST[i] )
        {
            if( ! *r->name )
            {
                break;
            }
            else if( 0 == strcmp(r->name, name) )
            {
                return cpdo_rc.AccessError;
            }
        }
        if( i == CPDO_DRIVER_LIST_LENGTH )
        {
            return cpdo_rc.AllocError;
        }
        assert( r && !*r->name );
        /*
            Reminder to self: set the factory before the name,
            to preempt a corner case in the un-thread-safety which
            could cause cpdo_driver_search() to match the name as its
            last byte is being written, but then step on a null factory
            handle.
        */        
        r->factory = factory;
        memcpy( r->name, name, nlen );
        return 0;
    }
}

char const * const * cpdo_available_drivers()
{

    static char const * names[CPDO_DRIVER_MAX_NAME_LENGTH+1];
    cpdo_driver_reg * r = NULL;
    int i = 0;
    int x = 0;
    names[CPDO_DRIVER_MAX_NAME_LENGTH] = NULL;
    for( r = &CPDO_DRIVER_LIST[0];
         i < CPDO_DRIVER_LIST_LENGTH;
         ++i, r = &CPDO_DRIVER_LIST[i] )
    {
        if( *r->name )
        {
            names[x++] = r->name;
        }
    }
    for( i = x; i < CPDO_DRIVER_LIST_LENGTH; ++i )
    {
        names[i] = NULL;
    }
    return names;
}


/** @internal

Tokenizes an input string on a given separator. Inputs are:

- (inp) = is a pointer to the pointer to the start of the input.

- (separator) = the separator character

- (end) = a pointer to NULL. i.e. (*end == NULL)

This function scans *inp for the given separator char or a NULL char.
Successive separators at the start of *inp are skipped. The effect is
that, when this function is called in a loop, all neighboring
separators are ignored. e.g. the string "aa.bb...cc" will tokenize to
the list (aa,bb,cc) if the separator is '.' and to (aa.,...cc) if the
separator is 'b'.

Returns 0 (false) if it finds no token, else non-0 (true).

Output:

- (*inp) will be set to the first character of the next token.

- (*end) will point to the one-past-the-end point of the token.

If (*inp == *end) then the end of the string has been reached
without finding a token.

Post-conditions:

- (*end == *inp) if no token is found.

- (*end > *inp) if a token is found.

It is intolerant of NULL values for (inp, end), and will assert() in
debug builds if passed NULL as either parameter.
*/
char cpdo_next_token( char const ** inp, char separator, char const ** end )
{
    char const * pos = NULL;
    assert( inp && end && *inp );
    if( ! inp || !end ) return 0;
    else if( *inp == *end ) return 0;
    pos = *inp;
    if( !*pos )
    {
        *end = pos;
        return 0;
    }
    for( ; *pos && (*pos == separator); ++pos) { /* skip preceeding splitters */ }
    *inp = pos;
    for( ; *pos && (*pos != separator); ++pos) { /* find next splitter */ }
    *end = pos;
    return (pos > *inp) ? 1 : 0;
}

char cpdo_token_bool_val(char const * str)
{
    return (str && *str && ((*str=='1')||(*str=='t')||(*str=='T')||(*str=='y')||(*str=='Y'))
            )
        ? 1
        : 0;
}

int cpdo_bind_val_clean( cpdo_bind_val * b )
{
    if( ! b ) return cpdo_rc.ArgError;
    else
    {
        switch(b->type)
        {
          case CPDO_TYPE_CUSTOM:
              if( b->valu.custom.dtor )
              {
                  b->valu.custom.dtor( b->valu.custom.mem );
              }
              break;
          case CPDO_TYPE_BLOB:
          case CPDO_TYPE_STRING:
              free( b->valu.blob.mem );
              b->valu.blob.length = 0;
              b->valu.blob.mem = NULL;
              /* fall through */
          default:
              break;
        };
        *b = cpdo_bind_val_empty;
        return 0;
    }
}

int cpdo_bind_val_free( cpdo_bind_val * b )
{
    int const rc = cpdo_bind_val_clean(b);
    if( 0 == rc )
    {
        free(b);
    }
    return rc;
}

int cpdo_bind_val_custom( cpdo_bind_val * b, void * mem,
                          void (*dtor)(void *), int typeTag )
{
    if( ! b ) return cpdo_rc.ArgError;
    else
    {
        cpdo_bind_val_clean(b);
        b->type = CPDO_TYPE_CUSTOM;
        b->valu.custom.dtor = dtor;
        b->valu.custom.mem = mem;
        b->valu.custom.type_tag = typeTag;
        return 0;
    }
}

int cpdo_bind_val_null( cpdo_bind_val * b )
{
    if( ! b ) return cpdo_rc.ArgError;
    else
    {
        cpdo_bind_val_clean(b);
        b->type = CPDO_TYPE_NULL;
        return 0;
    }
}

int cpdo_bind_val_int8( cpdo_bind_val * b, int8_t v )
{
    if( ! b ) return cpdo_rc.ArgError;
    else
    {
        cpdo_bind_val_clean(b);
        b->type = CPDO_TYPE_INT8;
        b->valu.i8 = v;
        return 0;
    }
}
int cpdo_bind_val_int16( cpdo_bind_val * b, int16_t v )
{
    if( ! b ) return cpdo_rc.ArgError;
    else
    {
        cpdo_bind_val_clean(b);
        b->type = CPDO_TYPE_INT16;
        b->valu.i16 = v;
        return 0;
    }
}

int cpdo_bind_val_int32( cpdo_bind_val * b, int32_t v )
{
    if( ! b ) return cpdo_rc.ArgError;
    else
    {
        cpdo_bind_val_clean(b);
        b->type = CPDO_TYPE_INT32;
        b->valu.i32 = v;
        return 0;
    }
}
int cpdo_bind_val_int64( cpdo_bind_val * b, int64_t v )
{
    if( ! b ) return cpdo_rc.ArgError;
    else
    {
        cpdo_bind_val_clean(b);
        b->type = CPDO_TYPE_INT64;
        b->valu.i64 = v;
        return 0;
    }
}
    
int cpdo_bind_val_double( cpdo_bind_val * b, double v )
{
    if( ! b ) return cpdo_rc.ArgError;
    else
    {
        cpdo_bind_val_clean(b);
        b->type = CPDO_TYPE_DOUBLE;
        b->valu.dbl = v;
        return 0;
    }
}

int cpdo_bind_val_float( cpdo_bind_val * b, float v )
{
    if( ! b ) return cpdo_rc.ArgError;
    else
    {
        cpdo_bind_val_clean(b);
        b->type = CPDO_TYPE_FLOAT;
        b->valu.flt = v;
        return 0;
    }
}

/**
   Internal impl of cpdo_bind_val_string() and cpdo_bind_val_blob().
   If isString is true then the former, else the latter.
*/
static int cpdo_bind_val_strblob( cpdo_bind_val * b, char isString, void const * v, uint32_t len )
{
    if( ! b ) return cpdo_rc.ArgError;
    else
    {
        void * mem = NULL;
        if( (b->type == CPDO_TYPE_STRING) || (b->type == CPDO_TYPE_BLOB) )
        { /* see if we can re-use the buffer... */
            if( (b->valu.blob.length >= len) && b->valu.blob.mem )
            {
                if( v )
                { /* copy v */
                    memcpy(b->valu.blob.mem, v, len);
                    memset((char *)b->valu.blob.mem + len, 0,
                           b->valu.blob.length - len);
                }
                else
                {
                    memset(b->valu.blob.mem, 0, b->valu.blob.length);
                }
                b->type = isString ? CPDO_TYPE_STRING : CPDO_TYPE_BLOB
                    /* just in case we're switching from blob to
                       string or vice versa. */
                    ;
                return 0;
            }
        }
        cpdo_bind_val_clean(b);
        if( NULL != v
            /* even if len is 0, so we treat literal null and empty
               string differently*/
            )
        {
            mem = malloc(len+1);
            if( NULL == mem ) return cpdo_rc.AllocError;
            else
            {
                memcpy( mem, v, len+1 );
                ((char *)mem)[len] = 0;
                b->type = isString ? CPDO_TYPE_STRING : CPDO_TYPE_BLOB;
                b->valu.blob.mem = mem;
                b->valu.blob.length = len;
                return 0;
            }
        }
        else if( ! len )
        {
            b->type = isString ? CPDO_TYPE_STRING : CPDO_TYPE_BLOB;
            b->valu.blob.mem = NULL;
            b->valu.blob.length = 0;
            return 0;
        }
        else /* allocate the blob ourselves. */
        {
            b->type = isString ? CPDO_TYPE_STRING : CPDO_TYPE_BLOB;
            b->valu.blob.mem = calloc(len+1,1);
            if( ! b->valu.blob.mem ) return cpdo_rc.AllocError;
            b->valu.blob.length = len;
            return 0;
        }
    }
}

int cpdo_bind_val_string( cpdo_bind_val * b, char const * v, uint32_t len )
{
    return cpdo_bind_val_strblob( b, 1, v, len );
}

int cpdo_bind_val_blob( cpdo_bind_val * b, void const * v, uint32_t len )
{
    return cpdo_bind_val_strblob( b, 0, v, len );
}

cpdo_bind_val * cpdo_bind_val_list_new( uint16_t len )
{
    if( ! len ) return NULL;
    else
    {
        cpdo_bind_val * rc = (cpdo_bind_val *)malloc(len * sizeof(cpdo_bind_val));
        if( NULL != rc )
        {
            uint16_t i = 0;
            for( ; i < len; ++i )
            {
                rc[i] = cpdo_bind_val_empty;
            }
        }
        return rc;
    }
}

int cpdo_bind_val_list_free( cpdo_bind_val * list, uint16_t len )
{
    if( ! list || !len ) return cpdo_rc.ArgError;
    else
    {
        cpdo_bind_val * v = list;
        uint16_t i = 0;
        for( ; i < len; ++i )
        {
            cpdo_bind_val_clean( &v[i] );
        }
        free(list);
        return 0;
    }

}
cpdo_data_type cpdo_get_type( cpdo_stmt * st, uint16_t ndx )
{
    cpdo_data_type rc = CPDO_TYPE_ERROR;
    if( st ) st->api->get.type(st, ndx, &rc);
    return rc;
}
int8_t cpdo_get_int8( cpdo_stmt * st, uint16_t ndx )
{
    int8_t v = 0;
    if( st ) st->api->get.i8( st, ndx, &v);
    return v;
}
int16_t cpdo_get_int16( cpdo_stmt * st, uint16_t ndx )
{
    int16_t v = 0;
    if( st ) st->api->get.i16( st, ndx, &v);
    return v;
}
    
int32_t cpdo_get_int32( cpdo_stmt * st, uint16_t ndx )
{
    int32_t v = 0;
    if( st ) st->api->get.i32( st, ndx, &v);
    return v;
}

int64_t cpdo_get_int64( cpdo_stmt * st, uint16_t ndx )
{
    int64_t v = 0;
    if( st ) st->api->get.i64( st, ndx, &v);
    return v;
}

double cpdo_get_double( cpdo_stmt * st, uint16_t ndx )
{
    double v = 0.0;
    if( st ) st->api->get.dbl( st, ndx, &v);
    return v;
}

float cpdo_get_float( cpdo_stmt * st, uint16_t ndx )
{
    float v = 0.0;
    if( st ) st->api->get.flt( st, ndx, &v);
    return v;
}

char const * cpdo_get_string( cpdo_stmt * st, uint16_t ndx, uint32_t * len )
{
    char const * v = NULL;
    if( st ) st->api->get.string( st, ndx, &v, len);
    return v;
}

void const * cpdo_get_blob( cpdo_stmt * st, uint16_t ndx, uint32_t * len )
{
    void const * v = NULL;
    if( st ) st->api->get.blob( st, ndx, &v, len);
    return v;
}


int cpdo_bind_int8( cpdo_stmt * st, uint16_t ndx, int8_t v )
{
    return st
        ? st->api->bind.i8( st, ndx, v)
        : cpdo_rc.ArgError;
}

int cpdo_bind_int16( cpdo_stmt * st, uint16_t ndx, int16_t v )
{
    return st
        ? st->api->bind.i16( st, ndx, v)
        : cpdo_rc.ArgError;
}

int cpdo_bind_int32( cpdo_stmt * st, uint16_t ndx, int32_t v )
{
    return st
        ? st->api->bind.i32( st, ndx, v)
        : cpdo_rc.ArgError;
}

int cpdo_bind_int64( cpdo_stmt * st, uint16_t ndx, int64_t v )
{
    return st
        ? st->api->bind.i64( st, ndx, v)
        : cpdo_rc.ArgError;
}

int cpdo_bind_float( cpdo_stmt * st, uint16_t ndx, float v )
{
    return st
        ? st->api->bind.flt( st, ndx, v)
        : cpdo_rc.ArgError;
}

int cpdo_bind_double( cpdo_stmt * st, uint16_t ndx, double v )
{
    return st
        ? st->api->bind.dbl( st, ndx, v)
        : cpdo_rc.ArgError;
}

int cpdo_bind_string( cpdo_stmt * st, uint16_t ndx, char const * v, uint32_t length )
{
    return st
        ? st->api->bind.string( st, ndx, v, length)
        : cpdo_rc.ArgError;
}

int cpdo_bind_blob( cpdo_stmt * st, uint16_t ndx, void const * v, uint32_t length )
{
    return st
        ? st->api->bind.blob( st, ndx, v, length)
        : cpdo_rc.ArgError;
}

int cpdo_close( cpdo_driver * drv )
{
    return (drv&&drv->api)
        ? drv->api->close(drv)
        : cpdo_rc.ArgError;
}
int cpdo_driver_connect( cpdo_driver * drv, cpdo_connect_opt const * opt )
{
    return (drv&&drv->api)
        ? drv->api->connect(drv,opt)
        : cpdo_rc.ArgError;
}

int cpdo_stmt_finalize( cpdo_stmt * st )
{
    return (st&&st->api)
        ? st->api->finalize(st)
        : cpdo_rc.ArgError;
}


cpdo_step_code cpdo_step( cpdo_stmt * st )
{
    return (st&&st->api)
        ? st->api->step(st)
        : CPDO_STEP_ERROR;
}

char const * cpdo_driver_name( cpdo_driver const * drv )
{
    return drv ?
        drv->api->constants.driver_name
        : NULL;
}

int cpdo_prepare( cpdo_driver * drv, cpdo_stmt ** tgt, char const * sql, uint32_t length )
{
    return (drv && tgt && sql && *sql)
        ? drv->api->prepare(drv, tgt, sql, length)
        : cpdo_rc.ArgError;
}

uint64_t cpdo_last_insert_id( cpdo_driver * drv, char const * hint )
{
    uint64_t rv = 0;
    if( drv ) drv->api->last_insert_id(drv, &rv, hint);
    return rv;
}



/**
   Returns true (non-0) if ch is an SQL named parameter identifier
   character. If isFirst, then numberic characters will not
   be considered a match. Pass true only for the first character
   in the sequence you are testing.
*/
static char is_param_char(char ch, char isFirst)
{
    return ((ch == '_')
            || ((ch >= 'a') && (ch <= 'z'))
            || ((ch >= 'A') && (ch <= 'Z'))
            || (!isFirst
                && ((ch >= '0')
                    && (ch <= '9'))
                )
            )
        ;
}

char cpdo_find_next_named_param( char const * inp,
                                 uint32_t len,
                                 char paramChar,
                                 char alsoDoQMarks,
                                 char const **paramBegin,
                                 char const **paramEnd )
{
    char const * pos = inp;
    char const * markBegin = NULL;
    char const * inpEnd = inp + len;
    char ch;
    char isEsc = 0;
    char quoteChar = 0;
    if( !inp || !paramBegin || !paramEnd ) return 0;
    else if( ('"'==paramChar)
             || ('\''==paramChar)
             || ('\\'==paramChar)
             || ('?'==paramChar)
             )
    {
        /* for sanity's sake! */
        return 0;
    }
    for( ; (pos < inpEnd) && *pos; ++pos )
    {
        ch = *pos;
        if( isEsc )
        {
            isEsc = 0;
            continue;
        }
        else if( ('\'' == ch) || ('"'==ch) )
        {
            if( ch == quoteChar ) quoteChar = 0 /* end of string */;
            else if( ! quoteChar ) quoteChar = ch /* begining of string */;
            /* else we're in a string */
            continue;
        }
        else if( '\\' == ch )
        {
            isEsc = 1;
            continue;
        }
        else if( quoteChar /* we're in a string */) continue;
        else if( alsoDoQMarks && ('?' == ch) )
        { /* special case: treat '?' as an identifier */
            *paramBegin = pos++;
            *paramEnd = pos;
            return 1;
        }
        else if( '-' == ch  )
        { /* possible SQL comment ... */
            if( '-' == pos[1] )
            {
                for( ++pos ; (pos < inpEnd) && ('\n' != *pos); ++pos )
                {
                    /* read until EOL */
                }
            }
            continue;
        }
        else if( paramChar == ch )
        { /* parse out the parameter. We're assuming that it's well-formed! */
            markBegin = pos;
            for( ++pos ; (pos < inpEnd) && *pos; ++pos )
            {
                ch = *pos;
                if( is_param_char(ch, (markBegin==(pos+1))) ) {
                    continue;
                }
                else {
                    break;
                }
            }
            if( (pos-markBegin) > 1 )
            {
                *paramBegin = markBegin;
                *paramEnd = pos;
                return 1;
            }
        }
    }
    return 0;
}

int cpdo_named_params_to_qmarks( char const * inp,
                                 uint32_t len,
                                 char paramChar,
                                 char alsoDoQMarks,
                                 uint16_t * count,
                                 char ** out,
                                 uint32_t * outLen,
                                 char *** nameList )
{
    char * mem;
    char * mem2;
    char * outPos;
    char const * pos = inp;
    char const * inpEnd = inp + len;
    char const * begin = inp;
    char const * end = NULL;
    char ** list = NULL;
    uint16_t rc = 0;
    enum { BufSize = 100 };
    uint32_t osize = 0;
    uint32_t slen = 0;
    uint32_t i = 0;
    struct holder {
        char const * b;
        char const * e;
        uint16_t len;
    } h[BufSize];
    if( !count || !inp || !out ) return cpdo_rc.ArgError;
    mem = (char *)calloc( len + 1, 1 );
    if( ! mem ) return cpdo_rc.AllocError;
    memset( &h, 0, sizeof(h) );
    outPos = mem;
    while( cpdo_find_next_named_param( pos, (inpEnd-pos), paramChar, alsoDoQMarks, &begin, &end ) )
    {
        if( rc >= BufSize /* need last element to mark end of list */ )
        {
            free(mem);
            return cpdo_rc.RangeError;
        }
        for( ; pos < begin; ++pos )
        { /* write out bytes PRECEEDING named param. */
            *(outPos++) = *pos;
        }
        *(outPos++) = '?';
        h[rc].b = begin;
        h[rc].e = end;
        h[rc].len = end-begin;
        ++rc;
        pos = end;
        begin = end = NULL;
    }
    if( ! rc )
    {
        free(mem);
        *out = NULL;
        *count = 0;
        if( outLen ) *outLen = 0;
        return 0;
    }
    for( ; pos < inpEnd; ++pos )
    { /* write out trailing bytes. */
        *(outPos++) = *pos;
    }
    if( ! nameList )
    {
        *out = mem;
        *count = rc;
        if( outLen ) *outLen = (outPos-mem);
        return 0;
    }
    /* Now jump through some hoops to stuff the returned names into the
       same memory buffer as *out...
    */
    slen = strlen(mem);
    /* Figure out how much space we need... */
    osize = slen + 1/*NUL*/
        + (rc * sizeof(char *) /*nameList*/);
    for( i = 0; i < rc; ++i )
    {
        osize += h[i].len + 1/*NUL*/;
    }
    mem2 = (char *)realloc( mem, osize );
    if( ! mem2 )
    {
        free(mem);
        return cpdo_rc.AllocError;
    }
    mem = mem2;
    /* this code easily qualifies as trying to be far too clever... */
    memset( mem + slen, 0, osize - slen ) /* clear trailing bytes */;
    list = (char **)(mem + slen + 1);
    mem2 = mem + slen + 1 + (rc*sizeof(char*));
    *nameList = list;
    /** Now copy the stored parameter names into *nameList area... */
    for( i = 0; i < rc; ++i )
    {
        list[i] = mem2;
        memcpy( mem2, h[i].b, h[i].len );
        mem2[h[i].len] = 0;
        mem2 += h[i].len + 1;
    }
    *out = mem;
    *count = rc;
    if( outLen ) *outLen = slen;
    return 0;
}

#if CPDO_ENABLE_64_BIT
typedef uint64_t cpdo_hash_t;
#else
typedef uint32_t cpdo_hash_t;
#endif
int cpdo_bind_val_tag_type_hash( cpdo_driver_api const * key, int v )
{
    return ((int)((cpdo_hash_t) key) & 0xffffff00) | v;
}


char cpdo_bind_val_tag_type_check_origin( cpdo_driver_api const * key, int const v )
{
    return ( (((cpdo_hash_t) key) & 0xffffff00) & v) ? 1 : 0;
}


char * cpdo_mprintf_v( char const * fmt, va_list vargs )
{
    return cpdo_printfv_str( fmt, vargs );
}

char * cpdo_mprintf( char const * fmt, ... )
{
    char * ret = NULL;
    va_list vargs;
    va_start( vargs, fmt );
    ret = cpdo_printfv_str( fmt, vargs );
    va_end( vargs );
    return ret;
}

int cpdo_prepare_f_v( cpdo_driver * drv, cpdo_stmt ** tgt, char const * fmt, va_list vargs)
{
    char * sql;
    int rc;
    if( ! drv || !tgt || !fmt || !*fmt ) return cpdo_rc.ArgError;
    sql = cpdo_mprintf_v( fmt, vargs );
    if( ! sql ) return cpdo_rc.AllocError;
    rc = cpdo_prepare( drv, tgt, sql, strlen(sql) );
    free(sql);
    return rc;
}

int cpdo_prepare_f( cpdo_driver * drv, cpdo_stmt ** tgt, char const * fmt, ... )
{
    int ret;
    va_list vargs;
    va_start( vargs, fmt );
    ret = cpdo_prepare_f_v( drv, tgt, fmt, vargs );
    va_end( vargs );
    return ret;
}

int cpdo_exec_f_v(  cpdo_driver * drv, char const * fmt, va_list vargs)
{
    char * sql;
    int rc;
    sql = cpdo_mprintf_v( fmt, vargs );
    if( ! sql ) return cpdo_rc.AllocError;
    rc = cpdo_exec( drv, sql, strlen(sql) );
    free(sql);
    return rc;
}

int cpdo_exec_f(  cpdo_driver * drv, char const * fmt, ... )
{
    int ret;
    va_list vargs;
    if( ! drv || !fmt || !*fmt ) return cpdo_rc.ArgError;
    va_start( vargs, fmt );
    ret = cpdo_exec_f_v( drv, fmt, vargs );
    va_end( vargs );
    return ret;
}

int cpdo_bind_string_f_v( cpdo_stmt * st, uint16_t ndx, char const * fmt, va_list vargs )
{
    char * sql;
    int rc;
    if( !st || !fmt || !*fmt ) return cpdo_rc.ArgError;
    sql = cpdo_mprintf_v( fmt, vargs );
    if( ! sql ) return cpdo_rc.AllocError;
    rc = cpdo_bind_string( st, ndx, sql, strlen(sql) );
    free(sql);
    return rc;
}

int cpdo_bind_string_f( cpdo_stmt * st, uint16_t ndx, char const *fmt, ... )
{
    int ret;
    va_list vargs;
    va_start( vargs, fmt );
    ret = cpdo_bind_string_f_v( st, ndx, fmt, vargs );
    va_end( vargs );
    return ret;
}

int cpdo_driver_opt_set( cpdo_driver * self, char const * key, ... )
{
    int ret;
    va_list vargs;
    if( !self || !key || !*key ) return cpdo_rc.ArgError;
    va_start( vargs, key );
    ret = self->api->opt.set( self, key, vargs );
    va_end( vargs );
    return ret;
}

int cpdo_driver_opt_get( cpdo_driver * self, char const * key, ... )
{
    int ret;
    va_list vargs;
    if( !self || !key || !*key ) return cpdo_rc.ArgError;
    va_start( vargs, key );
    ret = self->api->opt.get( self, key, vargs );
    va_end( vargs );
    return ret;
}

uint16_t cpdo_param_index( cpdo_stmt * st, char const * name )
{
    return (!st || !name || !*name || ('?'==*name))
        ? cpdo_rc.ArgError
        : st->api->bind.param_index( st, name );
}

char const * cpdo_param_name( cpdo_stmt * st, uint16_t ndx )
{
    return st
        ? st->api->bind.param_name( st, ndx )
        : NULL;
}

int cpdo_version_number()
{
    return CPDO_VERSION_NUMBER;
}

#undef MARKER
#if defined(__cplusplus)
} /*extern "C"*/
#endif
/* end of file cpdo.c */
/* start of file cpdo_skeleton.c */
/** @file cpdo_skeleton.c

    Dummy/empty cpdo_driver impl to provide a starting point for
    new drivers. The goal here is to create a skeleton which will
    compile, but won't actually work because it has no db-specific
    implementation code.
    
    To create a driver, first replace "_skel_" with "_driverName_"
    globally throughout this file. Then go through the whole file,
    from start to finish, and look for places to add the concrete
    impl code. There are many such places. Start with:
    
    - cpdo_skel_driver_alloc()
    - cpdo_skel_driver_free()
    - cpdo_skel_connect()
    - cpdo_skel_close()
    - cpdo_skel_stmt_alloc()
    - cpdo_skel_stmt_free()
    
    With those you can at least get connected and will have the basics
    (including the most important memory management) out of the way.
    
    After that comes the more intimate bits (_how_ intimate depends
    on the underlying driver). See the cpdo_sqlite3 and cpdo_mysql5
    implementations for two very different implementations (sqlite3
    makes it easy for us, MySQL not so much).

    DSN driver parameters:

   - abc=TYPE

   TODO:

    - There's always a list of TODOs.

   LICENSE:

    Add your license here.
*/
#include <assert.h>
#include <stdlib.h> /* malloc()/free() */
#include <string.h> /* strlen() */

#include <stdio.h> /* only for debuggering */
#include <inttypes.h> /* only(?) for debuggering */
#define MARKER if(1) printf("MARKER: %s:%d:%s():\t",__FILE__,__LINE__,__func__); if(1) printf

#if defined(__cplusplus)
extern "C" {
#endif

#define CPDO_DRIVER_NAME "FIXME_SET_THIS_TO_THE_DRIVERS_DSN_NAME"
/************************************************************************
 cpdo_driver_api members:
************************************************************************/
int cpdo_skel_connect( cpdo_driver * self, cpdo_connect_opt const * opt );
static int cpdo_skel_sql_quote( cpdo_driver * self, char const * src, uint32_t * len, char ** dest );
static int cpdo_skel_free_string( cpdo_driver * self, char * str);
static int cpdo_skel_prepare( cpdo_driver * self, cpdo_stmt ** tgt, const char * sql, uint32_t len );
static int cpdo_skel_error_info( cpdo_driver * self, char const ** dest, uint32_t * len, int * errorCode );
static char cpdo_skel_is_connected( cpdo_driver * self );
static int cpdo_skel_close( cpdo_driver * self );
static int cpdo_skel_last_insert_id( cpdo_driver * self, uint64_t * v, char const * hint );
static cpdo_driver_details const * cpdo_skel_driver_details();
static int cpdo_skel_driver_begin_transaction( cpdo_driver * self );
static int cpdo_skel_driver_commit( cpdo_driver * self );
static int cpdo_skel_driver_rollback( cpdo_driver * self );
static char cpdo_skel_driver_in_trans( cpdo_driver * self );
static int cpdo_skel_driver_opt_set( cpdo_driver * self, char const * key, va_list vargs );
static int cpdo_skel_driver_opt_get( cpdo_driver * self, char const * key, va_list vargs );
static int cpdo_skel_driver_opt_get_string_quote_char( cpdo_driver * self, char * ch );
const cpdo_driver_api cpdo_skel_driver_api =
{
    cpdo_skel_driver_details,
    cpdo_skel_connect,
    cpdo_skel_sql_quote,
    cpdo_skel_free_string,
    cpdo_skel_prepare,
    cpdo_skel_error_info,
    cpdo_skel_is_connected,
    cpdo_skel_close,
    cpdo_skel_last_insert_id,
    {/*transaction*/
         cpdo_skel_driver_begin_transaction,
         cpdo_skel_driver_commit,
         cpdo_skel_driver_rollback,
         cpdo_skel_driver_in_trans
    },
    {/*opt*/
        cpdo_skel_driver_opt_set,
        cpdo_skel_driver_opt_get,
        cpdo_skel_driver_opt_get_string_quote_char
    },
    {/*constants*/
    CPDO_DRIVER_NAME /*driver_name*/,
    '`' /*table_quote*/
    }
};

/************************************************************************
 cpdo_stmt_api members...
************************************************************************/
static cpdo_step_code cpdo_skel_stmt_step( cpdo_stmt * self );
static int cpdo_skel_stmt_error_info( cpdo_stmt * self, char const ** dest, uint32_t * len, int * errorCode );
static uint16_t cpdo_skel_stmt_column_count( cpdo_stmt * self );
static char const * cpdo_skel_stmt_column_name( cpdo_stmt * self, uint16_t ndx );
static int cpdo_skel_stmt_reset( cpdo_stmt * self );
static uint16_t cpdo_skel_stmt_bind_count( cpdo_stmt * self );
static uint16_t cpdo_skel_stmt_param_index( cpdo_stmt * self, char const * name );
static char const * cpdo_skel_stmt_param_name( cpdo_stmt * self, uint16_t ndx );
static int cpdo_skel_stmt_bind_null( cpdo_stmt * self, uint16_t ndx );
static int cpdo_skel_stmt_bind_int8( cpdo_stmt * self, uint16_t ndx, int8_t v );
static int cpdo_skel_stmt_bind_int16( cpdo_stmt * self, uint16_t ndx, int16_t v );
static int cpdo_skel_stmt_bind_int32( cpdo_stmt * self, uint16_t ndx, int32_t v );
static int cpdo_skel_stmt_bind_int64( cpdo_stmt * self, uint16_t ndx, int64_t v );
static int cpdo_skel_stmt_bind_float( cpdo_stmt * self, uint16_t ndx, float v );
static int cpdo_skel_stmt_bind_double( cpdo_stmt * self, uint16_t ndx, double v );
static int cpdo_skel_stmt_bind_string( cpdo_stmt * self, uint16_t ndx, char const * v, uint32_t len );
static int cpdo_skel_stmt_bind_blob( cpdo_stmt * self, uint16_t ndx, void const * v, uint32_t len );
static int cpdo_skel_stmt_get_type_ndx( cpdo_stmt * self, uint16_t ndx, cpdo_data_type * val );
static int cpdo_skel_stmt_get_int8_ndx( cpdo_stmt * self, uint16_t ndx, int8_t * val );
static int cpdo_skel_stmt_get_int16_ndx( cpdo_stmt * self, uint16_t ndx, int16_t * val );
static int cpdo_skel_stmt_get_int32_ndx( cpdo_stmt * self, uint16_t ndx, int32_t * val );
static int cpdo_skel_stmt_get_int64_ndx( cpdo_stmt * self, uint16_t ndx, int64_t * val );
static int cpdo_skel_stmt_get_float_ndx( cpdo_stmt * self, uint16_t ndx, float * val );
static int cpdo_skel_stmt_get_double_ndx( cpdo_stmt * self, uint16_t ndx, double * val );
static int cpdo_skel_stmt_get_string_ndx( cpdo_stmt * self, uint16_t ndx, char const ** val, uint32_t * len );
static int cpdo_skel_stmt_get_blob_ndx( cpdo_stmt * self, uint16_t ndx, void const ** v, uint32_t * len );
static int cpdo_skel_stmt_finalize( cpdo_stmt * self );
const cpdo_stmt_api cpdo_skel_stmt_api = {
    cpdo_skel_stmt_step,
    cpdo_skel_stmt_error_info,
    cpdo_skel_stmt_finalize,
    {/*bind*/
        cpdo_skel_stmt_reset,
        cpdo_skel_stmt_bind_count,
        cpdo_skel_stmt_param_index,
        cpdo_skel_stmt_param_name,
        cpdo_skel_stmt_bind_null,
        cpdo_skel_stmt_bind_int8,
        cpdo_skel_stmt_bind_int16,
        cpdo_skel_stmt_bind_int32,
        cpdo_skel_stmt_bind_int64,
        cpdo_skel_stmt_bind_float,
        cpdo_skel_stmt_bind_double,
        cpdo_skel_stmt_bind_string,
        cpdo_skel_stmt_bind_blob
    },
    {/*get*/
        cpdo_skel_stmt_column_count,
        cpdo_skel_stmt_column_name,
        cpdo_skel_stmt_get_type_ndx,
        cpdo_skel_stmt_get_int8_ndx,
        cpdo_skel_stmt_get_int16_ndx,
        cpdo_skel_stmt_get_int32_ndx,
        cpdo_skel_stmt_get_int64_ndx,
        cpdo_skel_stmt_get_float_ndx,
        cpdo_skel_stmt_get_double_ndx,
        cpdo_skel_stmt_get_string_ndx,
        cpdo_skel_stmt_get_blob_ndx
    }
};


/** Internal data types */
typedef struct cpdo_skel_stmt cpdo_skel_stmt;
static int cpdo_skel_stmt_free(cpdo_skel_stmt *s);
static cpdo_skel_stmt * cpdo_skel_stmt_alloc();

typedef struct cpdo_skel_driver cpdo_skel_driver;
static int cpdo_skel_driver_free(cpdo_skel_driver *d);
static cpdo_skel_driver * cpdo_skel_driver_alloc();


typedef void * FIXME_DB_TYPE;
struct cpdo_skel_driver
{
    FIXME_DB_TYPE conn;
    char isConnected;
    char inTransaction;
    cpdo_driver self;
};


const cpdo_skel_driver cpdo_skel_driver_empty = {
    NULL/*conn*/,
    0/*isConnected*/,
    0/*inTransaction*/,
    {/*self*/
        &cpdo_skel_driver_api /*api*/,
        NULL /*impl*/
    }
};
typedef void * FIXME_STMT_TYPE;
struct cpdo_skel_stmt
{
    FIXME_STMT_TYPE stmt;
    cpdo_skel_driver * driver;
    uint16_t colCount;
    uint16_t paramCount;
    cpdo_stmt self;
};

const cpdo_skel_stmt cpdo_skel_stmt_empty = {
    NULL /*stmt*/,
    NULL /*driver*/,
    0 /* colCount */,
    0 /* paramCount */,
    {/*self*/
        &cpdo_skel_stmt_api /*api*/,
        NULL /*impl*/
    }
};

static cpdo_skel_driver * cpdo_skel_driver_alloc()
{
    cpdo_skel_driver * s = (cpdo_skel_driver*)malloc(sizeof(cpdo_skel_driver));
    if( s )
    {
        /* FIXME: instantiate the connection here if needed. */
        FIXME_DB_TYPE conn = NULL;
        if( ! conn )
        {
            free(s);
            return NULL;
        }
        else
        {
            *s = cpdo_skel_driver_empty;
            s->conn = conn;
            s->self.impl = s;
        }
    }
    return s;
}

/**
   Closes d->conn and frees all memory associated with d.  d does not
   track statements it opens, and all statements must be closed before
   closing the db, else Undefined Behaviour.
*/
static int cpdo_skel_driver_free(cpdo_skel_driver *d)
{
    int rc = cpdo_rc.ArgError;
    if( d )
    {
        rc = 0;
        if( d->conn )
        {
            /*FIXME: call FIXME_DB_TYPE's destructor here:  mysql_close(d->conn); */
        }
        *d = cpdo_skel_driver_empty;
        free(d);
    }
    return rc;
}


/**
   Allocates a new cpdo_skel_stmt and initializes
   its self.impl member to point to the returned
   object.
*/
static cpdo_skel_stmt * cpdo_skel_stmt_alloc()
{
    cpdo_skel_stmt * s = (cpdo_skel_stmt*)malloc(sizeof(cpdo_skel_stmt));
    if( s )
    {
        *s = cpdo_skel_stmt_empty;
        s->self.impl = s;
    }
    return s;
}

/**
   Frees all resources belonging to this statement.  It can return
   non-0, but there is no generic recovery strategy for this, and s is
   freed regardless of whether or not sqlite3_finalize() succeeds.
*/
static int cpdo_skel_stmt_free(cpdo_skel_stmt *st)
{
    int rc = cpdo_rc.ArgError;
    if( st )
    {
        rc = 0;
        if( st->stmt )
        {
            /* FIXME: call FIXME_STMT_TYPE destructor here!
                mysql_stmt_close(st->stmt);
            */
        }
        *st = cpdo_skel_stmt_empty;
        free( st );
    }
    return rc;
}


/**
   cpdo_driver_factory_f() impl._ Allocates a new cpdo_skel_driver.
*/
int cpdo_skel_driver_new( cpdo_driver ** tgt )
{
    if( ! tgt ) return cpdo_rc.ArgError;
    else
    {
        cpdo_skel_driver * d = cpdo_skel_driver_alloc();
        if( d )
        {
            *tgt = &d->self;
            return 0;
        }
        else return cpdo_rc.AllocError;
    }
}

/******************************************************
Convenience macros, called often later on...
*****************************************************/
#define DRV_DECL(RC) cpdo_skel_driver * drv = (self && self->impl && (self->api==&cpdo_skel_driver_api)) \
        ? (cpdo_skel_driver *)self->impl : NULL; \
    if( ! drv ) return RC

#define STMT_DECL(RC) cpdo_skel_stmt * stmt = (self && self->impl && (self->api==&cpdo_skel_stmt_api)) \
        ? (cpdo_skel_stmt *)self->impl : NULL; \
    if( ! stmt ) return RC

#define GETNDX_DECL(NDX) STMT_DECL(cpdo_rc.ArgError); if((NDX) >= stmt->colCount) return cpdo_rc.RangeError;
#define BINDNDX_DECL(NDX) STMT_DECL(cpdo_rc.ArgError); if( !(NDX) || ((NDX) > stmt->paramCount)) return cpdo_rc.RangeError;

static int cpdo_skel_last_insert_id( cpdo_driver * self, uint64_t * v, char const * hint )
{
    DRV_DECL(cpdo_rc.ArgError);
    if( ! v ) return cpdo_rc.ArgError;
    else
    {
        return cpdo_rc.NYIError;
    }
}
    
static int cpdo_skel_close( cpdo_driver * self )
{
    DRV_DECL(cpdo_rc.ArgError);
    cpdo_skel_driver_free(drv);
    return 0;
}

static char cpdo_skel_is_connected( cpdo_driver * self )
{
    DRV_DECL(0);
    return drv->isConnected;
}

static int cpdo_skel_error_info( cpdo_driver * self, char const ** dest, uint32_t * len, int * errorCode )
{
    DRV_DECL(cpdo_rc.ArgError);
    if( ! drv->conn ) return cpdo_rc.ConnectionError;
    else
    {
        return cpdo_rc.NYIError;
#if 0 /* it should look something like this: */
        if( errorCode ) *errorCode = mysql_errno(drv->conn);
        if( dest )
        {
            *dest = mysql_error(drv->conn);
            if( len )
            {
                *len = *dest ? strlen(*dest) : 0;
            }
        }
        return 0;
#endif
    }
}

static int cpdo_skel_sql_quote( cpdo_driver * self, char const * str, uint32_t * len, char ** dest )
{
    if( ! len || !dest ) return cpdo_rc.ArgError;
    else if( NULL == str )
    {
        char * tmp = (char *)malloc(5);
        if( ! tmp ) return cpdo_rc.AllocError;
        strcpy( tmp, "NULL" );
        *dest = tmp;
        *len = 4;
        return 0;
    }
    else
    {
#if 0 /* something like: */
        char * to = NULL;
        unsigned long aLen;
        DRV_DECL(cpdo_rc.ArgError);
        if( ! len ) return cpdo_rc.ArgError;
        aLen = *len * 2 + 1;
        to = calloc(aLen,1);
        if( ! to ) return cpdo_rc.AllocError;
        *len = mysql_real_escape_string( drv->conn, to, str, *len );
        *dest = to;
        return 0;
#else
        return cpdo_rc.NYIError;
#endif
    }
}

static int cpdo_skel_free_string( cpdo_driver * self, char * str)
{
    return str ? (free(str),0) : cpdo_rc.ArgError;
}



static int cpdo_skel_prepare( cpdo_driver * self, cpdo_stmt ** tgt, char const * sql, uint32_t len  )
{
    cpdo_skel_stmt * st = NULL;
    cpdo_stmt * cst = NULL;
    DRV_DECL(cpdo_rc.ArgError);
    st = cpdo_skel_stmt_alloc();
    cst = &st->self;
    /* ... add impl here ... on error be sure to clean up st */
    
    cst->api->finalize(cst) /* is part of st, and will destroy it all */;
    return cpdo_rc.NYIError;
}

int cpdo_skel_connect( cpdo_driver * self, cpdo_connect_opt const * opt )
{
    DRV_DECL(cpdo_rc.ArgError);
    if( ! opt || !opt->dsn ) return cpdo_rc.ArgError;
    else
    {
        enum { BufSize = 128U };
        char const * tokBegin = opt->dsn;
        char const * tokEnd = NULL;
        char kbuf[BufSize] = {0,0};
        char pDbName[BufSize] = {0,0};
        char pHost[BufSize] = {0,0};
        int port = 0;
        int rc = 0;
        if( drv->isConnected ) return cpdo_rc.ConnectionError;
        for( ; *tokBegin && (*tokBegin != ':'); ++tokBegin ) {
            /* skip driver name part of dsn. */
        }
        if( ':' != *tokBegin ) return cpdo_rc.RangeError;
        ++tokBegin /* skip ':'*/;
        port = rc = 0;
         /* Parse DSN options... */
        while( cpdo_next_token( &tokBegin, ';', &tokEnd) )
        { /* TODO: wrap most of this into a helper function
             which does the key/value splitting. We'll need
             this in other drivers.
          */
            if( tokBegin == tokEnd ) break;
            else
            {
                char const * key = tokBegin;
                char const * value = NULL;
                char * at = kbuf;
                if( (tokEnd - tokBegin) >= BufSize ) return cpdo_rc.RangeError;
                memset( kbuf, 0, BufSize );
                /* Write the key part to the buffer... */
                for( ; (key<tokEnd) && *key && ('='!=*key); ++key ) {
                    *(at++) = *key;
                }
                *(at++) = 0;
                value = at;
                if( '=' == *key ) {
                    ++key;
                }
                /* now write the value part to the buffer... */
                for( ; (key<tokEnd) && *key; ++key ) {
                    *(at++) = *key;
                }
                key = kbuf;
                /*MARKER("key=[%s] value=[%s]\n", key, value);*/

                /* Done parsing. Now see if we understand how to use
                   this option... */
                if( 0 == strcmp("port",key) )
                { /* remember that mysql ignores the port number when
                     connecting to localhost via a UNIX socket.
                  */
                    port = *value ? atoi(value) : 0;
                    if( port < 0 ) port = 0;
                }
                else if( 0 == strcmp("dbname",key) )
                {
                    size_t const slen = strlen(value);
                    if( slen >= BufSize ) return cpdo_rc.RangeError;
                    memcpy( pDbName, value, slen );
                    pDbName[slen] = 0;
                }
                else if( 0 == strcmp("host",key) )
                {
                    size_t const slen = strlen(value);
                    if( slen >= BufSize ) return cpdo_rc.RangeError;
                    memcpy( pHost, value, slen );
                    pDbName[slen] = 0;
                }
                else
                {
                    /* ignore unknown keys: this is optional in the CPDO
                       interface.
                    */
                }
                /* set up for the next token... */
                tokBegin = tokEnd;
                tokEnd = NULL;
            }
        } /* options parsing */
        
        /**
            TODO: establish the connection to drv->conn.
            On success set (drv->isConnected = 1).
        */
        
        return cpdo_rc.NYIError;
    }
}


static int cpdo_skel_driver_begin_transaction( cpdo_driver * self )
{
    int rc;
    DRV_DECL(cpdo_rc.ArgError);
    if( drv->inTransaction ) return cpdo_rc.UnsupportedError;
    rc = cpdo_exec( self, "BEGIN", 5 );
    if( 0 == rc ) drv->inTransaction = 1;
    return rc;
}

static int cpdo_skel_driver_commit( cpdo_driver * self )
{
    int rc;
    DRV_DECL(cpdo_rc.ArgError);
    rc = cpdo_exec( self, "COMMIT", 6 );
    drv->inTransaction = 0;
    return (0==rc)
        ? 0
        : cpdo_rc.CheckDbError;
}

static int cpdo_skel_driver_rollback( cpdo_driver * self )
{
    int rc;
    DRV_DECL(cpdo_rc.ArgError);
    rc = cpdo_exec( self, "ROLLBACK", 8 );
    drv->inTransaction = 0;
    return (0==rc)
        ? 0
        : cpdo_rc.CheckDbError;
}

static char cpdo_skel_driver_in_trans( cpdo_driver * self )
{
    DRV_DECL(0);
    return drv->inTransaction;
}

static int cpdo_skel_driver_opt_set( cpdo_driver * self, char const * key, va_list vargs )
{
    return cpdo_rc.NYIError;
}
static int cpdo_skel_driver_opt_get( cpdo_driver * self, char const * key, va_list vargs )
{
    return cpdo_rc.NYIError;
}

static int cpdo_skel_driver_opt_get_string_quote_char( cpdo_driver * self, char * ch )
{
    if( NULL == ch ) return cpdo_rc.ArgError;
    else
    {
        *ch = '\'';
        return 0;
    }
}

static cpdo_step_code cpdo_skel_stmt_step( cpdo_stmt * self )
{
    STMT_DECL(CPDO_STEP_ERROR);
    if( ! stmt->stmt ) return CPDO_STEP_ERROR;
    return CPDO_STEP_ERROR;
}

static int cpdo_skel_stmt_reset( cpdo_stmt * self )
{
    STMT_DECL(cpdo_rc.ArgError);
    return cpdo_rc.NYIError;
}

static uint16_t cpdo_skel_stmt_column_count( cpdo_stmt * self )
{
    STMT_DECL(cpdo_rc.ArgError);
    return 0;
}

static char const * cpdo_skel_stmt_column_name( cpdo_stmt * self, uint16_t ndx )
{
    STMT_DECL(NULL);
    return NULL;
}

static uint16_t cpdo_skel_stmt_bind_count( cpdo_stmt * self )
{
    STMT_DECL(0);
    return 0;
}

static uint16_t cpdo_skel_stmt_param_index( cpdo_stmt * self, char const * name )
{
    STMT_DECL(0);
    return 0;
}

static char const * cpdo_skel_stmt_param_name( cpdo_stmt * self, uint16_t ndx )
{
    STMT_DECL(NULL);
    return NULL;
}

static int cpdo_skel_stmt_bind_null( cpdo_stmt * self, uint16_t ndx )
{
    STMT_DECL(cpdo_rc.ArgError);
    return cpdo_rc.NYIError;
}


static int cpdo_skel_stmt_bind_int8( cpdo_stmt * self, uint16_t ndx, int8_t v )
{
    BINDNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_bind_int16( cpdo_stmt * self, uint16_t ndx, int16_t v )
{
    BINDNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_bind_int32( cpdo_stmt * self, uint16_t ndx, int32_t v )
{
    BINDNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_bind_int64( cpdo_stmt * self, uint16_t ndx, int64_t v )
{
    BINDNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_bind_float( cpdo_stmt * self, uint16_t ndx, float v )
{
    BINDNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_bind_double( cpdo_stmt * self, uint16_t ndx, double v )
{
    BINDNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_bind_string( cpdo_stmt * self, uint16_t ndx, char const * v, uint32_t len )
{
    BINDNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_bind_blob( cpdo_stmt * self, uint16_t ndx, void const * v, uint32_t len )
{
    BINDNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_get_type_ndx( cpdo_stmt * self, uint16_t ndx, cpdo_data_type * val )
{
    GETNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_get_int8_ndx( cpdo_stmt * self, uint16_t ndx, int8_t * val )
{
    GETNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_get_int16_ndx( cpdo_stmt * self, uint16_t ndx, int16_t * val )
{
    GETNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_get_int32_ndx( cpdo_stmt * self, uint16_t ndx, int32_t * val )
{
    GETNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_get_int64_ndx( cpdo_stmt * self, uint16_t ndx, int64_t * val )
{
    GETNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_get_double_ndx( cpdo_stmt * self, uint16_t ndx, double * val )
{
    GETNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_get_float_ndx( cpdo_stmt * self, uint16_t ndx, float * val )
{
    GETNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_get_string_ndx( cpdo_stmt * self, uint16_t ndx, char const ** val, uint32_t * len )
{
    GETNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_get_blob_ndx( cpdo_stmt * self, uint16_t ndx, void const ** val, uint32_t * len )
{
    GETNDX_DECL(ndx);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_error_info( cpdo_stmt * self, char const ** dest, uint32_t * len, int * errorCode )
{
    STMT_DECL(cpdo_rc.ArgError);
    return cpdo_rc.NYIError;
}

static int cpdo_skel_stmt_finalize( cpdo_stmt * self )
{
    STMT_DECL(cpdo_rc.ArgError);
    return cpdo_skel_stmt_free(stmt);
}

static cpdo_driver_details const * cpdo_skel_driver_details()
{
    static const cpdo_driver_details bob = {
    CPDO_DRIVER_NAME/*driver_name*/,
    "FIXME:VERSION"/*driver_version*/,
    "FIXME:LICENSE"/*license*/,
    "http://fossil.wanderinghorse.net/repos/cpdo/" /*url*/,
    "FIXME: NAME (email or URL)" /*authors*/
    };
    return &bob;
}

int cpdo_driver_skel_register()
{
    return cpdo_driver_register( CPDO_DRIVER_NAME, cpdo_skel_driver_new );
}


#if defined(__cplusplus)
} /*extern "C"*/
#endif

#undef DRV_DECL
#undef STMT_DECL
#undef GETNDX_DECL
#undef BINDNDX_DECL
#undef MARKER
#undef CPDO_DRIVER_NAME
/* end of file cpdo_skeleton.c */
/* start of file cpdo_printf.c */
/************************************************************************
The printf-like implementation in this file is based on the one found
in the sqlite3 distribution is in the Public Domain.

This copy was forked for use with the clob API in Feb 2008 by Stephan
Beal (http://wanderinghorse.net/home/stephan/) and modified to send
its output to arbitrary targets via a callback mechanism. Also
refactored the %X specifier handlers a bit to make adding/removing
specific handlers easier.

All code in this file is released into the Public Domain.

The printf implementation (cpdo_printfv()) is pretty easy to extend
(e.g. adding or removing %-specifiers for cpdo_printfv()) if you're
willing to poke around a bit and see how the specifiers are declared
and dispatched. For an example, grep for 'etSTRING' and follow it
through the process of declaration to implementation.

See below for several CPDO_PRINTF_OMIT_xxx macros which can be set to
remove certain features/extensions.
************************************************************************/

#include <stdio.h> /* FILE */
#include <string.h> /* strlen() */
#include <stdlib.h> /* free/malloc() */
#include <ctype.h>
#include <stdint.h>
#if defined(__cplusplus)
extern "C" {
#endif

typedef long double LONGDOUBLE_TYPE;

/*
   If CPDO_PRINTF_OMIT_FLOATING_POINT is defined to a true value, then
   floating point conversions are disabled.
*/
#ifndef CPDO_PRINTF_OMIT_FLOATING_POINT
#  define CPDO_PRINTF_OMIT_FLOATING_POINT 0
#endif

/*
   If CPDO_PRINTF_OMIT_SIZE is defined to a true value, then
   the %n specifier is disabled.
*/
#ifndef CPDO_PRINTF_OMIT_SIZE
#  define CPDO_PRINTF_OMIT_SIZE 0
#endif

/*
   If CPDO_PRINTF_OMIT_SQL is defined to a true value, then
   the %q and %Q specifiers are disabled.
*/
#ifndef CPDO_PRINTF_OMIT_SQL
#  define CPDO_PRINTF_OMIT_SQL 0
#endif

/*
   If CPDO_PRINTF_OMIT_HTML is defined to a true value then the %h (HTML
   escape), %t (URL escape), and %T (URL unescape) specifiers are
   disabled.
*/
#ifndef CPDO_PRINTF_OMIT_HTML
#  define CPDO_PRINTF_OMIT_HTML 0
#endif

/*
Most C compilers handle variable-sized arrays, so we enable
that by default. Some (e.g. tcc) do not, so we provide a way
to disable it: set CPDO_PRINTF_HAVE_VARARRAY to 0

One approach would be to look at:

  defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 199901L)

but some compilers support variable-sized arrays even when not
explicitly running in c99 mode.
*/
#if !defined(CPDO_PRINTF_HAVE_VARARRAY)
#  if defined(__TINYC__)
#    define CPDO_PRINTF_HAVE_VARARRAY 0
#  elif defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 199901L)
#    define CPDO_PRINTF_HAVE_VARARRAY 1
#  else
#    define CPDO_PRINTF_HAVE_VARARRAY 0
#  endif
#endif

/**
CPDO_PRINTF_CHARARRAY is a helper to allocate variable-sized arrays.
This exists mainly so this code can compile with the tcc compiler.
*/
#if CPDO_PRINTF_HAVE_VARARRAY
#  define CPDO_PRINTF_CHARARRAY(V,N) char V[N+1]; memset(V,0,N+1);
#  define CPDO_PRINTF_CHARARRAY_FREE(V)
#else
#  define CPDO_PRINTF_CHARARRAY(V,N) char * V = (char *)malloc(N+1); memset(V,0,N+1);
#  define CPDO_PRINTF_CHARARRAY_FREE(V) free(V)
#endif

/*
   Conversion types fall into various categories as defined by the
   following enumeration.
*/
enum PrintfCategory {etRADIX = 1, /* Integer types.  %d, %x, %o, and so forth */
		     etFLOAT = 2, /* Floating point.  %f */
		     etEXP = 3, /* Exponentional notation. %e and %E */
		     etGENERIC = 4, /* Floating or exponential, depending on exponent. %g */
		     etSIZE = 5, /* Return number of characters processed so far. %n */
		     etSTRING = 6, /* Strings. %s */
		     etDYNSTRING = 7, /* Dynamically allocated strings. %z */
		     etPERCENT = 8, /* Percent symbol. %% */
		     etCHARX = 9, /* Characters. %c */
/* The rest are extensions, not normally found in printf() */
		     etCHARLIT = 10, /* Literal characters.  %' */
#if !CPDO_PRINTF_OMIT_SQL
		     etSQLESCAPE = 11, /* Strings with '\'' doubled.  %q */
		     etSQLESCAPE2 = 12, /* Strings with '\'' doubled and enclosed in '',
                          NULL pointers replaced by SQL NULL.  %Q */
		     etSQLESCAPE3 = 16, /* %w -> Strings with '\"' doubled */
#endif /* !CPDO_PRINTF_OMIT_SQL */
		     etPOINTER = 15, /* The %p conversion */
		     etORDINAL = 17, /* %r -> 1st, 2nd, 3rd, 4th, etc.  English only */
#if ! CPDO_PRINTF_OMIT_HTML
                     etHTML = 18, /* %h -> basic HTML escaping. */
                     etURLENCODE = 19, /* %t -> URL encoding. */
                     etURLDECODE = 20, /* %T -> URL decoding. */
#endif
		     etPLACEHOLDER = 100
};

/*
   An "etByte" is an 8-bit unsigned value.
*/
typedef unsigned char etByte;

/*
   Each builtin conversion character (ex: the 'd' in "%d") is described
   by an instance of the following structure
*/
typedef struct et_info {   /* Information about each format field */
  char fmttype;            /* The format field code letter */
  etByte base;             /* The base for radix conversion */
  etByte flags;            /* One or more of FLAG_ constants below */
  etByte type;             /* Conversion paradigm */
  etByte charset;          /* Offset into aDigits[] of the digits string */
  etByte prefix;           /* Offset into aPrefix[] of the prefix string */
} et_info;

/*
   Allowed values for et_info.flags
*/
enum et_info_flags { FLAG_SIGNED = 1,    /* True if the value to convert is signed */
		     FLAG_EXTENDED = 2,  /* True if for internal/extended use only. */
		     FLAG_STRING = 4     /* Allow infinity precision */
};

/*
  Historically, the following table was searched linearly, so the most
  common conversions were kept at the front.

  Change 2008 Oct 31 by Stephan Beal: we reserve an array or ordered
  entries for all chars in the range [32..126]. Format character
  checks can now be done in constant time by addressing that array
  directly.  This takes more static memory, but reduces the time and
  per-call overhead costs of cpdo_printfv().
*/
static const char aDigits[] = "0123456789ABCDEF0123456789abcdef";
static const char aPrefix[] = "-x0\000X0";
static const et_info fmtinfo[] = {
/**
   If CPDO_PRINTF_FMTINFO_FIXED is 1 then we use the original
   implementation: a linear list of entries. Search time is linear. If
   CPDO_PRINTF_FMTINFO_FIXED is 0 then we use a fixed-size array which
   we index directly using the format char as the key.
*/
#define CPDO_PRINTF_FMTINFO_FIXED 0
#if CPDO_PRINTF_FMTINFO_FIXED
  {  'd', 10, FLAG_SIGNED, etRADIX,      0,  0 },
  {  's',  0, FLAG_STRING, etSTRING,     0,  0 },
  {  'g',  0, FLAG_SIGNED, etGENERIC,    30, 0 },
  {  'z',  0, FLAG_STRING, etDYNSTRING,  0,  0 },
  {  'c',  0, 0, etCHARX,      0,  0 },
  {  'o',  8, 0, etRADIX,      0,  2 },
  {  'u', 10, 0, etRADIX,      0,  0 },
  {  'x', 16, 0, etRADIX,      16, 1 },
  {  'X', 16, 0, etRADIX,      0,  4 },
  {  'i', 10, FLAG_SIGNED, etRADIX,      0,  0 },
#if !CPDO_PRINTF_OMIT_FLOATING_POINT
  {  'f',  0, FLAG_SIGNED, etFLOAT,      0,  0 },
  {  'e',  0, FLAG_SIGNED, etEXP,        30, 0 },
  {  'E',  0, FLAG_SIGNED, etEXP,        14, 0 },
  {  'G',  0, FLAG_SIGNED, etGENERIC,    14, 0 },
#endif /* !CPDO_PRINTF_OMIT_FLOATING_POINT */
  {  '%',  0, 0, etPERCENT,    0,  0 },
  {  'p', 16, 0, etPOINTER,    0,  1 },
  {  'r', 10, (FLAG_EXTENDED|FLAG_SIGNED), etORDINAL,    0,  0 },
#if ! CPDO_PRINTF_OMIT_SQL
  {  'q',  0, FLAG_STRING, etSQLESCAPE,  0,  0 },
  {  'Q',  0, FLAG_STRING, etSQLESCAPE2, 0,  0 },
  {  'w',  0, FLAG_STRING, etSQLESCAPE3, 0,  0 },
#endif /* !CPDO_PRINTF_OMIT_SQL */
#if ! CPDO_PRINTF_OMIT_HTML
  {  'h',  0, FLAG_STRING, etHTML, 0, 0 },
  {  't',  0, FLAG_STRING, etURLENCODE, 0, 0 },
  {  'T',  0, FLAG_STRING, etURLDECODE, 0, 0 },
#endif /* !CPDO_PRINTF_OMIT_HTML */
#if !CPDO_PRINTF_OMIT_SIZE
  {  'n',  0, 0, etSIZE,       0,  0 },
#endif
#else /* CPDO_PRINTF_FMTINFO_FIXED */
  /*
    These entries MUST stay in ASCII order, sorted
    on their fmttype member!
  */
  {' '/*32*/, 0, 0, 0, 0, 0 },
  {'!'/*33*/, 0, 0, 0, 0, 0 },
  {'"'/*34*/, 0, 0, 0, 0, 0 },
  {'#'/*35*/, 0, 0, 0, 0, 0 },
  {'$'/*36*/, 0, 0, 0, 0, 0 },
  {'%'/*37*/, 0, 0, etPERCENT, 0, 0 },
  {'&'/*38*/, 0, 0, 0, 0, 0 },
  {'\''/*39*/, 0, 0, 0, 0, 0 },
  {'('/*40*/, 0, 0, 0, 0, 0 },
  {')'/*41*/, 0, 0, 0, 0, 0 },
  {'*'/*42*/, 0, 0, 0, 0, 0 },
  {'+'/*43*/, 0, 0, 0, 0, 0 },
  {','/*44*/, 0, 0, 0, 0, 0 },
  {'-'/*45*/, 0, 0, 0, 0, 0 },
  {'.'/*46*/, 0, 0, 0, 0, 0 },
  {'/'/*47*/, 0, 0, 0, 0, 0 },
  {'0'/*48*/, 0, 0, 0, 0, 0 },
  {'1'/*49*/, 0, 0, 0, 0, 0 },
  {'2'/*50*/, 0, 0, 0, 0, 0 },
  {'3'/*51*/, 0, 0, 0, 0, 0 },
  {'4'/*52*/, 0, 0, 0, 0, 0 },
  {'5'/*53*/, 0, 0, 0, 0, 0 },
  {'6'/*54*/, 0, 0, 0, 0, 0 },
  {'7'/*55*/, 0, 0, 0, 0, 0 },
  {'8'/*56*/, 0, 0, 0, 0, 0 },
  {'9'/*57*/, 0, 0, 0, 0, 0 },
  {':'/*58*/, 0, 0, 0, 0, 0 },
  {';'/*59*/, 0, 0, 0, 0, 0 },
  {'<'/*60*/, 0, 0, 0, 0, 0 },
  {'='/*61*/, 0, 0, 0, 0, 0 },
  {'>'/*62*/, 0, 0, 0, 0, 0 },
  {'?'/*63*/, 0, 0, 0, 0, 0 },
  {'@'/*64*/, 0, 0, 0, 0, 0 },
  {'A'/*65*/, 0, 0, 0, 0, 0 },
  {'B'/*66*/, 0, 0, 0, 0, 0 },
  {'C'/*67*/, 0, 0, 0, 0, 0 },
  {'D'/*68*/, 0, 0, 0, 0, 0 },
  {'E'/*69*/, 0, FLAG_SIGNED, etEXP, 14, 0 },
  {'F'/*70*/, 0, 0, 0, 0, 0 },
  {'G'/*71*/, 0, FLAG_SIGNED, etGENERIC, 14, 0 },
  {'H'/*72*/, 0, 0, 0, 0, 0 },
  {'I'/*73*/, 0, 0, 0, 0, 0 },
  {'J'/*74*/, 0, 0, 0, 0, 0 },
  {'K'/*75*/, 0, 0, 0, 0, 0 },
  {'L'/*76*/, 0, 0, 0, 0, 0 },
  {'M'/*77*/, 0, 0, 0, 0, 0 },
  {'N'/*78*/, 0, 0, 0, 0, 0 },
  {'O'/*79*/, 0, 0, 0, 0, 0 },
  {'P'/*80*/, 0, 0, 0, 0, 0 },
  {'Q'/*81*/, 0, FLAG_STRING, etSQLESCAPE2, 0, 0 },
  {'R'/*82*/, 0, 0, 0, 0, 0 },
  {'S'/*83*/, 0, 0, 0, 0, 0 },
  {'T'/*84*/,  0, FLAG_STRING, etURLDECODE, 0, 0 },
  {'U'/*85*/, 0, 0, 0, 0, 0 },
  {'V'/*86*/, 0, 0, 0, 0, 0 },
  {'W'/*87*/, 0, 0, 0, 0, 0 },
  {'X'/*88*/, 16, 0, etRADIX,      0,  4 },
  {'Y'/*89*/, 0, 0, 0, 0, 0 },
  {'Z'/*90*/, 0, 0, 0, 0, 0 },
  {'['/*91*/, 0, 0, 0, 0, 0 },
  {'\\'/*92*/, 0, 0, 0, 0, 0 },
  {']'/*93*/, 0, 0, 0, 0, 0 },
  {'^'/*94*/, 0, 0, 0, 0, 0 },
  {'_'/*95*/, 0, 0, 0, 0, 0 },
  {'`'/*96*/, 0, 0, 0, 0, 0 },
  {'a'/*97*/, 0, 0, 0, 0, 0 },
  {'b'/*98*/, 0, 0, 0, 0, 0 },
  {'c'/*99*/, 0, 0, etCHARX,      0,  0 },
  {'d'/*100*/, 10, FLAG_SIGNED, etRADIX,      0,  0 },
  {'e'/*101*/, 0, FLAG_SIGNED, etEXP,        30, 0 },
  {'f'/*102*/, 0, FLAG_SIGNED, etFLOAT,      0,  0},
  {'g'/*103*/, 0, FLAG_SIGNED, etGENERIC,    30, 0 },
  {'h'/*104*/, 0, FLAG_STRING, etHTML, 0, 0 },
  {'i'/*105*/, 10, FLAG_SIGNED, etRADIX,      0,  0},
  {'j'/*106*/, 0, 0, 0, 0, 0 },
  {'k'/*107*/, 0, 0, 0, 0, 0 },
  {'l'/*108*/, 0, 0, 0, 0, 0 },
  {'m'/*109*/, 0, 0, 0, 0, 0 },
  {'n'/*110*/, 0, 0, etSIZE, 0, 0 },
  {'o'/*111*/, 8, 0, etRADIX,      0,  2 },
  {'p'/*112*/, 16, 0, etPOINTER, 0, 1 },
  {'q'/*113*/, 0, FLAG_STRING, etSQLESCAPE,  0, 0 },
  {'r'/*114*/, 10, (FLAG_EXTENDED|FLAG_SIGNED), etORDINAL,    0,  0},
  {'s'/*115*/, 0, FLAG_STRING, etSTRING,     0,  0 },
  {'t'/*116*/,  0, FLAG_STRING, etURLENCODE, 0, 0 },
  {'u'/*117*/, 10, 0, etRADIX,      0,  0 },
  {'v'/*118*/, 0, 0, 0, 0, 0 },
  {'w'/*119*/, 0, FLAG_STRING, etSQLESCAPE3, 0, 0 },
  {'x'/*120*/, 16, 0, etRADIX,      16, 1  },
  {'y'/*121*/, 0, 0, 0, 0, 0 },
  {'z'/*122*/, 0, FLAG_STRING, etDYNSTRING,  0,  0},
  {'{'/*123*/, 0, 0, 0, 0, 0 },
  {'|'/*124*/, 0, 0, 0, 0, 0 },
  {'}'/*125*/, 0, 0, 0, 0, 0 },
  {'~'/*126*/, 0, 0, 0, 0, 0 },
#endif /* CPDO_PRINTF_FMTINFO_FIXED */
};
#define etNINFO  (sizeof(fmtinfo)/sizeof(fmtinfo[0]))

#if ! CPDO_PRINTF_OMIT_FLOATING_POINT
/*
   "*val" is a double such that 0.1 <= *val < 10.0
   Return the ascii code for the leading digit of *val, then
   multiply "*val" by 10.0 to renormalize.
**
   Example:
       input:     *val = 3.14159
       output:    *val = 1.4159    function return = '3'
**
   The counter *cnt is incremented each time.  After counter exceeds
   16 (the number of significant digits in a 64-bit float) '0' is
   always returned.
*/
static int et_getdigit(LONGDOUBLE_TYPE *val, int *cnt){
  int digit;
  LONGDOUBLE_TYPE d;
  if( (*cnt)++ >= 16 ) return '0';
  digit = (int)*val;
  d = digit;
  digit += '0';
  *val = (*val - d)*10.0;
  return digit;
}
#endif /* !CPDO_PRINTF_OMIT_FLOATING_POINT */

/*
   On machines with a small(?) stack size, you can redefine the
   CPDO_PRINTF_BUF_SIZE to be less than 350.  But beware - for smaller
   values some %f conversions may go into an infinite loop.
*/
#ifndef CPDO_PRINTF_BUF_SIZE
#  define CPDO_PRINTF_BUF_SIZE 350  /* Size of the output buffer for numeric conversions */
#endif

#if ! defined(__STDC__) && !defined(__TINYC__)
#ifdef CPDO_PRINTF_INT64_TYPE
  typedef CPDO_PRINTF_INT64_TYPE int64_t;
  typedef unsigned CPDO_PRINTF_INT64_TYPE uint64_t;
#elif defined(_MSC_VER) || defined(__BORLANDC__)
  typedef __int64 int64_t;
  typedef unsigned __int64 uint64_t;
#else
  typedef long long int int64_t;
  typedef unsigned long long int uint64_t;
#endif
#endif

#if 0
/   Not yet used. */
enum PrintfArgTypes {
TypeInt = 0,
TypeIntP = 1,
TypeFloat = 2,
TypeFloatP = 3,
TypeCString = 4
};
#endif


#if 0
/   Not yet used. */
typedef struct cpdo_printf_spec_handler_def
{
	char letter; /   e.g. %s */
	int xtype; /* reference to the etXXXX values, or fmtinfo[*].type. */
	int ntype; /* reference to PrintfArgTypes enum. */
} spec_handler;
#endif

/**
   cpdo_printf_spec_handler is an almost-generic interface for farming
   work out of cpdo_printfv()'s code into external functions.  It doesn't
   actually save much (if any) overall code, but it makes the cpdo_printfv()
   code more manageable.


   REQUIREMENTS of implementations:

   - Expects an implementation-specific vargp pointer.
   cpdo_printfv() passes a pointer to the converted value of
   an entry from the format va_list. If it passes a type
   other than the expected one, undefined results.

   - If it calls pf then it must return the return value
   from that function.

   - If it calls pf it must do: pf( pfArg, D, N ), where D is
   the data to export and N is the number of bytes to export.
   It may call pf() an arbitrary number of times

   - If pf() successfully is called, the return value must be the
   accumulated totals of its return value(s), plus (possibly, but
   unlikely) an imnplementation-specific amount.

   - If it does not call pf() then it must return 0 (success)
   or a negative number (an error) or do all of the export
   processing itself and return the number of bytes exported.


   SIGNIFICANT LIMITATIONS:

   - Has no way of iterating over the format string,
   so handling precisions and such here can't work too
   well.
*/
typedef long (*cpdo_printf_spec_handler)( cpdo_printf_appender pf,
				       void * pfArg,
				       void * vargp );


/**
  cpdo_printf_spec_handler for etSTRING types. It assumes that varg is a
  null-terminated (char [const] *)
*/
static long spech_string( cpdo_printf_appender pf,
			  void * pfArg,
			  void * varg )
{
	char const * ch = (char const *) varg;
	return ch ? pf( pfArg, ch, strlen(ch) ) : 0;
}

/**
  cpdo_printf_spec_handler for etDYNSTRING types.  It assumes that varg
  is a non-const (char *). It behaves identically to spec_string() and
  then calls free() on that (char *).
*/
static long spech_dynstring( cpdo_printf_appender pf,
			     void * pfArg,
			     void * varg )
{
  long ret = spech_string( pf, pfArg, varg );
  free( (char *) varg );
  return ret;
}

#if !CPDO_PRINTF_OMIT_HTML
static long spech_string_to_html( cpdo_printf_appender pf,
                                  void * pfArg,
                                  void * varg )
{
    char const * ch = (char const *) varg;
    long ret = 0;
    if( ! ch ) return 0;
    ret = 0;
    for( ; *ch; ++ch )
    {
        switch( *ch )
        {
          case '<': ret += pf( pfArg, "&lt;", 4 );
              break;
          case '&': ret += pf( pfArg, "&amp;", 5 );
              break;
          default:
              ret += pf( pfArg, ch, 1 );
              break;
        };
    }
    return ret;
}

static int httpurl_needs_escape( int c )
{
    /*
      Definition of "safe" and "unsafe" chars
      was taken from:

      http://www.codeguru.com/cpp/cpp/cpp_mfc/article.php/c4029/
    */
    return ( (c >= 32 && c <=47)
             || ( c>=58 && c<=64)
             || ( c>=91 && c<=96)
             || ( c>=123 && c<=126)
             || ( c<32 || c>=127)
             );
}

/**
   The handler for the etURLENCODE specifier.

   It expects varg to be a string value, which it will preceed to
   encode using an URL encoding algothrim (certain characters are
   converted to %XX, where XX is their hex value) and passes the
   encoded string to pf(). It returns the total length of the output
   string.
 */
static long spech_urlencode( cpdo_printf_appender pf,
                             void * pfArg,
                             void * varg )
{
    char const * str = (char const *) varg;
    long ret = 0;
    char ch = 0;
    char const * hex = "0123456789ABCDEF";
#define xbufsz 10
    char xbuf[xbufsz];
    int slen = 0;
    if( ! str ) return 0;
    memset( xbuf, 0, xbufsz );
    ch = *str;
#define xbufsz 10
    slen = 0;
    for( ; ch; ch = *(++str) )
    {
        if( ! httpurl_needs_escape( ch ) )
        {
            ret += pf( pfArg, str, 1 );
            continue;
        }
        else {
            slen = sprintf( xbuf, "%%%c%c",
                            hex[((ch>>4)&0xf)],
                            hex[(ch&0xf)]);
            ret += pf( pfArg, xbuf, slen );
        }
    }
#undef xbufsz
    return ret;
}

/* 
   hexchar_to_int():

   For 'a'-'f', 'A'-'F' and '0'-'9', returns the appropriate decimal
   number.  For any other character it returns -1.
    */
static int hexchar_to_int( int ch )
{
    if( (ch>='a' && ch<='f') ) return ch-'a'+10;
    else if( (ch>='A' && ch<='F') ) return ch-'A'+10;
    else if( (ch>='0' && ch<='9') ) return ch-'0';
    return -1;
}

/**
   The handler for the etURLDECODE specifier.

   It expects varg to be a ([const] char *), possibly encoded
   with URL encoding. It decodes the string using a URL decode
   algorithm and passes the decoded string to
   pf(). It returns the total length of the output string.
   If the input string contains malformed %XX codes then this
   function will return prematurely.
 */
static long spech_urldecode( cpdo_printf_appender pf,
                             void * pfArg,
                             void * varg )
{
    char const * str = (char const *) varg;
    long ret = 0;
    char ch = 0;
    char ch2 = 0;
    char xbuf[4];
    int decoded;
    ch = *str;
    if( ! str ) return 0;
    while( ch )
    {
        if( ch == '%' )
        {
            ch = *(++str);
            ch2 = *(++str);
            if( isxdigit(ch) &&
                isxdigit(ch2) )
            {
                decoded = (hexchar_to_int( ch ) * 16)
                    + hexchar_to_int( ch2 );
                xbuf[0] = (char)decoded;
                xbuf[1] = 0;
                ret += pf( pfArg, xbuf, 1 );
                ch = *(++str);
                continue;
            }
            else
            {
                xbuf[0] = '%';
                xbuf[1] = ch;
                xbuf[2] = ch2;
                xbuf[3] = 0;
                ret += pf( pfArg, xbuf, 3 );
                ch = *(++str);
                continue;
            }
        }
        else if( ch == '+' )
        {
            xbuf[0] = ' ';
            xbuf[1] = 0;
            ret += pf( pfArg, xbuf, 1 );
            ch = *(++str);
            continue;
        }
        xbuf[0] = ch;
        xbuf[1] = 0;
        ret += pf( pfArg, xbuf, 1 );
        ch = *(++str);
    }
    return ret;
}

#endif /* !CPDO_PRINTF_OMIT_HTML */


#if !CPDO_PRINTF_OMIT_SQL
/**
   Quotes the (char *) varg as an SQL string 'should'
   be quoted. The exact type of the conversion
   is specified by xtype, which must be one of
   etSQLESCAPE, etSQLESCAPE2, or etSQLESCAPE3.

   Search this file for those constants to find
   the associated documentation.
*/
static long spech_sqlstring_main( int xtype,
				  cpdo_printf_appender pf,
				  void * pfArg,
				  void * varg )
{
    int i, j, n, ch, isnull;
    int needQuote;
    char q = ((xtype==etSQLESCAPE3)?'"':'\'');   /* Quote character */
    char const * escarg = (char const *) varg;
    long ret;
	char * bufpt = 0;
        isnull = escarg==0;
        if( isnull ) escarg = (xtype==etSQLESCAPE2 ? "NULL" : "(NULL)");
        for(i=n=0; (ch=escarg[i])!=0; i++){
          if( ch==q )  n++;
        }
        needQuote = !isnull && xtype==etSQLESCAPE2;
        n += i + 1 + needQuote*2;
	/* FIXME: use a static buffer here instead of malloc()! Shame on you!*/
	bufpt = (char *)malloc( n );
	if( ! bufpt ) return -1;
        j = 0;
        if( needQuote ) bufpt[j++] = q;
        for(i=0; (ch=escarg[i])!=0; i++){
          bufpt[j++] = ch;
          if( ch==q ) bufpt[j++] = ch;
        }
        if( needQuote ) bufpt[j++] = q;
        bufpt[j] = 0;
	ret = pf( pfArg, bufpt, j );
	free( bufpt );
	return ret;
}

static long spech_sqlstring1( cpdo_printf_appender pf,
			      void * pfArg,
			      void * varg )
{
	return spech_sqlstring_main( etSQLESCAPE, pf, pfArg, varg );
}

static long spech_sqlstring2( cpdo_printf_appender pf,
			      void * pfArg,
			      void * varg )
{
	return spech_sqlstring_main( etSQLESCAPE2, pf, pfArg, varg );
}

static long spech_sqlstring3( cpdo_printf_appender pf,
			      void * pfArg,
			      void * varg )
{
	return spech_sqlstring_main( etSQLESCAPE3, pf, pfArg, varg );
}

#endif /* !CPDO_PRINTF_OMIT_SQL */

				      

/*
   The root printf program.  All variations call this core.  It
   implements most of the common printf behaviours plus (optionally)
   some extended ones.

   INPUTS:

     pfAppend : The is a cpdo_printf_appender function which is responsible
     for accumulating the output. If pfAppend returns a negative integer
     then processing stops immediately.

     pfAppendArg : is ignored by this function but passed as the first
     argument to pfAppend. pfAppend will presumably use it as a data
     store for accumulating its string.

     fmt : This is the format string, as in the usual printf().

     ap : This is a pointer to a list of arguments.  Same as in
     vprintf() and friends.

   OUTPUTS:

   The return value is the total number of characters sent to the
   function "func".  Returns -1 on a error.

   Note that the order in which automatic variables are declared below
   seems to make a big difference in determining how fast this beast
   will run.

   Much of this code dates back to the early 1980's, supposedly.

   Known change history (most historic info has been lost):

   10 Feb 2008 by Stephan Beal: refactored to remove the 'useExtended'
   flag (which is now always on). Added the cpdo_printf_appender typedef to
   make this function generic enough to drop into other source trees
   without much work.

   31 Oct 2008 by Stephan Beal: refactored the et_info lookup to be
   constant-time instead of linear.
*/
long cpdo_printfv(
  cpdo_printf_appender pfAppend,          /* Accumulate results here */
  void * pfAppendArg,                /* Passed as first arg to pfAppend. */
  const char *fmt,                   /* Format string */
  va_list ap                         /* arguments */
){
    /**
       HISTORIC NOTE (author and year unknown):

       Note that the order in which automatic variables are declared below
       seems to make a big difference in determining how fast this beast
       will run.
    */

#if CPDO_PRINTF_FMTINFO_FIXED
  const int useExtended = 1; /* Allow extended %-conversions */
#endif
  long outCount = 0;          /* accumulated output count */
  int pfrc = 0;              /* result from calling pfAppend */
  int c;                     /* Next character in the format string */
  char *bufpt = 0;           /* Pointer to the conversion buffer */
  int precision;             /* Precision of the current field */
  int length;                /* Length of the field */
  int idx;                   /* A general purpose loop counter */
  int width;                 /* Width of the current field */
  etByte flag_leftjustify;   /* True if "-" flag is present */
  etByte flag_plussign;      /* True if "+" flag is present */
  etByte flag_blanksign;     /* True if " " flag is present */
  etByte flag_alternateform; /* True if "#" flag is present */
  etByte flag_altform2;      /* True if "!" flag is present */
  etByte flag_zeropad;       /* True if field width constant starts with zero */
  etByte flag_long;          /* True if "l" flag is present */
  etByte flag_longlong;      /* True if the "ll" flag is present */
  etByte done;               /* Loop termination flag */
  uint64_t longvalue;   /* Value for integer types */
  LONGDOUBLE_TYPE realvalue; /* Value for real types */
  const et_info *infop = 0;      /* Pointer to the appropriate info structure */
  char buf[CPDO_PRINTF_BUF_SIZE];       /* Conversion buffer */
  char prefix;               /* Prefix character.  "+" or "-" or " " or '\0'. */
  etByte errorflag = 0;      /* True if an error is encountered */
  etByte xtype = 0;              /* Conversion paradigm */
  char * zExtra = 0;              /* Extra memory used for etTCLESCAPE conversions */
#if ! CPDO_PRINTF_OMIT_FLOATING_POINT
  int  exp, e2;              /* exponent of real numbers */
  double rounder;            /* Used for rounding floating point values */
  etByte flag_dp;            /* True if decimal point should be shown */
  etByte flag_rtz;           /* True if trailing zeros should be removed */
  etByte flag_exp;           /* True to force display of the exponent */
  int nsd;                   /* Number of significant digits returned */
#endif
    cpdo_printf_spec_handler spf;


  /* CPDO_PRINTF_RETURN, CPDO_PRINTF_CHECKERR, and CPDO_PRINTF_SPACES
     are internal helpers.
  */
#define CPDO_PRINTF_RETURN if( zExtra ) free(zExtra); return outCount;
#define CPDO_PRINTF_CHECKERR(FREEME) if( pfrc<0 ) { CPDO_PRINTF_CHARARRAY_FREE(FREEME); CPDO_PRINTF_RETURN; } else outCount += pfrc;
#define CPDO_PRINTF_SPACES(N) \
if(1){				       \
    CPDO_PRINTF_CHARARRAY(zSpaces,N);		      \
    memset( zSpaces,' ',N);			      \
    pfrc = pfAppend(pfAppendArg, zSpaces, N);	      \
    CPDO_PRINTF_CHECKERR(zSpaces);			      \
    CPDO_PRINTF_CHARARRAY_FREE(zSpaces);		      \
}

  length = 0;
  bufpt = 0;
  for(; (c=(*fmt))!=0; ++fmt){
    if( c!='%' ){
      int amt;
      bufpt = (char *)fmt;
      amt = 1;
      while( (c=(*++fmt))!='%' && c!=0 ) amt++;
      pfrc = pfAppend( pfAppendArg, bufpt, amt);
      CPDO_PRINTF_CHECKERR(0);
      if( c==0 ) break;
    }
    if( (c=(*++fmt))==0 ){
      errorflag = 1;
      pfrc = pfAppend( pfAppendArg, "%", 1);
      CPDO_PRINTF_CHECKERR(0);
      break;
    }
    /* Find out what flags are present */
    flag_leftjustify = flag_plussign = flag_blanksign = 
     flag_alternateform = flag_altform2 = flag_zeropad = 0;
    done = 0;
    do{
      switch( c ){
        case '-':   flag_leftjustify = 1;     break;
        case '+':   flag_plussign = 1;        break;
        case ' ':   flag_blanksign = 1;       break;
        case '#':   flag_alternateform = 1;   break;
        case '!':   flag_altform2 = 1;        break;
        case '0':   flag_zeropad = 1;         break;
        default:    done = 1;                 break;
      }
    }while( !done && (c=(*++fmt))!=0 );
    /* Get the field width */
    width = 0;
    if( c=='*' ){
      width = va_arg(ap,int);
      if( width<0 ){
        flag_leftjustify = 1;
        width = -width;
      }
      c = *++fmt;
    }else{
      while( c>='0' && c<='9' ){
        width = width*10 + c - '0';
        c = *++fmt;
      }
    }
    if( width > CPDO_PRINTF_BUF_SIZE-10 ){
      width = CPDO_PRINTF_BUF_SIZE-10;
    }
    /* Get the precision */
    if( c=='.' ){
      precision = 0;
      c = *++fmt;
      if( c=='*' ){
        precision = va_arg(ap,int);
        if( precision<0 ) precision = -precision;
        c = *++fmt;
      }else{
        while( c>='0' && c<='9' ){
          precision = precision*10 + c - '0';
          c = *++fmt;
        }
      }
    }else{
      precision = -1;
    }
    /* Get the conversion type modifier */
    if( c=='l' ){
      flag_long = 1;
      c = *++fmt;
      if( c=='l' ){
        flag_longlong = 1;
        c = *++fmt;
      }else{
        flag_longlong = 0;
      }
    }else{
      flag_long = flag_longlong = 0;
    }
    /* Fetch the info entry for the field */
    infop = 0;
#if CPDO_PRINTF_FMTINFO_FIXED
    for(idx=0; idx<etNINFO; idx++){
      if( c==fmtinfo[idx].fmttype ){
        infop = &fmtinfo[idx];
        if( useExtended || (infop->flags & FLAG_EXTENDED)==0 ){
          xtype = infop->type;
        }else{
	    CPDO_PRINTF_RETURN;
        }
        break;
      }
    }
#else
#define FMTNDX(N) (N - fmtinfo[0].fmttype)
#define FMTINFO(N) (fmtinfo[ FMTNDX(N) ])
    infop = ((c>=(fmtinfo[0].fmttype)) && (c<fmtinfo[etNINFO-1].fmttype))
	? &FMTINFO(c)
	: 0;
    if( infop ) xtype = infop->type;
#undef FMTINFO
#undef FMTNDX
#endif /* CPDO_PRINTF_FMTINFO_FIXED */
    zExtra = 0;
    if( (!infop) || (!infop->type) ){
	CPDO_PRINTF_RETURN;
    }


    /* Limit the precision to prevent overflowing buf[] during conversion */
    if( precision>CPDO_PRINTF_BUF_SIZE-40 && (infop->flags & FLAG_STRING)==0 ){
      precision = CPDO_PRINTF_BUF_SIZE-40;
    }

    /*
       At this point, variables are initialized as follows:
    **
         flag_alternateform          TRUE if a '#' is present.
         flag_altform2               TRUE if a '!' is present.
         flag_plussign               TRUE if a '+' is present.
         flag_leftjustify            TRUE if a '-' is present or if the
                                     field width was negative.
         flag_zeropad                TRUE if the width began with 0.
         flag_long                   TRUE if the letter 'l' (ell) prefixed
                                     the conversion character.
         flag_longlong               TRUE if the letter 'll' (ell ell) prefixed
                                     the conversion character.
         flag_blanksign              TRUE if a ' ' is present.
         width                       The specified field width.  This is
                                     always non-negative.  Zero is the default.
         precision                   The specified precision.  The default
                                     is -1.
         xtype                       The class of the conversion.
         infop                       Pointer to the appropriate info struct.
    */
    switch( xtype ){
      case etPOINTER:
        flag_longlong = sizeof(char*)==sizeof(int64_t);
        flag_long = sizeof(char*)==sizeof(long int);
        /* Fall through into the next case */
      case etORDINAL:
      case etRADIX:
        if( infop->flags & FLAG_SIGNED ){
          int64_t v;
          if( flag_longlong )   v = va_arg(ap,int64_t);
          else if( flag_long )  v = va_arg(ap,long int);
          else                  v = va_arg(ap,int);
          if( v<0 ){
            longvalue = -v;
            prefix = '-';
          }else{
            longvalue = v;
            if( flag_plussign )        prefix = '+';
            else if( flag_blanksign )  prefix = ' ';
            else                       prefix = 0;
          }
        }else{
          if( flag_longlong )   longvalue = va_arg(ap,uint64_t);
          else if( flag_long )  longvalue = va_arg(ap,unsigned long int);
          else                  longvalue = va_arg(ap,unsigned int);
          prefix = 0;
        }
        if( longvalue==0 ) flag_alternateform = 0;
        if( flag_zeropad && precision<width-(prefix!=0) ){
          precision = width-(prefix!=0);
        }
        bufpt = &buf[CPDO_PRINTF_BUF_SIZE-1];
        if( xtype==etORDINAL ){
	    /** i sure would like to shake the hand of whoever figured this out: */
          static const char zOrd[] = "thstndrd";
          int x = longvalue % 10;
          if( x>=4 || (longvalue/10)%10==1 ){
            x = 0;
          }
          buf[CPDO_PRINTF_BUF_SIZE-3] = zOrd[x*2];
          buf[CPDO_PRINTF_BUF_SIZE-2] = zOrd[x*2+1];
          bufpt -= 2;
        }
        {
          const char *cset;
          int base;
          cset = &aDigits[infop->charset];
          base = infop->base;
          do{                                           /* Convert to ascii */
            *(--bufpt) = cset[longvalue%base];
            longvalue = longvalue/base;
          }while( longvalue>0 );
        }
        length = &buf[CPDO_PRINTF_BUF_SIZE-1]-bufpt;
        for(idx=precision-length; idx>0; idx--){
          *(--bufpt) = '0';                             /* Zero pad */
        }
        if( prefix ) *(--bufpt) = prefix;               /* Add sign */
        if( flag_alternateform && infop->prefix ){      /* Add "0" or "0x" */
          const char *pre;
          char x;
          pre = &aPrefix[infop->prefix];
          if( *bufpt!=pre[0] ){
            for(; (x=(*pre))!=0; pre++) *(--bufpt) = x;
          }
        }
        length = &buf[CPDO_PRINTF_BUF_SIZE-1]-bufpt;
        break;
      case etFLOAT:
      case etEXP:
      case etGENERIC:
        realvalue = va_arg(ap,double);
#if ! CPDO_PRINTF_OMIT_FLOATING_POINT
        if( precision<0 ) precision = 6;         /* Set default precision */
        if( precision>CPDO_PRINTF_BUF_SIZE/2-10 ) precision = CPDO_PRINTF_BUF_SIZE/2-10;
        if( realvalue<0.0 ){
          realvalue = -realvalue;
          prefix = '-';
        }else{
          if( flag_plussign )          prefix = '+';
          else if( flag_blanksign )    prefix = ' ';
          else                         prefix = 0;
        }
        if( xtype==etGENERIC && precision>0 ) precision--;
#if 0
        /* Rounding works like BSD when the constant 0.4999 is used.  Wierd! */
        for(idx=precision, rounder=0.4999; idx>0; idx--, rounder*=0.1);
#else
        /* It makes more sense to use 0.5 */
        for(idx=precision, rounder=0.5; idx>0; idx--, rounder*=0.1){}
#endif
        if( xtype==etFLOAT ) realvalue += rounder;
        /* Normalize realvalue to within 10.0 > realvalue >= 1.0 */
        exp = 0;
#if 1
	if( (realvalue)!=(realvalue) ){
	    /* from sqlite3: #define sqlite3_isnan(X)  ((X)!=(X)) */
	    /* This weird array thing is to avoid constness violations
	       when assinging, e.g. "NaN" to bufpt.
	    */
	    static char NaN[4] = {'N','a','N','\0'};
	    bufpt = NaN;
          length = 3;
          break;
        }
#endif
        if( realvalue>0.0 ){
          while( realvalue>=1e32 && exp<=350 ){ realvalue *= 1e-32; exp+=32; }
          while( realvalue>=1e8 && exp<=350 ){ realvalue *= 1e-8; exp+=8; }
          while( realvalue>=10.0 && exp<=350 ){ realvalue *= 0.1; exp++; }
          while( realvalue<1e-8 && exp>=-350 ){ realvalue *= 1e8; exp-=8; }
          while( realvalue<1.0 && exp>=-350 ){ realvalue *= 10.0; exp--; }
          if( exp>350 || exp<-350 ){
            if( prefix=='-' ){
		static char Inf[5] = {'-','I','n','f','\0'};
		bufpt = Inf;
            }else if( prefix=='+' ){
		static char Inf[5] = {'+','I','n','f','\0'};
		bufpt = Inf;
            }else{
		static char Inf[4] = {'I','n','f','\0'};
		bufpt = Inf;
            }
            length = strlen(bufpt);
            break;
          }
        }
        bufpt = buf;
        /*
           If the field type is etGENERIC, then convert to either etEXP
           or etFLOAT, as appropriate.
        */
        flag_exp = xtype==etEXP;
        if( xtype!=etFLOAT ){
          realvalue += rounder;
          if( realvalue>=10.0 ){ realvalue *= 0.1; exp++; }
        }
        if( xtype==etGENERIC ){
          flag_rtz = !flag_alternateform;
          if( exp<-4 || exp>precision ){
            xtype = etEXP;
          }else{
            precision = precision - exp;
            xtype = etFLOAT;
          }
        }else{
          flag_rtz = 0;
        }
        if( xtype==etEXP ){
          e2 = 0;
        }else{
          e2 = exp;
        }
        nsd = 0;
        flag_dp = (precision>0) | flag_alternateform | flag_altform2;
        /* The sign in front of the number */
        if( prefix ){
          *(bufpt++) = prefix;
        }
        /* Digits prior to the decimal point */
        if( e2<0 ){
          *(bufpt++) = '0';
        }else{
          for(; e2>=0; e2--){
            *(bufpt++) = et_getdigit(&realvalue,&nsd);
          }
        }
        /* The decimal point */
        if( flag_dp ){
          *(bufpt++) = '.';
        }
        /* "0" digits after the decimal point but before the first
           significant digit of the number */
        for(e2++; e2<0 && precision>0; precision--, e2++){
          *(bufpt++) = '0';
        }
        /* Significant digits after the decimal point */
        while( (precision--)>0 ){
          *(bufpt++) = et_getdigit(&realvalue,&nsd);
        }
        /* Remove trailing zeros and the "." if no digits follow the "." */
        if( flag_rtz && flag_dp ){
          while( bufpt[-1]=='0' ) *(--bufpt) = 0;
          /* assert( bufpt>buf ); */
          if( bufpt[-1]=='.' ){
            if( flag_altform2 ){
              *(bufpt++) = '0';
            }else{
              *(--bufpt) = 0;
            }
          }
        }
        /* Add the "eNNN" suffix */
        if( flag_exp || (xtype==etEXP && exp) ){
          *(bufpt++) = aDigits[infop->charset];
          if( exp<0 ){
            *(bufpt++) = '-'; exp = -exp;
          }else{
            *(bufpt++) = '+';
          }
          if( exp>=100 ){
            *(bufpt++) = (exp/100)+'0';                /* 100's digit */
            exp %= 100;
          }
          *(bufpt++) = exp/10+'0';                     /* 10's digit */
          *(bufpt++) = exp%10+'0';                     /* 1's digit */
        }
        *bufpt = 0;

        /* The converted number is in buf[] and zero terminated. Output it.
           Note that the number is in the usual order, not reversed as with
           integer conversions. */
        length = bufpt-buf;
        bufpt = buf;

        /* Special case:  Add leading zeros if the flag_zeropad flag is
           set and we are not left justified */
        if( flag_zeropad && !flag_leftjustify && length < width){
          int i;
          int nPad = width - length;
          for(i=width; i>=nPad; i--){
            bufpt[i] = bufpt[i-nPad];
          }
          i = prefix!=0;
          while( nPad-- ) bufpt[i++] = '0';
          length = width;
        }
#endif /* !CPDO_PRINTF_OMIT_FLOATING_POINT */
        break;
#if !CPDO_PRINTF_OMIT_SIZE
      case etSIZE:
        *(va_arg(ap,int*)) = outCount;
        length = width = 0;
        break;
#endif
      case etPERCENT:
        buf[0] = '%';
        bufpt = buf;
        length = 1;
        break;
      case etCHARLIT:
      case etCHARX:
        c = buf[0] = (xtype==etCHARX ? va_arg(ap,int) : *++fmt);
        if( precision>=0 ){
          for(idx=1; idx<precision; idx++) buf[idx] = c;
          length = precision;
        }else{
          length =1;
        }
        bufpt = buf;
        break;
      case etSTRING:
      case etDYNSTRING: {
	  bufpt = va_arg(ap,char*);
	  spf = (xtype==etSTRING)
              ? spech_string : spech_dynstring;
	  pfrc = spf( pfAppend, pfAppendArg, bufpt );
	  CPDO_PRINTF_CHECKERR(0);
	  length = 0;
	  if( precision>=0 && precision<length ) length = precision;
	}
        break;
#if ! CPDO_PRINTF_OMIT_HTML
      case etHTML:
	  bufpt = va_arg(ap,char*);
	  pfrc = spech_string_to_html( pfAppend, pfAppendArg, bufpt );
	  CPDO_PRINTF_CHECKERR(0);
	  length = 0;
        break;
      case etURLENCODE:
	  bufpt = va_arg(ap,char*);
	  pfrc = spech_urlencode( pfAppend, pfAppendArg, bufpt );
	  CPDO_PRINTF_CHECKERR(0);
	  length = 0;
        break;
      case etURLDECODE:
          bufpt = va_arg(ap,char *);
	  pfrc = spech_urldecode( pfAppend, pfAppendArg, bufpt );
	  CPDO_PRINTF_CHECKERR(0);
          length = 0;
          break;
#endif /* CPDO_PRINTF_OMIT_HTML */
#if ! CPDO_PRINTF_OMIT_SQL
      case etSQLESCAPE:
      case etSQLESCAPE2:
      case etSQLESCAPE3: {
	      cpdo_printf_spec_handler spf =
		      (xtype==etSQLESCAPE)
		      ? spech_sqlstring1
		      : ((xtype==etSQLESCAPE2)
			 ? spech_sqlstring2
			 : spech_sqlstring3
			 );
	      bufpt = va_arg(ap,char*);
	      pfrc = spf( pfAppend, pfAppendArg, bufpt );
	      CPDO_PRINTF_CHECKERR(0);
	      length = 0;
	      if( precision>=0 && precision<length ) length = precision;
      }
#endif /* !CPDO_PRINTF_OMIT_SQL */
    }/* End switch over the format type */
    /*
       The text of the conversion is pointed to by "bufpt" and is
       "length" characters long.  The field width is "width".  Do
       the output.
    */
    if( !flag_leftjustify ){
      int nspace;
      nspace = width-length;
      if( nspace>0 ){
	      CPDO_PRINTF_SPACES(nspace);
      }
    }
    if( length>0 ){
      pfrc = pfAppend( pfAppendArg, bufpt, length);
      CPDO_PRINTF_CHECKERR(0);
    }
    if( flag_leftjustify ){
      int nspace;
      nspace = width-length;
      if( nspace>0 ){
	      CPDO_PRINTF_SPACES(nspace);
      }
    }
    if( zExtra ){
      free(zExtra);
      zExtra = 0;
    }
  }/* End for loop over the format string */
  CPDO_PRINTF_RETURN;
} /* End of function */


#undef CPDO_PRINTF_SPACES
#undef CPDO_PRINTF_CHECKERR
#undef CPDO_PRINTF_RETURN
#undef CPDO_PRINTF_OMIT_FLOATING_POINT
#undef CPDO_PRINTF_OMIT_SIZE
#undef CPDO_PRINTF_OMIT_SQL
#undef CPDO_PRINTF_BUF_SIZE
#undef CPDO_PRINTF_OMIT_HTML

long cpdo_printf(cpdo_printf_appender pfAppend,          /* Accumulate results here */
	    void * pfAppendArg,                /* Passed as first arg to pfAppend. */
	    const char *fmt,                   /* Format string */
	    ... )
{
	va_list vargs;
    long ret;
	va_start( vargs, fmt );
	ret = cpdo_printfv( pfAppend, pfAppendArg, fmt, vargs );
	va_end(vargs);
	return ret;
}


long cpdo_printf_FILE_appender( void * a, char const * s, long n )
{
	FILE * fp = (FILE *)a;
    long ret;
	if( ! fp ) return -1;
	ret = fwrite( s, sizeof(char), n, fp );
	return (ret >= 0) ? ret : -2;
}


long cpdo_printf_file( FILE * fp, char const * fmt, ... )
{
	va_list vargs;
    int ret;
	va_start( vargs, fmt );
	ret = cpdo_printfv( cpdo_printf_FILE_appender, fp, fmt, vargs );
	va_end(vargs);
	return ret;
}

/**
   Internal implementation details for cpdo_printfv_appender_stringbuf.
*/
typedef struct cpdo_printfv_stringbuf
{
    /** dynamically allocated buffer */
    char * buffer;
    /** bytes allocated to buffer */
    size_t alloced;
    /** Current position within buffer. */
    size_t pos;
} cpdo_printfv_stringbuf;
static const cpdo_printfv_stringbuf cpdo_printfv_stringbuf_init = { 0, 0, 0 };

/**
   A cpdo_printfv_appender implementation which requires arg to be a
   (cpdo_printfv_stringbuf*). It appends n bytes of data to the
   cpdo_printfv_stringbuf object's buffer, reallocating it as
   needed. Returns less than 0 on error, else the number of bytes
   appended to the buffer. The buffer will always be null terminated.
*/
static long cpdo_printfv_appender_stringbuf( void * arg, char const * data, long n )
{
    cpdo_printfv_stringbuf * sb = (cpdo_printfv_stringbuf*)arg;
    size_t npos;
    size_t asz;
    char * buf;
    long rc;
    if( ! sb || (n<0) ) return -1;
    if( ! n ) return 0;
    npos = sb->pos + n;
    if( npos >= sb->alloced )
    {
	asz = (npos * 1.5) + 1;
	if( asz < npos ) return -1; /* overflow */
	buf = (char *)realloc( sb->buffer, asz );
	if( ! buf ) return -1;
	memset( buf + sb->pos, 0, asz - sb->pos );
	sb->buffer = buf;
	sb->alloced = asz;
    }
    rc = 0;
    for( ; rc < n; ++rc, ++sb->pos )
    {
        sb->buffer[sb->pos] = data[rc];
    }
    return rc;
}


char * cpdo_printfv_str( char const * fmt, va_list vargs )
{
    cpdo_printfv_stringbuf sb;
    long rc;
    if( ! fmt ) return 0;
    sb = cpdo_printfv_stringbuf_init;
    rc = cpdo_printfv( cpdo_printfv_appender_stringbuf, &sb, fmt, vargs );
    if( rc <= 0 )
    {
	free( sb.buffer );
	sb.buffer = 0;
    }
    return sb.buffer;
}

char * cpdo_printf_str( char const * fmt, ... )
{
    char * ret;
    va_list vargs;
    va_start( vargs, fmt );
    ret = cpdo_printfv_str( fmt, vargs );
    va_end( vargs );
    return ret;
}
#undef etNINFO
#undef CPDO_PRINTF_FMTINFO_FIXED
#undef CPDO_PRINTF_RETURN
#undef CPDO_PRINTF_CHECKERR
#undef CPDO_PRINTF_SPACES

#if defined(__cplusplus)
} /* extern "C" */
#endif
/* end of file cpdo_printf.c */
#if CPDO_ENABLE_SQLITE3
/** @file cpdo_sqlite3.c
    
   sqlite3 driver implementation for cpdo_driver interface.

   Peculiarities vis-a-vis the interface specification:

   - This is the reference driver implementation, and has no known
   incompatibilities with the interface's required features.


   Using this driver:

   The simplest approach is to link it to you app and do:

   @code
   extern int cpdo_driver_sqlite3_register();
   ...
   cpdo_driver_sqlite3_register();
   @endcode

   If you are using C++, or can use C++ for one file of your
   project, you can have that code automatically run by assigning
   a dummy static variable like this:

   @code
   namespace { static int reg_sqlite3 = cpdo_driver_sqlite3_register(); }
   @endcode

   
*/
#include <sqlite3.h>
#include <stdlib.h> /* malloc()/free() */
#include <string.h> /* strlen() */


#if defined(__cplusplus)
extern "C" {
#endif

/************************************************************************
 cpdo_driver_api members:
************************************************************************/
#define CPDO_DRIVER_NAME "sqlite3"
int cpdo_sq3_connect( cpdo_driver * self, cpdo_connect_opt const * opt );
static int cpdo_sq3_sql_quote( cpdo_driver * self, char const * src, uint32_t * len, char ** dest );
static int cpdo_sq3_free_string( cpdo_driver * self, char * str);
static int cpdo_sq3_prepare( cpdo_driver * self, cpdo_stmt ** tgt, char const * sql, uint32_t len );
static int cpdo_sq3_error_info( cpdo_driver * self, char const ** dest, uint32_t * len, int * errorCode );
static char cpdo_sq3_is_connected( cpdo_driver * self );
static int cpdo_sq3_close( cpdo_driver * self );
static int cpdo_sq3_last_insert_id( cpdo_driver * self, uint64_t * v, char const * hint );
static cpdo_driver_details const * cpdo_sq3_driver_details();

static int cpdo_sq3_driver_begin_transaction( cpdo_driver * self );
static int cpdo_sq3_driver_commit( cpdo_driver * self );
static int cpdo_sq3_driver_rollback( cpdo_driver * self );
static char cpdo_sq3_driver_in_trans( cpdo_driver * self );

static int cpdo_sq3_driver_opt_set( cpdo_driver * self, char const * key, va_list vargs );
static int cpdo_sq3_driver_opt_get( cpdo_driver * self, char const * key, va_list vargs );
static int cpdo_sq3_driver_opt_get_string_quote_char( cpdo_driver * self, char * ch );

const cpdo_driver_api cpdo_sq3_driver_api =
{
    cpdo_sq3_driver_details,
    cpdo_sq3_connect,
    cpdo_sq3_sql_quote,
    cpdo_sq3_free_string,
    cpdo_sq3_prepare,
    cpdo_sq3_error_info,
    cpdo_sq3_is_connected,
    cpdo_sq3_close,
    cpdo_sq3_last_insert_id,
    {/*transaction*/
         cpdo_sq3_driver_begin_transaction,
         cpdo_sq3_driver_commit,
         cpdo_sq3_driver_rollback,
         cpdo_sq3_driver_in_trans
    },
    {/*opt*/
        cpdo_sq3_driver_opt_set,
        cpdo_sq3_driver_opt_get,
        cpdo_sq3_driver_opt_get_string_quote_char
    },
    {/*constants*/
    CPDO_DRIVER_NAME /*driver_name*/,
    '"' /*table_quote*/
    }
};

/************************************************************************
cpdo_stmt_api members...
************************************************************************/
static cpdo_step_code cpdo_sq3_stmt_step( cpdo_stmt * self );
static int cpdo_sq3_stmt_error_info( cpdo_stmt * self, char const ** dest, uint32_t * len, int * errorCode );
static uint16_t cpdo_sq3_stmt_column_count( cpdo_stmt * self );
static char const * cpdo_sq3_stmt_column_name( cpdo_stmt * self, uint16_t ndx );
static int cpdo_sq3_stmt_reset( cpdo_stmt * self );
static uint16_t cpdo_sq3_stmt_bind_count( cpdo_stmt * self );
static uint16_t cpdo_sq3_stmt_param_index( cpdo_stmt * self, char const * name );
static char const * cpdo_sq3_stmt_param_name( cpdo_stmt * self, uint16_t ndx );
static int cpdo_sq3_stmt_bind_null( cpdo_stmt * self, uint16_t ndx );
static int cpdo_sq3_stmt_bind_int8( cpdo_stmt * self, uint16_t ndx, int8_t v );
static int cpdo_sq3_stmt_bind_int16( cpdo_stmt * self, uint16_t ndx, int16_t v );
static int cpdo_sq3_stmt_bind_int32( cpdo_stmt * self, uint16_t ndx, int32_t v );
static int cpdo_sq3_stmt_bind_int64( cpdo_stmt * self, uint16_t ndx, int64_t v );
static int cpdo_sq3_stmt_bind_float( cpdo_stmt * self, uint16_t ndx, float v );
static int cpdo_sq3_stmt_bind_double( cpdo_stmt * self, uint16_t ndx, double v );
static int cpdo_sq3_stmt_bind_string( cpdo_stmt * self, uint16_t ndx, char const * v, uint32_t len );
static int cpdo_sq3_stmt_bind_blob( cpdo_stmt * self, uint16_t ndx, void const * v, uint32_t len );
static int cpdo_sq3_stmt_get_type_ndx( cpdo_stmt * self, uint16_t ndx, cpdo_data_type * val );
static int cpdo_sq3_stmt_get_int8_ndx( cpdo_stmt * self, uint16_t ndx, int8_t * val );
static int cpdo_sq3_stmt_get_int16_ndx( cpdo_stmt * self, uint16_t ndx, int16_t * val );
static int cpdo_sq3_stmt_get_int32_ndx( cpdo_stmt * self, uint16_t ndx, int32_t * val );
static int cpdo_sq3_stmt_get_int64_ndx( cpdo_stmt * self, uint16_t ndx, int64_t * val );
static int cpdo_sq3_stmt_get_float_ndx( cpdo_stmt * self, uint16_t ndx, float * val );
static int cpdo_sq3_stmt_get_double_ndx( cpdo_stmt * self, uint16_t ndx, double * val );
static int cpdo_sq3_stmt_get_string_ndx( cpdo_stmt * self, uint16_t ndx, char const ** val, uint32_t * len );
static int cpdo_sq3_stmt_get_blob_ndx( cpdo_stmt * self, uint16_t ndx, void const ** v, uint32_t * len );
static int cpdo_sq3_stmt_finalize( cpdo_stmt * self );
const cpdo_stmt_api cpdo_sq3_stmt_api = {
    cpdo_sq3_stmt_step,
    cpdo_sq3_stmt_error_info,
    cpdo_sq3_stmt_finalize,
    {/*bind*/
        cpdo_sq3_stmt_reset,
        cpdo_sq3_stmt_bind_count,
        cpdo_sq3_stmt_param_index,
        cpdo_sq3_stmt_param_name,
        cpdo_sq3_stmt_bind_null,
        cpdo_sq3_stmt_bind_int8,
        cpdo_sq3_stmt_bind_int16,
        cpdo_sq3_stmt_bind_int32,
        cpdo_sq3_stmt_bind_int64,
        cpdo_sq3_stmt_bind_float,
        cpdo_sq3_stmt_bind_double,
        cpdo_sq3_stmt_bind_string,
        cpdo_sq3_stmt_bind_blob
    },
    {/*get*/
        cpdo_sq3_stmt_column_count,
        cpdo_sq3_stmt_column_name,
        cpdo_sq3_stmt_get_type_ndx,
        cpdo_sq3_stmt_get_int8_ndx,
        cpdo_sq3_stmt_get_int16_ndx,
        cpdo_sq3_stmt_get_int32_ndx,
        cpdo_sq3_stmt_get_int64_ndx,
        cpdo_sq3_stmt_get_float_ndx,
        cpdo_sq3_stmt_get_double_ndx,
        cpdo_sq3_stmt_get_string_ndx,
        cpdo_sq3_stmt_get_blob_ndx
    }
};



typedef struct cpdo_sq3_stmt cpdo_sq3_stmt;
static int cpdo_sq3_stmt_free(cpdo_sq3_stmt *s);
static cpdo_sq3_stmt * cpdo_sq3_stmt_alloc();

typedef struct cpdo_sq3_driver cpdo_sq3_driver;
static int cpdo_sq3_driver_free(cpdo_sq3_driver *d);
static cpdo_sq3_driver * cpdo_sq3_driver_alloc();


struct cpdo_sq3_driver
{
    sqlite3 * db;
    char inTransaction;
    cpdo_driver self;
};


struct cpdo_sq3_stmt
{
    sqlite3_stmt * stmt;
    cpdo_sq3_driver * driver;
    cpdo_stmt self;
};

const cpdo_sq3_driver cpdo_sq3_driver_empty = {
    NULL /*db*/,
    0/*inTransaction*/,
    {/*self*/
        &cpdo_sq3_driver_api /*api*/,
        NULL /*impl*/
    }
};

const cpdo_sq3_stmt cpdo_sq3_stmt_empty = {
    NULL /*stmt*/,
    NULL /*driver*/,
    {/*self*/
        &cpdo_sq3_stmt_api /*api*/,
        NULL /*impl*/
    }
};

static cpdo_sq3_driver * cpdo_sq3_driver_alloc()
{
    cpdo_sq3_driver * s = (cpdo_sq3_driver*)malloc(sizeof(cpdo_sq3_driver));
    if( s )
    {
        *s = cpdo_sq3_driver_empty;
        s->self.impl = s;
    }
    return s;
}

static int cpdo_sq3_driver_free(cpdo_sq3_driver *d)
{
    int rc = cpdo_rc.ArgError;
    if( d )
    {
        rc = 0;
        if( d->db )
        {
            rc = sqlite3_close(d->db);
            if(rc) rc = cpdo_rc.UnknownError
                /* we can't use CheckDbError
                   here because we're destroying the
                   db the client would be checking.
                */
                ;
        }
        *d = cpdo_sq3_driver_empty;
        free(d);
    }
    return rc;
}


/**
   Allocates a new cpdo_sq3_stmt and initializes
   its self.impl member to point to the returned
   object.
*/
static cpdo_sq3_stmt * cpdo_sq3_stmt_alloc()
{
    cpdo_sq3_stmt * s = (cpdo_sq3_stmt*)malloc(sizeof(cpdo_sq3_stmt));
    if( s )
    {
        *s = cpdo_sq3_stmt_empty;
        s->self.impl = s;
    }
    return s;
}

/**
   Frees all resources belonging to this statement.  It can return
   non-0, but there is no generic recovery strategy for this, and s is
   freed regardless of whether or not sqlite3_finalize() succeeds.
*/
static int cpdo_sq3_stmt_free(cpdo_sq3_stmt *s)
{
    int rc = cpdo_rc.ArgError;
    if( s )
    {
        rc = 0;
        if( s->stmt )
        {
            rc = sqlite3_finalize(s->stmt);
            if(0 != rc ) rc = cpdo_rc.CheckDbError;
        }
        *s = cpdo_sq3_stmt_empty;
        free(s);
    }
    return rc;
}


int cpdo_sq3_driver_new( cpdo_driver ** tgt )
{
    if( ! tgt ) return cpdo_rc.ArgError;
    else
    {
        cpdo_sq3_driver * d = cpdo_sq3_driver_alloc();
        if( d )
        {
            *tgt = &d->self;
            return 0;
        }
        else return cpdo_rc.AllocError;
    }
}

#define DRV_DECL(RC) cpdo_sq3_driver * drv = (self && self->impl && (self->api==&cpdo_sq3_driver_api)) \
        ? (cpdo_sq3_driver *)self->impl : NULL; \
    if( ! drv ) return RC
#define STMT_DECL(RC) cpdo_sq3_stmt * stmt = (self && self->impl && (self->api==&cpdo_sq3_stmt_api)) \
        ? (cpdo_sq3_stmt *)self->impl : NULL; \
    if( ! stmt ) return RC

static int cpdo_sq3_last_insert_id( cpdo_driver * self, uint64_t * v, char const * hint )
{
    DRV_DECL(cpdo_rc.ArgError);
    if( ! v ) return cpdo_rc.ArgError;
    else
    {
        *v = sqlite3_last_insert_rowid(drv->db);
        return 0;
    }
}
static int cpdo_sq3_close( cpdo_driver * self )
{
    DRV_DECL(cpdo_rc.ArgError);
    cpdo_sq3_driver_free(drv);
    return 0;
}

static char cpdo_sq3_is_connected( cpdo_driver * self )
{
    DRV_DECL(0);
    return drv->db ? 1 : 0;
}

static int cpdo_sq3_error_info( cpdo_driver * self, char const ** dest, uint32_t * len, int * errorCode )
{
    DRV_DECL(cpdo_rc.ArgError);
    if( ! drv->db ) return cpdo_rc.ConnectionError;
    else
    {
        if( errorCode ) *errorCode =
#if (SQLITE_VERSION_NUMBER >= 3003009 /* FIXME: which version number is correct???*/)
			    sqlite3_extended_errcode
#else
			    sqlite3_errcode
#endif
			    (drv->db);
        if( dest )
        {
            *dest = sqlite3_errmsg(drv->db);
            if( len )
            {
                *len = *dest ? strlen(*dest) : 0;
            }
        }
        return 0;
    }
}

    
static int cpdo_sq3_sql_quote( cpdo_driver * self, char const * str, uint32_t * len, char ** dest )
{
    DRV_DECL(cpdo_rc.ArgError);
    if( ! len || !dest ) return cpdo_rc.ArgError;
    else if( NULL == str )
    {
        char * tmp = (char *)malloc(5);
        if( ! tmp ) return cpdo_rc.AllocError;
        strcpy( tmp, "NULL" );
        *dest = tmp;
        *len = 4;
        return 0;
    }
    else
    {
        return cpdo_sql_escape( str, len, dest,
                                '\'',
                                '\'',
                                1 );
    }
}

static int cpdo_sq3_free_string( cpdo_driver * self, char * str)
{
    return str ? (free(str),0) : cpdo_rc.ArgError;
}

static int cpdo_sq3_prepare( cpdo_driver * self, cpdo_stmt ** tgt, char const * sql, uint32_t len )
{
    int rc;
    sqlite3_stmt * st3 = NULL;
    cpdo_sq3_stmt * stmt = NULL;
    DRV_DECL(cpdo_rc.ArgError);
    if(!drv->db) return cpdo_rc.ConnectionError;
    else if( ! tgt ) return cpdo_rc.ArgError;
    rc =
#if (SQLITE_VERSION_NUMBER >= 3003009)
	sqlite3_prepare_v2
#else
	sqlite3_prepare
#endif
	( drv->db, sql, (int)len, &st3, NULL );
    if( 0 != rc ) return cpdo_rc.CheckDbError;
    stmt = cpdo_sq3_stmt_alloc();
    if( ! stmt )
    {
        sqlite3_finalize(st3);
        return cpdo_rc.AllocError;
    }
    stmt->stmt = st3;
    stmt->driver = drv;
    *tgt = &stmt->self;
    return 0;
}

int cpdo_sq3_connect( cpdo_driver * self, cpdo_connect_opt const * opt )
{
    int rc;
    DRV_DECL(cpdo_rc.ArgError);
    if( ! opt ) return cpdo_rc.ArgError;
    else if( drv->db ) return cpdo_rc.ConnectionError;
    {
        enum { BufSize = 256U };
        char buf[BufSize];
        char const * params = NULL;
#if (SQLITE_VERSION_NUMBER >= 3005001)
        int flags; flags = 0; /* not yet used */
#endif
        rc = cpdo_split_dsn( opt->dsn, buf, BufSize, &params );
        if( rc ) return rc;
        /*
          FIXME: strip any parameters after the first ';' separator
          (just replace the first ';' with a NUL).
         */
#if (SQLITE_VERSION_NUMBER >= 3005001)
        rc = flags
            ? sqlite3_open_v2( params, &drv->db, flags, NULL )
            : sqlite3_open( params, &drv->db );
#else
        rc = sqlite3_open( params, &drv->db );
#endif
        /* reminder: don't close so the caller can get error info. */
        return rc ? cpdo_rc.CheckDbError : 0;
    }
}


static int cpdo_sq3_driver_begin_transaction( cpdo_driver * self )
{
    char const * sql = NULL;
    int rc;
    DRV_DECL(cpdo_rc.ArgError);
    if( drv->inTransaction ) return cpdo_rc.UnsupportedError;
    sql = "BEGIN TRANSACTION";
    rc = cpdo_exec( self, sql, strlen(sql) );
    if( 0 == rc ) drv->inTransaction = 1;
    return rc;
}

static int cpdo_sq3_driver_commit( cpdo_driver * self )
{
    char const * sql = NULL;
    int rc;
    DRV_DECL(cpdo_rc.ArgError);
    sql = "COMMIT";
    rc = cpdo_exec( self, sql, strlen(sql) );
    drv->inTransaction = 0;
    return rc;
}

static int cpdo_sq3_driver_rollback( cpdo_driver * self )
{
    char const * sql = NULL;
    int rc;
    DRV_DECL(cpdo_rc.ArgError);
    sql = "ROLLBACK";
    rc = cpdo_exec( self, sql, strlen(sql) );
    drv->inTransaction = 0;
    return rc;
}

static char cpdo_sq3_driver_in_trans( cpdo_driver * self )
{
    DRV_DECL(0);
    return drv->inTransaction;
}

static int cpdo_sq3_driver_opt_set( cpdo_driver * self, char const * key, va_list vargs )
{
    return cpdo_rc.NYIError;
}
static int cpdo_sq3_driver_opt_get( cpdo_driver * self, char const * key, va_list vargs )
{
    return cpdo_rc.NYIError;
}

static int cpdo_sq3_driver_opt_get_string_quote_char( cpdo_driver * self, char * ch )
{
    if( NULL == ch ) return cpdo_rc.ArgError;
    else
    {
        *ch = '\'';
        return 0;
    }
}


static cpdo_step_code cpdo_sq3_stmt_step( cpdo_stmt * self )
{
    STMT_DECL(CPDO_STEP_ERROR);
    switch( sqlite3_step( stmt->stmt ) )
    {
      case SQLITE_ROW:
          return CPDO_STEP_OK;
      case SQLITE_DONE:
          return CPDO_STEP_DONE;
      default:
          return CPDO_STEP_ERROR;
    }
}

static int cpdo_sq3_stmt_reset( cpdo_stmt * self )
{
    STMT_DECL(cpdo_rc.ArgError);
    return sqlite3_reset( stmt->stmt ) ? cpdo_rc.CheckDbError : 0;
}

static uint16_t cpdo_sq3_stmt_column_count( cpdo_stmt * self )
{
    int rc;
    STMT_DECL(0);
    rc = sqlite3_column_count( stmt->stmt );
    return (rc>0) ? (uint32_t)rc : 0;
}

static char const * cpdo_sq3_stmt_column_name( cpdo_stmt * self, uint16_t ndx )
{
    STMT_DECL(NULL);
    return sqlite3_column_name( stmt->stmt, (int)ndx );
}

static uint16_t cpdo_sq3_stmt_bind_count( cpdo_stmt * self )
{
    int rc;
    STMT_DECL(0);
    rc = sqlite3_bind_parameter_count( stmt->stmt );
    return (rc<=0) ? 0 : (uint16_t)rc;
}


static uint16_t cpdo_sq3_stmt_param_index( cpdo_stmt * self, char const * name )
{
    int rc;
    STMT_DECL(0);
    if( ! name ) return 0;
    else
    {
        rc = sqlite3_bind_parameter_index(stmt->stmt, name);
        return (rc<=0) ? 0U : (uint16_t)rc;
    }
}

static char const * cpdo_sq3_stmt_param_name( cpdo_stmt * self, uint16_t ndx )
{
    STMT_DECL(NULL);
    return sqlite3_bind_parameter_name( stmt->stmt, (int)ndx );
}

/** Converts sqlite3_bind_xxx() return value to cpdo_rc. */
#define SQ3_TO_CPDO_BIND_RC(RC) \
    if( 0 == (RC) ) return (RC); \
    if( SQLITE_NOMEM == (RC) ) return cpdo_rc.AllocError; \
    else if( SQLITE_RANGE == (RC) ) return cpdo_rc.RangeError; \
    else return cpdo_rc.CheckDbError
    
static int cpdo_sq3_stmt_bind_null( cpdo_stmt * self, uint16_t ndx )
{
    int rc;
    STMT_DECL(cpdo_rc.ArgError);
    rc = sqlite3_bind_null( stmt->stmt, (int)ndx );
    SQ3_TO_CPDO_BIND_RC(rc);
}

static int cpdo_sq3_stmt_bind_int8( cpdo_stmt * self, uint16_t ndx, int8_t v )
{
    int rc;
    STMT_DECL(cpdo_rc.ArgError);
    rc = sqlite3_bind_int( stmt->stmt, (int)ndx, (int)v );
    SQ3_TO_CPDO_BIND_RC(rc);
}

static int cpdo_sq3_stmt_bind_int16( cpdo_stmt * self, uint16_t ndx, int16_t v )
{
    int rc;
    STMT_DECL(cpdo_rc.ArgError);
    rc = sqlite3_bind_int( stmt->stmt, (int)ndx, (int)v );
    SQ3_TO_CPDO_BIND_RC(rc);
}
    
static int cpdo_sq3_stmt_bind_int32( cpdo_stmt * self, uint16_t ndx, int32_t v )
{
    int rc;
    STMT_DECL(cpdo_rc.ArgError);
    rc = sqlite3_bind_int( stmt->stmt, (int)ndx, (int)v );
    SQ3_TO_CPDO_BIND_RC(rc);
}

static int cpdo_sq3_stmt_bind_int64( cpdo_stmt * self, uint16_t ndx, int64_t v )
{
    int rc;
    typedef
#if SQLITE_VERSION_NUMBER <= 3003006
	/*FIXME: in which version did they rename sqlite_int64 to
	  sqlite3_int64?*/
	sqlite_int64
#else
	sqlite3_int64
#endif
	sq3_int64_t;
    STMT_DECL(cpdo_rc.ArgError);
    rc = sqlite3_bind_int64( stmt->stmt, (int)ndx, (sq3_int64_t)v );
    SQ3_TO_CPDO_BIND_RC(rc);
}

static int cpdo_sq3_stmt_bind_float( cpdo_stmt * self, uint16_t ndx, float v )
{
    int rc;
    STMT_DECL(cpdo_rc.ArgError);
    rc = sqlite3_bind_double( stmt->stmt, (int)ndx, v );
    SQ3_TO_CPDO_BIND_RC(rc);
}

static int cpdo_sq3_stmt_bind_double( cpdo_stmt * self, uint16_t ndx, double v )
{
    int rc;
    STMT_DECL(cpdo_rc.ArgError);
    rc = sqlite3_bind_double( stmt->stmt, (int)ndx, v );
    SQ3_TO_CPDO_BIND_RC(rc);
}

static int cpdo_sq3_stmt_bind_string( cpdo_stmt * self, uint16_t ndx, char const * v, uint32_t len )
{
    int rc;
    STMT_DECL(cpdo_rc.ArgError);
    if( v )
    {
        rc = sqlite3_bind_text( stmt->stmt, (int)ndx, (char const *)v, (int)len, SQLITE_TRANSIENT );
    }
    else
    {
        rc = sqlite3_bind_null( stmt->stmt, (int)ndx );
    }
    SQ3_TO_CPDO_BIND_RC(rc);
}

static int cpdo_sq3_stmt_bind_blob( cpdo_stmt * self, uint16_t ndx, void const * v, uint32_t len )
{
    
    if( (NULL == v) || (0==len) )
    {
        return cpdo_sq3_stmt_bind_null( self, ndx );
    }
    else
    { 
        int rc;
        STMT_DECL(cpdo_rc.ArgError);
        rc = sqlite3_bind_blob( stmt->stmt, (int)ndx, v, (int)len, SQLITE_TRANSIENT );
        SQ3_TO_CPDO_BIND_RC(rc);
    }
}
#undef SQ3_TO_CPDO_BIND_RC

static int cpdo_sq3_stmt_get_type_ndx( cpdo_stmt * self, uint16_t ndx, cpdo_data_type * val )
{
    int rc = 0;
    STMT_DECL(cpdo_rc.ArgError);
    if( ! val ) return cpdo_rc.ArgError;
    switch( sqlite3_column_type(stmt->stmt, (int)ndx ) )
    {
      case SQLITE_INTEGER:
          *val = CPDO_TYPE_INT64;
          break;
      case SQLITE_FLOAT:
          *val = CPDO_TYPE_DOUBLE;
          break;
      case SQLITE_TEXT: /* my sqlite3.h defines
                           both SQLITE_TEXT and SQLITE3_TEXT
                           to the same value.
                        */
          *val = CPDO_TYPE_STRING;
          break;
      case SQLITE_BLOB:
          *val = CPDO_TYPE_BLOB;
          break;
      case SQLITE_NULL:
          *val = CPDO_TYPE_NULL;
          break;
      default:
          rc = cpdo_rc.TypeError;
          break;
    }
    return rc;
}

/** Returns cpdo_rc.RangeError if 0-based ndx is out of bounds. */
#define STMT_CHECK_GET_NDX if( ndx >= sqlite3_column_count(stmt->stmt) ) return cpdo_rc.RangeError

static int cpdo_sq3_stmt_get_int8_ndx( cpdo_stmt * self, uint16_t ndx, int8_t * val )
{
    STMT_DECL(cpdo_rc.ArgError);
    STMT_CHECK_GET_NDX;
    else if( val ) *val = (int8_t) sqlite3_column_int( stmt->stmt, (int)ndx );
    return 0;
}
static int cpdo_sq3_stmt_get_int16_ndx( cpdo_stmt * self, uint16_t ndx, int16_t * val )
{
    STMT_DECL(cpdo_rc.ArgError);
    STMT_CHECK_GET_NDX;
    else if( val ) *val = (int16_t) sqlite3_column_int( stmt->stmt, (int)ndx );
    return 0;
}

static int cpdo_sq3_stmt_get_int32_ndx( cpdo_stmt * self, uint16_t ndx, int32_t * val )
{
    STMT_DECL(cpdo_rc.ArgError);
    STMT_CHECK_GET_NDX;
    else if( val ) *val = (int32_t) sqlite3_column_int( stmt->stmt, (int)ndx );
    return 0;
}

static int cpdo_sq3_stmt_get_int64_ndx( cpdo_stmt * self, uint16_t ndx, int64_t * val )
{
    STMT_DECL(cpdo_rc.ArgError);
    STMT_CHECK_GET_NDX;
    else if( val ) *val = (int64_t) sqlite3_column_int64( stmt->stmt, (int)ndx );
    return 0;
}

static int cpdo_sq3_stmt_get_float_ndx( cpdo_stmt * self, uint16_t ndx, float * val )
{
    STMT_DECL(cpdo_rc.ArgError);
    STMT_CHECK_GET_NDX;
    else if( val ) *val = (float)sqlite3_column_double( stmt->stmt, (int)ndx );
    return 0;
}
    
static int cpdo_sq3_stmt_get_double_ndx( cpdo_stmt * self, uint16_t ndx, double * val )
{
    STMT_DECL(cpdo_rc.ArgError);
    STMT_CHECK_GET_NDX;
    else if( val ) *val = sqlite3_column_double( stmt->stmt, (int)ndx );
    return 0;
}

static int cpdo_sq3_stmt_get_string_ndx( cpdo_stmt * self, uint16_t ndx, char const ** val, uint32_t * len )
{
    STMT_DECL(cpdo_rc.ArgError);
    if( ! val ) return cpdo_rc.ArgError;
    else STMT_CHECK_GET_NDX;
    else
    {
        sqlite3_value * sv = sqlite3_column_value(stmt->stmt, (int)ndx);
        if( ! sv ) return cpdo_rc.RangeError;
        *val = (SQLITE_NULL == sqlite3_value_type(sv))
            ? NULL
            : (char const *)sqlite3_column_text( stmt->stmt, (int)ndx );
        if( len )
        {
            *len = (val && *val) ? strlen(*val) : 0;
        }
        return 0;
    }
}

static int cpdo_sq3_stmt_get_blob_ndx( cpdo_stmt * self, uint16_t ndx, void const ** val, uint32_t * len )
{
    STMT_DECL(cpdo_rc.ArgError);
    if( ! val ) return cpdo_rc.ArgError;
    else STMT_CHECK_GET_NDX;
    else
    {
        *val = sqlite3_column_blob( stmt->stmt, (int)ndx )
            /* reminder: sqlite3_column_blob() returns NULL for
               length-zero blobs. */
                ;
        if( len )
        {
            *len = *val
                ? (uint32_t)sqlite3_column_bytes( stmt->stmt, (int)ndx )
                : 0
                ;
        }
        return 0;
    }
}
#undef STMT_CHECK_GET_NDX

int cpdo_sq3_stmt_error_info( cpdo_stmt * self, char const ** dest, uint32_t * len, int * errorCode )
{
    STMT_DECL(cpdo_rc.ArgError);
    return cpdo_sq3_error_info( &stmt->driver->self, dest, len, errorCode );
}

    
static int cpdo_sq3_stmt_finalize( cpdo_stmt * self )
{
    STMT_DECL(cpdo_rc.ArgError);
    return cpdo_sq3_stmt_free(stmt);
}



static cpdo_driver_details const * cpdo_sq3_driver_details()
{
    static const cpdo_driver_details bob = {
    CPDO_DRIVER_NAME/*driver_name*/,
    "20110131"/*driver_version*/,
    "Dual Public Domain/MIT"/*license*/,
    "http://fossil.wanderinghorse.net/repos/cpdo/",
    "Stephan Beal (http://wanderinghorse.net)"
    };
    return &bob;
}

int cpdo_driver_sqlite3_register()
{
    return cpdo_driver_register( CPDO_DRIVER_NAME, cpdo_sq3_driver_new );
}




#if defined(__cplusplus)
} /*extern "C"*/
#endif

#undef DRV_DECL
#undef STMT_DECL
#undef CPDO_DRIVER_NAME
#endif /*CPDO_ENABLE_SQLITE3*/
#if CPDO_ENABLE_MYSQL5
/** @file cpdo_mysql5.c

  MySQL v5 driver implementation for cpdo_driver interface.

   DSN driver parameters:

   - port=NUM

   - autocommit=BOOL

   - host=STRING

   - dbname=STRING

   - fieldbuffersize=INTEGER. When fetching string/blob data, if the
   db cannot tell us the maximum length for the field then this value
   is used as a fallback. The driver ignores "very small" values, but
   how small "very small" is is not specified.


   TODO:

   - DSN option: debug=BOOL [default=false]
   
   - DSN option: logfile=STRING [default=NULL]

   Peculiarities vis-a-vis, and optional features supported from, the
   cpdo interface specification:
   
   - There are no known incompatibilities with the CPDO interface's
   required features.
   
   - When the autocommit DSN parameter is used and
   cpdo_stmt_api::transaction::begin() is called, auto-commit mode is
   disabled until commit() or rollback() are called. It is then
   re-enabled. If the autocommit parameter is not explicitly provided
   then no finagling of the autocommit mode is done.

   - When fetching string/blob data, if the driver cannot figure out
   the declared maximum size then it uses a fixed-size buffer, which
   won't work for large data. Use the fieldbuffersize=N DSN parameter
   to specify your own size, but beware that this will be used for all
   string fields when we cannot determine the size automatically.

   - The cpdo_stmt_api::get::string() impl can convert numeric and
   TIME/DATE/DATETIME/TIMESTAMP data to a string.

   - MySQL leaks some memory when connecting and calling
   mysql_library_end() at app shutdown does not always free it.
   i can do nothing about this.

   - MySQL does not natively support binding parameters by name, that
   feature is implemented using a custom parser. It is possible that
   that parser might misbehave. This feature defaults to enabled but
   can be disabled with the DSN option "enablenamedparams=false".


   Using this driver:

   The simplest approach is to link it to you app and do:

   @code
   extern int cpdo_driver_mysql5_register();
   ...
   cpdo_driver_mysql5_register();
   @endcode

   If you are using C++, or can use C++ for one file of your
   project, you can have that code automatically run by assigning
   a dummy static variable like this:

   @code
   extern int cpdo_driver_mysql5_register();
   namespace {
       static int reg_mysql5 = cpdo_driver_mysql5_register();
   }
   @endcode

   You also must link to mysql if the app/DLL containing _this_ code
   is not linked against it. The 'mysql_config' script (installed as
   part of the mysql packages) can give you the proper values for
   compiling/linking.
   
   LICENSE:

   Copyright 2011 Stephan Beal (http://wanderinghorse.net/home/stephan)
   
   This code may be used under the terms of the license(s) the client
   has accepted for the MySQL library which is used when building this
   software. Thus if the client has accepted the GNU GPL for his MySQL
   installation, then this software may be used under the terms of the
   GPL. If he has accepted a commercial license (e.g. from Oracle)
   then he may use those licensing terms.

   In other words, if you have accepted a MySQL license (which you
   presumably have, or you would not be using this driver) then you
   have already accepted the license for this code.
*/
/* From my inttypes.h, in regards to PRIi32 and friends:

   "The ISO C99 standard specifies that these macros must only be
   defined if explicitly requested."
*/
#if defined(__cplusplus) && !defined(__STDC_FORMAT_MACROS)
#  define __STDC_FORMAT_MACROS
#endif
#include <inttypes.h> /* PRIi32 and friends */

#include <assert.h>
#include <mysql/mysql.h>
#include <stdlib.h> /* malloc()/free() */
#include <string.h> /* strlen() */

#include <stdio.h> /* only for debuggering */

#define MEGADEBUG 0

#define MARKER if(1) printf("MARKER: %s:%d:%s():\t",__FILE__,__LINE__,__func__); if(1) printf

/** CPDO_MY5_HAS_PRINT64 is used to determine whether or not to install
    our own int64-to-string logic. C89 does not specify the equivalent
    of C99's PRIi64 format specifier.
    
    If CPDO_MY5_HAS_PRINT64 is true then we use PRIi64 and sprintf(),
    otherwise we use cpdo_printf() to do the conversion.
*/
#define CPDO_MY5_HAS_PRINT64 (CPDO_ENABLE_64_BIT || (__STDC_VERSION__ >= 199901L) || (HAVE_LONG_LONG == 1))

#if !CPDO_MY5_HAS_PRINT64
#endif

#if defined(__cplusplus)
extern "C" {
#endif

/************************************************************************
 cpdo_driver_api members:
************************************************************************/
#define CPDO_DRIVER_NAME "mysql5"
int cpdo_my5_connect( cpdo_driver * self, cpdo_connect_opt const * opt );
static int cpdo_my5_sql_quote( cpdo_driver * self, char const * src, uint32_t * len, char ** dest );
static int cpdo_my5_free_string( cpdo_driver * self, char * str);
static int cpdo_my5_prepare( cpdo_driver * self, cpdo_stmt ** tgt, const char * sql, uint32_t len );
static int cpdo_my5_error_info( cpdo_driver * self, char const ** dest, uint32_t * len, int * errorCode );
static char cpdo_my5_is_connected( cpdo_driver * self );
static int cpdo_my5_close( cpdo_driver * self );
static int cpdo_my5_last_insert_id( cpdo_driver * self, uint64_t * v, char const * hint );
static cpdo_driver_details const * cpdo_my5_driver_details();

static int cpdo_my5_driver_begin_transaction( cpdo_driver * self );
static int cpdo_my5_driver_commit( cpdo_driver * self );
static int cpdo_my5_driver_rollback( cpdo_driver * self );
static char cpdo_my5_driver_in_trans( cpdo_driver * self );

static int cpdo_my5_driver_opt_set( cpdo_driver * self, char const * key, va_list vargs );
static int cpdo_my5_driver_opt_get( cpdo_driver * self, char const * key, va_list vargs );
static int cpdo_my5_driver_opt_get_string_quote_char( cpdo_driver * self, char * ch );

const cpdo_driver_api cpdo_my5_driver_api =
{
    cpdo_my5_driver_details,
    cpdo_my5_connect,
    cpdo_my5_sql_quote,
    cpdo_my5_free_string,
    cpdo_my5_prepare,
    cpdo_my5_error_info,
    cpdo_my5_is_connected,
    cpdo_my5_close,
    cpdo_my5_last_insert_id,
    {/*transaction*/
         cpdo_my5_driver_begin_transaction,
         cpdo_my5_driver_commit,
         cpdo_my5_driver_rollback,
         cpdo_my5_driver_in_trans
    },
    {/*opt*/
        cpdo_my5_driver_opt_set,
        cpdo_my5_driver_opt_get,
        cpdo_my5_driver_opt_get_string_quote_char
    },
    {/*constants*/
    CPDO_DRIVER_NAME /*driver_name*/,
    '`' /*table_quote*/
    }
};

/************************************************************************
 cpdo_stmt_api members...
************************************************************************/
static cpdo_step_code cpdo_my5_stmt_step( cpdo_stmt * self );
static int cpdo_my5_stmt_error_info( cpdo_stmt * self, char const ** dest, uint32_t * len, int * errorCode );
static uint16_t cpdo_my5_stmt_column_count( cpdo_stmt * self );
static char const * cpdo_my5_stmt_column_name( cpdo_stmt * self, uint16_t ndx );
static int cpdo_my5_stmt_reset( cpdo_stmt * self );
static uint16_t cpdo_my5_stmt_bind_count( cpdo_stmt * self );
static uint16_t cpdo_my5_stmt_param_index( cpdo_stmt * self, char const * name );
static char const * cpdo_my5_stmt_param_name( cpdo_stmt * self, uint16_t ndx );
static int cpdo_my5_stmt_bind_null( cpdo_stmt * self, uint16_t ndx );
static int cpdo_my5_stmt_bind_int8( cpdo_stmt * self, uint16_t ndx, int8_t v );
static int cpdo_my5_stmt_bind_int16( cpdo_stmt * self, uint16_t ndx, int16_t v );
static int cpdo_my5_stmt_bind_int32( cpdo_stmt * self, uint16_t ndx, int32_t v );
static int cpdo_my5_stmt_bind_int64( cpdo_stmt * self, uint16_t ndx, int64_t v );
static int cpdo_my5_stmt_bind_float( cpdo_stmt * self, uint16_t ndx, float v );
static int cpdo_my5_stmt_bind_double( cpdo_stmt * self, uint16_t ndx, double v );
static int cpdo_my5_stmt_bind_string( cpdo_stmt * self, uint16_t ndx, char const * v, uint32_t len );
static int cpdo_my5_stmt_bind_blob( cpdo_stmt * self, uint16_t ndx, void const * v, uint32_t len );
static int cpdo_my5_stmt_get_type_ndx( cpdo_stmt * self, uint16_t ndx, cpdo_data_type * val );
static int cpdo_my5_stmt_get_int8_ndx( cpdo_stmt * self, uint16_t ndx, int8_t * val );
static int cpdo_my5_stmt_get_int16_ndx( cpdo_stmt * self, uint16_t ndx, int16_t * val );
static int cpdo_my5_stmt_get_int32_ndx( cpdo_stmt * self, uint16_t ndx, int32_t * val );
static int cpdo_my5_stmt_get_int64_ndx( cpdo_stmt * self, uint16_t ndx, int64_t * val );
static int cpdo_my5_stmt_get_float_ndx( cpdo_stmt * self, uint16_t ndx, float * val );
static int cpdo_my5_stmt_get_double_ndx( cpdo_stmt * self, uint16_t ndx, double * val );
static int cpdo_my5_stmt_get_string_ndx( cpdo_stmt * self, uint16_t ndx, char const ** val, uint32_t * len );
static int cpdo_my5_stmt_get_blob_ndx( cpdo_stmt * self, uint16_t ndx, void const ** v, uint32_t * len );
static int cpdo_my5_stmt_finalize( cpdo_stmt * self );
const cpdo_stmt_api cpdo_my5_stmt_api = {
    cpdo_my5_stmt_step,
    cpdo_my5_stmt_error_info,
    cpdo_my5_stmt_finalize,
    {/*bind*/
        cpdo_my5_stmt_reset,
        cpdo_my5_stmt_bind_count,
        cpdo_my5_stmt_param_index,
        cpdo_my5_stmt_param_name,
        cpdo_my5_stmt_bind_null,
        cpdo_my5_stmt_bind_int8,
        cpdo_my5_stmt_bind_int16,
        cpdo_my5_stmt_bind_int32,
        cpdo_my5_stmt_bind_int64,
        cpdo_my5_stmt_bind_float,
        cpdo_my5_stmt_bind_double,
        cpdo_my5_stmt_bind_string,
        cpdo_my5_stmt_bind_blob
    },
    {/*get*/
        cpdo_my5_stmt_column_count,
        cpdo_my5_stmt_column_name,
        cpdo_my5_stmt_get_type_ndx,
        cpdo_my5_stmt_get_int8_ndx,
        cpdo_my5_stmt_get_int16_ndx,
        cpdo_my5_stmt_get_int32_ndx,
        cpdo_my5_stmt_get_int64_ndx,
        cpdo_my5_stmt_get_float_ndx,
        cpdo_my5_stmt_get_double_ndx,
        cpdo_my5_stmt_get_string_ndx,
        cpdo_my5_stmt_get_blob_ndx
    }
};



typedef struct cpdo_my5_stmt cpdo_my5_stmt;
static int cpdo_my5_stmt_free(cpdo_my5_stmt *s);
static cpdo_my5_stmt * cpdo_my5_stmt_alloc();

typedef struct cpdo_my5_driver cpdo_my5_driver;
static int cpdo_my5_driver_free(cpdo_my5_driver *d);
static cpdo_my5_driver * cpdo_my5_driver_alloc();


/**
    Internal impl of cpdo_driver.
*/
struct cpdo_my5_driver
{
    MYSQL * conn;
    char isConnected;
    char inTransaction;
    char explicitAutoCommit;
    uint32_t fieldBufferSize;
    char enableNamedParams;
    cpdo_my5_stmt * currentStmt;
    char * lastErrMsg;
    int lastErrNo;
    /** The "this" object of the instance. */
    cpdo_driver self;
};

/**
    Empty-initialized cpdo_my5_driver object.
*/
const cpdo_my5_driver cpdo_my5_driver_empty = {
    NULL/*conn*/,
    0/*isConnected*/,
    0/*inTransaction*/,
    -1/*explicitAutoCommit. -1 is a magic value later on, so don't change it!.*/,
    1024 * 4 /*fieldBufferSize*/,
    1 /*enablenamedparams*/,
    NULL /*currentStmt*/,
    NULL /* lastErrMsg */,
    0 /* lastErrNo */,
    {/*self*/
        &cpdo_my5_driver_api /*api*/,
        NULL /*impl*/
    }
};

/**
    Internan cpdo_stmt impl.
*/
struct cpdo_my5_stmt
{
    MYSQL_STMT * stmt;
    MYSQL_RES * colMeta;
    MYSQL_ROW * row;
    cpdo_my5_driver * driver;
    char needsExec;
    /**
        Used when driver->enableNamedParams is true to store
        the translated SQL.
    */
    char * sql;
    /**
       Buffers for holding bound parameter data.
     */
    struct
    {
        /** Number of bound parameters. */
        uint16_t count;
        /** MySQL's interface into the bound parameters.
            This is an array count items long.
        */
        MYSQL_BIND * myBinders;
        /** Our buffers where myBinders point to.
            This is an array count items long.
        */
        cpdo_bind_val * cBinders;
        /**
            If driver->enableNamedParams is true then this
            is an array, count items long, holding the names
            of the bound parameters. The name is "?" if
            the bound parameter is a question-mark parameter
            placeholder.
            
            As odd as this seems, this memory is owned by the sql
            pointer, and freeing that memory frees this as well.
            See cpdo_named_params_to_qmarks() for why.
        */
        char ** names;
    } pbind;
    /**
       Buffers for holding result set data.
     */
    struct
    {
        /** The number of columns in the result set.
        */
        uint16_t count;
        /** MySQL's interface into the result data columsn.
            This is an array count items long.
        */
        MYSQL_BIND * myBinders;
        /** Our buffers where myBinders point to.
            This is an array count items long.
        */
        cpdo_bind_val * cBinders;
        /**
            Buffers for holding T-to-String conversions.
            This is an array count items long.
        */
        cpdo_bind_val * convBuf;
    } rbind;
    /** The "this" object of the instance. */
    cpdo_stmt self;
};

/**
    Empty-initialized cpdo_my5_stmt object.
*/
const cpdo_my5_stmt cpdo_my5_stmt_empty = {
    NULL /*stmt*/,
    NULL /*colMeta*/,
    NULL /*row*/,
    NULL /*driver*/,
    1 /*needsExec*/,
    NULL /*sql*/,
    {/*pbind*/
        0/*count*/,
        NULL /*myBinders*/,
        NULL /*cBinders*/,
        NULL /*names*/
    },
    {/*rbind*/
        0/*count*/,
        NULL /*myBinders*/,
        NULL /*cBinders*/,
        NULL /*convBuf*/
    },
    {/*self*/
        &cpdo_my5_stmt_api /*api*/,
        NULL /*impl*/
    }
};

/**
    Allocates a new cpdo_my5_driver and its conn member, and
    points theObject->self.impl at theObject for later reference
    and proper cleanup.

    Returns NULL on error. On success the caller owns the
    object, of course.
*/
static cpdo_my5_driver * cpdo_my5_driver_alloc()
{
    cpdo_my5_driver * s = (cpdo_my5_driver*)malloc(sizeof(cpdo_my5_driver));
    if( s )
    {
        MYSQL * con = mysql_init(NULL);
        if( ! con )
        {
            free(s);
            return NULL;
        }
        else
        {
            *s = cpdo_my5_driver_empty;
            s->conn = con;
            s->self.impl = s;
        }
    }
    return s;
}

/**
   Closes d->conn and frees all memory associated with d.  d does not
   track statements it opens, and all statements must be closed before
   closing the db, else Undefined Behaviour.
*/
static int cpdo_my5_driver_free(cpdo_my5_driver *d)
{
    int rc = cpdo_rc.ArgError;
    if( d )
    {
        rc = 0;
        free( d->lastErrMsg );
        if( d->conn )
        {
            mysql_close(d->conn);
        }
        *d = cpdo_my5_driver_empty;
        free(d);
    }
    return rc;
}


/**
   Allocates a new cpdo_my5_stmt and initializes
   its self.impl member to point to the returned
   object.
   
   Returns NULL on error. On success the caller owns the
   object, of course.
*/
static cpdo_my5_stmt * cpdo_my5_stmt_alloc()
{
    cpdo_my5_stmt * s = (cpdo_my5_stmt*)malloc(sizeof(cpdo_my5_stmt));
    if( s )
    {
        *s = cpdo_my5_stmt_empty;
        s->self.impl = s;
    }
    return s;
}

/**
   Frees all resources belonging to this statement.  It can return
   non-0, but there is no generic recovery strategy for this, and s is
   freed regardless of whether or not sqlite3_finalize() succeeds.
*/
static int cpdo_my5_stmt_free(cpdo_my5_stmt *st)
{
    int rc = cpdo_rc.ArgError;
    if( st )
    {
        rc = 0;
        if( st->sql )
        {
            assert( 0 != st->pbind.count );
            free( st->sql );
            st->pbind.names = NULL /* memory is owned by sql string!*/;
        }
        if( st->stmt )
        {
            mysql_stmt_close(st->stmt);
        }
        if( st->colMeta )
        {
            mysql_free_result(st->colMeta);
        }
        if( st->pbind.myBinders )
        {
            assert( 0 != st->pbind.count );
            free(st->pbind.myBinders);
        }
        if( st->pbind.cBinders )
        {
            assert( 0 != st->pbind.count );
            cpdo_bind_val_list_free( st->pbind.cBinders, st->pbind.count );
        }
        if( st->rbind.convBuf )
        {
            assert( 0 != st->rbind.count );
            cpdo_bind_val_list_free( st->rbind.convBuf, st->rbind.count );
        }
        if( st->rbind.myBinders )
        {
            assert( 0 != st->rbind.count );
            free(st->rbind.myBinders);
        }
        if( st->rbind.cBinders )
        {
            assert( 0 != st->rbind.count );
            cpdo_bind_val_list_free( st->rbind.cBinders, st->rbind.count );
        }
        *st = cpdo_my5_stmt_empty;
        free( st );
    }
    return rc;
}


/**
   cpdo_driver_factory_f() impl._ Allocates a new cpdo_my5_driver.
*/
int cpdo_my5_driver_new( cpdo_driver ** tgt )
{
    if( ! tgt ) return cpdo_rc.ArgError;
    else
    {
        cpdo_my5_driver * d = cpdo_my5_driver_alloc();
        if( d )
        {
            static char inited = 0;
            if( ! inited && (inited=1) )
            {
                atexit( mysql_library_end );
            }
            *tgt = &d->self;
            return 0;
        }
        else return cpdo_rc.AllocError;
    }
}

#define DRV_DECL(RC) cpdo_my5_driver * drv = (self && self->impl && (self->api==&cpdo_my5_driver_api)) \
        ? (cpdo_my5_driver *)self->impl : NULL; \
    if( ! drv ) return RC

#define STMT_DECL(RC) cpdo_my5_stmt * stmt = (self && self->impl && (self->api==&cpdo_my5_stmt_api)) \
        ? (cpdo_my5_stmt *)self->impl : NULL; \
    if( ! stmt ) return RC
#define PBIND_DECL(NDX) MYSQL_BIND * mybin; cpdo_bind_val * cbin;     \
        STMT_DECL(cpdo_rc.ArgError);                                    \
        if(!(NDX) || ((NDX)>stmt->pbind.count)) return cpdo_rc.RangeError;  \
        mybin = &stmt->pbind.myBinders[(NDX)-1]; cbin = &stmt->pbind.cBinders[(NDX)-1]



static int cpdo_my5_drv_err2( cpdo_my5_driver * self, int n, char const * msg )
{
    size_t const slen = msg ? strlen(msg) : 0;
    char * x;
    free( self->lastErrMsg );
    self->lastErrMsg = NULL;
    self->lastErrNo = n;
    if( ! slen ) return 0;
    x = (char *)malloc( slen + 1 );
    if( !x ) return cpdo_rc.AllocError;
    else
    {
        memcpy( x, msg, slen );
        x[slen] = 0;
        self->lastErrMsg = x;
        return 0;
    }
}

static int cpdo_my5_drv_err( cpdo_my5_driver * drv )
{
    return cpdo_my5_drv_err2( drv, mysql_errno(drv->conn), mysql_error(drv->conn) );
}
static int cpdo_my5_stmt_err( cpdo_my5_stmt * self )
{
    return cpdo_my5_drv_err2( self->driver,
                              mysql_stmt_errno(self->stmt),
                              mysql_stmt_error(self->stmt) );
}

static int cpdo_my5_last_insert_id( cpdo_driver * self, uint64_t * v, char const * hint )
{
    DRV_DECL(cpdo_rc.ArgError);
    if( ! v ) return cpdo_rc.ArgError;
    else
    {
        *v = mysql_insert_id(drv->conn);
        return 0;
    }
}

#if 0
static void cpdo_my5_clear_err( cpdo_my5_driver * drv )
{
    cpdo_my5_drv_err2( drv, 0, NULL );
}
#endif

static int cpdo_my5_close( cpdo_driver * self )
{
    DRV_DECL(cpdo_rc.ArgError);
    cpdo_my5_driver_free(drv);
    return 0;
}

static char cpdo_my5_is_connected( cpdo_driver * self )
{
    DRV_DECL(0);
    return drv->isConnected;
}

static int cpdo_my5_error_info( cpdo_driver * self, char const ** dest, uint32_t * len, int * errorCode )
{
    DRV_DECL(cpdo_rc.ArgError);
    if( ! drv->conn ) return cpdo_rc.ConnectionError;
    else
    {
        if( errorCode )
        {
            *errorCode = drv->lastErrMsg ? drv->lastErrNo : mysql_errno(drv->conn);
        }
        if( dest )
        {
            *dest = drv->lastErrMsg ? drv->lastErrMsg : mysql_error(drv->conn);
            if( len )
            {
                *len = *dest ? strlen(*dest) : 0;
            }
        }
        return 0;
    }
}

/**
   RESET_DRV_ERR should be called in each function which might return
   cpdo_rc.CheckDbError. (Because those are the functions which
   update drv->lastErrMsg.)

   We need this to avoid a use-case (corner case?) in error handling
   where drv->lastErrMsg would shadow the value from mysql_error().

   That said, there probably are some odd corner-cases this laying
   around from this hack (which was necessary for us to be able to
   report statement-preparation-failed error info).
 */
#define RESET_DRV_ERR(DRIVER) cpdo_my5_drv_err2( (DRIVER), 0, NULL )

static int cpdo_my5_sql_quote( cpdo_driver * self, char const * str, uint32_t * len, char ** dest )
{
    DRV_DECL(cpdo_rc.ArgError);
    RESET_DRV_ERR(drv);
    if( ! len || !dest ) return cpdo_rc.ArgError;
    else if( NULL == str )
    {
        char * tmp = (char *)malloc(5);
        if( ! tmp ) return cpdo_rc.AllocError;
        strcpy( tmp, "NULL" );
        *dest = tmp;
        *len = 4;
        return 0;
    }
    else
    {
        char * to = NULL;
        unsigned long aLen;
        cpdo_my5_drv_err2( drv, 0, NULL );
        aLen = *len * 2 + 1;
        to = (char *)calloc(aLen,1);
        if( ! to ) return cpdo_rc.AllocError;
        *len = mysql_real_escape_string( drv->conn, to, str, *len );
        *dest = to;
        return 0;
    }
}

static int cpdo_my5_free_string( cpdo_driver * self, char * str)
{
    return str ? (free(str),0) : cpdo_rc.ArgError;
}


/**
   Allocates enough space for paramCount bound parameters and
   columnCount result columns, not including the memory we will need
   to point MYSQ_BIND to for result data.

   Returns 0 on success.
*/
static int cpdo_my5_setup_bind_buffers( cpdo_my5_stmt * stmt, uint16_t paramCount,
                                        uint16_t columnCount  )
{
    if( paramCount > 0 )
    { /* bound parameters ... */
        stmt->pbind.myBinders = (MYSQL_BIND*) calloc(sizeof(MYSQL_BIND),paramCount);
        if( ! stmt->pbind.myBinders ) return cpdo_rc.AllocError;
        stmt->pbind.count = (uint16_t)paramCount
            /* reminder we need this value set here in case the next ops fail. */
            ;
        stmt->pbind.cBinders = cpdo_bind_val_list_new(stmt->pbind.count);
        if( ! stmt->pbind.cBinders ) return cpdo_rc.AllocError;
    }
    if( columnCount > 0 )
    { /* fetchable fields... */
        stmt->rbind.myBinders = (MYSQL_BIND*) calloc(sizeof(MYSQL_BIND), columnCount);
        if( ! stmt->rbind.myBinders ) return cpdo_rc.AllocError;
        stmt->rbind.count = (uint16_t)columnCount
            /* reminder we need this value set here in case the next ops fail. */
            ;
        stmt->rbind.cBinders = cpdo_bind_val_list_new(stmt->rbind.count);
        if( ! stmt->rbind.cBinders ) return cpdo_rc.AllocError;

        stmt->rbind.convBuf = cpdo_bind_val_list_new(stmt->rbind.count);
        if( ! stmt->rbind.convBuf ) return cpdo_rc.AllocError;

    }
    if( stmt->colMeta && !stmt->rbind.count ) return cpdo_rc.InternalError;
    return 0;
}

/**
   Frees v, which is expected to be a MYSQL_TIME value
   stored by cpdo_my5_setup_result_bindings().

   Used by the MYSQL_TIME/DATE/DATETIME/TIMESTAMP-binding code.
*/
static void cpdo_my5_MYSQL_TIME_free( void * v )
{
    free(v);
}
/**
   Sets up stmt->rbind depending on the column state of stmt->stmt. It
   sets up the buffers needed by MySQL for binding fetchable results.

   Returns 0 on success. On error stmt initialization must
   be considered to have failed. The only realistic errors here
   are:

   a) Bugs in this code. i'm not aware of any, but we normally aren't.

   b) An allocation error. This can certainly happen if someone
   fetches huge string/blob fields.
*/
static int cpdo_my5_setup_result_bindings( cpdo_my5_stmt * stmt )
{
    if( ! stmt->rbind.count ) return 0;
    else if( ! stmt->colMeta ) return cpdo_rc.InternalError;
    else if( ! stmt->rbind.count ) return 0;
    else
    {
        uint16_t i;
        MYSQL_FIELD * fld = NULL;
        MYSQL_BIND * bin = NULL;
        cpdo_bind_val * bv = NULL;
        int rc;
        for( i = 0; i < stmt->rbind.count; ++i )
        {
            fld = &stmt->stmt->fields[i];
            bin = &stmt->rbind.myBinders[i];
            bv = &stmt->rbind.cBinders[i];
            bin->is_null = &bv->is_null;
            bin->error = &bv->has_error;
            switch( fld->type )
            {
              case MYSQL_TYPE_TINY:
                  cpdo_bind_val_int8( bv, 0 );
                  bin->buffer = (char *)&bv->valu.i8;
                  bin->buffer_type = fld->type;
                  break;
              case MYSQL_TYPE_SHORT:
                  cpdo_bind_val_int16( bv, 0 );
                  bin->buffer = (char *)&bv->valu.i16;
                  bin->buffer_type = fld->type;
                  break;
              case MYSQL_TYPE_LONG:
                  cpdo_bind_val_int32( bv, 0 );
                  bin->buffer = (char *)&bv->valu.i32;
                  bin->buffer_type = fld->type;
                  break;
              case MYSQL_TYPE_LONGLONG:
                  cpdo_bind_val_int64( bv, 0 );
                  bin->buffer = (char *)&bv->valu.i64;
                  bin->buffer_type = fld->type;
                  break;
              case MYSQL_TYPE_FLOAT:
                  cpdo_bind_val_float( bv, 0.0 );
                  bin->buffer = (char *)&bv->valu.flt;
                  bin->buffer_type = fld->type;
                  break;
              case MYSQL_TYPE_DOUBLE:
                  cpdo_bind_val_double( bv, 0.0 );
                  bin->buffer = (char *)&bv->valu.dbl;
                  bin->buffer_type = fld->type;
                  break;
              case MYSQL_TYPE_VAR_STRING:
              case MYSQL_TYPE_STRING: {
                  unsigned int const allocLen = fld->length
                      ? fld->length
                      : stmt->driver->fieldBufferSize
                      ;
                  rc = cpdo_bind_val_string( bv, NULL, allocLen );
                  if( rc ) return rc;
                  bin->buffer = (char *)bv->valu.blob.mem;
                  bin->buffer_type = fld->type;
                  bin->buffer_length = bv->valu.blob.length;
                  bin->length = &bv->valu.blob.length;
                  break;
              }
              case MYSQL_TYPE_BLOB: {
                  unsigned int allocLen = fld->length
                      ? fld->length
                      : stmt->driver->fieldBufferSize
                      ;
                  rc = cpdo_bind_val_blob( bv, NULL, allocLen );
                  if( rc ) return rc;
                  bin->buffer = (char *)bv->valu.blob.mem;
                  bin->buffer_type = fld->type;
                  bin->buffer_length = bv->valu.blob.length;
                  bin->length = &bv->valu.blob.length;
                  break;
              }
              case MYSQL_TYPE_DATE:
              case MYSQL_TYPE_TIME:
              case MYSQL_TYPE_DATETIME:
              case MYSQL_TYPE_TIMESTAMP: {
                  MYSQL_TIME * mt = (MYSQL_TIME *)calloc(sizeof(MYSQL_TIME),1);
                  if( ! mt ) return cpdo_rc.AllocError;
                  rc = cpdo_bind_val_custom( bv, mt,
                                             cpdo_my5_MYSQL_TIME_free,
                                             cpdo_bind_val_tag_type_hash(&cpdo_my5_driver_api,fld->type));
                  if( rc )
                  {
                      free(mt);
                      return rc;
                  }
                  bin->buffer = (char *)mt;
                  bin->buffer_type = fld->type;
                  bin->buffer_length = sizeof(MYSQL_TIME);
                  bin->length = &bv->valu.custom.length;
                  break;
              }
              default:
                  MARKER("WARNING: UNHANDLED MYSQL_TYPE_XXX #%d IN PARAMETER DATA\n",fld->type);
                  return cpdo_rc.TypeError;
            };
        }
        return 0;
    }

}

static int cpdo_my5_prepare( cpdo_driver * self, cpdo_stmt ** tgt, char const * sql, uint32_t len  )
{
    int rc = 0;
    cpdo_my5_stmt * st = NULL;
    MYSQL_STMT * myst = NULL;
    MYSQL_RES * meta = NULL;
    char * xlate = NULL /* "translated" SQL, for named params support. */;
    uint32_t xlateLen = 0 /* length of xlate */;
    char ** nameList = NULL /* bound params names. Memory is owned by xlate's block! */;
    uint16_t paramCount = 0;
    uint16_t fieldCount = 0;
    DRV_DECL(cpdo_rc.ArgError);
    RESET_DRV_ERR(drv);
    myst = mysql_stmt_init( drv->conn );
    if( NULL == myst )
    {
        cpdo_my5_drv_err( drv );
        return cpdo_rc.CheckDbError;
    }
    if( drv->enableNamedParams )
    { /* Do custom bound parameter name parsing... */
        rc = cpdo_named_params_to_qmarks( sql, len, ':', 1, &paramCount,
                                          &xlate, &xlateLen, &nameList );
        if( rc )
        {
            assert( NULL == xlate );
            mysql_stmt_close( myst );
            return rc;
        }
    }
    rc = xlate
        ? mysql_stmt_prepare( myst, xlate, xlateLen )
        : mysql_stmt_prepare( myst, sql, len );
    if( rc )
    {
        /* FIXME:

        The client has no way to get this error info. We could stuff it into the
        driver object, but that introduces threading-related problems.

        MySQL does not document (and google doesn't know) the lifetime
        of the bytes returned by mysql_stmt_error().
        */
#if MEGADEBUG
        MARKER("prepare failed: mysql_stmt_error(): %s\n", mysql_stmt_error(myst));
#endif
        cpdo_my5_drv_err2( drv, mysql_stmt_errno(myst), mysql_stmt_error(myst) );
        mysql_stmt_close( myst );
        free(xlate);
        return cpdo_rc.CheckDbError;
    }
    if( drv->enableNamedParams )
    {
        if( (uint16_t)mysql_stmt_param_count( myst ) != paramCount )
        { /* indicative of a bug in our parsing. */
            mysql_stmt_close( myst );
            free( xlate );
            return cpdo_rc.InternalError;
        }
    }
    else
    {
        paramCount = (uint16_t)mysql_stmt_param_count( myst );
    }
    fieldCount = (uint16_t)mysql_stmt_field_count( myst );
    meta = mysql_stmt_result_metadata( myst )/* can legally be NULL*/;
    st = cpdo_my5_stmt_alloc();
    if( NULL == st )
    {
        if( meta ) mysql_free_result( meta );
        mysql_stmt_close( myst );
        free(xlate);
        return cpdo_rc.AllocError;
    }
    st->stmt = myst;
    st->sql = xlate;
    st->pbind.names = nameList;
    st->driver = drv;
    st->colMeta = meta;
    rc = cpdo_my5_setup_bind_buffers( st, paramCount, fieldCount );
    assert( paramCount == st->pbind.count );
    if( 0 == rc ) rc = cpdo_my5_setup_result_bindings( st );
    if( 0 == rc ) *tgt = &st->self;
    else cpdo_my5_stmt_free(st);
    if( MEGADEBUG && (0 == rc) )
    {
        MARKER("Created statement @%p\n", (void const *)self);
    }

    return rc;
}

int cpdo_my5_connect( cpdo_driver * self, cpdo_connect_opt const * opt )
{
    DRV_DECL(cpdo_rc.ArgError);
    if( ! opt || !opt->dsn ) return cpdo_rc.ArgError;
    else
    {
        enum {
            /** Max size for parameter keys and values, including
            trailing NUL.
            */
            BufSize = 128U
        };
        char const * tokBegin = opt->dsn;
        char const * tokEnd = NULL;
        char kbuf[BufSize] = {0,0};
        char pDbName[BufSize] = {0,0};
        char pHost[BufSize] = {0,0};
        int port = 0;
        int rc = 0;
        if( drv->isConnected ) return cpdo_rc.ConnectionError;
        for( ; *tokBegin && (*tokBegin != ':'); ++tokBegin ) {
            /* skip driver name part of dsn. */
        }
        if( ':' != *tokBegin ) return cpdo_rc.RangeError;
        ++tokBegin /* skip ':'*/;
        port = rc = 0;
        while( cpdo_next_token( &tokBegin, ';', &tokEnd) )
        { /* TODO: wrap most of this into a helper function
             which does the key/value splitting. We'll need
             this in other drivers.
          */
            if( tokBegin == tokEnd ) break;
            else
            {
                char const * key = tokBegin;
                char const * value = NULL;
                char * at = kbuf;
                if( (tokEnd - tokBegin) >= BufSize ) return cpdo_rc.RangeError;
                memset( kbuf, 0, BufSize );
                /* Write the key part to the buffer... */
                for( ; (key<tokEnd) && *key && ('='!=*key); ++key ) {
                    *(at++) = *key;
                }
                *(at++) = 0;
                value = at;
                if( '=' == *key ) {
                    ++key;
                }
                /* Write the value part to the buffer... */
                for( ; (key<tokEnd) && *key; ++key ) {
                    *(at++) = *key;
                }
                key = kbuf;
                /*MARKER("key=[%s] value=[%s]\n", key, value);*/

                /* Done parsing. Now see if we understand how to use
                   this option... */
                if( 0 == strcmp("port",key) )
                { /* remember that mysql ignores the port number when
                     connecting to localhost via a UNIX socket.
                  */
                    port = *value ? atoi(value) : 0;
                    if( port < 0 ) port = 0;
                }
                else if( 0 == strcmp("dbname",key) )
                {
                    size_t const slen = strlen(value);
                    if( slen >= BufSize ) return cpdo_rc.RangeError;
                    memcpy( pDbName, value, slen );
                    pDbName[slen] = 0;
                }
                else if( 0 == strcmp("host",key) )
                {
                    size_t const slen = strlen(value);
                    if( slen >= BufSize ) return cpdo_rc.RangeError;
                    memcpy( pHost, value, slen );
                    pHost[slen] = 0;
                }
                else if( 0 == strcmp("autocommit",key) )
                {
                    drv->explicitAutoCommit = cpdo_token_bool_val(value);
                }
                else if( 0 == strcmp("fieldbuffersize",key) )
                {
                    size_t const slen = strlen(value);
                    int32_t i;
                    if( slen >= BufSize ) return cpdo_rc.RangeError;
                    i = atoi(value);
                    if( i > 64 )
                    {
                        drv->fieldBufferSize = (uint32_t)i;
                    }
                }
                else if( 0 == strcmp("enablenamedparams",key) )
                {
                    drv->enableNamedParams = cpdo_token_bool_val(value);
                }
                else
                {
                    /* ignore unknown keys: this is optional in the CPDO
                       interface. If we add warning support, i'll add the
                       warning here. Or if i'm feeling pedantic later i'll
                       throw the error here.
                    */
                }
                /* set up for the next token... */
                tokBegin = tokEnd;
                tokEnd = NULL;
            }
        } /* options parsing */
        rc = (drv->conn ==
              mysql_real_connect( drv->conn, pHost,
                                  opt->user_name, opt->password,
                                  pDbName, port,
                                  NULL/*unix socket*/, 0 /*"client flag"*/))
            ? 0 :  cpdo_rc.CheckDbError
            ;
        if( (0 == rc)
            && (drv->explicitAutoCommit!=-1
                /* only set autocommit explicitly if we got an autocommit parameter*/)
            )
        {
            mysql_autocommit( drv->conn, drv->explicitAutoCommit );
        }
        if( 0 == rc )
        {
            drv->isConnected = 1;
        }
        else if( cpdo_rc.CheckDbError == rc )
        {
            cpdo_my5_drv_err( drv );
        }
        return rc;
    }
}


static int cpdo_my5_driver_begin_transaction( cpdo_driver * self )
{
    int rc;
    DRV_DECL(cpdo_rc.ArgError);
    RESET_DRV_ERR(drv);
    if( drv->inTransaction ) return cpdo_rc.UnsupportedError;
    /**
        i can find no API for BEGINING a transaction in MySQL,
        but there are mysql_commit() and mysql_rollback().
        Though the API docs don't SAY THIS, turning off autocommit
        is _apparently_ the same as "BEGIN", except that when
        i run "BEGIN" from here the statement preparation fails
        with error code 1. (From the command-line mysql client it works
        fine.)
    */
    rc = mysql_autocommit(drv->conn, 0);
    /*rc = cpdo_exec( self, "BEGIN", 5 );*/
    if( 0 == rc ) drv->inTransaction = 1;
    if( rc )
    {
        cpdo_my5_drv_err( drv );
        return cpdo_rc.CheckDbError;
    }
    else return 0;
}

static int cpdo_my5_driver_opt_set( cpdo_driver * self, char const * key, va_list vargs )
{
    return cpdo_rc.NYIError;
}
static int cpdo_my5_driver_opt_get( cpdo_driver * self, char const * key, va_list vargs )
{
    return cpdo_rc.NYIError;
}

static int cpdo_my5_driver_opt_get_string_quote_char( cpdo_driver * self, char * ch )
{
    /* TODO: support configurable single- or double-quote char. */
    if( NULL == ch ) return cpdo_rc.ArgError;
    else
    {
        *ch = '\'';
        return 0;
    }
}

static int cpdo_my5_driver_commit( cpdo_driver * self )
{
    int rc;
    DRV_DECL(cpdo_rc.ArgError);
    RESET_DRV_ERR(drv);
    rc = mysql_commit( drv->conn );
    if( drv->explicitAutoCommit >= 0 /* == was explicitly set by the client.*/ )
    {
        mysql_autocommit(drv->conn, drv->explicitAutoCommit );
    }
    drv->inTransaction = 0;
    if( rc )
    {
        cpdo_my5_drv_err( drv );
        return cpdo_rc.CheckDbError;
    }
    else return 0;
}

static int cpdo_my5_driver_rollback( cpdo_driver * self )
{
    int rc;
    DRV_DECL(cpdo_rc.ArgError);
    RESET_DRV_ERR(drv);
    rc = mysql_rollback( drv->conn );
    if( drv->explicitAutoCommit >= 0 )
    {
        mysql_autocommit(drv->conn, drv->explicitAutoCommit);
    }
    drv->inTransaction = 0;
    if( rc )
    {
        cpdo_my5_drv_err( drv );
        return cpdo_rc.CheckDbError;
    }
    else return 0;
}

static char cpdo_my5_driver_in_trans( cpdo_driver * self )
{
    DRV_DECL(0);
    return drv->inTransaction;
}

/**
   Cleans up the innards of st->rbind.convBuf. To be called
   before stepping the cursor.
*/
static void cpdo_my5_cleanup_scratchpads( cpdo_my5_stmt * st )
{
    uint16_t i;
    assert( st );
    for( i = 0; i < st->rbind.count; ++i )
    {
        cpdo_bind_val_clean( &st->rbind.convBuf[i] );
    }
}

static cpdo_step_code cpdo_my5_stmt_step( cpdo_stmt * self )
{
    STMT_DECL(CPDO_STEP_ERROR);
    if( ! stmt->stmt ) return CPDO_STEP_ERROR;
    if( stmt->pbind.count )
    {
        if( mysql_stmt_bind_param( stmt->stmt, stmt->pbind.myBinders ) )
        {
            return CPDO_STEP_ERROR;
        }
    }
    if( stmt->rbind.count )
    { /* fetching data */
        int rc;
        cpdo_my5_cleanup_scratchpads( stmt );
        if( mysql_stmt_bind_result( stmt->stmt, stmt->rbind.myBinders ) )
        {
            return CPDO_STEP_ERROR;
        }
        if( stmt->needsExec )
        {
            if( mysql_stmt_execute( stmt->stmt ) ) return CPDO_STEP_ERROR;
            stmt->needsExec = 0;
        }
        rc = mysql_stmt_fetch( stmt->stmt );
        if( 0 == rc ) return CPDO_STEP_OK;
        else if( MYSQL_NO_DATA == rc ) return CPDO_STEP_DONE;
        else return CPDO_STEP_ERROR;
    }
    else
    { /* non-fetching query */
        if( mysql_stmt_execute( stmt->stmt ) ) return CPDO_STEP_ERROR;
        stmt->needsExec = 0;
        return CPDO_STEP_DONE;
    }
}

static int cpdo_my5_stmt_reset( cpdo_stmt * self )
{
    STMT_DECL(cpdo_rc.ArgError);
    RESET_DRV_ERR(stmt->driver);
    if( 0==mysql_stmt_reset(stmt->stmt) )
    {
        stmt->needsExec = 1;
        return 0;
    }
    else
    {
        cpdo_my5_stmt_err( stmt );
        return cpdo_rc.CheckDbError;
    }
}

static uint16_t cpdo_my5_stmt_column_count( cpdo_stmt * self )
{
    STMT_DECL(cpdo_rc.ArgError);
    return (uint32_t)mysql_stmt_field_count(stmt->stmt);
}

static char const * cpdo_my5_stmt_column_name( cpdo_stmt * self, uint16_t ndx )
{
    STMT_DECL(NULL);
    return
    /* these should all be equivalent... */
#if 0
        ( ndx >= mysql_stmt_field_count(stmt->stmt) )
#elif 1
        ( ndx >= stmt->stmt->field_count )
#elif 0
        ( ndx >= cpdo_my5_stmt_column_count( stmt )
#else
        ( ndx >= stmt->api->column_count(stmt) )
#endif        
        ? NULL
        : stmt->stmt->fields[ndx].name
        ;
}

static uint16_t cpdo_my5_stmt_bind_count( cpdo_stmt * self )
{
    STMT_DECL(0);
    return stmt->pbind.count;
}

static uint16_t cpdo_my5_stmt_param_index( cpdo_stmt * self, char const * name )
{
    /*
      We need this function:

      http://dev.mysql.com/doc/refman/5.0/en/mysql-stmt-param-metadata.html

      But its docs say: "This function currently does nothing."
    */
    uint16_t i;
    char const * key;
    STMT_DECL(0);
    if( ! name || !*name || ('?'==*name) )
    {
        /* Reminder: we catch '?' here because this routine will only
           ever match the first one with that name. */
        return cpdo_rc.ArgError;
    }
    for( i = 0; i < stmt->pbind.count; ++i )
    {
        key = stmt->pbind.names[i];
        if( key && (0==strcmp(key,name)) )
        {
            return i+1;
        }
    }
    return 0;
}

static char const * cpdo_my5_stmt_param_name( cpdo_stmt * self, uint16_t ndx )
{
    STMT_DECL(NULL);
    if( !ndx || (ndx > stmt->pbind.count) ) return NULL;
    assert( stmt->pbind.names && stmt->pbind.names[ndx-1] );
    return stmt->pbind.names[ndx-1];
}

static int cpdo_my5_stmt_bind_null( cpdo_stmt * self, uint16_t ndx )
{
    PBIND_DECL(ndx);
    memset(mybin, 0, sizeof(MYSQL_BIND));
    mybin->buffer_type = MYSQL_TYPE_NULL;
    cpdo_bind_val_null( cbin );
    return 0;
}

static int cpdo_my5_stmt_bind_int8( cpdo_stmt * self, uint16_t ndx, int8_t v )
{
    PBIND_DECL(ndx);
    memset(mybin, 0, sizeof(MYSQL_BIND));
    cpdo_bind_val_int8( cbin, v );
    mybin->buffer_type = MYSQL_TYPE_TINY;
    mybin->buffer = (char *)&cbin->valu.i8;
    mybin->is_null = 0;
    return 0;
}

static int cpdo_my5_stmt_bind_int16( cpdo_stmt * self, uint16_t ndx, int16_t v )
{
    PBIND_DECL(ndx);
    memset(mybin, 0, sizeof(MYSQL_BIND));
    cpdo_bind_val_int16( cbin, v );
    mybin->buffer_type = MYSQL_TYPE_SHORT;
    mybin->buffer = (char *)&cbin->valu.i16;
    mybin->is_null = 0;
    return 0;
}

static int cpdo_my5_stmt_bind_int32( cpdo_stmt * self, uint16_t ndx, int32_t v )
{
    PBIND_DECL(ndx);
    memset(mybin, 0, sizeof(MYSQL_BIND));
    cpdo_bind_val_int32( cbin, v );
    mybin->buffer_type = MYSQL_TYPE_LONG;
    mybin->buffer = (char *)&cbin->valu.i32;
    mybin->is_null = 0;
    return 0;
}

static int cpdo_my5_stmt_bind_int64( cpdo_stmt * self, uint16_t ndx, int64_t v )
{
    PBIND_DECL(ndx);
    memset(mybin, 0, sizeof(MYSQL_BIND));
    cpdo_bind_val_int64( cbin, v );
    mybin->buffer_type = MYSQL_TYPE_LONGLONG;
    mybin->buffer = (char *)&cbin->valu.i64;
    mybin->is_null = 0;
    return 0;
}

static int cpdo_my5_stmt_bind_float( cpdo_stmt * self, uint16_t ndx, float v )
{
    PBIND_DECL(ndx);
    memset(mybin, 0, sizeof(MYSQL_BIND));
    cpdo_bind_val_float( cbin, v );
    mybin->buffer_type = MYSQL_TYPE_FLOAT;
    mybin->buffer = (char *)&cbin->valu.flt;
    mybin->is_null = 0;
    return 0;
}

static int cpdo_my5_stmt_bind_double( cpdo_stmt * self, uint16_t ndx, double v )
{
    PBIND_DECL(ndx);
    memset(mybin, 0, sizeof(MYSQL_BIND));
    cpdo_bind_val_double( cbin, v );
    mybin->buffer_type = MYSQL_TYPE_DOUBLE;
    mybin->buffer = (char *)&cbin->valu.dbl;
    mybin->is_null = 0;
    return 0;
}

static int cpdo_my5_stmt_bind_string( cpdo_stmt * self, uint16_t ndx, char const * v, uint32_t len )
{
    static char isNullYes = 1;
    static char isNullNo = 0;
    int rc;
    PBIND_DECL(ndx);
    memset(mybin, 0, sizeof(MYSQL_BIND));
    rc = cpdo_bind_val_string( cbin, v, len );
    if( rc ) return rc;
    else
    {
        mybin->buffer_type = MYSQL_TYPE_STRING;
        mybin->buffer = (char *)cbin->valu.blob.mem;
        mybin->is_null = v
            ? &isNullNo
            : &isNullYes;
        mybin->buffer_length = len;
        return 0;
    }
}

static int cpdo_my5_stmt_bind_blob( cpdo_stmt * self, uint16_t ndx, void const * v, uint32_t len )
{
    static char isNullYes = 1;
    static char isNullNo = 0;
    int rc;
    PBIND_DECL(ndx);
    memset(mybin, 0, sizeof(MYSQL_BIND));
    rc = cpdo_bind_val_blob( cbin, v, len );
    if( rc ) return rc;
    else
    {
        mybin->buffer_type = MYSQL_TYPE_BLOB;
        mybin->buffer = (char *)cbin->valu.blob.mem;
        mybin->is_null = (v && len)
            ? &isNullNo
            : &isNullYes;
        mybin->buffer_length = len;
        return 0;
    }
}

static int cpdo_my5_stmt_get_type_ndx( cpdo_stmt * self, uint16_t ndx, cpdo_data_type * val )
{
    STMT_DECL(cpdo_rc.ArgError);
    if( ! val ) return cpdo_rc.ArgError;
    else if( ndx >= stmt->rbind.count ) return cpdo_rc.RangeError;
    else
    {
        cpdo_bind_val const * bv = &stmt->rbind.cBinders[ndx];
        *val = (bv->is_null) ? CPDO_TYPE_NULL : bv->type;
        return 0;
    }
}

/**
   Get-by-index impl for the int8..int64 number types.
*/
static int cpdo_my5_stmt_get_int_types( cpdo_my5_stmt * stmt,
                                        uint16_t ndx,
                                        int64_t * val )
{
    assert( stmt && (ndx<stmt->rbind.count));
    if( ! val ) return cpdo_rc.ArgError;
    else if( ndx >= stmt->rbind.count ) return cpdo_rc.RangeError;
    else
    {
        cpdo_bind_val * bv = &stmt->rbind.cBinders[ndx];
        if( bv->is_null )
        {
            *val = 0;
            return 0;
        }
        switch( bv->type )
        {
          case CPDO_TYPE_INT8:
              *val = bv->valu.i8;
              break;
          case CPDO_TYPE_INT16:
              *val = bv->valu.i16;
              break;
          case CPDO_TYPE_INT32:
              *val = bv->valu.i32;
              break;
          case CPDO_TYPE_INT64:
              *val = bv->valu.i64;
              break;
          case CPDO_TYPE_FLOAT:
              *val = (int64_t)bv->valu.flt;
              break;
          case CPDO_TYPE_DOUBLE:
              *val = (int64_t)bv->valu.dbl;
              break;
          case CPDO_TYPE_NULL:
              *val = 0;
              break;
          default:
              return cpdo_rc.TypeError;
        }
        return 0;
    }
}



static int cpdo_my5_stmt_get_int8_ndx( cpdo_stmt * self, uint16_t ndx, int8_t * val )
{
    int64_t x;
    int rc;
    STMT_DECL(cpdo_rc.ArgError);
    rc = cpdo_my5_stmt_get_int_types( stmt, ndx, &x );
    if( 0 == rc )
    {
        *val = (int8_t)x;
    }
    return rc;
}

static int cpdo_my5_stmt_get_int16_ndx( cpdo_stmt * self, uint16_t ndx, int16_t * val )
{
    int64_t x;
    int rc;
    STMT_DECL(cpdo_rc.ArgError);
    rc = cpdo_my5_stmt_get_int_types( stmt, ndx, &x );
    if( 0 == rc )
    {
        *val = (int16_t)x;
    }
    return rc;
}

static int cpdo_my5_stmt_get_int32_ndx( cpdo_stmt * self, uint16_t ndx, int32_t * val )
{
    int64_t x;
    int rc;
    STMT_DECL(cpdo_rc.ArgError);
    rc = cpdo_my5_stmt_get_int_types( stmt, ndx, &x );
    if( 0 == rc )
    {
        *val = (int32_t)x;
    }
    return rc;
}

static int cpdo_my5_stmt_get_int64_ndx( cpdo_stmt * self, uint16_t ndx, int64_t * val )
{
    STMT_DECL(cpdo_rc.ArgError);
    return cpdo_my5_stmt_get_int_types( stmt, ndx, val );
}

static int cpdo_my5_stmt_get_double_ndx( cpdo_stmt * self, uint16_t ndx, double * val )
{
    STMT_DECL(cpdo_rc.ArgError);
    if( ! val ) return cpdo_rc.ArgError;
    else if( ndx >= stmt->rbind.count ) return cpdo_rc.RangeError;
    else
    {
        cpdo_bind_val * bv = &stmt->rbind.cBinders[ndx];
        if( bv->is_null || (bv->type==CPDO_TYPE_NULL) )
        {
            *val = 0.0;
            return 0;
        }
        switch( bv->type )
        {
          case CPDO_TYPE_INT8:
          case CPDO_TYPE_INT16:
          case CPDO_TYPE_INT32:
          case CPDO_TYPE_INT64: {
              int64_t i64 = 0;
              int rc = cpdo_my5_stmt_get_int_types( stmt, ndx, &i64 );
              if( rc ) return rc;
              *val = (double)i64;
              break;
          }
          case CPDO_TYPE_FLOAT:
              *val = bv->valu.flt;
              break;
          case CPDO_TYPE_DOUBLE:
              *val = bv->valu.dbl;
              break;
          case CPDO_TYPE_NULL:
              *val = 0.0;
              break;
          default:
              return cpdo_rc.TypeError;
        }
        return 0;
    }
}

static int cpdo_my5_stmt_get_float_ndx( cpdo_stmt * self, uint16_t ndx, float * val )
{
    double d = 0.0;
    int rc = cpdo_my5_stmt_get_double_ndx( self, ndx, &d );
    if( (0 == rc) && val ) *val = (float)d;
    return rc;
}
#if !CPDO_MY5_HAS_PRINT64
typedef struct {
    char * str;
    long maxLen;
    long pos;
} My5StringAppender;

static long cpdo_my5_appender_string( void * arg, char const * data, long n )
{
    long rc = -1;
    My5StringAppender * my = (My5StringAppender*) arg;
    if( ! arg || ((my->pos+n) > my->maxLen) || (n<0) ) return rc;
    for( rc = 0; rc < n; ++data, ++rc )
    {
        my->str[my->pos++] = *data;
    }
    return rc;
}
#endif /*!CPDO_MY5_HAS_PRINT64*/

static int cpdo_my5_stmt_get_string_ndx( cpdo_stmt * self, uint16_t ndx, char const ** val, uint32_t * len )
{
    STMT_DECL(cpdo_rc.ArgError);
    if( ! val ) return cpdo_rc.ArgError;
    else if( ndx >= stmt->rbind.count ) return cpdo_rc.RangeError;
    else
    {
        enum { NumBufSize = 64 };
        int rc;
        cpdo_bind_val * scratch = NULL;
        cpdo_bind_val * bv = &stmt->rbind.cBinders[ndx];
        if( bv->is_null || (bv->type==CPDO_TYPE_NULL) )
        {
            *val = NULL;
            if( len ) *len = 0;
            return 0;
        }
        else if( bv->type == CPDO_TYPE_CUSTOM )
        {
            enum { BufSize = 20 /* for time/date-to-string (timestamp sz=19)*/ };
            MYSQL_BIND * bin = &stmt->rbind.myBinders[ndx];
            if(! cpdo_bind_val_tag_type_check_origin(&cpdo_my5_driver_api,
                                             bv->valu.custom.type_tag ))
            {
                return cpdo_rc.TypeError;
            }
            switch( bin->buffer_type )
            {
              case MYSQL_TYPE_DATE:
              case MYSQL_TYPE_TIME:
              case MYSQL_TYPE_DATETIME:
              case MYSQL_TYPE_TIMESTAMP: {
                  MYSQL_TIME * tm;
                  scratch = &stmt->rbind.convBuf[ndx];
                  if( CPDO_TYPE_STRING == scratch->type )
                  {/* already done the conversion, so re-use it.. */
                      *val = (char const *)scratch->valu.blob.mem;
                      if(len) *len = scratch->valu.blob.length;
                      return 0;
                  }
                  rc = cpdo_bind_val_string( scratch, NULL, BufSize );
                  if( rc ) return rc;
                  tm = (MYSQL_TIME*)bv->valu.custom.mem;
                  assert( tm );
                  if( ! tm ) return cpdo_rc.InternalError;
                  if( MYSQL_TYPE_DATE == bin->buffer_type )
                  {
                      sprintf( (char *)scratch->valu.blob.mem,
                               "%04d-%02d-%02d",
                               tm->year, tm->month, tm->day);
                  }
                  else if( MYSQL_TYPE_TIME == bin->buffer_type )
                  {
                      sprintf( (char *)scratch->valu.blob.mem,
                               "%02d:%02d:%02d",
                               tm->hour, tm->minute, tm->second);
                  }
                  else
                  {
                      assert( (MYSQL_TYPE_TIMESTAMP == bin->buffer_type)
                            || (MYSQL_TYPE_DATETIME == bin->buffer_type)
                            );
                      sprintf( (char *)scratch->valu.blob.mem,
                               "%04d-%02d-%02d %02d:%02d:%02d",
                               tm->year, tm->month, tm->day,
                               tm->hour, tm->minute, tm->second);
                  }
                  scratch->valu.blob.length = strlen( (char *)scratch->valu.blob.mem );
                  *val = (char const *)scratch->valu.blob.mem;
                  if(len) *len = scratch->valu.blob.length;
                  return 0;                  
              }
              default:
                  break;
            }
            return cpdo_rc.TypeError;
        }
        else if( CPDO_TYPE_STRING == bv->type )
        { /* shortcut - no need to convert this */
            *val = (char const *)bv->valu.blob.mem;
            if( len )
            {
                *len = bv->valu.blob.length;
            }
            return 0;
        }
#if 0
        else if( CPDO_TYPE_BLOB == bv->type )
        { /* Arguable: optimistically assume blob is a legal string */
            *val = (char const *)bv->valu.blob.mem;
            if( len )
            {
                *len = bv->valu.blob.length;
            }
            return 0;
        }
#endif
        else
        { /* convert numbers to strings... */
            cpdo_bind_val * scratch = &stmt->rbind.convBuf[ndx];
            int sprc;
            char buf[NumBufSize];
            if( CPDO_TYPE_STRING == scratch->type )
            {/* already done the conversion, so re-use it.. */
                *val = (char const *)scratch->valu.blob.mem;
                if(len) *len = scratch->valu.blob.length;
                return 0;
            }
            switch( bv->type )
            {
              case CPDO_TYPE_INT8:
                  sprc = sprintf( buf, "%"PRIi8, bv->valu.i8 );
                  break;
              case CPDO_TYPE_INT16:
                  sprc = sprintf( buf, "%"PRIi16, bv->valu.i16 );
                  break;
              case CPDO_TYPE_INT32:
                  sprc = sprintf( buf, "%"PRIi32, bv->valu.i32 );
                  break;
              case CPDO_TYPE_INT64:
#if CPDO_MY5_HAS_PRINT64

             sprc = sprintf( buf, "%"PRIi64, bv->valu.i64 );
#else
              /*
              We  use cpdo_printf() to implement this on 32-bit platforms
              because the PRIi64 specifier can map to a value which is not
              specified in C89.
              */
                {
                    enum { I64BufLen = 40 };
                    char buf[I64BufLen];
                    My5StringAppender myStr;
                    myStr.str = buf;
                    myStr.maxLen = I64BufLen;
                    myStr.pos = 0;
                    sprc = cpdo_printf( cpdo_my5_appender_string, &myStr, "%"PRIi64, bv->valu.i64 );
                }
#endif
                break;
              case CPDO_TYPE_DOUBLE:
                  sprc = sprintf( buf, "%f", bv->valu.dbl );
                  break;
              case CPDO_TYPE_FLOAT:
                  sprc = sprintf( buf, "%f", bv->valu.flt );
                  break;
              default:
                  MARKER("WARNING: UNHANDLED MYSQL_TYPE_XXX #%d IN RESULT DATA\n",
                         stmt->rbind.myBinders[ndx].buffer_type);
                  return cpdo_rc.TypeError;
            };
            if(sprc>0)
            { /* Strip trailing zeroes before passing it on... */
                unsigned int urc = (unsigned int)sprc;
                char * pos = buf + urc - 1;
                for( ; ('0' == *pos) && urc && (*(pos-1) != '.')&& (*(pos-1) != ',');
                     --pos, --urc )
                {
                    *pos = 0;
                }
                assert(urc && *pos);
            }
            rc = cpdo_bind_val_string( scratch, buf, strlen(buf) );
            if( rc ) return rc;
            *val = (char const *)scratch->valu.blob.mem;
            if( len ) *len = scratch->valu.blob.length;
            return 0;
        }
    }
}

static int cpdo_my5_stmt_get_blob_ndx( cpdo_stmt * self, uint16_t ndx, void const ** val, uint32_t * len )
{
    STMT_DECL(cpdo_rc.ArgError);
    if( ! val ) return cpdo_rc.ArgError;
    else if( ndx >= stmt->rbind.count ) return cpdo_rc.RangeError;
    else
    {
        /*MYSQL_BIND * bin = &stmt->rbind.myBinders[ndx];*/
        cpdo_bind_val * bv = &stmt->rbind.cBinders[ndx];
        if( bv->is_null || !bv->valu.blob.length )
        {
            *val = NULL;
            if(len) *len = 0;
            return 0;
        }
        switch( bv->type )
        {
          case CPDO_TYPE_BLOB:
              *val = (char const *)bv->valu.blob.mem;
              if(len) *len = bv->valu.blob.length;
              break;
          case CPDO_TYPE_NULL:
              *val = 0;
              if(len) *len = 0;
              break;
          default:
              return cpdo_rc.TypeError;
        }
        return 0;
    }
}

static int cpdo_my5_stmt_error_info( cpdo_stmt * self, char const ** dest, uint32_t * len, int * errorCode )
{
    STMT_DECL(cpdo_rc.ArgError);
    else
    {
        if( errorCode ) *errorCode = mysql_stmt_errno( stmt->stmt );
        if( dest )
        {
            *dest = mysql_stmt_error( stmt->stmt );
            if( len )
            {
                *len = *dest ? strlen(*dest) : 0;
            }
        }
        return 0;
    }
}

static int cpdo_my5_stmt_finalize( cpdo_stmt * self )
{
    STMT_DECL(cpdo_rc.ArgError);
    if(MEGADEBUG)
    {
        MARKER("Finalizing statement @%p\n", (void const *)self);
    }
    return cpdo_my5_stmt_free(stmt);
}

static cpdo_driver_details const * cpdo_my5_driver_details()
{
    static const cpdo_driver_details bob = {
    CPDO_DRIVER_NAME/*driver_name*/,
    "20110202"/*driver_version*/,
    "Same as your MySQL"/*license*/,
    "http://fossil.wanderinghorse.net/repos/cpdo/" /*url*/,
    "Stephan Beal (http://wanderinghorse.net)" /*authors*/
    };
    return &bob;
}

int cpdo_driver_mysql5_register()
{
    return cpdo_driver_register( CPDO_DRIVER_NAME, cpdo_my5_driver_new );
}


#if defined(__cplusplus)
} /*extern "C"*/
#endif

#undef DRV_DECL
#undef STMT_DECL
#undef PBIND_DECL
#undef MARKER
#undef CPDO_DRIVER_NAME
#undef CPDO_MY5_HAS_PRINT64
#undef MEGADEBUG
#undef RESET_DRV_ERR
#endif /*CPDO_ENABLE_MYSQL5*/
/* end of file cpdo_amalgamation.c */
/* start of file cpdopp.cpp */
#include <cassert>
#include <cstring>
#include <sstream>

/** @def CPDO_CPP_ENABLE_SAFETY_NET
    
    Set CPDO_CPP_ENABLE_SAFETY_NET to non-0 to enable some extra
    "is alive" checks. These are not needed for normal C++ use,
    i expect, but the intention is to support an eventual binding
    to JavaScript using Google's libv8.
*/
#if ! defined(CPDO_CPP_ENABLE_SAFETY_NET)
#define CPDO_CPP_ENABLE_SAFETY_NET 1
#endif
#define CPDO_STMT_CHECK_ALIVE if(CPDO_CPP_ENABLE_SAFETY_NET) this->assert_alive()


namespace cpdo {
    exception::exception( cpdo_driver * drv )
        : code(0), is_db_err(true), msg()
    {
        char const * str = NULL;
        if( drv )
        {
            drv->api->error_info( drv, &str, NULL, &this->code );
            this->msg = str ? str : "Unknown error.";
            drv->api->close(drv);
        }
        else
        {
            msg = "Cannot extract error info from a NULL cpdo_driver.";
            code = cpdo_rc.ArgError;
            is_db_err = false;
        }
        
    }

    exception::exception( int code )
                : code(code),
                is_db_err(false),
                msg()
    {
        std::ostringstream os;
        os << "cpdo_rc error code #"<<code<<" ("<<cpdo_rc_string(code)
            <<").";
        this->msg = os.str();
    }
    
    statement::statement( cpdo_stmt * st )
        : st(st)
    {
        assert( NULL != st );
    }

    statement::~statement() throw()
    {
        this->finalize();
    }

    void statement::finalize() throw()
    {
        if( this->st )
        {
            this->st->api->finalize(st);
            this->st = NULL;
        }
    }

    void statement::check_code( int code )
    {
        if( cpdo_rc.AllocError == code )
        {
            throw std::bad_alloc();
        }
        else if( cpdo_rc.CheckDbError == code )
        {
            char const * msg = NULL;
            int dbc = 0;
            this->st->api->error_info( st, &msg, NULL, &dbc );
            throw exception( dbc ? dbc : cpdo_rc.UnknownError,
                             (0 != dbc),
                             msg ? msg : "Unknown error" );
        }
        else if( code )
        {
            throw exception( code );
        }
    }

    bool statement::step()
    {
        CPDO_STMT_CHECK_ALIVE;
        switch(st->api->step(st))
        {
            case CPDO_STEP_OK: return true;
            case CPDO_STEP_DONE: return false;
            default:
                this->check_code( cpdo_rc.CheckDbError )/*will throw*/;
                return false /* won't be reached. */;
        }
    }

    void statement::assert_index( uint16_t ndx, unsigned char base )
    {
        if( 1 == base )
        {
            if(!ndx || (ndx > this->param_count()))
            {
                throw exception( cpdo_rc.RangeError, false,
                                "Bound parameter index out of range.");
            }
        }
        else
        {
            if(ndx >= this->col_count())
            {
                throw exception( cpdo_rc.RangeError, false,
                                 "Column index out of range.");
            }
        }
    }
    
    void statement::assert_alive() const
    {
        if( ! this->st )
        {
            throw exception( cpdo_rc.UsageError, 0,
                            "Mis-use: database statement handle has already been freed.");
        }
    }

    
    int statement::error_code()
    {
        CPDO_STMT_CHECK_ALIVE;
        int rc = 0;
        st->api->error_info( st, NULL, NULL, &rc );
        return rc;
    }

    std::string statement::error_text()
    {
        CPDO_STMT_CHECK_ALIVE;
        char const * s = NULL;
        st->api->error_info( st, &s, NULL, NULL );
        return s ? s : "";
    }

    uint16_t statement::param_count()
    {
        CPDO_STMT_CHECK_ALIVE;
        return st->api->bind.param_count(st);
    }

    uint16_t statement::param_index( char const * name )
    {
        CPDO_STMT_CHECK_ALIVE;
        return st->api->bind.param_index(st, name);
    }

    char const * statement::param_name( uint16_t ndx )
    {
        CPDO_STMT_CHECK_ALIVE;
        assert_index(ndx, 1);
        return st->api->bind.param_name(st, ndx);
    }
    
    void statement::bind( uint16_t ndx )
    {
        CPDO_STMT_CHECK_ALIVE;
        this->check_code( st->api->bind.null(st, ndx) );        
    }
    
    void statement::bind( uint16_t ndx, int8_t v )
    {
        CPDO_STMT_CHECK_ALIVE;
        this->check_code( st->api->bind.i8(st, ndx, v) );        
    }

    void statement::bind( uint16_t ndx, int16_t v )
    {
        CPDO_STMT_CHECK_ALIVE;
        this->check_code( st->api->bind.i16(st, ndx, v) );        
    }

    void statement::bind( uint16_t ndx, int32_t v )
    {
        CPDO_STMT_CHECK_ALIVE;
        this->check_code( st->api->bind.i32(st, ndx, v) );        
    }

    void statement::bind( uint16_t ndx, int64_t v )
    {
        CPDO_STMT_CHECK_ALIVE;
        this->check_code( st->api->bind.i64(st, ndx, v) );        
    }

    void statement::bind( uint16_t ndx, float v )
    {
        CPDO_STMT_CHECK_ALIVE;
        this->check_code( st->api->bind.flt( st, ndx, v) );        
    }

    void statement::bind( uint16_t ndx, double v )
    {
        CPDO_STMT_CHECK_ALIVE;
        this->check_code( st->api->bind.dbl(st, ndx, v) );        
    }

    void statement::bind( uint16_t ndx, char const * v, uint32_t len )
    {
        CPDO_STMT_CHECK_ALIVE;
        this->check_code( st->api->bind.string(st, ndx, v, len) );        
    }

    void statement::bind( uint16_t ndx, std::string const & v )
    {
        this->bind( ndx, v.c_str(), static_cast<uint32_t>(v.size()) );
    }

    void statement::bind( uint16_t ndx, void const * v, uint32_t len )
    {
        CPDO_STMT_CHECK_ALIVE;
        this->check_code( st->api->bind.blob(st, ndx, v, len) );        
    }

    void statement::reset()
    {
        CPDO_STMT_CHECK_ALIVE;
        this->check_code( st->api->bind.reset(st) );
    }

    uint16_t statement::col_count()
    {
        CPDO_STMT_CHECK_ALIVE;
        return st->api->get.column_count(st);
    }

    char const * statement::col_name( uint16_t ndx )
    {
        CPDO_STMT_CHECK_ALIVE;
        this->assert_index( ndx, 0 );
        return st->api->get.column_name(st,ndx);
    }

    cpdo_data_type statement::col_type( uint16_t ndx )
    {
        CPDO_STMT_CHECK_ALIVE;
        cpdo_data_type t = CPDO_TYPE_ERROR;
        this->check_code( st->api->get.type(st,ndx, &t) );
        return t;
    }
    int8_t statement::get_int8( uint16_t ndx )
    {
        CPDO_STMT_CHECK_ALIVE;
        int8_t rc = 0;
        this->check_code( st->api->get.i8( st, ndx, &rc) );
        return rc;
    }
    int16_t statement::get_int16( uint16_t ndx )
    {
        CPDO_STMT_CHECK_ALIVE;
        int16_t rc = 0;
        this->check_code( st->api->get.i16( st, ndx, &rc) );
        return rc;
    }
    int32_t statement::get_int32( uint16_t ndx )
    {
        CPDO_STMT_CHECK_ALIVE;
        int32_t rc = 0;
        this->check_code( st->api->get.i32( st, ndx, &rc) );
        return rc;
    }
    int64_t statement::get_int64( uint16_t ndx )
    {
        CPDO_STMT_CHECK_ALIVE;
        int64_t rc = 0;
        this->check_code( st->api->get.i64( st, ndx, &rc) );
        return rc;
    }
    float statement::get_float( uint16_t ndx )
    {
        CPDO_STMT_CHECK_ALIVE;
        float rc = 0.0;
        this->check_code( st->api->get.flt( st, ndx, &rc) );
        return rc;
    }
    double statement::get_double( uint16_t ndx )
    {
        CPDO_STMT_CHECK_ALIVE;
        double rc = 0.0;
        this->check_code( st->api->get.dbl( st, ndx, &rc) );
        return rc;
    }

    char const * statement::get_string( uint16_t ndx, uint32_t * size )
    {
        CPDO_STMT_CHECK_ALIVE;
        char const * rc = NULL;
        this->check_code( st->api->get.string(st, ndx, &rc, size) );
        return rc;
    }
    
    void const * statement::get_blob( uint16_t ndx, uint32_t * size )
    {
        CPDO_STMT_CHECK_ALIVE;
        void const * rc = NULL;
        this->check_code( st->api->get.blob(st, ndx, &rc, size) );
        return rc;
    }
    
    cpdo_stmt * statement::handle()
    {
        return this->st;
    }

    stmt::stmt(statement * st)
        :st(st)
    {
    }
    
    stmt::stmt()
        : st(NULL)
    {}
    
    stmt::~stmt()
    {
        this->finalize();
    }
    
    stmt & stmt::operator=(statement * st)
    {
        if( this->st != st )
        {
            this->finalize();
            this->st = st;
        }
        return *this;
    }

    void stmt::finalize()
    {
        if(this->st) delete this->st;
        this->st = NULL;
    }
    
    statement * stmt::operator->()
    {
        return this->st;
    }

    bool stmt::empty() const
    {
        return NULL == this->st;
    }

    statement * stmt::take()
    {
        statement * rc = this->st;
        this->st = NULL;
        return rc;
    }

    driver::~driver() throw()
    {
        this->close();
    }

    void driver::close() throw()
    {
        if( this->drv )
        {
            this->drv->api->close( this->drv );
            this->drv = NULL;
        }
    }

    driver::driver( std::string const & dsn,
                    std::string const & user,
                    std::string const & pass )
        : drv(NULL)
    {
        cpdo_driver * d = NULL;
        int rc = cpdo_driver_new_connect(&d, dsn.c_str(), user.c_str(), pass.c_str());
        if( rc ) {
           if( d ) { // means driver was loaded but connect failed
               throw exception( d ) /* transfers ownership of d */;
           }
           else {
               throw exception( cpdo_rc.UnsupportedError, 0,
                                "Could not load cpdo_driver!");
           }
       }
       this->drv = d;
    }

    driver::driver( cpdo_driver * d )
        : drv(NULL)
    {
        if( ! d || !d->api->is_connected(d) )
        {
            if( d ) d->api->close(d);
            throw exception( cpdo_rc.ArgError, 0,
                            "cpdo_driver is not connected!");
        }
        this->drv = d;
    }
    void driver::assert_connected() const
    {
        if( ! this->drv )
        {
            throw exception( cpdo_rc.UsageError, 0,
                            "Mis-use: database access driver has already been freed.");
        }
    }
    void driver::check_code( int code )
    {
        if( cpdo_rc.AllocError == code )
        {
            throw std::bad_alloc();
        }
        else if( cpdo_rc.CheckDbError == code )
        {
            char const * msg = NULL;
            int dbc = 0;
            this->drv->api->error_info( this->drv, &msg, NULL, &dbc );
            throw exception( dbc ? dbc : cpdo_rc.UnknownError,
                             (0 != dbc),
                             msg ? msg : "Unknown error" );
        }
        else if( code )
        {
            throw exception( code );
        }
    }

    statement * driver::prepare( char const * sql, uint32_t len )
    {
        if( ! sql || !*sql || !len ) throw exception( cpdo_rc.RangeError );
        this->assert_connected();
        cpdo_stmt * st = NULL;
        this->check_code( this->drv->api->prepare( this->drv, &st, sql, len ) );
        try
        {
            statement * rs = new statement(st);
            return rs;
        }
        catch(...)
        {
            st->api->finalize(st);
            throw;
        }
    }
    statement * driver::prepare_f( char const * fmt, ... )
    {
        this->assert_connected();
        va_list vargs;
        va_start(vargs,fmt);
        cpdo_stmt * st = NULL;
        int const rc = cpdo_prepare_f_v( this->drv, &st, fmt, vargs );
        va_end(vargs);
        this->check_code( rc );
        try
        {
            statement * rs = new statement(st);
            return rs;
        }
        catch(...)
        {
            st->api->finalize(st);
            throw;
        }
    }
    statement * driver::prepare( char const * sql )
    {
        return this->prepare( sql, sql ? std::strlen(sql) : 0 );
    }
    statement * driver::prepare( std::string const & sql )
    {
        return this->prepare( sql.c_str(), static_cast<uint32_t>(sql.size()) );
    }

    std::string driver::quote( std::string const & part )
    {
        this->assert_connected();
        char * dest = NULL;
        uint32_t slen = static_cast<uint32_t>(part.size());
        this->check_code( this->drv->api->quote( this->drv,
                            part.c_str(), &slen, &dest) );
        std::string const & rs( dest ? dest : "" );
        this->drv->api->free_string(this->drv, dest);
        return rs;
    }
    int driver::error_code()
    {
        this->assert_connected();
        int rc = 0;
        this->drv->api->error_info( this->drv, NULL, NULL, &rc );
        return rc;
    }

    std::string driver::error_text()
    {
        this->assert_connected();
        char const * str = NULL;
        this->drv->api->error_info( this->drv, &str, NULL, NULL );
        return str ? str : "";
    }

    uint64_t driver::last_insert_id( char const * hint )
    {
        this->assert_connected();
        uint64_t rc = 0;
        this->check_code( this->drv->api->last_insert_id( this->drv, &rc, hint ) );
        return rc;
    }
    void driver::begin()
    {
        this->assert_connected();
        this->check_code( this->drv->api->transaction.begin( this->drv ) );
    }
    void driver::commit()
    {
        this->assert_connected();
        this->check_code( this->drv->api->transaction.commit( this->drv ) );
    }

    void driver::rollback()
    {
        this->assert_connected();
        this->check_code( this->drv->api->transaction.rollback( this->drv ) );
    }
    
    bool driver::in_transaction()
    {
        this->assert_connected();
        return this->drv->api->transaction.is_in( this->drv ) ? true : false;
    }

    char const * driver::driver_name() const
    {
        this->assert_connected();
        return this->drv->api->constants.driver_name;
    }

    char driver::table_quote_char() const
    {
        this->assert_connected();
        return this->drv->api->constants.table_quote;
    }

    char driver::string_quote_char()
    {
        this->assert_connected();
        char ch = 0;
        int const rc = this->drv->api->opt.get_string_quote_char(this->drv, &ch);
        this->check_code( rc );
        return ch;
    }

    cpdo_driver * driver::handle()
    {
        return this->drv;
    }

    void driver::exec( char const * sql, uint32_t len )
    {
        this->assert_connected();
        this->check_code( cpdo_exec( this->drv, sql, len ) );
    }
    
    void driver::exec( std::string const & sql )
    {
        return this->exec( sql.c_str(),
                            static_cast<uint32_t>(sql.size()) );
    }
    
    void driver::exec_f( char const * fmt, ... )
    {
        this->assert_connected();
        va_list vargs;
        va_start(vargs,fmt);
        int const rc = cpdo_exec_f_v( this->drv, fmt, vargs );
        va_end(vargs);
        this->check_code( rc );
    }
} // namespace
#undef CPDO_STMT_CHECK_ALIVE
/* end of file cpdopp.cpp */
