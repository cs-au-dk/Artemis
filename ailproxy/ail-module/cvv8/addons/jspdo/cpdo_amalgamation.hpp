/* start of file cpdo_amalgamation.h */
#if !defined(CPDO_AMALGAMATION_BUILD)
#  define CPDO_AMALGAMATION_BUILD 1
#endif
#if !defined(CPDO_ENABLE_SQLITE3)
#  define CPDO_ENABLE_SQLITE3 0
#endif
#if !defined(CPDO_ENABLE_MYSQL5)
#  define CPDO_ENABLE_MYSQL5 0
#endif
/* start of file cpdo_printf.h */
#ifndef WANDERINGHORSE_NET_CPDO_PRINTF_H_INCLUDED
#define WANDERINGHORSE_NET_CPDO_PRINTF_H_INCLUDED 1
#include <stdarg.h>
#include <stdio.h> /* FILE handle */
#ifdef __cplusplus
extern "C" {
#endif
/** @page cpdo_printf_page_main cpdo_printf printf-like API

   This API contains a printf-like implementation which supports
   aribtrary data destinations.

   Authors: many, probably. This code supposedly goes back to the
   early 1980's.

   Current maintainer: Stephan Beal (http://wanderinghorse.net/home/stephan)

   License: Public Domain.

   The primary functions of interest are cpdo_printfv() and cpdo_printf(), which works
   similarly to printf() except that they take a callback function which they
   use to send the generated output to arbitrary destinations. e.g. one can
   supply a callback to output formatted text to a UI widget or a C++ stream
   object.
*/

/**
   @typedef long (*cpdo_printf_appender)( void * arg, char const * data, long n )


   The cpdo_printf_appender typedef is used to provide cpdo_printfv()
   with a flexible output routine, so that it can be easily
   send its output to arbitrary targets.

   The policies which implementations need to follow are:

   - arg is an implementation-specific pointer (may be 0) which is
   passed to vappendf. cpdo_printfv() doesn't know what this argument is
   but passes it to its cpdo_printf_appender. Typically it will be an
   object or resource handle to which string data is pushed or output.

   - The 'data' parameter is the data to append. If it contains
   embedded nulls, this function will stop at the first one. Thus
   it is not binary-safe.

   - n is the number of bytes to read from data. If n<0 then
   strlen(data) should be used.

   - Returns, on success, the number of bytes appended (may be 0).

   - Returns, on error, an implementation-specified negative number.
   Returning a negative error code will cause cpdo_printfv() to stop the
   processing of that string. Note that 0 is a success value (some
   printf format specifiers do not add anything to the output).
*/
typedef long (*cpdo_printf_appender)( void * arg,
				   char const * data,
				   long n );


/**
  This function works similarly to classical printf implementations,
  but instead of outputing somewhere specific, it uses a callback
  function to push its output somewhere. This allows it to be used for
  arbitrary external representations. It can be used, for example, to
  output to an external string, a UI widget, or file handle (it can
  also emulate printf by outputing to stdout this way).

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
 function "func", or a negative number on a pre-output error. If this
 function returns an integer greater than 1 it is in general
 impossible to know if all of the elements were output. As such
 failure can only happen if the callback function returns an error,
 and this type of error is very rare in a printf-like context, this is
 not considered to be a significant problem. (The same is true for any
 classical printf implementations, as far as i'm aware.)


 CURRENT (documented) PRINTF EXTENSIONS:

 %%z works like %%s, but takes a non-const (char *) and vappendf
 deletes the string (using free()) after appending it to the output.

 %%h (HTML) works like %s but converts certain characters (like '<' and '&' to
 their HTML escaped equivalents.

 %%t (URL encode) works like %%s but converts certain characters into a representation
 suitable for use in an HTTP URL. (e.g. ' ' gets converted to %%20)

 %%T (URL decode) does the opposite of %t - it decodes URL-encoded
 strings.

 %%r requires an int and renders it in "ordinal form". That is,
 the number 1 converts to "1st" and 398 converts to "398th".

 %%q quotes a string as required for SQL. That is, '\'' characters get
 doubled.

 %%Q as %%q, but includes the outer '\'' characters and null pointers
 replaced by SQL NULL.

 (The %%q and %%Q specifiers are options inherited from this printf
 implementation's sqlite3 genes.)

 These extensions may be disabled by setting certain macros when
 compiling vappendf.c (see that file for details).
*/
long cpdo_printfv(
  cpdo_printf_appender pfAppend,          /* Accumulate results here */
  void * pfAppendArg,                /* Passed as first arg to pfAppend. */
  const char *fmt,                   /* Format string */
  va_list ap                         /* arguments */
  );

/**
   Identical to cpdo_printfv() but takes a (...) ellipses list instead of a
   va_list.
*/
long cpdo_printf(cpdo_printf_appender pfAppend,
	     void * pfAppendArg,
	     const char *fmt,
	     ... );

/**
   Emulates fprintf() using cpdo_printfv().
*/
long cpdo_printf_file( FILE * fp, char const * fmt, ... );


/**
   Works like cpdo_printfv(), but appends all output to a
   dynamically-allocated string, expanding the string as necessary to
   collect all formatted data. The returned null-terminated string is
   owned by the caller and it must be cleaned up using free(). If !fmt
   or if the expanded string evaluates to empty, null is returned, not
   a 0-byte string.
*/
char * cpdo_printfv_str( char const * fmt, va_list vargs );

/**
   Equivalent to cpdo_printfv_str(), but takes elipsis arguments instead
   of a va_list.
*/
char * cpdo_printf_str( char const * fmt, ... );

#ifdef __cplusplus
} /* extern "C" */
#endif
#endif /* WANDERINGHORSE_NET_CPDO_PRINTF_H_INCLUDED */
/* end of file cpdo_printf.h */
/* start of file include/wh/cpdo/cpdo.h */
#if !defined(WANDERINGHORSE_NET_CPDO_H_INCLUDED)
#define WANDERINGHORSE_NET_CPDO_H_INCLUDED

/** @file cpdo.h

This file contains the public API for the "cpdo" library, a database
access abstraction API written in C and modelled heavily off of PHP's
PDO API (see http://php.net/manual/en/book.pdo.php).

Author: Stephan Beal (http://www.wanderinghorse.net/home/stephan/)

License: Dual Public Domain/MIT. The full license text is at the
bottom of the main header file (cpdo.h).

Requirements:

- C99, but only for the fixed-size integer defined in stdint.h.  The
rest of the code "should" work fine in C89 mode. In theory it should
work fine in C89 mode when including the C99-specified stdint.h, but
the portability of that approach is questionable.

- A db back-end for which we have a driver, including the required
headers and libraries needed for using that back-end.


Current code status:

- The public API is more or less complete. There will be some
additions to the cpdo_driver_api. e.g. for working with bound
parameters by name. Some utility (non-member) functions are probably
missing, but those will be added as the need for them is found.

- The sqlite3 driver implementation seems to work as documented for
the cpdo abstraction interface.

- Consider whether we want to support get-db-name and get-table-name
operations.

Design notes:

There are basically two ways to fire off SQL queries to a server:

- Send "plain SQL". This is the most common approach, and the easiest
for most purposes.

- Use "prepared statements."

This library is built upon the guiding principal of always using
prepared statements, and implements "plain queries" internally
on top of prepared statements.

*/

/** @page page_cpdo_main cpdo

This is the documentation for the cpdo library. The API
is completely documented in \ref cpdo.h.


*/

#include <stdint.h> /* fixed-size integers */
#include <stddef.h> /* NULL! */
#include <stdarg.h> /* va_list */

/** @def CPDO_VERSION_NUMBER

CPDO_VERSION_NUMBER contains the version
number of cpdo, encoded in the form
YYYYMMDD of the most recent changes,
in decimal format. e.g. the number
20110209 represents February 9th, 2011.
*/
#define CPDO_VERSION_NUMBER 20110209
/** @def CPDO_VERSION_STRING

CPDO_VERSION_STRING contains the string form
of CPDO_VERSION_NUMBER
*/
#define CPDO_VERSION_STRING "20110209"


/** @def CPDO_ENABLE_64_BIT

    Some internal code works either on 32-bit or 64-bit, but
    not both (well, not portably). We try to detect 64-bit
    with this macro, but if you get errors about "pointer being
    cast to integer of different size" while building cpdo
    then try defining this before including this file (e.g. from
    the compiler command line or in your impl file before you
    include this).
    
    In 64-bit mode, some internal masking operations may
    work differently. In 32-bit mode support for int64_t might
    be limited or unavailable in some contexts.
*/
#if !defined(CPDO_ENABLE_64_BIT)
/* Largely taken from http://predef.sourceforge.net/prearch.html

See also: http://poshlib.hookatooka.com/poshlib/trac.cgi/browser/posh.h
*/
#  if defined(_WIN64) || defined(__LP64__/*gcc*/) \
    || defined(_M_X64) || defined(__amd64__) || defined(__amd64) \
    ||  defined(__x86_64__) || defined(__x86_64) \
    || defined(__ia64__) || defined(__ia64) || defined(_IA64) || defined(__IA64__) \
    || defined(_M_IA64) \
    || defined(__sparc_v9__) || defined(__sparcv9) || defined(_ADDR64) \
    || defined(__64BIT__)
#    define CPDO_ENABLE_64_BIT 1
#  else
#    define CPDO_ENABLE_64_BIT 0
#  endif
#endif


#if defined(__cplusplus)
extern "C" {
#endif

    /** @var cpdo_rc

    This object defines the error codes used by cpdo.

    Library routines which return int values almost always return a
    value from this structure. None of the members in this struct have
    published values except for the OK member, which has the value 0.
    All other values might be incidentally defined where clients
    can see them, but the numbers might change from release to
    release, so clients must only use the symbolic names.

    Client code is expected to access these values via the shared
    cpdo_rc object, and use them as demonstrated here:

    @code
    int rc = cpdo_some_func(...);
    if( 0 == rc ) {...success...}
    else if( cpdo_rc.ArgError == rc ) { ... some argument was wrong ... }
    else if( cpdo_rc.AllocError == rc ) { ... allocation error ... }
    ...
    @endcode
   
    */

    /** @struct cpdo_rc_
        See \ref cpdo_rc for details.
    */
    static const struct cpdo_rc_
    {
        /** The generic success value. Guaranteed to be 0. */
        const int OK;
        /** Signifies an error in one or more arguments (e.g. NULL where it is not allowed). */
        const int ArgError;
        /** Signifies that some argument is not in a valid range. */
        const int RangeError;
        /** Signifies that some argument is not of the correct logical type. */
        const int TypeError;
        /** Signifies an input/ouput error. */
        const int IOError;
        /** Signifies an out-of-memory error. */
        const int AllocError;
        /** Signifies that the called code is "NYI" (Not Yet Implemented). */
        const int NYIError;
        /** Signifies that an internal error was triggered. If it happens, please report this as a bug! */
        const int InternalError;
        /** Signifies that the called operation is not supported in the
            current environment. e.g.  missing support from 3rd-party or
            platform-specific code.
        */
        const int UnsupportedError;
        /**
           Signifies that the request resource could not be found.
        */
        const int NotFoundError;
        /**
           Signifies an unknown error, possibly because an underlying
           3rd-party API produced an error and we have no other reasonable
           error code to convert it to.
        */
        const int UnknownError;
        /**
           A generic connection-related error, e.g. trying to prepare an
           SQL statement when the driver is not connected to the database.
        */
        const int ConnectionError;
        /**
           Signifies that the caller should check the db-specific or
           statement-specific error code (depending on the context)
           for more details.
        */
        const int CheckDbError;
        /**
           Signifies that some form of access was denied. What exactly
           what denied depends on the function returning this value.
        */
        const int AccessError;
        
        /**
            Indicates some form of usage error _other_ than those
            represented by ArgError. An example is trying to use
            a db connection after it has been closed (but often such
            a case cannot be caught, and might lead to a crash).
        */
        const int UsageError;
    } cpdo_rc = {
    0/*OK*/,
    1/*ArgError*/,
    2/*RangeError*/,
    3/*TypeError*/,
    4/*IOError*/,
    5/*AllocError*/,
    6/*NYIError*/,
    7/*InternalError*/,
    8/*UnsupportedError*/,
    9/*NotFoundError*/,
    10/*UnknownError*/,
    11/*ConnectionError*/,
    12/*CheckDbError*/,
    13/*AccessError*/,
    14/*UsageError*/
    };

    /**
       Returns the string form of the cpdo_rc code corresponding to rc,
       or some unspecified, non-NULL string if it is an unknown code.
       The returned bytes are static, and live as long as the application is
       running.
    */
    char const * cpdo_rc_string(int rc);

    typedef struct cpdo_driver_api cpdo_driver_api;
    typedef struct cpdo_stmt_api cpdo_stmt_api;
    typedef struct cpdo_driver cpdo_driver;
    typedef struct cpdo_stmt cpdo_stmt;
    typedef struct cpdo_driver_opt cpdo_driver_opt;
    typedef struct cpdo_connect_opt cpdo_connect_opt;
    typedef struct cpdo_driver_details cpdo_driver_details;
#if 0
    typedef int64_t cpdo_int_t;
    typedef double cpdo_double_t;
#endif

    /**
       SQL type identifiers. Note that none of them has a value of 0,
       to avoid confusion with 0 as a success code returned from most
       of the cpdo API. Clients must not rely on any specific values
       for these members, and i might just randomly change the values
       to make sure code is behaving as it should.

       Though this type makes a distinction between 8-, 16-, 32-, and
       64-bit integers, drivers which do not support the full range
       are encouraged to "fudge it" a little, and try to do what would
       be intuitive (or least surprising) for the user.

       Notes regarding type conversions:

       - Implementations are expected to be able to convert, for
       field-fetching purposes, numeric types to other numeric
       types, even if it means a loss in precision. e.g. a user
       should be able to fetch a double-typed field into an
       int16_t value if he wishes.

       - Converting non-string data to a string is an optional
       feature, but drivers are encouraged to implement it if
       feasible.

       - Conversions from strings to numeric data is also an optional
       feature, but may require more effort on the part of the driver
       implementor.
    */
    enum cpdo_data_type {
    CPDO_TYPE_ERROR = -1,
    /** Represents SQL NULL. */
    CPDO_TYPE_NULL = 1,
    /** Represents 1-byte integers. */
    CPDO_TYPE_INT8,
    /** Represents 2-byte integers. */
    CPDO_TYPE_INT16,
    /** Represents 4-byte integers. */
    CPDO_TYPE_INT32,
    /** Represents 8-byte integers. */
    CPDO_TYPE_INT64,
    /** Represents single-precision floating point values. */
    CPDO_TYPE_FLOAT,
    /** Represents double-precision floating point values. */
    CPDO_TYPE_DOUBLE,
    /** Represents SQL CHAR and VARCHAR values. The library assumes
        an encoding of UTF8.
    */
    CPDO_TYPE_STRING,
    /**
       Represents SQL BLOB/CLOB data.
     */
    CPDO_TYPE_BLOB,
    /** For internal use by driver implementations, so that they
        can support driver-specific types with some transparency
        (e.g. MySQL's TIMESTAMP field handling uses this).
     */
    CPDO_TYPE_CUSTOM
    };
    /** Convenience typedef. */
    typedef enum cpdo_data_type cpdo_data_type;

    /**
       Return values for cpdo_stmt::step(). Note that no entry has the
       value 0. This is to avoid accidental confusion with the 0 success
       value returned by most functions in this API. Clients must not rely
       on these have any specific value, and i may change them just to
       make sure test code is behaving how it's supposed to.
    */
    enum cpdo_step_code {
    /**
       Means the next row in the result set was fetched successfully.
       Some non-fetchable queries might return this value, instead of
       CPDO_STEP_DONE, because it is not always possible to know if a
       driver-specific SQL construct wants to return results or not.  In
       such cases, trying to access the field data will not work (error
       codes, as opposed to crashes, unless the driver is poorly written).
    */
    CPDO_STEP_OK = 1,
    /**
       Means the end of a result set or non-fetchable statement, was
       reached without encountering an error. For fetchable results, the
       result set is not valid when this value is returned.  See the notes
       for CPDO_STEP_OK.
    */
    CPDO_STEP_DONE = 2,
    /**
       Signifies that an error occurred while fetching
       the next row of the result set. This is normally
       one of two things:

       - The client passed an invalid statement handle.

       - The statement is not fetchable or we have already fetched all the
       data. In that case, the cpdo_stmt::error_info() routine should give
       more information about the error (or it might not, depending on
       internal details of the driver).
    */
    CPDO_STEP_ERROR = 3
    };
    /** Convenience typedef. */
    typedef enum cpdo_step_code cpdo_step_code;

    /**
       A place for storing miscellaneous human-readable
       info about a driver.
    */
    struct cpdo_driver_details
    {
        /**
           The name used by DSNs for identifying this
           driver. e.g. "sqlite3" or "mysql5".
        */
        char const * driver_name;
        /**
           Version of the driver and optionally the version
           of the underlying database driver.
        */
        char const * driver_version;
        /**
           Brief description of the driver. e.g. "MySQL 5.x".
        */
        char const * description;
        /**
           License conditions of the driver. Ideally a URL
           to a well-known license, or simply its name
           (e.g. "GNU GPL version 2").
        */
        char const * license;
        /**
           Home page of the driver.
        */
        char const * url;
        /**
           Holds author names/email/URL/whatever.
           Entries should be separated by a newline.
        */
        char const * authors;
    };
    /** Empty-initialized cpdo_driver_details object. */
#define cpdo_driver_details_empty_m {           \
        "Unnamed"/*driver_name*/,                \
            "Unversioned"/*driver_version*/,     \
            "Undescribed"/*description*/,       \
            "Unknown"/*license*/,               \
            "Unknown"/*authors*/,               \
            "Unknown"/*url*/                    \
            }
    /** Empty-initialized cpdo_driver_details object. */
    extern const cpdo_driver_details cpdo_driver_details_empty;

    /**
       Holds connection-related options.

       TODO: how are we gonna get driver-specific options passed via this
       object? Still thinking about how to handle them.
    */
    struct cpdo_connect_opt
    {
        /**
           DSN for the connection.
        */
        char const * dsn;
        /**
           User name for the connection login.
         */
        char const * user_name;
        /**
           Password for the connection login.
         */
        char const * password;
    };
#define cpdo_connect_opt_empty_m {              \
        NULL/*dsn*/,                    \
            NULL/*user_name*/,                  \
            NULL/*password*/,                   \
            }
    extern const cpdo_connect_opt cpdo_connect_opt_empty;

    /**
       This type holds the "vtbl", or "virtual" operations, specified for
       the cpdo_driver interface. All instances of a specific driver type
       share a single instance of this class.
    */
    struct cpdo_driver_api
    {
        /**
           Returns human-readable details about the driver.

           Implementations are required to use an immutable/const instance
           of cpdo_driver_details so that we have no lifetime-related
           issues involving the string data in the returned object.
        */
        cpdo_driver_details const * (*driver_details)();

        /**
           Establishes the connection to the database. Whether or not the
           opt parameter is used, and which parts of it are used,
           are driver-dependent.

           Ownership of self is not changed by this call.

           Returns 0 on success, non-0 (probably cpdo_rc.CheckDbError) on
           error.

           Regardless of success or failure, this function must not
           be called more than once for the same connection object.
           Violating this may lead to resource leaks. Implementations
           are encourages to return an error code if they detect
           that connect() is being called a second time.

           Implementations "should" try to ensure that if connection
           fails, the client can use error_info() to get the
           error information. i.e. don't clean up the underlying
           connection object if this fails - wait until close()
           is called.

           Drivers which do not require login information must ignore
           the user/password info, as opposed to returning an error.

           Drivers may ignore DSN-specified options which they do not
           understand or they may treat them as an error. If they
           treat it as an error, the next call to
           self->api->error_info(self) MUST return the reason for the
           error (if it does not, the user will have no indication as
           to why the connection, using otherwise valid valid login
           info, failed).
        */
        int (*connect)( cpdo_driver * self, cpdo_connect_opt const * opt );

        /**
           str is the string to quote. *len must be its length.
   
           Allocates a new string with the contents of str, contained in
           single-quotes, and all single quotes in the string get
           doubled.

           If str is NULL then drivers must treat that as an SQL NULL value,
           assign *dest to the string "NULL" (without any quotes) and assign
           *len to 4.

           On success, 0 is returned and *dest is pointed to the new string,
           and *len is assigned to the length of the new string. The caller
           owns the string and must eventually free it using
           self->api->free_string(self, str).

           On error non-0 is returned (one of the cpdo_rc values) and *len and
           *dest are unmodified. The most likely error codes are cpdo_rc.ArgError
           (an invalid argument or combination of arguments) and cpdo_rc.AllocError
           (if the new string cannot be allocated).

           ACHTUNG: this is itended for use with individual SQL values,
           not whole SQL statements.
        */
        int (*quote)( cpdo_driver * self, char const * str, uint32_t * len, char ** dest );

        /**
           Frees a string allocated by quote(). Results are undefined
           if the string came from another source. It must return 0 on
           success. It must, like free(), gracefully ignore a NULL string
           value.
        */
        int (*free_string)( cpdo_driver * self, char * str);

        /**
           Must initialize a statement object for the given self from the
           first len bytes of the given sql, and populte *tgt object with
           the results.  Must return 0 on success, non-zero on error. On
           error, *tgt must not be modified.

           On success the caller must eventually clean up the result with
           result->api->finalize(result).

           Whether or not the given sql may be legally terminated with a
           semicolon is driver-dependent. For best results, do not include
           a semicolon (e.g. Oracle OCI says it's an invalid character).
           Most drivers, in my experience, do not care one way or the
           other.
        */
        int (*prepare)( cpdo_driver * self, cpdo_stmt ** tgt, char const * sql, uint32_t len );

        /**
           Must return the last error information associated with the
           connection.

           IFF the dest parameter is non null then it must point *dest at
           the error string and set *len (if it is not NULL) to the length
           the message.

           IFF errorCode is not null then it must assign *errorCode to the
           driver-dependent error code.

           Implementations must allow arbitrary combinations of NULL for
           the dest/len/errorCode parameters, to allow clients to specify
           exactly which information they're interested in.
       
           Returns 0 on success (meaning that it fetched the info from the
           underlying driver). On success *dest and/or *len and/or
           *errorCode may be set to 0 if the driver has no error to
           report. Some drivers may return other strings on error (sqlite3
           infamously uses "not an error" for this case).

           It is ASSUMED that the underlying driver owns the returned
           string, and this API allows the lifetime of the returned
           bytes to expire at the next call into the underlying driver
           (including this function!). Thus clients must copy it if
           needed.

           Implementations may invalidate/reset the error state for any
           operations, any string fetched here may be invalidated
           (e.g. its memory cleaned up) at the next database operation via
           this driver.

           Portability notes:

           - Some drivers (e.g. Oracle OCI) automatically add a newline to
           the end of the error message (which is somewhat tasteles, IMO).

           - sqlite3 infamously uses the error string "not an error" when
           there is no error, instead of using a NULL/empty string. A driver
           for sqlite3 MAY convert that to a null/empty string.
        */
        int (*error_info)( cpdo_driver * self, char const ** dest,
                           uint32_t * len, int * errorCode );

        /**
           Must return non-zero (true) if the self object is connected, or
           false if !self or self is not connected. A return value of true is
           NOT a guaranty that the connection actually works at the
           moment, but that a connection has, at some point, been
           established.

           Implementations may optionally check whether the connection is
           live here, but are not required to do so.
        */
        char (*is_connected)( cpdo_driver * self );

        /**
           Must clean up all internal resources and then free the self
           object using a mechanism appropriate for its allocation.

           After calling close(), the self object is invalidated and must
           not be used further by the client.
        */
        int (*close)( cpdo_driver * self );

        /**
           This is an optional feature.

           Should return the value of the most recent insertion
           operation by writing it to *v.

           The hint parameter is required by drivers which need, e.g.,
           a sequence name from which to extract the id. Drivers which
           do not need this may ignore the parameter (and must not
           treat its existence as an error).

           Note that some databases use signed integers as IDs, but as
           far as i am aware those do not actually employ negative ID
           numbers. This API makes the assumption that all IDs of this
           type are positive values.
           
           Must return 0 on success. On error v must not be modified.
           If v is NULL implementations must return cpdo_rc.ArgError.

           Drivers which do not support this operation must return
           cpdo_rc.UnsupportedError.
        */
        int (*last_insert_id)( cpdo_driver * self, uint64_t * v, char const * hint );
        
        /**
           Transaction-related functions. Implementations which do not
           support transactions must return cpdo_rc.UnsupportedError
           from these functions.

           Note that drivers which support transactions do not
           necessarily allow nested transactions. This API assumes
           that only one level of transaction is supported, and
           clients should also assume that.

           ACHTUNG: this part of the API _might_ be removed because...
           The only private state, other than the underlying db
           handle, which the driver impls currently hold has to do
           with the transaction-related APIs (they need to remember if
           they're in a transaction or not). If we remove this API
           then we can allow those drivers to be multi-thread-capable
           as long as the underlying driver supports it.

           Additionally, the is_in() operation relies 100% on the client
           using only this API to start transactions, so it is not reliable
           if clients manually send BEGIN/COMMIT commands.
        */
        struct cpdo_driver_api_transaction
        {
            /**
               Tries to start an SQL transaction. Note that
               not all drivers, or not all storage engines supported
               by a given driver, may support transactions.

               If the driver is requested to start a transaction while
               it is already in one, it must return
               cpdo_rc.UnsupportedError if it does not support nested
               transactions.
               
               Returns 0 on success.
            */
            int (*begin)( cpdo_driver * self );
            /**
               Commits the current transaction.
       
               Returns 0 on success.
            */
            int (*commit)( cpdo_driver * self );
            /**
               Rolls back the current transaction.
           
               Returns 0 on success.
            */
            int (*rollback)( cpdo_driver * self );
            /**
               Returns true if, in the driver's humble opinion, it is
               within an active transaction.  This determination is
               not fool-proof, and can only work consistently when
               used in conjunction with this class'
               transaction-related APIs, as opposed to manually
               sending BEGIN/COMMIT SQL.

               Implementations must return 0 if self is NULL.
            */
            char (*is_in)( cpdo_driver * self );
        } transaction;
        /**
            Holds functions related to setting or fetching driver-level
            options.
        */
        struct cpdo_driver_api_options
        {
            /** Do not use - i have not settled on the interface conventions
            yet.
            */
            int (*set)( cpdo_driver * self, char const * key, va_list vargs );

            /** Do not use - i have not settled on the interface conventions
            yet.
            */
            int (*get)( cpdo_driver * self, char const * key, va_list vargs );
            
            /**
                Must set *ch to the character used for quoting strings.
                Must return 0 on success, non-0 on error.
                Must return cpdo_rc.ArgError if ch is NULL.
                
                The driver may support a NULL value for the self object
                (e.g. if the quote character is constant for that driver),
                in which case it should set *ch to the quoting character
                and return 0. If the driver requires a non-NULL self
                pointer and a NULL is passed then the function must
                return cpdo_rc.ArgError. Alternately, it may set *ch to
                "some sane default" (i.e. a single-quote character) and
                return 0.
                
                Some drivers support both single- and double-quotes,
                but the use of double quotes is discouraged for compatibility
                reasons.
            */
            int (*get_string_quote_char)( cpdo_driver * self, char * ch );
        } opt;
        /**
           Holds non-function constants used by the driver implementation.

           FIXME: the table_quote member should be a function
           so that driver-specific options can be used to change them. e.g.
           MySQL supports (it turns out) an option to enable ANSI-style quoting
           (which is not its native string format). Alternately, we could
           implement such differences by using a separate instance of
           cpdo_driver_api for those cases, but that quickly adds complications
           to internal code which otherwise doesn't care about these configurable
           options.
        */
        struct cpdo_driver_api_nonfunc
        {
            /**
               Must be the driver name string associated with this
               driver. It must not change. Ever.
            */
            char const * driver_name;
        
            /**
               The character which "should" be used to quote table and field
               names.
            */
            char const table_quote;
        } constants;
    };

    /**
       This type holds the "vtbl", or "virtual" operations, specified for
       the cpdo_stmt interface. All cpdo_stmt instances originating from a
       given cpdo_driver implementation share a single instance of this class.
    */
    struct cpdo_stmt_api
    {
        /**
           "Steps" the cursor one place. For INSERT, DROP, and DELETE
           operations and such, this executes the insert. For SELECT, it
           steps one row in the result set. Certain DB-specific SQL constructs
           (e.g. MySQL's "SHOW TABLES") are also traversable using
           this mechanism.

           Must return:

           CPDO_STEP_ERROR on error.

           CPDO_STEP_OK means a row was fetched and its data can be
           pulled from the self object's getter functions.
       
           CPDO_STEP_DONE means the end of the result set has been reached
           without an notable error. No result set is actually fetched,
           and the client must not try to fetch row data from the self
           object after CPDO_STEP_DONE is returned.

           Using the various getter routines on a statement has undefined
           results if step() does not return CPDO_STEP_OK.

           Looping over result sets is done like:

           @code
           cpdo_step_code scode;
           while( CPDO_STEP_OK == (scode=st->api->step(st)) ) {
               ... fetch row data ...
           }
           // scode will be CPDO_STEP_DONE or CPDO_STEP_ERR now
           // unless we prematurely ended the loop.
           if( CPDO_STEP_ERROR == scode ) {
               ... there was an error during fetch.
               ... Use st->api->error_info() for (hopefully) details.
           }
           @endcode

        */
        cpdo_step_code (*step)( cpdo_stmt * self );


        /** Has semantics identical to cpdo_driver::error_info(),
            and may produce the same results as that function,
            depending on the driver.
        */
        int (*error_info)( cpdo_stmt * self, char const ** dest,
                           uint32_t * len, int * errorCode );

    
        /**
           Must clean up any memory owned by self and then free the self
           the statement object.

           All statements opened for a given database MUST be finalized
           by the client before the db is closed, or undefined behaviour
           ensues. When used in environments which use garbage
           collection for object destruction (e.g. a script language
           binding), implementor may have to take extra care to ensure
           that statements are not finalized after their parent
           connection has been finalized.
        */
        int (*finalize)( cpdo_stmt * self );

        /**
           The "bind" API is used for binding parameters to prepared
           statements.

           Note that these use 1-based indexes, whereas the getter
           functions use 0-based indexes. i didn't invent the
           conventions, i just try to follow them. The bind functions
           will return cpdo_rc.RangeError if the index is out of
           range.

           Note that not all drivers support binding parameters
           by name (e.g. MySQL 5). For those which don't,
           cpdo_driver implementors may wish to take a look at
           cpdo_named_params_to_qmarks(), which takes a huge number of
           parameters and can be used to add this feature on top of
           APIs which do not natively support it.
        */
        struct cpdo_stmt_api_bind
        {

            /**
               Must re-set the statement so that it can be executed again.
               This is necessary after binding values to a prepared INSERT
               statement, executing the insert (with step()), and then you
               want to do another insert with the same statement.

               Whether or not this un-binds bound values is
               implementation-defined. For portable behaviour, always re-bind
               them between resets.
            */
            int (*reset)( cpdo_stmt * self );
            /**
               Returns the number of bound parameters, or 0 if it has
               none, on error, or if self is NULL.
            */
            uint16_t (*param_count)( cpdo_stmt * self );

            /**
               Returns the 1-based index of the given parameter name
               (not column name!), or 0 on error or if there is no
               such named parameter.

               This is an OPTIONAL feature, because some drivers
               do not support it natively (e.g. MySQL 5).

               The name provided here must exactly match the name in
               the prepared query. e.g. if the query uses ":name" then
               that same string (including the ':' prefix) must be
               passed here. Drivers which internally do not use the
               prefix may simply skip the prefix character.

               Also beware that different drivers support different
               naming conventions. e.g. sqlite3 supports several
               different ones (see
               http://sqlite.org/c3ref/bind_parameter_name.html).
            */
            uint16_t (*param_index)( cpdo_stmt * self, char const * name );

            /**
               Returns the parameter name (not column name!) bound to
               the given 1-based column index, or NULL on error.

               This is an OPTIONAL feature, because some drivers
               do not support it natively (e.g. MySQL 5).
            */
            char const * (*param_name)( cpdo_stmt * self, uint16_t ndx );

            /**
               Binds a NULL value to the given 1-based index.

               Returns 0 on success.
            */
            int (*null)( cpdo_stmt * self, uint16_t ndx );

            /**
               Binds an int8_t value to the given 1-based index.

               Returns 0 on success.
            */
            int (*i8)( cpdo_stmt * self, uint16_t ndx, int8_t v );

            /**
               Binds an int16_t value to the given 1-based index.

               Returns 0 on success.
            */
            int (*i16)( cpdo_stmt * self, uint16_t ndx, int16_t v );

            /**
               Binds an int32_t value to the given 1-based index.

               Returns 0 on success.
            */
            int (*i32)( cpdo_stmt * self, uint16_t ndx, int32_t v );

            /**
               Binds an int64_t value to the given 1-based index.

               Returns 0 on success.
            */
            int (*i64)( cpdo_stmt * self, uint16_t ndx, int64_t v );


            /**
               Binds a float value to the given 1-based index.

               Returns 0 on success.
            */
            int (*flt)( cpdo_stmt * self, uint16_t ndx, float v );

            /**
               Binds a double value to the given 1-based index.

               Returns 0 on success.
            */
            int (*dbl)( cpdo_stmt * self, uint16_t ndx, double v );
        
            /**
               Binds the first len bytes of v as a string value to the
               given 1-based index.

               Implementations MUST distinguish between (v==NULL) and
               (v!=NULL, len==0). The former must be treated as SQL NULL
               and the latter as an empty string.
           
               Returns 0 on success.
            */
            int (*string)( cpdo_stmt * self, uint16_t ndx, char const * v, uint32_t len );

            /**
               Binds the first len bytes of v as a BLOB value at the given
               index.  Blob support is not required to be implemented, and
               drivers which do not support it must return
               cpdo_rc.UnsupportedError from this function.
               
               Implementations must treat (v==NULL) or (len==0) as SQL
               NULL.

               Returns 0 on success.
            */
            int (*blob)( cpdo_stmt * self, uint16_t ndx, void const * v, uint32_t len );
        } bind;

        /**
           The "getter" API, for fetching column data from SELECT-like
           queries.

           Note that the lifetime of fetched string/blob bytes
           may (depending on the driver) expire the next time
           the statement is stepped or when it is cleaned up,
           so clients must copy such data if they need it for
           later.

           Note that these use 0-based indexes, whereas the bind
           functions use 1-based indexes. i didn't invent the
           conventions, i just try to follow them. The getter
           functions must return cpdo_rc.RangeError if the client-provided
           index is out of range.

           Implementations of the index-based getter functions SHOULD
           return cpdo_rc.RangeError if the index is out of range. However,
           some wrappers might not have the range information without the
           overhead of another call into the underlying driver, so they MAY
           simply pass on the index to the driver and accept what it returns.
        */
        struct cpdo_stmt_api_get
        {
            /**
               Returns the number of columns in the query, or 0 on error
               or if the statement has no columns (e.g. a DROP TABLE
               command).
            */
            uint16_t (*column_count)( cpdo_stmt * self );
            /**
               Returns the name of the 0-based column index, or NULL
               on error.

               Note that not all DB drivers guaranty the exact string
               returned for any given column name will have any
               particular value unless the SQL explicitly uses 'AS' to
               alias the column. sqlite3, in particular, has that
               property, and can legally return "possibly unexpected"
               results if the query does not explicitly alias each
               column.
   
               What that means is:

               @code
               // This might provide unexpected column names for (a,b):
               SELECT a, b FROM t;
               // That might return "t.a" and "t.b", or something
               // entirely different, for the column names.

               // This approach guarantees a specific column name will be returned:
               SELECT a AS a, b AS b FROM t;
               @endcode

               Thus clients should always alias all column names with
               'AS' if they want this function to behave predictably.
            */
            char const * (*column_name)( cpdo_stmt * self, uint16_t ndx );
            /**
               Assigns the cpdo data type of the given 0-based column index
               to *val.

               Returns 0 on success. On error, *val is not modified.

               Implementations "should" return the type of the value at
               the current row in the same result set. e.g. a
               driver should return the type NULL for a STRING field
               if the current record has an SQL NULL value. However, it is
               easy to see how unclear driver-level documentation can lead
               to confusion about about exactly which type data is
               returned for such a case (the declared type or the NULL
               type).

                TODO:

                - Make sure the existing drivers return CPDO_TYPE_NULL
                for NULL values.

                - And make sure that's the philosophically correct thing
                to do.
            */
            int (*type)( cpdo_stmt * self, uint16_t ndx, cpdo_data_type * val );

            /**
               Assigns the int8_t value of the given 0-based column index
               to *val.

               Returns 0 on success. On error, *val is not modified.

               Implementations are required to convert other numeric
               types to int8_t for this purpose. NULL values must
               convert to 0.
            */
            int (*i8)( cpdo_stmt * self, uint16_t ndx, int8_t * val );

            /**
               Assigns the int16_t value of the given 0-based column index
               to *val.

               Returns 0 on success. On error, *val is not modified.

               Implementations are required to convert other numeric
               types to int16_t for this purpose. NULL values must
               convert to 0.
            */
            int (*i16)( cpdo_stmt * self, uint16_t ndx, int16_t * val );

            /**
               Assigns the int32_t value of the given 0-based column index
               to *val.

               Returns 0 on success. On error, *val is not modified.

               Implementations are required to convert other numeric
               types to int32_t for this purpose. NULL values must
               convert to 0.
            */
            int (*i32)( cpdo_stmt * self, uint16_t ndx, int32_t * val );
            /**
               Assigns the int64_t value of the given 0-based column index
               to *val.

               Returns 0 on success. On error, *val is not modified.

               Implementations are required to convert other numeric
               types to int64_t for this purpose. NULL values must
               convert to 0.
            */
            int (*i64)( cpdo_stmt * self, uint16_t ndx, int64_t * val );

            /**
               Assigns the double value of the given 0-based column index
               to *val.

               Returns 0 on success. On error, *val is not modified.

               Implementations are required to convert other numeric
               types to float for this purpose. NULL values must
               convert to 0.0.
            */
            int (*flt)( cpdo_stmt * self, uint16_t ndx, float * val );

            /**
               Assigns the double value of the given 0-based column index
               to *val.

               Returns 0 on success. On error, *val is not modified.

               Implementations are required to convert other numeric
               types to double for this purpose. NULL values must
               convert to 0.0.
            */
            int (*dbl)( cpdo_stmt * self, uint16_t ndx, double * val );
        
            /**
               Assigns the string value of the given 0-based column index
               to *val. Note that some (most?) drivers will convert just about
               anything to a string, so this can normally be used to
               fetch numeric fields.

               If len is not NULL then on success it is set to the
               length of the fetched string. (Returned strings are
               always NUL-terminated, so the length is not always
               required by the client.)
           
               The memory is owned by the statement handle, and it may be
               invalidated the next time the handle is step()'d or
               when it is cleaned up. Thus clients must copy the data
               if needed.

               Drivers are not required to convert arbitrary
               non-string fields to strings for this purpose, but they
               are encouraged to do so if feasible. If they cannot do
               a conversion to string, they must return cpdo_rc.TypeError
               from this function.
           
               The driver is responsible for ensuring that the string
               is NUL-terminated.

               The data will be encoded using whatever format the
               server sent. Generally speaking, the library assumes an
               encoding of UTF8, but it does not enforce this.

               Returns 0 on success. On error, *val is not modified.

               Drivers must return SQL NULL values by setting *val to NULL
               if at all possible. It is recognized, however, that some
               underlying APIs may not allow clients to distinguish between
               an empty string and an SQL NULL, in which case implementations
               should assign *val to an empty string.
            */
            int (*string)( cpdo_stmt * self, uint16_t ndx, char const ** val, uint32_t * len );

            /**
               Assigns the blob value of the given 0-based column index
               to *val.

               Blob support is optional, and implementations which don't
               support it must return cpdo_rc.UnsupportedError from this
               function.
               
               Implementations must treat a zero-length BLOB as a NULL
               value.

               The returned memory is owned by the statement handle, and
               it may be invalidated the next time the handle is step()'d
               or when it is cleaned up. Thus clients must copy the data
               if needed. *len is assigned to the length, in bytes, of the
               memory.

               Implementations must allow a NULL len value, under the
               assumption that the client knows that the hell he's doing
               and has some way to count the number of bytes himself.

               Note that drivers may have "relatively small" limits on
               blobs.  e.g. sqlite3 uses int as the blob size, and
               therefore cannot handle "really big" blobs.
           
               Returns 0 on success. On error, *val and *len must not be
               modififed.

               See string() for more notes.
            */
            int (*blob)( cpdo_stmt * self, uint16_t ndx, void const ** val, uint32_t * len );
        } get;
    };

    /** @struct cpdo_driver

        This class represents a single instance of a concrete database
        driver implementation.

       Clients may use the 'api' member but must not touch
       the 'impl' member.

    */
    struct cpdo_driver
    {
        /**
           The "vtbl" of "virtual" operations. That is, those
           which are specified by the cpdo interface but which require
           driver-specific implementations. This must not be NULL.

           All instances of a given driver share the same instance
           of cpdo_driver_api.
        */
        cpdo_driver_api const * api;

        /**
           Holds all implementation-specific data. Client code must
           _never_ use this field, and any modification from anwhere other
           than the concrete driver implementation invokes undefined
           behaviour.
        */
        void * impl;
    };

#if 0
#define cpdo_driver_empty_m {NULL/*api*/, NULL/*impl*/}
#endif

    /**@struct cpdo_stmt

       Represents a single "statement" _and_ result set,
       similar to PHP's PDOStatement.

       Clients may use the 'api' member but must not touch
       the 'impl' member.
    */
    struct cpdo_stmt
    {
        /**
           The "vtbl" for statement handles. That is, those
           which are specified by the cpdo interface but which require
           driver-specific implementations. This must not be NULL.

           All instances of cpdo_stmt which originate from the same
           driver share the same instance of cpdo_stmt_api.
        */
        cpdo_stmt_api const * api;

        /**
           Arbitrary implementation-dependent data. Client code
           must not touch this.
        */
        void * impl;
    };

    /** Empty-initialized cpdo_stmt object. */
#define cpdo_stmt_empty_m {                     \
        NULL/*api*/,                            \
        NULL/*impl*/                        \
    }

    /** Empty-initialized cpdo_stmt object. */
    extern const cpdo_stmt cpdo_stmt_empty;

    /**
       Tries to load a new database driver instance, using the
       given driver name.

       On success *tgt is assigned to the new instance, which the
       caller owns and must eventually free using
       driver->api->close(driver).

       On error, non-0 is returned and *tgt is not modified.

       The opt is currently ignored and may be NULL. This may
       eventually be used to pass PDO-style option/parameter strings,
       or it might be removed altogether.

       After this returns, use driver->api->connect(driver,...) to
       connect to a specific database.

       @code
       cpdo_driver * drv = NULL; // do not forget the NULL!
       int rc = cpdo_driver_new( &drv, "sqlite3", NULL );
       if( rc ) {
           printf("Error: #%d: %s\n",rc, cpdo_rc_string(rc));
           return ...;
       }
       else {
          ... use db ...
          ... eventually close it ...
          drv->api->close(drv);
       }
       @endcode

       Note that in the error case, drv is NULL. This is in contrast
       to cpdo_driver_new_connect().
       
       @see cpdo_driver_new_connect()
    */
    int cpdo_driver_new( cpdo_driver ** tgt, char const * driver,
                         char const * opt );

    /**
       Similar to cpdo_driver_new(), but also tries to connect
       and has slightly different return value semantics
       for the *drv parameter.

       Neither of drv or driver may be NULL. The user and password
       parameters are given to the driver, and may or may not be
       required for that driver (see its documentation).
       
       Tries to load a new db driver using the given dsn string, and
       then connect to it.

       On success, returns 0 and assigns *drv to the new connection,
       which the caller owns.

       On error non-zero is returned and the caller STILL owns *drv.
       The reason for this is so that he can fetch any db-level
       error information before destroying it. If the function
       fails before it can create a driver, *drv is not modified,
       so the client should assign it to NULL before calling this
       to ensure that he can distinguish that case.

       Note that not all drivers require user/password parameters, and
       these arguments may be NULL for such drivers. errMsg may always
       be NULL, but is the only way to get any useful error information
       when connection fails, because the client cannot later fetch
       the driver-level error info
       info

       Example:

       @code
       cpdo_driver * drv = NULL; // do not forget the NULL!
       int rc = cpdo_driver_new_connect( &drv, .... );
       if( rc ) {
           if( drv ) { // means driver was loaded but connect failed
               int err;
               char const * msg = NULL;
               drv->api->error_info( drv, &msg, NULL, &err );
               printf("Error: #%d: %s\n",err,msg);
               drv->api->close(drv);
           }
           else {
               puts("Could not load driver!")
           }
           return ...;
       }
       else {
          ... use db ...
          ... eventually close it ...
          drv->api->close(drv);
       }
       @endcode

       
       Notice that in the error case drv might not be NULL and we
       still have to clean it up. This is the only way to allow
       clients to fetch the connection error information.  We say
       "might" be NULL: if it is NULL then the error happened before a
       connection attempt could be made. e.g. no driver could be found
       for the given driver name, some required argument was NULL,
       or a memory allocation error prevented the object from being
       created.

       @see cpdo_driver_new_connect()
    */
    int cpdo_driver_new_connect( cpdo_driver ** drv, char const * dsn,
                                 char const * user, char const * passwd );

    /**
       A generic SQL quoting algorithm, intended mainly for use by driver
       implementations which use ANSI SQL-style quoting.

       str is the string to quote. *len must be its length.
   
       Allocates a new string with the contents of str, and all quoteChar
       characters in the string gets escaped by escapeChar. If addQuotes
       is not 0 then the returned value is also wrapped in the quote
       character defined by quoteChar, otherwise it is returned without
       surrounding quotes.

       Results are undefined if str is not ASCII encoded. It MIGHT
       work as-is with UTF8, but i haven't tried it.
   
       On success, 0 is returned, *dest is pointed to the new string, and
       *len is assigned to the length of the new string. The caller owns
       the string and must eventually free() it.

       If str is NULL it is treated as an SQL NULL value. *len will be set
       to 4 and *dest will be set to "NULL" (without quotes).

       On error non-0 is returned (one of the cpdo_rc values) and *len and
       *dest are unmodified.

       This implementation sacrifices a bit of speed in favour of
       doing a single, best-fit allocation. It first counts how many
       characters it has to escape, the allocates the string, then
       copies/escapes the bytes.

       FIXME: port in the cson/sqlite3 utf8 traversal code, so we can
       make this safe for UTF8.
    */
    int cpdo_sql_escape( char const * str, uint32_t * len, char ** dest,
                         char quoteChar, char escapeChar, char addQuotes );

    /**
       Preparaes and executes the first len bytes of the given SQL code in
       a single step. This is only useful for query types which do not
       have any sensible result set, or where one does not care about the
       result set. e.g. CREATE TABLE or INSERT.
    */
    int cpdo_exec( cpdo_driver * drv, char const * sql, uint32_t len );

    /**
       Returns the driver's name, or NULL if drv is NULL.
    */
    char const * cpdo_driver_name( cpdo_driver const * drv );

    /**
       A typedef for cpdo_driver factory functions.

       The must try to instantiate a new instance, assign it to *tgt, and
       return 0 on success. On error they must return non-0 (preferably a
       value from cpdo_rc) and must not modify *tgt.
    */
    typedef int (*cpdo_driver_factory_f)( cpdo_driver ** tgt );

    /**
       Registers a factory for a cpdo_driver using the given name.

       On success it returns 0. On error the factory is not registered,
       and the return code should give you some idea about why.

       If a registration already exists with this name,
       cpdo_rc.AccessError is returned.
   
       Caveats:

       - This is not thread-safe. If called multiple times concurrently,
       or concurrent to cpdo_available_drivers(), results are undefined.
       See cpdo_available_drivers() for more details.

       - The internal list has a fixed maximum size. It "should" be "large
       enough", but if it fills up then subsequent registrations will
       cause cpdo_rc.AllocError to be returned (though there is no actual
       allocation going on, it's a logical allocation error because we
       cannot (or do not) expand the list at runtime). The API guarantees
       that at least 20 slots are available for client use. It's not
       that we expect to have that many drivers, but to allow us to add
       aliases. e.g. if MySQL 6 DBs can be used with the MySQL 5 driver
       then we might want to alias "mysql6" to the "mysql5" driver.

    */
    int cpdo_driver_register( char const * name, cpdo_driver_factory_f );

    /**
       Returns an array containing the names of all registered drivers.

       The last entry in the array is NULL.

       This function is not thread-safe. If called concurrent to
       cpdo_driver_register(), results are undefined. The return result
       itself is also not thread-safe in conjunction with
       cpdo_driver_register(), and calling that function may change the
       values pointed to by this array. It won't change their addresses
       (the pointers will still be valid) but might change their
       contents. In such a case, nothing horribly drastic will happen. e.g.
       if cpdo_driver_register() is called concurrently with
       cpdo_driver_new() using the same driver name, the worst that will
       happen is that cpdo_driver_new() won't find the driver.
    */
    char const * const * cpdo_available_drivers();

    /** Do not use - its interface is as yet undecided. */
    int cpdo_driver_opt_set( cpdo_driver * self, char const * key, ... );
    /** Do not use - its interface is as yet undecided. */
    int cpdo_driver_opt_get( cpdo_driver * self, char const * key, ... );

    /**
       Returns true (non-0) if st is NULL or if st->api->get.type(st,ndx)
       is CPDO_TYPE_NULL. This only has meaningful results when used
       on fetchable statements (e.g. SELECT).
    */
    char cpdo_stmt_col_is_null( cpdo_stmt const * st, uint16_t ndx );

    /**
       Convenience form of st->api->get.type() which returns
       CPDO_TYPE_ERROR on error.
    */
    cpdo_data_type cpdo_get_type( cpdo_stmt * st, uint16_t ndx );
    
    /**
       Convenience form of st->api->get.i8() which returns 0
       on error.
    */
    int8_t cpdo_get_int8( cpdo_stmt * st, uint16_t ndx );

    /**
       Convenience form of st->api->get.i16() which returns 0
       on error.
    */
    int16_t cpdo_get_int16( cpdo_stmt * st, uint16_t ndx );

    /**
       Convenience form of st->api->get.i32() which returns 0
       on error.
    */
    int32_t cpdo_get_int32( cpdo_stmt * st, uint16_t ndx );

    /**
       Convenience form of st->api->get.i64() which returns 0
       on error.
    */
    int64_t cpdo_get_int64( cpdo_stmt * st, uint16_t ndx );

    /**
       Convenience form of st->api->get.dbl() which returns 0
       on error.
    */
    double cpdo_get_double( cpdo_stmt * st, uint16_t ndx );

    /**
       Convenience form of st->api->get.flt() which returns 0
       on error.
    */
    float cpdo_get_float( cpdo_stmt * st, uint16_t ndx );

    /**
       Convenience form of st->api->get.string() which returns NULL on
       error.
    */
    char const * cpdo_get_string( cpdo_stmt * st, uint16_t ndx, uint32_t * len );
    
    /**
       Convenience form of st->api->get.string() which returns NULL on
       error.
    */
    void const * cpdo_get_blob( cpdo_stmt * st, uint16_t ndx, uint32_t * len );

    /**
       Convenience form of st->api->bind.int8().
    */
    int cpdo_bind_int8( cpdo_stmt * st, uint16_t ndx, int8_t v );

    /**
       Convenience form of st->api->bind.int16().
    */
    int cpdo_bind_int16( cpdo_stmt * st, uint16_t ndx, int16_t v );

    /**
       Convenience form of st->api->bind.int32().
    */
    int cpdo_bind_int32( cpdo_stmt * st, uint16_t ndx, int32_t v );

    /**
       Convenience form of st->api->bind.int64().
    */
    int cpdo_bind_int64( cpdo_stmt * st, uint16_t ndx, int64_t v );

    /**
       Convenience form of st->api->bind.flt().
    */
    int cpdo_bind_float( cpdo_stmt * st, uint16_t ndx, float v );

    /**
       Convenience form of st->api->bind.double().
    */
    int cpdo_bind_double( cpdo_stmt * st, uint16_t ndx, double v );

    /**
       Convenience form of st->api->bind.string().
    */
    int cpdo_bind_string( cpdo_stmt * st, uint16_t ndx, char const * v, uint32_t length );

    /**
       Convenience form of st->api->bind.blob().
    */
    int cpdo_bind_blob( cpdo_stmt * st, uint16_t ndx, void const * v, uint32_t length );
    
    /**
       Convenience form of drv->api->close(drv).

       After calling this, drv is no longer valid.
    */
    int cpdo_close( cpdo_driver * drv );

    /**
       Convenience form of drv->api->connect( drv, opt );
    */
    int cpdo_driver_connect( cpdo_driver * drv, cpdo_connect_opt const * opt );

    /**
       Convenience form of drv->api->prepare(drv, tgt, sql, length).
    */
    int cpdo_prepare( cpdo_driver * drv, cpdo_stmt ** tgt, char const * sql, uint32_t length );

    /**
       Convenience form of st->api->step(st).
    */
    cpdo_step_code cpdo_step( cpdo_stmt * st );

    /**
       Convenience form of st->api->finalize(st).

       After calling this, st is no longer valid.

       All statements opened for a given database MUST be finalized
       before the db is closed, or undefined behaviour ensues.
    */
    int cpdo_stmt_finalize( cpdo_stmt * st );

    /**
       Convenience form of drv->api->close(drv).

       After calling this, drv is no longer valid.

       All statements opened for a given database MUST be finalized
       before the db is closed, or undefined behaviour ensues.
    */
    int cpdo_close( cpdo_driver * drv );

    /**
       Convenience form of drv->api->last_insert_id(drv,...,hint)
       which returns 0 on error.
    */
    uint64_t cpdo_last_insert_id( cpdo_driver * drv, char const * hint );


    /**
       Works like vprintf(), but appends all output to a
       dynamically-allocated string, expanding the string as necessary to
       collect all formatted data. The returned nul-terminated string is
       owned by the caller and it must be cleaned up using free(). If !fmt
       or if the expanded string evaluates to empty, null is returned, not
       a length-0 (1-byte) string.
       
       This implementation of printf() has several custom format
       specifiers:
       
        %%z works like %%s, but takes a non-const (char *) and this 
        code deletes the string (using free()) after appending it to 
        the output.

         %%h (HTML) works like %s but converts certain characters 
         (like '<' and '&' to their HTML escaped equivalents.

         %%t (URL encode) works like %%s but converts certain 
         characters into a representation suitable for use in an 
         HTTP URL. (e.g. ' ' gets converted to %%20)

         %%T (URL decode) does the opposite of %t - it decodes 
         URL-encoded strings.

         %%r requires an int and renders it in "ordinal form". That 
         is, the number 1 converts to "1st" and 398 converts to 
         "398th".

         %%q quotes a string as required for SQL. That is, '\'' 
         characters get doubled. ONLY use this when you know that the
         underlying driver supports ANSI-SQL-style strings.

         %%Q as %%q, but includes the outer '\'' characters and null pointers
         are replaced by SQL NULL.

         (The %%q and %%Q specifiers are options inherited from this printf
         implementation's sqlite3 genes.)

         These extensions may be disabled by setting certain macros when
         compiling the library (see cpdo_printf.c for the gory details).
    */
    char * cpdo_mprintf_v( char const * fmt, va_list vargs );

    /**
        Equivalent to cpdo_mprintf_v(), but takes elipsis arguments instead
        of a va_list.
    */
    char * cpdo_mprintf( char const * fmt, ... );

    /**
        A convenience wrapper around cpdo_mprintf() and 
        cpdo_prepare(), which allows one to create SQL using 
        printf-style formatting specifiers.
        
        Returns 0 on success.
    */
    int cpdo_prepare_f_v( cpdo_driver * drv, cpdo_stmt ** tgt, char const * fmt, va_list );

    /**
        Equivalent to cpdo_prepare_f_v() but takes elipsis arguments.
    */
    int cpdo_prepare_f( cpdo_driver * drv, cpdo_stmt ** tgt, char const * fmt, ... );

    /**
        A convenience wrapper around cpdo_mprintf() and 
        cpdo_exec(), which allows one to create SQL using 
        printf-style formatting specifiers.
        
        Returns 0 on success.
    */
    int cpdo_exec_f_v(  cpdo_driver * drv, char const * fmt, va_list );

    /**
        Equivalent to cpdo_exec_f_v() but takes elipsis arguments.
    */
    int cpdo_exec_f(  cpdo_driver * drv, char const * fmt, ... );

    /**
        A convenience wrapper around cpdo_mprintf() and 
        cpdo_bind_string(), which allows one to set string values using 
        printf-style formatting specifiers.
        
        Returns 0 on success.
    */
    int cpdo_bind_string_f_v( cpdo_stmt * st, uint16_t ndx, char const *fmt, va_list );

    /**
        Equivalent to cpdo_bind_string_f_v() but takes elipsis arguments.
    */
    int cpdo_bind_string_f( cpdo_stmt * st, uint16_t ndx, char const * fmt, ... );
    
    /**
        Convenience form of st->api->bind.param_name(st, name).
        
        Returns 0 if st is NULL.
    */
    uint16_t cpdo_param_index( cpdo_stmt * st, char const * name );

    /**
        convenience form of st->api->bind.param_name(st, ndx).
        
        Returns NULL if st is NULL.
    */
    char const * cpdo_param_name( cpdo_stmt * st, uint16_t ndx );

    /**
        Returns the value of CPDO_VERSION_NUMBER this library was
        compiled against.

        Added in version 20110209.
    */
    int cpdo_version_number();
    
    /** LICENSE

    This software's source code, including accompanying documentation and
    demonstration applications, are licensed under the following
    conditions...

    The author (Stephan G. Beal [http://wanderinghorse.net/home/stephan/])
    explicitly disclaims copyright in all jurisdictions which recognize
    such a disclaimer. In such jurisdictions, this software is released
    into the Public Domain.

    In jurisdictions which do not recognize Public Domain property
    (e.g. Germany as of 2011), this software is Copyright (c) 2011
    by Stephan G. Beal, and is released under the terms of the MIT License
    (see below).

    In jurisdictions which recognize Public Domain property, the user of
    this software may choose to accept it either as 1) Public Domain, 2)
    under the conditions of the MIT License (see below), or 3) under the
    terms of dual Public Domain/MIT License conditions described here, as
    they choose.

    The MIT License is about as close to Public Domain as a license can
    get, and is described in clear, concise terms at:

    http://en.wikipedia.org/wiki/MIT_License

    The full text of the MIT License follows:

    --
    Copyright (c) 2011 Stephan G. Beal (http://wanderinghorse.net/home/stephan/)

    Permission is hereby granted, free of charge, to any person
    obtaining a copy of this software and associated documentation
    files (the "Software"), to deal in the Software without
    restriction, including without limitation the rights to use,
    copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the
    Software is furnished to do so, subject to the following
    conditions:

    The above copyright notice and this permission notice shall be
    included in all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
    EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
    OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
    HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
    WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
    FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
    OTHER DEALINGS IN THE SOFTWARE.

    --END OF MIT LICENSE--

    For purposes of the above license, the term "Software" includes
    documentation and demonstration source code which accompanies
    this software. ("Accompanies" = is contained in the Software's
    primary public source code repository.)

    */

#if defined(__cplusplus)
} /*extern "C"*/
#endif

#endif /* WANDERINGHORSE_NET_CPDO_H_INCLUDED */
/* end of file include/wh/cpdo/cpdo.h */
/* start of file include/wh/cpdo/cpdo_internal.h */
#if !defined(WANDERINGHORSE_NET_CPDO_INTERNAL_H_INCLUDED)
#define WANDERINGHORSE_NET_CPDO_INTERNAL_H_INCLUDED

/** @file cpdo_internal.h

This function contains the "semi-private" API for the cpdo library.
This mainly includes rountines and types which might be useful
for specific cpdo_driver implementations.

Author: Stephan Beal (http://www.wanderinghorse.net/home/stephan/)

License: Dual Public Domain/MIT. The full license text is at the
bottom of the main header file (cpdo.h).

*/


#if defined(__cplusplus)
extern "C" {
#endif

    /** @internal

    Semi-internal: intended for use by concrete driver implementations,
    for parsing DSN parameters.

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
    debug builds if passed NULL as either parameter. In non-debug builds
    it will return 0 in that case.

    Sample usage (because it might not be obvious based on the details
    given above:


    @code
    char const * tokBegin = "foo/bar///baz";
    char const * tokEnd = NULL;
    while( cpdo_next_token( &tokBegin, '/', &tokEnd) ) {
    if( tokBegin == tokEnd ) break;
    else {
    ... the "half-open" range [tokBegin,tokEnd) now
    ... contains token bytes. Note that they are not
    ... NUL-terminated and they immediately preceed the
    ... next token's bytes, so they must normally be
    ... copied to a NUL-terminated buffer in order to
    ... be useful.

    ... When finished, set up the pointers for the next
    ... loop iteration:

    tokBegin = tokEnd;
    tokEnd = NULL;
    }
    }
    @endcode

    Given those sample inputs, the above loop would run 3 times, fetching
    the tokens "foo", "bar", and "baz".

    */
    char cpdo_next_token( char const ** inp, char separator, char const ** end );

    /**
       Returns non-0 if str is not NULL and starts with any of
       [1tTyY], else returns 1. Intended primarily for use with tokens
       parsed from cpdo_next_token(), e.g. boolean DSN parameter
       values.
    */
    char cpdo_token_bool_val(char const * str);

    /**
       Semi-internal: intended for driver implementations.

       This function takes a DSN-style string and splits it
       into two parts.

       out must be valid memory at least outLen bytes long.  If dsn is
       as long or longer than outLen then cpdo_rc.RangeError is
       returned (we need one extra byte to ensure a NUL terminator).
       The contents of out (up to outLen bytes) will be initialized by
       this function, so the caller need not memset() it before
       calling this.

       On success, will contain two parts: the part of the dsn up to the
       first ':' character. That ':' will be replaced by a NUL byte. The
       *paramPos parameter (if not NULL) will be assigned to point to the
       byte directly after the new NUL byte, i.e. the parameters part of
       the DSN.

       On error, non-0 is returned and the output must not be used.

       Error conditions include:

       - dsn==NULL: cpdo_rc.ArgError

       - dsn with a length of less than 2 or dsn length>=outLen:
       cpdo_rc.RangeError. (2 is the minimum legal length length for
       a driver taking no parameters, e.g. "x:".)

       This function does not validate that the driver part of the
       string or the parameter parts are actually syntactically or
       symantically valid.
       
       Example:

       Given the DSN "drivername:foo=bar...", after this returns,
       out would contain "drivername<NUL>foo=bar...", and *paramPos
       (if not NULL) will point to "foo=bar...".
    */
    int cpdo_split_dsn( char const * dsn, char * out, uint32_t outLen,
                        char const ** paramPos );

    
    typedef struct cpdo_bind_val cpdo_bind_val;

    /** @struct cpdo_bind_val

       Semi-internal - intended only for driver developers.
    
       This type exists to give driver bindings a place to store
       result buffers (for drivers which require the client to
       supply such buffers).

       To properly manage their memory, use the cpdo_bind_val_TYPE()
       family of functions to set their values and
       cpdo_bind_val_clean() or cpdo_bind_val_free() (see their docs
       for the difference) to clean them up.

       These objects, if used at all, are for internal use within a
       given driver binding, and are not intended to leak out into
       client code. Thus the driver code is free to take a few
       liberties with these objects (in terms of memory management and
       whatnot), provided he does not violate the rules specified in
       the documentation.
    */
    struct cpdo_bind_val
    {
        /**
           Specifies which member of the valu member was last used to
           store a value in this object.

           If this type is CPDO_TYPE_NULL or CPDO_TYPE_ERROR, then it
           is not legal to read any of the valu union fields.
        */
        cpdo_data_type type;

        /**
           Drivers MAY set this to non-0 to signify that the value is
           SQL NULL. They MUST set type=CPDO_TYPE_NULL for that, but
           this member exists because MySQL wants a pointer to a spot
           where it can set the value itself.
         */
        char is_null;

        /**
           Drivers MAY set this to non-0 to signify that the value has
           some error condition. e.g. the MySQL driver wants a pointer
           to a spot where it can set the value itself, and it sets
           this flag for us on fetch errors.
        */
        char has_error;

        /**
           The raw value for this object.  Note that it's a union and
           that this class' "type" member specifies which member of
           valu is legal to read. Reading any other values results, as
           specified by the rules for unions, in undefined behaviour.
         */
        union cpdo_bind_val_union_t
        {
            int8_t i8;
            int16_t i16;
            int32_t i32;
            int64_t i64;
            float flt;
            double dbl;
            /**
               Used for both string and binary data.
            */
            struct cpdo_bind_val_blob_t
            {
                /**
                   Memory for the blob, owned by this
                   object.
                */
                void * mem;
                /**
                   The number of bytes in mem.
                */
                unsigned long length;
            } blob;

            /**
               Low-low-level place to store pointers to custom data
               types.
             */
            struct cpdo_bind_val_custom_t
            {
                /**
                   The raw memory. If dtor is not NULL then
                   this object owns the memory, otherwise
                   the user must manage it.
                 */
                void * mem;
                /**
                   Arbitrary value. e.g. (MYSQL_TIME*) for a 
                   MYSQL_TYPE_TIMESTAMP value (or equivalent for a 
                   given driver). Drivers can use this to 
                   distinguish between multiple types bound with the 
                   cpdo type CPDO_TYPE_CUSTOM.
                   
                   See cpdo_bind_val_custom() for more notes on this.
                 */
                int type_tag;
                /**
                   This only exists to please MySQL and similar 
                   drivers. It writes the length of inbound data 
                   (stored in the mem pointer) here.
                 */
                unsigned long length;
                /**
                   Must free the memory passed it (at least
                   semantically). Must accept a parameter of NULL
                   without crashing. i.e. it must behave like free().
                 */
                void (*dtor)( void * );
            } custom;
        } valu;
    };

    /** An empty-initialized cpdo_bind_val object. */    
#define cpdo_bind_val_empty_m { \
        CPDO_TYPE_NULL/*type*/,\
            0/*is_null*/, \
            0/*has_error*/,\
        {/*valu*/0}\
    }

    /** An empty-initialized cpdo_bind_val object. */
    extern const cpdo_bind_val cpdo_bind_val_empty;

    /**
       Cleans any internals owned by b and sets it to a "non-value"
       with the type CPOD_TYPE_NULL. Does not free b.  Returns 0 on
       success. The only detectable error condition is if b is NULL,
       and passing an object with invalid internal state
       (e.g. b->valu.blob.mem is pointed to memory b does not own)
       results in undefined behaviour.
    */
    int cpdo_bind_val_clean( cpdo_bind_val * b );

    /**
       Calls cpdo_bind_val_clean() and then frees b.
       See cpdo_bind_val_clean() for the return values.
    */
    int cpdo_bind_val_free( cpdo_bind_val * b );

    /**
       Calls cpdo_bind_val_clean() and then sets b to be of type
       CPDO_TYPE_NULL. See cpdo_bind_val_clean() for the return
       values.
    */
    int cpdo_bind_val_null( cpdo_bind_val * b );

    /**
       Calls cpdo_bind_val_clean() and then sets b to be of type
       CPDO_TYPE_CUSTOM, with the given memory, destructor, and
       "typeTag" (which can be whatever the implementor wants.

       mem must point to the bound object. dtor may be NULL
       or may point to a function which will be used to free
       mem when b is cleaned up.

       Any of the parameters may be NULL/0 except for b.

       The inspiration here is that we want to be able to support
       MySql TIMESTAMP fields.

       Please don't use this unless you really know what
       you're doing with it!

       See cpdo_bind_val_clean() for the return values.
       
       Be VERY AWARE that the downstream interpretation of the mem 
       pointer depends entirely on a unique combination of the 
       underlying cpdo_driver (which is presumably using this 
       function) and the value of typeTag. Since 20 different 
       drivers could all have a custom type where they use typeTag 
       2, a more robust mechanism for dolling out typeTags might be 
       in order. On idea is to hash the driver's name, use (say) 24 
       bits from that hash as the top 24 bits of typeTag, and use a 
       value 0-255 for the lower byte. It ain't pretty, but it 
       should help avoid collisions. The small size of the hashing 
       space (all available driver names) is so small that it's 
       highly unlikely that a collision would occur unless a very 
       mismatched hash routine is used. An alternate, which is 
       easier to  implement: use the high bytes of some internally-used
       static object (e.g. the local cpdo_driver::api's address)
       as the mask, and map the custom type ID into the lower byte. 
       The only collision cases might be when two internally-defined 
       cpdo_driver_api instances are allocated with the same
       mask of its upper 24 bytes (we lose bits after 64 because
       of the conversion to int tagType). Since each 
       driver is implemented in its own file (with the excepion of 
       during the cpdo Amalgamation Build), it is exceedingly 
       unlikely that multiple instances will fall into the same 
       255-byte range. By inserting a dummy char array 255 bytes 
       long immediately after the private cpdo_driver_api is set up, 
       we can probably (maybe?) even guaranty no collisions.
       
       The purpose of such an exercise would be to future-proof the 
       driver for when i eventually (possibly) add CPDO_TYPE_CUSTOM 
       support to the public API (remember, this function is 
       semi-private, intended for driver developers). If that is added,
       client code could easily inadvertently pass a type tag from
       a different type, and we can check that by using the masking
       option. The client would probably need to call into the driver
       API to generate such a mask, or we could add it to the public API,
       and use driver->api as the address to mask against. Hmmm...
    */
    int cpdo_bind_val_custom( cpdo_bind_val * b, void * mem,
                              void (*dtor)(void *), int typeTag );

    
    /**
       Calls cpdo_bind_val_clean() and then sets b to be of type
       CPDO_TYPE_INT8. See cpdo_bind_val_clean() for the return
       values.

       On success, sets b->valu.i8 to v.
    */
    int cpdo_bind_val_int8( cpdo_bind_val * b, int8_t v );

    /**
       Calls cpdo_bind_val_clean() and then sets b to be of type
       CPDO_TYPE_INT16. See cpdo_bind_val_clean() for the return
       values.

       On success, sets b->valu.i16 to v.
    */
    int cpdo_bind_val_int16( cpdo_bind_val * b, int16_t v );

    /**
       Calls cpdo_bind_val_clean() and then sets b to be of type
       CPDO_TYPE_INT32. See cpdo_bind_val_clean() for the return
       values.

       On success, sets b->valu.i132 to v.
    */
    int cpdo_bind_val_int32( cpdo_bind_val * b, int32_t v );

    /**
       Calls cpdo_bind_val_clean() and then sets b to be of type
       CPDO_TYPE_INT64. See cpdo_bind_val_clean() for the return
       values.

       On success, sets b->valu.i64 to v.
    */
    int cpdo_bind_val_int64( cpdo_bind_val * b, int64_t v );

    /**
       Calls cpdo_bind_val_clean() and then sets b to be of type
       CPDO_TYPE_DOUBLE. See cpdo_bind_val_clean() for the return
       values.

       On success, sets b->valu.dbl to v.
    */
    int cpdo_bind_val_double( cpdo_bind_val * b, double v );

    /**
       Calls cpdo_bind_val_clean() and then sets b to be of type
       CPDO_TYPE_FLOAT. See cpdo_bind_val_clean() for the return
       values.

       On success, sets b->valu.dbl to v.
    */
    int cpdo_bind_val_float( cpdo_bind_val * b, float v );

    /**
       Calls cpdo_bind_val_clean() and then sets b to be of type
       CPDO_TYPE_STRING. See cpdo_bind_val_clean() for the return
       values.

       The first len bytes of v are copied by this function and the
       copy is owned by b.  A NUL terminator is added to the copied
       data.

       If v is NULL and len is not then len bytes are allocated
       dynamically and set to 0.

       On success, sets b->valu.blob.mem to the copied memory
       and b->valu.blob.length to len.
    */
    int cpdo_bind_val_string( cpdo_bind_val * b, char const * v, uint32_t len );

    /**
       Calls cpdo_bind_val_clean() and then sets b to be of type
       CPDO_TYPE_BLOB. See cpdo_bind_val_clean() for the return
       values.

       The first len bytes of v are copied by this function and the
       copy is owned by b. The library may, at its descretion, add a
       NUL terminator to the copied data, for sanity's sake.

       If v is NULL and len is not then len bytes are allocated
       dynamically and set to 0.

       On success, sets b->valu.blob.mem to the copied memory
       and b->valu.blob.length to len.
    */
    int cpdo_bind_val_blob( cpdo_bind_val * b, void const * v, uint32_t len );

    /**
       Allocates a list of n cpdo_bind_val object, each initialized to
       hold the default state (that of cpdo_bind_val_empty).

       Returns NULL on allocation error or if n is 0.

       On success the caller owns the returned object and must
       eventually free it using cpdo_bind_val_list_free().
    */
    cpdo_bind_val * cpdo_bind_val_list_new( uint16_t n );

    /**
       Cleans up and frees lists created using
       cpdo_bind_val_list_new().  list must be an array len items
       long, and it must have been allocated via
       cpdo_bind_val_list_new() (or compatible).  Each item in the
       list is passed to cpdo_value_clean(), and then list is freed.

       Returns 0 on success, non-0 on error. The only detectable error
       conditions are if list is NULL or len in 0. It cannot detect if
       someone mucked about incorrectly with the individual values'
       pointer data.
    */
    int cpdo_bind_val_list_free( cpdo_bind_val * list, uint16_t len );


    /**
       Semi-internal: intended to support the MySQL driver but might
       find uses elsewhere.
       
       Searches an SQL string for named parameters in the form :paramName,
       where the ':' character is defined by the paramChar parameter.

       If alsoDoQMarks is true then embedded question-mark
       placeholders are also treated as being identifiers, otherwise
       they are not counted. This is required if SQL uses a mixture of
       names and unnamed bound parameters and you need to know the
       exact bind index of a named parameter.  In such cases, the
       matched parameter name will simply be the question mark.
       
       This code assumes backslash-style escaping rules, a-la MySQL,
       and not ANSI SQL escaping rules. That said: it will behave
       correctly with ANSI-style escaped SQL, but only if the SQL is
       100% well-formed.  See below for more details.
       
       On success non-0 (true) is returned *paramBegin will point to
       the start of the named parameter and *paramEnd points to the
       one-after-the-end position. On error (bad parameters or no
       matches found) *paramBegin and *paramEnd are not modified.

       This function tries to do robust handling of escaped strings,
       strings-within-string, and whatnot, but it can be fooled if
       passed ANSI-SQL-quoted strings which themselves have
       bound-parameter-like substrings within them.

       inpBegin must point to the begining of the input string, which
       is assumed to be well-formed SQL (i.e., that a "prepare"
       operation would succeed as far as the syntax is concerned, not
       counting missing support for named bound parameters).

       len is the number of bytes to scan.

       paramChar must be the prefix character used for binding
       parameters. If it is either a backlash, question mark, single
       quote, or double quote, it is rejected and false is returned
       (to avoid amgbuities in the rest of the parser).

       paramBegin must be a pointer to a string to hold the starting
       position of the result. Likewise, paramEnd must point to place
       where we can store the result position.

       Parameter identifiers are assumed to follow conventional
       identifier naming rules: they start with a alpha- or underscore
       character and containing any number alphanumeric or underscore
       characters.
       
       Example:

       @code
       char const * sql =
           "INSERT INTO T VALUES("
            "\"string 'stuff'\""
            ", :param1"
            ", ':nonParam'"
            ", \"\\\":nonParam\\\"\""
            ", :finalParam"
            ")";
       uint32_t slen = strlen(sql);
       char const * begin = sql;
       char const * end = NULL;
       while( cpdo_find_next_named_param( begin, slen, ':', 0, &begin, &end ) ) {
           printf("Found parameter: ");
           for( ; begin < end; ++begin ) putchar(*begin);
           putchar('\n');
           end = NULL; // set up for next loop iteration.
       }
       @endcode

       If fed input which is not syntactically valid SQL, it _may_ produce
       incorrect results.

       The following legal SQL will actually work here, by a weird
       accident of design:

       @code
       "'''ANSI-style :thisWillNOTLookLikeAParameter''\"
       @endcode

       But the following will produce unexpected results because the enclosing
       string is not quoted properly:
    
       @code
       "''ANSI-style :thisWILLLookLikeAParameter''\"
       @endcode

       Such a statement cannot be prepared by the database (we hope!), so
       it is arguable that a mis-match here will have any real effect on
       usage.

    */
    char cpdo_find_next_named_param( char const * inpBegin,
                                     uint32_t len,
                                     char paramChar,
                                     char alsoDoQMarks,
                                     char const **paramBegin,
                                     char const **paramEnd );

    /**
       Semi-internal: intended to support the MySQL driver but might
       find uses elsewhere.

       This function uses cpdo_find_next_named_param() to parse the
       first len bytes of inp for named parameter markers.  It
       replaces those markers with question marks.  See
       cpdo_find_next_named_param() for the meanings of the first 4
       parameters.

       If any arguments are illegal, *out is not modified and
       cpdo_rc.ArgError is returned.
       
       If it [thinks it] finds any named parameters, it returns the
       number of markers replaced by assigning *count to that value,
       and places a copy of the translated, NUL-terminated string in
       *out.  If outLen is not NULL, the length of the new string is
       written there. The caller must eventually free() the
       *out-stored string.

       If it finds no matches, it returns 0 (success), sets *out
       to NULL, and outLen (if not NULL) to 0.
       
       SQL comments (starting with "--" and going to the next newline character)
       are skipped, and comments inside a quoted string are seen as part
       of the string, not part of a comment.
       
       If the nameList parameter is not NULL and parameters are found
       then the names of all found are stored as a list here (in the
       order they are found). The list will have the same number of
       entries as *count, and will contain NUL-terminated strings. If
       this function returns an error or finds no matches, nameList is
       never modified. The name list, if used, is allocated into the
       same block of memory as the *out memory, and is freed when that
       memory is freed by the caller.

       This function has an internal hard-coded limit on the number of
       parameters it will parse, and if this limit is exceeded it is
       treated as an error (i.e. *out is not modified), returning
       cpdo_rc.RangeError. The limit is guaranteed to be at least 100.

       This function takes the record (within in the cpdo API) for the
       number of parameters it takes. It also represents my very first
       (char ***) parameter.
    */
    int cpdo_named_params_to_qmarks( char const * inp,
                                     uint32_t len,
                                     char paramChar,
                                     char alsoDoQMarks,
                                     uint16_t * count,
                                     char ** out,
                                     uint32_t * outLen,
                                     char *** nameList 
                                     );


    /**
        Given a "tag type" (see cpdo_bind_val::custom::tag_type and 
        cpdo_bind_val_custom) and the address of some internal 
        static data (doesn't really matter what, as long as it's 
        unique per driver), this function returns a hashcode which 
        can later (in the same app session) be used to help ensure 
        that the driver is later working with the proper custom data 
        type.
        
        i know it sounds confusing... i'm trying.
        
        This can be used to "mangle" custom type IDs in such a way 
        that collisions with type_tags used by other drivers is 
        essentially ... well, highly, highly unlikely.
        
        The return value is intended to be passed to 
        cpdo_hash_type_tag_validate() at some point.
        
        This hash is not guaranteed to be persistent across app
        sessions (and almost certainly won't be).
        
        It is assumed that driver-level type IDs (e.g. MYSQL_TYPE_STRING)
        have values less than 256, occupying only 1 byte of tagType.
        If they have higher values, the hash routine will have a higher
        chance of producing collisions across different keys. (Still not high,
        but higher.)
        
        This can be used in conjunction with cpdo_bind_val_custom() so that 
        we can start future-proofing the code to avoid problems of 
        getting incorrect types passed to us from client code when/if i 
        add CPDO_TYPE_CUSTOM support to the public API. With this, we 
        can validate whether a given CPDO_TYPE_CUSTOM/type_flag 
        combination came from this driver or a different one.
        
        Maybe, anyway.
    */
    int cpdo_bind_val_tag_type_hash( cpdo_driver_api const * key, int tagType );
    
    /**
        Expects a hash value calculated by cpdo_bind_val_tag_type_hash(key). 
        If tagHash appears to have been generated by that function, as 
        opposed to coming from another source, this function returns 
        non-0 (true), else false. This does not verify the exact type
        encoded in tagHash, but verifies (to the best of its ability)
        that the given hashcode was generated by a call to
        cpdo_bind_val_tag_type_hash(key,someValue).
    */
    char cpdo_bind_val_tag_type_check_origin( cpdo_driver_api const * key, int tagHash );
    
    /* LICENSE

    This software's source code, including accompanying documentation
    and demonstration applications, are licensed under the following
    conditions...

    The author (Stephan G. Beal [http://wanderinghorse.net/home/stephan/])
    explicitly disclaims copyright in all jurisdictions which recognize
    such a disclaimer. In such jurisdictions, this software is released
    into the Public Domain.

    In jurisdictions which do not recognize Public Domain property
    (e.g. Germany as of 2011), this software is Copyright (c) 2011
    by Stephan G. Beal, and is released under the terms of the MIT License
    (see below).

    In jurisdictions which recognize Public Domain property, the user of
    this software may choose to accept it either as 1) Public Domain, 2)
    under the conditions of the MIT License (see below), or 3) under the
    terms of dual Public Domain/MIT License conditions described here, as
    they choose.

    The MIT License is about as close to Public Domain as a license can
    get, and is described in clear, concise terms at:

    http://en.wikipedia.org/wiki/MIT_License

    The full text of the MIT License follows:

    --
    Copyright (c) 2011 Stephan G. Beal (http://wanderinghorse.net/home/stephan/)

    Permission is hereby granted, free of charge, to any person
    obtaining a copy of this software and associated documentation
    files (the "Software"), to deal in the Software without
    restriction, including without limitation the rights to use,
    copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the
    Software is furnished to do so, subject to the following
    conditions:

    The above copyright notice and this permission notice shall be
    included in all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
    EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
    OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
    HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
    WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
    FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
    OTHER DEALINGS IN THE SOFTWARE.

    --END OF MIT LICENSE--

    For purposes of the above license, the term "Software" includes
    documentation and demonstration source code which accompanies
    this software. ("Accompanies" = is contained in the Software's
    primary public source code repository.)

    */

#if defined(__cplusplus)
} /*extern "C"*/
#endif

#endif /* WANDERINGHORSE_NET_CPDO_INTERNAL_H_INCLUDED */
/* end of file include/wh/cpdo/cpdo_internal.h */
#if CPDO_ENABLE_SQLITE3
#if !defined(WANDERINGHORSE_NET_CPDO_CPDO_SQLITE3_H_INCLUDED)
#define WANDERINGHORSE_NET_CPDO_CPDO_SQLITE3_H_INCLUDED
#ifdef __cplusplus
extern "C" {
#endif
/**
    Registers the sqlite3 driver with the cpdo library.
    Returns 0 on success, non-0 on error (see cpdo_driver_register() for
    the return codes).
*/
int cpdo_driver_sqlite3_register();

#if defined(__cplusplus)
} /*extern "C"*/
#endif

#endif /* WANDERINGHORSE_NET_CPDO_CPDO_SQLITE3_H_INCLUDED */

#endif /*CPDO_ENABLE_SQLITE3*/
#if CPDO_ENABLE_MYSQL5
#if !defined(WANDERINGHORSE_NET_CPDO_CPDO_MYSQL5_H_INCLUDED)
#define WANDERINGHORSE_NET_CPDO_CPDO_MYSQL5_H_INCLUDED
#ifdef __cplusplus
extern "C" {
#endif
/**
    Registers the mysql5 driver with the cpdo library.
    Returns 0 on success, non-0 on error (see cpdo_driver_register() for
    the return codes).
*/
int cpdo_driver_mysql5_register();

#if defined(__cplusplus)
} /*extern "C"*/
#endif
#endif /* WANDERINGHORSE_NET_CPDO_CPDO_MYSQL5_H_INCLUDED */

#endif /*CPDO_ENABLE_MYSQL5*/
/* end of file cpdo_amalgamation.h */
/* start of file include/wh/cpdo/cpdo.hpp */
#if !defined(WANDERINGHORSE_NET_CPDO_CPDO_HPP_H_INCLUDED)
#define WANDERINGHORSE_NET_CPDO_CPDO_HPP_H_INCLUDED
#include <stdexcept>
#include <string>

/**
    The cpdo namespace houses a C++ wrapper around the cpdo C API.
    The primary distinction between this API and the C API is that
    this one uses exceptions to report errors whereever doing so
    makes sense.
*/
namespace cpdo {
/** @def THROWS_ON_ERROR
Temporary (file-scope) macro to mark functions which throw on error.
*/
#define THROWS_ON_ERROR
    class statement;
    class driver;

    /**
        Exception class used by the cpdo API for all errors
        exception allocation errors, which are reported via
        std::bad_alloc (because reporting them via this class
        would require allocating memory to do so, and we
        presumably cannot do that on an allocation error).

        These objects are only created/thrown by driver and statement
        objects.
    */
    class exception : public std::exception
    {
        public:
        ~exception() throw() {}

        /**
            Returns this exception's message string.
        */
        virtual char const * what() const throw()
        { return this->msg.c_str(); }

        /**
            Returns the associated error code. If is_db_error() returns
            true then the error code is from a DB API, and its exact
            value depends on that driver's implementation. e.g. it might be
            a MySQL-specific doe. If is_db_error() returns false then this
            code will be one of the cpdo_rc codes.
        */
        int error_code() const throw()
        { return this->code; }

        /**
            Returns true if error_code()'s return value represents a
            db-driver-specific code, else the error_code() is assumed to
            be a cpdo_rc code.
        */
        bool is_db_error() const throw()
        { return this->is_db_err; }
        
        private:
            friend class statement;
            friend class driver;
            /**
                Extracts error information from drv and closes drv. Ownership
                of drv is passed to this object, and it is destroyed before the
                constructor returns.

                this->is_db_error() will return true if drv is not NULL, else
                it will return false.
            */
            exception( cpdo_driver * drv );
            //TODO?: exception( cpdo_stmt * st );
            exception( int code, bool isDbErr, std::string const & msg )
                : code(code), is_db_err(isDbErr), msg(msg)
            {}
            /**
                Assumes code is a cpdo_rc error code and builds a basic
                error string from it.
            */
            exception( int code );
            int code;
            bool is_db_err;
            std::string msg;
            
    };

    /**
        A simple wrapper around the cpdo_stmt C class.
        These objects can only be instantiated by using driver::prepare(),
        and each instance MUST be destroyed (using the delete operator)
        BEFORE its parent driver is destroyed, or undefined results will
        ensue. If a statement is destroyed after its underlying driver,
        a segfault is almost certain. If it is not destroyed, a leak is certain.
    */
    class statement
    {
        private:
            cpdo_stmt * st;
            friend class driver;
            //! Instantiated only via driver::prepare().
            statement( cpdo_stmt * );
            //! Not allowed/implemented.
            statement( statement const & );
            //! Not allowed/implemented.
            statement & operator=( statement const & );
            //! Throws if code is not 0.
            void check_code( int code );
            /**
                Throws if code ndx is out of range. If base is 1
                then BIND (1-based) indexes as assumed, else GET
                (0-based) are assumed.
            */
            void assert_index( uint16_t ndx, unsigned char base );
            /**
                Closes the underlying statement handle, but does not
                destroy this object. It is illegal to use any member
                functions of this object after calling this.
            */
            void finalize() throw();

            /**
                Throws if finalize() has been called.
            */
            void assert_alive() const  THROWS_ON_ERROR;
        public:
            ~statement() throw();

            /** Returns true for CPDO_STEP_ROW, false for CPDO_STEP_DONE,
                and throws on CPDO_STEP_ERROR.
            */
            bool step() THROWS_ON_ERROR;
            /**
                Returns the last driver-level error code, or 0 if there is none.
            */
            int error_code();
            
            /**
                Returns the last driver-level error message. If there was no
                recent error, this function _might_ return an empty string or
                _might_ return some other value, depending on how the underlying
                db driver does it (e.g. sqlite3 uses "not an error").
            */
            std::string error_text();

            /**
                Returns the number of bound parameter placeholders are in
                the prepared query.
            */  
            uint16_t param_count();

            /**
                Returns the 1-based BIND parameter for the given placeholder name,
                or 0 if no such parameter is found or on error (e.g. if the
                driver does not support named parameters).
            */
            uint16_t param_index( char const * name );

            /**
                Returns the name for the given 1-based BIND parameter
                index, throwing on error (e.g. out of bounds).
                Returns NULL if the driver reports no name for the
                given parameter.
            */
            char const * param_name( uint16_t ndx )  THROWS_ON_ERROR;

            /**
                Binds the NULL value to the given 1-based index.
                Throws if ndx is out of bounds.
            */
            void bind( uint16_t ndx ) THROWS_ON_ERROR;
            /**
                Binds the given value to the given 1-based index.
                Throws if ndx is out of bounds or if there is a driver-level
                error when binding the value.
            */
            void bind( uint16_t ndx, int8_t v ) THROWS_ON_ERROR;
            /**
                Binds the given value to the given 1-based index.
                Throws if ndx is out of bounds or if there is a driver-level
                error when binding the value.
            */
            void bind( uint16_t ndx, int16_t v ) THROWS_ON_ERROR;
            /**
                Binds the given value to the given 1-based index.
                Throws if ndx is out of bounds or if there is a driver-level
                error when binding the value.
            */
            void bind( uint16_t ndx, int32_t v ) THROWS_ON_ERROR;
            /**
                Binds the given value to the given 1-based index.
                Throws if ndx is out of bounds or if there is a driver-level
                error when binding the value.
            */
            void bind( uint16_t ndx, int64_t v ) THROWS_ON_ERROR;
            /**
                Binds the given value to the given 1-based index.
                Throws if ndx is out of bounds or if there is a driver-level
                error when binding the value.
            */
            void bind( uint16_t ndx, float v ) THROWS_ON_ERROR;
            /**
                Binds the given value to the given 1-based index.
                Throws if ndx is out of bounds or if there is a driver-level
                error when binding the value.
            */
            void bind( uint16_t ndx, double v ) THROWS_ON_ERROR;
            /**
                Binds the given value to the given 1-based index.
                Throws if ndx is out of bounds or if there is a driver-level
                error when binding the value.
            */
            void bind( uint16_t ndx, char const * v, uint32_t len ) THROWS_ON_ERROR;
            /**
                Binds the given value to the given 1-based index.
                Throws if ndx is out of bounds or if there is a driver-level
                error when binding the value.
            */
            void bind( uint16_t ndx, std::string const & v ) THROWS_ON_ERROR;
            /**
                Binds the given "blob" value to the given 1-based index.
                Throws if ndx is out of bounds or if there is a driver-level
                error when binding the value as a blob.
            */
            void bind( uint16_t ndx, void const * v, uint32_t len ) THROWS_ON_ERROR;

            /**
                Resets a statement to its pre-execution state so that it
                can be executed again. This is most often used between loop
                iterations when performing INSERT operations.
                See cpdo_stmt_api::reset().
            */
            void reset() THROWS_ON_ERROR;

            /**
                Returns the number of columns in the result set, or 0 for
                non-fetching queries or on error.                
            */
            uint16_t col_count();
            /**
                Returns the name of the column at the given index.
                Throws if ndx is out of bounds
                or there is a driver-level error while fetching the data.
                The returned bytes are owned by the underlying driver and may
                be invalidated on the next step() operation (or when the statement
                is freed), so they must be copied if needed for later.
                See cpdo_stmt_api::get::col_name().
            */
            char const * col_name( uint16_t ndx ) THROWS_ON_ERROR;
            /**
                See cpdo_stmt_api::get::type(). Throws if ndx is out of bounds.
            */
            cpdo_data_type col_type( uint16_t ndx ) THROWS_ON_ERROR;
            /**
                See cpdo_stmt_api::get::i8(). Throws if ndx is out of bounds
                or there is a driver-level error while fetching the data.
                NULL values translate to 0.
            */
            int8_t get_int8( uint16_t ndx ) THROWS_ON_ERROR;
            /**
                See cpdo_stmt_api::get::i16(). Throws if ndx is out of bounds
                or there is a driver-level error while fetching the data.
                NULL values translate to 0.
            */
            int16_t get_int16( uint16_t ndx ) THROWS_ON_ERROR;
            /**
                See cpdo_stmt_api::get::i32(). Throws if ndx is out of bounds
                or there is a driver-level error while fetching the data.
                NULL values translate to 0.
            */
            int32_t get_int32( uint16_t ndx ) THROWS_ON_ERROR;
            /**
                See cpdo_stmt_api::get::i64(). Throws if ndx is out of bounds
                or there is a driver-level error while fetching the data.
                NULL values translate to 0.
            */
            int64_t get_int64( uint16_t ndx ) THROWS_ON_ERROR;
            /**
                See cpdo_stmt_api::get::flt(). Throws if ndx is out of bounds
                or there is a driver-level error while fetching the data.
                NULL values translate to 0.
            */
            float get_float( uint16_t ndx ) THROWS_ON_ERROR;
            /**
                See cpdo_stmt_api::get::dbl(). Throws if ndx is out of bounds
                or there is a driver-level error while fetching the data.
                NULL values translate to 0.
            */
            double get_double( uint16_t ndx ) THROWS_ON_ERROR;
            /**
                See cpdo_stmt_api::get::string(). Throws if ndx is out of bounds
                or there is a driver-level error while fetching the data.
                If size is not NULL then the length of the fetched string
                is written to it.
            */
            char const * get_string( uint16_t ndx, uint32_t * size = NULL ) THROWS_ON_ERROR;

            /**
                Fetches blob data from the given 0-based column.
                A length-0 blob is returned as a NULL pointer.
                On success a pointer to the bytes is returned and
                *size is set to their length. size may be NULL,
                but if it is then the caller will have no way of
                knowing the length.
            */
            void const * get_blob( uint16_t ndx, uint32_t * size ) THROWS_ON_ERROR;

            /**
                Returns the underlying cpdo_stmt handle. The handle is owned
                by this object and MUST NOT be closed/destroyed by the caller,
                nor may it be used concurrently with this object (e.g.
                multi-threaded). This function is primarily provided so that the
                C++ API can be used with generic C routines which are not part
                of the cpdo_stmt_api interface.
            */
            cpdo_stmt * handle();
            
    };

    /**
        This convenience class is intended to be used similarly to
        std::auto_ptr to protect against leaks when a locally-created
        statement object throws an exception. It is recommended that
        client code use these objects in conjunction with the return
        values from driver::prepare() to simplify error handling in the
        case that using the prepared statement throws. Statements will
        be returned from a function, do not use this class or use its
        take() member to transfer ownership to the caller.

        These objects are intended to be created only on the stack, not via
        (new stmt).

        Example:

        @code
        stmt st( myDriver->prepare(...) );
        // Now use the '->' operator to access the statement's API, e.g.:
        while( st->step() ) { puts(st->get_string(0)); }
        // To take over ownership of the statement object:
        statement * s = st.take();
        @endcode
    */
    class stmt
    {
        private:
            statement * st;
            //! Not allowed/implemented.
            stmt(stmt const &);
            //! Not allowed/implemented.
            stmt & operator=(stmt const &);
        public:
            /**
                Empty-initializes this object. Use operator=()
                to assign a statement to it.
            */
            stmt();
            /**
                Transfers ownership of st to this object.

                If st is NULL then invoking operator->() will
                result in undefined behaviour. empty() can be used
                to check if the statement is NULL.
            */
            explicit stmt(statement * st);
            /**
                Destroys any existing statement and transfers
                ownership of st to this object.
            */
            stmt & operator=(statement * st);
            /**
                Destroys the statement owned by this object.
            */
            ~stmt();
            
            /**
                Destroys the statement owned by this object. This is
                automatically called during destruction, and need not
                normally be called by client code.
            */
            void finalize();
            
            /**
                Returns true if this object is "empty" (its statement
                is NULL).
            */
            bool empty() const;
            
            /**
                Returns the statement object owned by this object.
                Ownership
            */
            statement * operator->();
            
            /**
                Transfers ownership of the statement owned by
                this object to the caller. After calling this,
                empty() returns true and calling operator->() will
                result in undefined behaviour.
            */
            statement * take();
    };

    /**
        A simple wrapper around the cpdo_driver C class. Each instance of
        this class manages (and owns) one cpdo_driver instance.
    */
    class driver
    {
        private:
            cpdo_driver * drv;
            //! Throws if code is not 0.
            void check_code( int code ) THROWS_ON_ERROR;
            void assert_connected() const THROWS_ON_ERROR;
        public:
            /**
                Opens a connection to the given dsn using the rules
                described for cpdo_driver_new_connect().

                Throws if no driver can be loaded or connection fails.
            */
            driver( std::string const & dsn, std::string const & user = "",
                    std::string const & pass = "" ) THROWS_ON_ERROR;
            /**
                Transfers ownership of d to this object. Throws if d is
                not already connected. It keeps ownership (and closes d)
                even if it throws, to simplify client-side error handling.
            */
            driver( cpdo_driver * d ) THROWS_ON_ERROR;
            
            /**
                Closes the database connection and frees internal
                resources. statement objects created via prepare()
                MUST be destroyed BEFORE this object destructs,
                or undefined behaviour ensues.
            */
            ~driver() throw();
            
            
            /**
                Closes the database connection. It is illegal to do
                any of the following after calling this:
                
                - Call any member functions of this class. They will
                throw. The exception to that rule is that calling
                close() multiple times is a no-op after the first
                call.
                
                - Destroy any statements created by prepare(). They
                must be destroyed before the connection is closed or
                not at all. Violating that will likely lead to a
                segmentation fault.
            */ 
            void close() throw();
            
            /**
                Works like cpdo_prepare(). Ownership of the returned statement
                is transfered to the caller, and it MUST be destroyed before
                this object closed/destroyed or undefined behaviour will result.

                Throws if sql is NULL or an empty string, or if preparation
                of the statement fails.

                It is recommended that clients use the stmt convenience class
                for catching the return result, to simplify error handling
                if the returned statement subsequently throws an exception.
            */
            statement * prepare( char const * sql, uint32_t len ) THROWS_ON_ERROR;

            /**
                Convenience form of prepare(sql,strlen(sql)).
            */
            statement * prepare( char const * sql ) THROWS_ON_ERROR;

            /**
                Convenience form of prepare(sql.c_str(),sql.size()).
            */
            statement * prepare( std::string const & sql ) THROWS_ON_ERROR;

            /**
                Works like cpdo_prepare_f(), but throws on error.
                See the two-argument form of prepare() for details about
                the return value.
            */
            statement * prepare_f( char const * fmt, ... ) THROWS_ON_ERROR;
            
            /**
                Returns the SQL-quoted form of the given SQL "part". It is
                NOT intended to be used on whole SQL statements, but on
                individual values. See cpdo_driver_api::quote() for details,
                but note that the ownership of the string, as documented
                in that interface, is instead transfered to the returned
                std::string object.

                Throws on error, but the only error case would be an allocation.
            */
            std::string quote( std::string const & part ) THROWS_ON_ERROR;
            /**
                Returns the last driver-level error code, or 0 if there is none.
            */
            int error_code();
            
            /**
                Returns the last driver-level error message. If there was no
                recent error, this function _might_ return an empty string or
                _might_ return some other value, depending on how the underlying
                db driver does it (e.g. sqlite3 uses "not an error").
            */
            std::string error_text();
            
            /**
                Returns the most recent insertion ID, as documented for
                cpdo_driver_api::last_insert_id().

                Throws on error.
            */
            uint64_t last_insert_id( char const * hint = NULL ) THROWS_ON_ERROR;
            /**
                Begins a transaction, as documented for cpdo_driver_api::transaction::begin().

                Throws on error.
            */
            void begin() THROWS_ON_ERROR;
            /**
                Begins a transaction, as documented for cpdo_driver_api::transaction::commit().

                Throws on error.
            */
            void commit() THROWS_ON_ERROR;
            /**
                Begins a transaction, as documented for cpdo_driver_api::transaction::rollback().

                Throws on error.
            */
            void rollback() THROWS_ON_ERROR;
            /**
                As documented for cpdo_driver_api::transaction::is_in(). See
                that function for important caveats.
            */
            bool in_transaction();
            /**
                Returns the cpdo driver name for the current connection. The bytes
                are owned by the underying driver, and may be invalidated when
                it is closed (or they may not - it's implementation-defined).
            */
            char const * driver_name() const;
            /**
                Returns the character which should be used to quote table names
                in SQL strings. The library does not enforce this, but requests
                that clients honor it. This is almost always a backtick.
            */
            char table_quote_char() const;
            
            /**
                Returns the character which should be used to quote SQL string
                values. The library does not enforce this, but requests
                that clients honor it. This is almost always a single-quote.
                
                Reminder to self: this "should" be const, but to do that
                we would need to make the underlying driver handle mutable.
            */
            char string_quote_char();

            /**
                Returns the underlying cpdo_driver handle. The handle is owned
                by this object and MUST NOT be closed/destroyed by the caller,
                nor may it be used concurrently with this object (e.g.
                multi-threaded). This function is primarily provided so that the
                C++ API can be used with generic C routines which are not part
                of the cpdo_driver_api interface.
            */
            cpdo_driver * handle();
            
            /**
                Equivalent to cpdo_exec(), but throws on error.
            */
            void exec( char const * sql, uint32_t len );
            
            /**
                Convenience form of exec() which takes a std::string.
            */
            void exec( std::string const & sql );
            
            /**
                Equivalent to cpdo_exec_f(), but throws on error.
            */
            void exec_f( char const * fmt, ... );
    };
#undef THROWS_ON_ERROR
}
#endif /* WANDERINGHORSE_NET_CPDO_CPDO_HPP_H_INCLUDED */
/* end of file include/wh/cpdo/cpdo.hpp */
