/* auto-generated on Fri Aug 26 20:59:39 CEST 2011. Do not edit! */
#if !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200112L /* needed for ftello() and friends */
#endif
/* begin file include/wh/whprintf.h */
#ifndef WANDERINGHORSE_NET_WHPRINTF_H_INCLUDED
#define WANDERINGHORSE_NET_WHPRINTF_H_INCLUDED 1
#include <stdarg.h>
#include <stdio.h> /* FILE handle */
#ifdef __cplusplus
extern "C" {
#endif
/** @page whprintf_page_main whprintf printf-like API

   This API contains a printf-like implementation which supports
   aribtrary data destinations.

   Authors: many, probably. This code supposedly goes back to the
   early 1980's.

   Current maintainer: Stephan Beal (http://wanderinghorse.net/home/stephan)

   License: Public Domain.

   The primary functions of interest are whprintfv() and whprintf(), which works
   similarly to printf() except that they take a callback function which they
   use to send the generated output to arbitrary destinations. e.g. one can
   supply a callback to output formatted text to a UI widget or a C++ stream
   object.
*/

/**
   @typedef long (*whprintf_appender)( void * arg, char const * data, long n )


   The whprintf_appender typedef is used to provide whprintfv()
   with a flexible output routine, so that it can be easily
   send its output to arbitrary targets.

   The policies which implementations need to follow are:

   - arg is an implementation-specific pointer (may be 0) which is
   passed to whprintf(). whprintfv() doesn't know what this argument is
   but passes it to its whprintf_appender. Typically it will be an
   object or resource handle to which string data is pushed or output.

   - The 'data' parameter is the data to append. If it contains
   embedded nulls, this function will stop at the first one. Thus
   it is not binary-safe.

   - n is the number of bytes to read from data. If n<0 then
   strlen(data) should be used.

   - Returns, on success, the number of bytes appended (may be 0).

   - Returns, on error, an implementation-specified negative number.
   Returning a negative error code will cause whprintfv() to stop the
   processing of that string. Note that 0 is a success value (some
   printf format specifiers do not add anything to the output).
*/
typedef long (*whprintf_appender)( void * arg,
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

 pfAppend : The is a whprintf_appender function which is responsible
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

 %%z works like %%s, but takes a non-const (char *) and whprintf()
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
 compiling whprintf.c (see that file for details).
*/
long whprintfv(
  whprintf_appender pfAppend,          /* Accumulate results here */
  void * pfAppendArg,                /* Passed as first arg to pfAppend. */
  const char *fmt,                   /* Format string */
  va_list ap                         /* arguments */
  );

/**
   Identical to whprintfv() but takes a (...) ellipses list instead of a
   va_list.
*/
long whprintf(whprintf_appender pfAppend,
	     void * pfAppendArg,
	     const char *fmt,
	     ... );

/**
   Emulates fprintf() using whprintfv().
*/
long whprintf_file( FILE * fp, char const * fmt, ... );


/**
   Works like whprintfv(), but appends all output to a
   dynamically-allocated string, expanding the string as necessary to
   collect all formatted data. The returned null-terminated string is
   owned by the caller and it must be cleaned up using free(). If !fmt
   or if the expanded string evaluates to empty, null is returned, not
   a 0-byte string.
*/
char * whprintfv_str( char const * fmt, va_list vargs );

/**
   Equivalent to whprintfv_str(), but takes elipsis arguments instead
   of a va_list.
*/
char * whprintf_str( char const * fmt, ... );

#ifdef __cplusplus
} /* extern "C" */
#endif
#endif /* WANDERINGHORSE_NET_WHPRINTF_H_INCLUDED */
/* end file include/wh/whprintf.h */
/* begin file include/wh/whalloc_amalgamation.h */
/* auto-generated on Tue Aug 23 09:55:32 CEST 2011. Do not edit! */
#define WHALLOC_AMALGAMATION_BUILD 1
#if ! defined __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS 1
#endif
#if defined(__cplusplus) && !defined(restrict)
#define restrict
#endif
/* begin file whalloc_namespace.h */
#ifndef WANDERINGHORSE_NET_WHALLOC_NAMESPACE_H_INCLUDED
#define WANDERINGHORSE_NET_WHALLOC_NAMESPACE_H_INCLUDED 1
/** @def WHALLOC_API

    WHALLOC_API must be a macro taking a single token which is suitable
    as part of a function or type name. It is used to construct the
    type/function names used by this API because i have several use cases
    in mind where i want to compile different variants with different
    names.

    The use of this construct is probably going to confuse doxygen :/.
    To filter the API while doxygen is processing it, add this line to
    your Doxyfile:

    @code
    INPUT_FILTER = "perl -pe 's|WHALLOC_API\(([^)]+)\)|TOKEN_$1|g;'"
    @endcode

    Where "TOKEN_" is the prefix defined by this macro.
    
*/
#define WHALLOC_API(X) whalloc_ ## X

#endif /* WANDERINGHORSE_NET_WHALLOC_NAMESPACE_H_INCLUDED */
/* end file whalloc_namespace.h */
/* begin file whalloc.h */
#ifndef WANDERINGHORSE_NET_WHALLOC_POOL_H_INCLUDED
#define WANDERINGHORSE_NET_WHALLOC_POOL_H_INCLUDED 1

#if defined(__cplusplus) &&  !defined(__STDC_FORMAT_MACROS)
#  define __STDC_FORMAT_MACROS /* used by C++ for enabling PRIxNN defines. */
#endif


#include <stdint.h> /* fixed-size int types. */
#include <stdio.h> /* FILE*/
#include <inttypes.h> /* PRIxNN printf-specifier macros for the standard int types. */
#ifdef __cplusplus
extern "C" {
#endif
    /** @page whalloc_page_main whalloc memory allocation API

    The whalloc API is home to several "alternative memory allocators"
    for C. That is, it provides functions similar to malloc() and
    free(), but which use a client-provided memory range for all
    allocations. It is particularly intended to be used for routines
    which need to allocate lots of small objects, but where calling
    malloc() dozens (or hundreds) of times is not appropriate.

    It was originally based off of code found here:

    http://pastebin.com/f207f6232

    which was PRESUMABLY originally written by Chris M. Thomasson, as his
    name was on the pastebin.com post and the code had no credits.

    This variant was written by Stephan Beal
    (http://wanderinghorse.net/home/stephan), with input from Amir
    "Ashran" Mohammadkhani (http://modme.info), and has been extended
    in many ways (see below).

    License: This code is Public Domain in jurisdictions which
    acknowledge Public Domain property. For other jurisdictions it is
    released under the terms of the MIT Licenses (which is about as
    close to Public Domain as a license can get). The MIT License is
    compatible with the GPL and with commercial licenses.

    The more signiciant classes are:

    - WHALLOC_API(bt): an almost-general-purpose allocator,
    particularly useful for apps which want to place a hard cap on the
    amount of memory they can allocate.

    - WHALLOC_API(page) and WHALLOC_API(book): special-purpose
    allocators for doling out memory blocks of a fixed size and
    re-using deallocated objects.

    The WHALLOC_API(ht) class, prevelantly seen in the API docs, is
    considered obsoleted by the WHALLOC_API(bt) class, and might be
    removed from this API.
    */

    /** @page whalloc_page_portability whalloc Portability Notes


    Code Portability:

    The core whalloc library (not necessarily the test code) compiles
    cleaning in either C89/C90 or C99 modes, but it requires the
    C99-standard stdint.h and inttypes.h headers for the standard
    fixed-size integers and their corresponding standardized printf
    format specifiers. If those are not available, the user will have
    to hack a bit to remove the offending headers and provide
    equivalent typedefs. Much of this code relies in part on
    fixed-sized integer types.

    Memory Alignment:

    Most of the API does not do anything special to support "proper"
    alignment of memory allocated via this API. This may prove
    problematic on platforms which care about objects being aligned on
    some boundary.

    The following API members provide at least some way to guaranty a
    specific alignment:

    - See WHALLOC_API(bt_init)() for how to initialize a WHALLOC_API(bt)
    such that it always returns properly aligned pointers.

    - The WHALLOC_API(region) _can_ provide alignment guarantees IF
    the client initializes it using a properly aligned buffer AND all
    allocations are of a size which is a multiple of the platform's
    alignment.
    */
    
    /** @def WHALLOC_BITNESS

        WHALLOC_BITNESS must be set to one of 8, 16, or 32. It
        determines the overall memory layout. 16 bits is a good
        trade-off for space efficiency in the internal tables.
    */

    /** @def WHALLOC_BITNESS_OVERRIDE

        WHALLOC_BITNESS_OVERRIDE is an internal-use only macro to
        allow us to build seperate bitnesses of the library for
        testing purpose without changing this file. It should NOT be
        used by clients unless they are rebuilding this library along
        with their application/library build.
    */

  /** @def WHALLOC_MASK

      WHALLOC_MASK must be a bitmask where the right-most
      WHALLOC_BITNESS bits are on and all other bits (if there are
      more bits) are off. This is used by some of the allocators
      in constructing hashing masks.
   */

  /** @def WHALLOC_SIZE_T_PFMT

      WHALLOC_SIZE_T_PFMT is the equivalent of one of the standard
      PRIuNNN macros from <inttypes.h>, where NNN is the same as
      WHALLOC_BITNESS. It should be used instead of a hard-coded
      specifier in printf-like strings so that the code will compile
      cleanly on machines with different word sizes. e.g.  do not use
      percent-u directly, use this instead. If you do not, compilation
      in certain environments will warn about the width of the type
      vis-a-vis the expected format specifier. Particularly
      problematic in this regard are size_t objects, as size_t does
      not have a fixed size - a format specifier which compiles
      cleanly on 32-bit machines might fail loudly on 64-bit machines
      (and vice versa). Thus the fixed-size integers (and their
      standard format specifier macros) should generally be preferred
      over size_t (and other non-fixed-size integer types).
   */
#if defined(WHALLOC_BITNESS_OVERRIDE)
#    define WHALLOC_BITNESS (WHALLOC_BITNESS_OVERRIDE)
#else
#    define WHALLOC_BITNESS_OVERRIDE 0 /* only to keep doxygen happy. */
#    define WHALLOC_BITNESS 16
#endif
#if 8 == WHALLOC_BITNESS
    typedef uint8_t WHALLOC_API(size_t);
#   define WHALLOC_MASK 0x00ff
#   define WHALLOC_SIZE_T_PFMT PRIu8
#elif 16 == WHALLOC_BITNESS
    typedef uint16_t WHALLOC_API(size_t);
#   define WHALLOC_MASK 0x0000ffff
#   define WHALLOC_SIZE_T_PFMT PRIu16
#elif 32 == WHALLOC_BITNESS
    typedef uint32_t WHALLOC_API(size_t);
#   define WHALLOC_MASK 0xffffffff
#   define WHALLOC_SIZE_T_PFMT PRIu32
#elif 64 == WHALLOC_BITNESS
    typedef uint64_t WHALLOC_API(size_t);
#   define WHALLOC_MASK ((WHALLOC_API(size_t))0xffffffffffffffff)
#   define WHALLOC_SIZE_T_PFMT PRIu64
#else
#  error "WHALLOC_BITNESS must be one of (8,16,32)!"
#endif
    /**
       Routines in this API which return an int value will almost
       always return a value described in terms of this type's
       members. They are accessed via the WHALLOC_API(rc) object.

       All
       of them have unique, but unspecified, non-zero values except:

       -  OK must be 0.

       - HashCodeError is ((WHALLOC_API(size_t))-1).

       - None of the integer members may have the value -1, to allow
       us to distinguish error codes from some system-level routines
       which return -1 and update errno on error.
    */
    struct WHALLOC_API(rc_t)
    {
        /** Always == 0. */
        int OK;
        /** Signals that some value was out of range. */
        int RangeError;
        /** Signals that an argument was of an unexpected value. */
        int ArgError;
        /** Signals that an internal error was found. */
        int InternalError;
        /** Signals an error related to the internal hashtable. */
        int HashingError;
        /** Signals a resource allocation error. */
        int AllocError;
        /** Signals a usage error. */
        int UsageError;
        /** Signals that some sort of data or state consistency
            problem was discovered. */
        int ConsistencyError;
        /** Signals that some form of mutex un/locking error was encountered.*/
        int LockingError;

        /** Always == ((WHALLOC_API(size_t))-1), but the *exact* value of
            -1 differs depending on the size of WHALLOC_API(size_t).
        */
        WHALLOC_API(size_t) HashCodeError;
    };
    typedef struct WHALLOC_API(rc_t) WHALLOC_API(rc_t);
    /**
       Functions in the whalloc API which return an integer
       error code will return one of the values defined in
       WHALLOC_API(rc_t). Clients can use this object to get
       those values.
    */
    extern const WHALLOC_API(rc_t) WHALLOC_API(rc);

    /**
       A mutex class used by some allocator classes.

       To activate the mutex for a class which contains one of these
       object, assign all of the members to appropriate values.
       You must either set neither or both of the lock() and unlock()
       members. The state member may be null if the lock/unlock functions
       do not use it.
    */
    struct WHALLOC_API(mutex)
    {
        /**
           Intended to lock a mutex. This interface does not require
           that it be a recursive lock, but it may need to be so if
           the client uses the same mutex for outer-level locking
           regarding a given allocator. It is passed the state member
           as its only parameter.

           Must return 0 on success, non-zero on error.

           API routines for allocators which support a mutex should
           return an error code if the mutex cannot be locked.
        */
        int (*lock)( void * );
        /**
           Intended to unlock the mutex locked by lock(). It is passed
           the state member as its only parameter.

           If lock is non-null then unluck must also be non-null and
           complementary to the lock function.

           Must return 0 on success, non-zero on error.
           
           BUGS: most (or all) of the allocator code ignores the
           return code from the unlock routine because they cannot
           sensibly "undo" the result of a re/de/allocation if
           unlocking fails.
        */
        int (*unlock)( void * );
        /** Arbitrary state data which should be passed to lock() and unlock(),
            e.g. a platform-specific mutex type.
        */
        void * state;
    };
    typedef struct WHALLOC_API(mutex) WHALLOC_API(mutex);

    /**
       An empty WHALLOC_API(mutex) initialization object.
    */
    extern const WHALLOC_API(mutex) WHALLOC_API(mutex_empty);

    /** @def whalloc_mutex_empty_m

       An empty WHALLOC_API(mutex) initialization object, for use when
       static allocation is necessary.
    */
#define whalloc_mutex_empty_m {0/*lock*/,0/*unlock*/,0/*data*/}

    /**
       WHALLOC_API(realloc_f) is a typedef for de/re/allocation
       routines semantically compatible with realloc(), but with the
       addition of a third parameter which can be used to pass
       allocator-specific state.

       This interface is used for allocating memory for use by the
       WHALLOC_API(page) and WHALLOC_API(book) classes. The intention
       is to allow clients to use their own allocators to de/allocate
       WHALLOC_API(page) and WHALLOC_API(book) objects.

       The allocState parameter should hold any state needed for the
       custom de/re/allocation algorithm. Ownership of that state object
       is completely dependent on the allocator and its rules, but it is
       typically a pointer to an allocator object with arbitrary
       allocator-internal data (e.g. a WHALLOC_API(bt) object, but any
       custom allocator which can support the overall realloc(3)
       interface/semantics would suffice).

       By default, most of the API which uses this type has a default
       implementation which simply forwards all calls to realloc(3)
       and ignores the third argument.

       An interesting ACHTUNG: realloc( someObject, 0 ) is apparently not
       guaranteed to return NULL, but may also return "some value suitable
       for passing to free()." Thus it is philosophically impossible to
       know if realloc(obj,0) ever really succeeds in freeing the memory
       because we have no constant to compare the return value against
       except NULL. Anyway... just something to be aware of.

       Rules for implementations:

       1) If passed (NULL,non-0,anything) they must behave like a malloc()
       request.

       2) If passed (anything,0,anything) they must behave like free()
       and return void. It may legally assert() (or similar) if passed
       memory it does not own/manage (this is common behaviour in
       standard free(3) implementations).

       3) If passed (non-NULL,non-0,anything), they have the following
       options:

       3a) If they support a realloc operation, it must be
       semantically compatible with realloc(3). That implies that
       conditions (1) and (2) are met.

       3b) If they do not support a realloc operation, they have two
       options:

       3b1) If the allocator knows that the new size does not require
       moving the memory (i.e. is equal to or smaller than the
       original size, or does not grow enough to move it into a new
       memory block), it may legally return the original pointer.

       3b2) Return NULL (failing the realloc).

       Provided that the third argument (allocState) is ignored,
       realloc(3) is considered a compliant implementation (indeed, it
       is the reference implementation) for all operations, meeting
       requirements 1, 2, and 3a.
    */
    typedef void * (*WHALLOC_API(realloc_f))( void * m, unsigned int n, void * allocState );

    /**
       An abstract interface for a class containing data for use
       with the WHALLOC_API(realloc_f)() interface.
    */
    struct WHALLOC_API(allocator)
    {
        /**
           The de/re/allocator function. Must conform to the
           WHALLOC_API(realloc_f)() interface specifications.
        */
        WHALLOC_API(realloc_f) realloc;
        /**
           State data for the realloc member, passed as the third
           argument to that function.
        */
        void * state;
    };
    /** Convenience typedef. */
    typedef struct WHALLOC_API(allocator) WHALLOC_API(allocator);

    /** A WHALLOC_API(allocator) object which is initialized to use
        realloc(3) as its memory source.
    */
    extern const WHALLOC_API(allocator) WHALLOC_API(allocator_realloc3);
    /**
       An empty-initialized WHALLOC_API(allocator) object.
    */
    extern const WHALLOC_API(allocator) WHALLOC_API(allocator_empty);

    /** @def whalloc_allocator_empty_m
        
       An empty WHALLOC_API(allocator) initialization object, for use
       when static allocation is necessary.
    */
#define whalloc_allocator_empty_m {NULL/*realloc*/,NULL/*reallocState*/}

    /** @deprecated The WHALLOC_API(bt) API is preferred.

       Metadata for a single WHALLOC_API(ht) entry.
    */
    struct WHALLOC_API(ht_entry)
    {
        /**
           Length of the record ((WHALLOC_BITNESS-1) low bits) plus 1
           is-used flag bit (the high bit).
        */
        WHALLOC_API(size_t) lenfl;
    };
    typedef struct WHALLOC_API(ht_entry) WHALLOC_API(ht_entry);

    /**
       An empty WHALLOC_API(ht_entry) initialization object.
    */
    extern const WHALLOC_API(ht_entry) WHALLOC_API(ht_entry_empty);

    /** @def whalloc_ht_entry_empty_m
       An empty WHALLOC_API(ht_entry) initialization object.
    */
#define whalloc_ht_entry_empty_m { 0/*lenfl*/ }

    /**
       WHALLOC_API(log_f)() is a printf()-compatible print function
       intended only for debugging purposes.
    */
    typedef int (*WHALLOC_API(log_f))( char const * fmt, ... );

    /** @deprecated The WHALLOC_API(allocator) interface is more flexible.

        This class abstracts "fallback allocators" for the
        WHALLOC_API(ht) and WHALLOC_API(bt) classes.

        TODO: remove this interface in favour of the
        WHALLOC_API(allocator) interface.
    */
    struct WHALLOC_API(fallback)
    {
        /** A allocation routine which should allocate n bytes and
            return a pointer to the first one, or NULL on error.

            Must be semantically compatible with realloc(3).

            Remember that realloc(NULL,n) behaves like malloc(n) and
            that realloc(ptr,0) behaves like free().
        */
        void * (*realloc)( void *, size_t  n );
        /**
           Must be semantically compatible with free(3) and be
           complementary to the alloc member.

           This member WILL GO AWAY once WHALLOC_API(ht_realloc)() is
           implemented, since free() can be implemented in terms of
           realloc().
        */
        void (*free)();
    };
    /** Convenience typedef. */
    typedef struct WHALLOC_API(fallback) WHALLOC_API(fallback);
    /**
       An empty WHALLOC_API(fallback) object for use in static
       initialization.
    */
#define whalloc_fallback_empty_m {0/*alloc*/,0/*free*/}
    /** An initialization WHALLOC_API(fallback) object which uses the C-standard
        malloc() and free.
    */
    extern const WHALLOC_API(fallback) WHALLOC_API(fallback_stdalloc);
    /** An initialization object for an empty WHALLOC_API(fallback). */
    extern const WHALLOC_API(fallback) WHALLOC_API(fallback_empty);

    /**
       A helper type which consolidates data required by some concrete
       allocator implementations. See WHALLOC_API(ht) and
       WHALLOC_API(bt) for classes which use this.
    */
    struct WHALLOC_API(allocator_base)
    {
        /** The start of the managed memory range. */
        unsigned char * mem;
        /** One-past-the-end of the managed memory range.
            That is, (mem+size).
        */
        unsigned char const * end;
        /**
           A pointer somewhere between [mem,end) which refers to the
           start of the memory which can be used for actual
           allocations, as opposed to allocator-internal data.
        */
        unsigned char * uspace;
        /** The size of the managed memory range, in bytes. */
        WHALLOC_API(size_t) size;
        /** The "usable" size of the managed memory range, in
            bytes. "Unusuable" space is used for the allocator's
            internals.
         */
        WHALLOC_API(size_t) usize;
        /** The block size used for partitioning memory. */
        WHALLOC_API(size_t) blockSize;
        /** The maximum number of items the pool can managed.
            This is a function of (size/blockSize), adjusted for
            memory taken up by the allocator.
        */
        WHALLOC_API(size_t) blockCount;
        /**
           A bitmask where the bitCount-most right values are set and
           all others are unset.
        */
        WHALLOC_API(size_t) hashMask;
        /**
           The number of active allocations. This is incremented
           on alloc() and decremented on free().
         */
        WHALLOC_API(size_t) allocCount;
        /**
           The number of blocks used by active allocations. This is
           incremented on alloc() and decremented on free().
         */
        WHALLOC_API(size_t) allocBlockCount;
        /**
           A hint to the allocator about where the next free
           memory might be. The value is an index into its
           internal table (i.e. a memory block ID).
        */
        WHALLOC_API(size_t) freeIndexHint;
        /**
           Allocators may optionally store their last error
           code here.
        */
        int errorCode;
        /** The number of bits needed for creating a minimal hashcode
            for doing memory-to-index mapping.  This is function of
            the maximum item count, and should be set to the N, where
            2^N is the smallest power of 2 necessary for holding the
            number in blockCount.

            This number is, not incidentally, the number of bits set
            in the hashMask member.
        */
        uint8_t bitCount;
        /**
           Optional mutex which can be configured by the client.  The
           allocator API will use this mutex if it is set, otherwise
           it does no locking.
        */
        WHALLOC_API(mutex) mutex;

        /**
           Optional memory allocation routines which may be supplied
           by the caller.

           If allocation cannot work and fallback.alloc is set, that
           function will be used to fetch the memory.  When memory is
           passed to the pool's free() routine and it is outside the
           range associated with the pool, if fallback.free is set
           then it is called to free the memory.

           If alloc is set then free MUST be set, or an assertion
           may be triggered in functions which use the fallback
           allocator.

           TODO: replace this with WHALLOC_API(allocator).
        */
        WHALLOC_API(fallback) fallback;
        /**
           Optional logging/debugging function. Set this to non-null
           to intercept (potentially lots of) debugging messages.
           This is typically only enabled if the library is built
           in debugging mode (i.e. NDEBUG is not defined).

           TODO: make this an object with a callback function and a
           state pointer.
        */
        WHALLOC_API(log_f) log;
    };
    /** Convenience typedef. */
    typedef struct WHALLOC_API(allocator_base) WHALLOC_API(allocator_base);
    /** Empty WHALLOC_API(allocator_base) initialization object. */
#define whalloc_allocator_base_empty_m {\
        0/*mem*/,                               \
            0/*end*/,                           \
            0/*uspace*/,                        \
            0/*size*/,                          \
            0/*usize*/,                         \
            8/*blockSize*/,                     \
            0/*blockCount*/,                      \
            0/*hashMask*/,                        \
            0/*allocCount*/,                      \
            0/*allocBlockCount*/,                 \
            0/*errorCode*/,                       \
            0/*bitCount*/,                        \
            0/*freeIndexHint*/,                   \
            whalloc_mutex_empty_m,                \
            whalloc_fallback_empty_m,           \
            0/*log*/                 \
    }
    /** Empty WHALLOC_API(allocator_base) initialization object. */
    extern const WHALLOC_API(allocator_base) WHALLOC_API(allocator_base_empty);
    /** @deprecated The WHALLOC_API(bt) API is preferred.

       A holder for allocator data for use with WHALLOC_API(ht_alloc)() and
       WHALLOC_API(ht_free)().  They can be created on the stack or with
       malloc(), but must be initialized with WHALLOC_API(ht_init)()
       before they are used.

       This class is not thread-safe by default. To enable locking,
       the client must setup the mutex member to use his lock/unlock
       routines of choice.

       Performance: for the average cases, if the allocation size is
       less than or equal to the pool's block size, this allocator
       performs O(1) for both allocation and deallocation. For certain
       usage patterns it would worst-case at near O(N), but that would
       require that one fills the whole list, deallocates the first
       and last items (in any order), then allocate two more
       items. Only that last allocation would be O(N). The others
       would be O(1) (or very, very close to it). When allocating
       larger than a single block, there are linear components. We
       have to check for a free range, and that requires traversing at
       least N hashtable records, where N is the number of blocks
       we're traversing. If the block span is not free, we have to
       search further, making this a relatively expensive operation
       compared to single-block allocations.

       This API can map no more than 2^WHALLOC_BITNESS bytes in one
       allocator, and no single allocation from an allocator can be
       more than (2^(WHALLOC_BITNESS-1)) bytes.
       
    */
    struct WHALLOC_API(ht)
    {
        /** Holds the "base-most" allocator data, which is common to multiple allocator
            implementations. */
        WHALLOC_API(allocator_base) base;
        /**
           Hashtable (lives within mem, before uspace).
        */
        struct Hashtable
        {
            /**
               Points to space somewhere in WHALLOC_API(ht)::mem.

               Will hold 'len' elements, but only [0,end) are valid.
            */
            WHALLOC_API(ht_entry) * head;
            /** The real number of entries in the hashtable. The hashtable
                might have more allocated space than are used. */
            WHALLOC_API(size_t) len;
            /** The size of the hashtable data, in bytes. */
            WHALLOC_API(size_t) sizeOf;
            /**
               Index of one-after-the-end entry.  This is also
               incidentally the true capacity of this object, and may
               actually be smaller than len.
            */
            WHALLOC_API(size_t) end;
        } ht;
    };
    typedef struct WHALLOC_API(ht) WHALLOC_API(ht);
    /**
       An empty WHALLOC_API(ht) initialialization object.
    */
    extern const WHALLOC_API(ht) WHALLOC_API(ht_empty);
    /** @def whalloc_ht_empty_m
       An empty WHALLOC_API(ht) initialialization object.
    */
#define whalloc_ht_empty_m {                                          \
        whalloc_allocator_base_empty_m, \
            {/*ht*/ 0/*head*/,0/*len*/,0/*sizeOf*/,0/*endHash*/} \
        }

    

    /** @deprecated The WHALLOC_API(bt) API is preferred.
       Initializes a WHALLOC_API(ht) for use, such that it can be used to
       "allocate" memory from a user-defined memory range. The
       intention is to save on calls to malloc() by using
       stack-allocated memory as an allocation source.

       self must be an empty object, e.g. created on the stack and
       assigned from the WHALLOC_API(ht_empty) initializer object.

       buffer is memory which will be used as storage by this allocator.

       size is the number of bytes in the buffer argument. If it is
       not a multiple of 2, it will be reduced by one for purposes of
       memory management. It must also fall within certain bounds: a
       minimum of 128 (arbitrarily chosen) and 2^(WHALLOC_BITNESS).

       blockSize is the size of each data page within the memory
       pool. Any allocation will "allocate" at least this many bytes
       internally. blockSize must be 2 or higher for this
       implementation, since the overhead for tracking size-1 blocks
       is so uselessly high.

       Some of the given buffer memory will be used for the internal
       allocation metadata, and thus the buffer will effectively
       become smaller than when the user passed it in. Host much
       smaller is a function of how long it is and the block size.  A
       high blockSize requires a smaller internal hashtable, and a
       small value will waste more space. Values of
       sizeof(WHALLOC_API(ht_entry)) or less won't work well. Values of 8
       or higher work fairly efficiently in terms of space management.

       It is not legal to manipulate the buffer as long as self is
       associated with it, except via pointers returned from
       WHALLOC_API(ht_alloc)().
   
       Returns WHALLOC_API(rc).OK on success. On error, one of the other
       integer values from WHALLOC_API(rc).

       When finished with the self object, call WHALLOC_API(ht_drain)() to
       wipe it clean (or just let it go out of scope). You can also call
       WHALLOC_API(ht_free)() to free individual elements, making their
       memory immediadately available for re-use.

       The buffer parameter is owned by the caller, but it must outlive
       self, and its memory position must not change (e.g. via realloc)
       during self's lifetime.

       After calling this, the client may assign self->mutex,
       self->log, and/or self->fallback to his preferred
       implementations. The mutex and fallback members must not be
       changed during self's lifetime, however. Doing so engenders
       Undefined Behaviour. The log can be set at will, as long as one
       locks the mutex (if set) before doing so. If the log member is
       set before calling this, error messages from the initialization
       process will be logged through it.

       After this call is complete, client code must never change any
       properties of self other than noted above. Doing so may corrupt
       the state of the allocator and lead to undefined behaviour. It
       is okay to read, but don't write.

       The maximum number of items which the pool will be able to allocate
       is calculated based on the size and blockSize.
       
       Example usage:

       @code
       WHALLOC_API(ht) pool = WHALLOC_API(ht_empty);
       enum { BufLen = 1024 * 8 };
       unsigned char buffer[BufLen];
       WHALLOC_API(size_t) blockSize = sizeof(my_type);
       int rc = WHALLOC_API(ht_init)(&pool, buffer, BufLen, blockSize );
       if( WHALLOC_API(rc).OK != rc ) { ... error ... }
       my_type * m = WHALLOC_API(ht_alloc)(&pool, sizeof(my_type));
       // ^^^ m now lives somewhere inside of buffer
       @endcode

       Design notes:

       Despite all the talk of "allocation" in these docs, this API uses no
       dynamic memory allocation. It does, however, abstractly allocate
       memory via a reserved memory area.

       The init routine double-checks its hashtable creation process
       to ensure that all hashcodes it generates are unique and that
       it does not generate too many (which would cause us to step out
       of bounds later on). Because of this consistency checking (A)
       subsequent operations can skimp on range checking (making them
       faster) and (B) the initialization is basically O(N), where N
       is the number of blocks.
       
       When WHALLOC_BITNESS is 16, this routine can (quite by happy
       accident) create a near-optimal hashtable for storing allocation
       metadata, without wasting much memory for small block sizes
       <4). The heuristics for 8- and 32-bit builds are not as optimized,
       but also don't waste too much.

       WHALLOC_API(ht_init)() is the only one of the public WHALLOC_API(ht) family of
       functions which does not check for self->base.mutex.lock. If the object
       must be locked for the initialization, it needs to be locked from
       the client code.
   
       @see WHALLOC_API(ht_alloc)()
       @see WHALLOC_API(ht_free)()
       @see WHALLOC_API(ht_drain)()
    */
    int WHALLOC_API(ht_init)( WHALLOC_API(ht) * const self, void* buffer, WHALLOC_API(size_t) size, WHALLOC_API(size_t) blockSize );

    /** @deprecated
       Tries to allocate an object of the given size from self's
       memory.

       On success a pointer is returned, owned by self. It may be freed
       using WHALLOC_API(ht_free)() or WHALLOC_API(ht_drain)(). That said, if
       the memory used by self is stack-allocated, and one never uses up
       the memory in the allocator, it is not necessary to clean it up -
       stack deallocation will do it when self goes out of scope.

       If size is zero, self->blockSize is assumed.

       The largest legal value for the size parameter is
       (2^(WHALLOC_BITNESS-1)) (that is, half the maximum value of a
       WHALLOC_API(size_t)). This is a side-effect of the internal
       memory-management mechanism, which saves lots of space by
       having this limitation.
       
       Error conditions include:

       - self is null

       - self is full
   
       - self has no more hashtable entries.

       - We cannot allocate enough contiguous blocks. If the list
       becomes fragmented due to unusual alloc/dealloc patterns then
       it might have enough memory, but not contiguous.
    */
    void * WHALLOC_API(ht_alloc)( WHALLOC_API(ht) * const self, WHALLOC_API(size_t) size );

    /** @deprecated
       If m is associated with self (was allocated via
       WHALLOC_API(ht_alloc)()) then it is marked as free for later
       allocation. Otherwise, if self->fallback.free is set then it is
       passed m. If self->fallback.free is set and self->fallback.alloc is
       NOT set then an assertion may be triggered (and if one is not,
       undefined behaviour will ensue unless you know exactly what you're
       doing).

       Returns WHALLOC_API(rc).OK on success, else some other whalloc_rc value.
       
       @see WHALLOC_API(ht_alloc)()
       @see WHALLOC_API(ht_init)()
    */
    int WHALLOC_API(ht_free)( WHALLOC_API(ht) * const self, void * m );

    /** @deprecated
       Requires that self be an initialized object (see WHALLOC_API(ht_init)()).
       This routine wipes out the allocation information for self,
       which semantically calls free() on all managed elements.
       That is, after calling this, any pointers which came from
       WHALLOC_API(ht_alloc)() are considered invalid/danging.

       This function does not accommodate any memory served by
       self->fallback, and if this function should not be used in conjunction
       with objects which have a fallback memory allocator then it
       should be called after WHALLOC_API(ht_free)() has been called for
       each managed element.

       After calling this, self can again be used with
       WHALLOC_API(ht_alloc)().

       It will only fail (returning non-zero) if !self or if the mutex
       locking is enabled but fails to lock.
       
       @see WHALLOC_API(ht_alloc)()
       @see WHALLOC_API(ht_free)()
       @see WHALLOC_API(ht_init)()
    */
    int WHALLOC_API(ht_drain)( WHALLOC_API(ht) * const self );


    /**
        A WHALLOC_API(mutex)::lock() implementation which may
        sends a debugging message to stderr.  It ignores its argument.
    */
    int WHALLOC_API(mutex_lock_trace)( void * );

    /**
       A WHALLOC_API(mutex)::unlock() implementation which sends a
       debugging message to stderr. It ignores its argument.
    */
    int WHALLOC_API(mutex_unlock_trace)( void * x );

    
    /**

        A WHALLOC_API(mutex) implementation which does no locking but sends
        a debugging message to stderr. The mutex functions ignore
        their arguments.
    */
    extern const WHALLOC_API(mutex) WHALLOC_API(mutex_trace);
    /** @def WHALLOC_API(mutex_trace_m)

        An inline-initialized form of WHALLOC_API(mutex_trace).
    */
#define whalloc_mutex_trace_m \
    {WHALLOC_API(mutex_lock_trace),WHALLOC_API(mutex_unlock_trace),0/*data*/}

    /**
       Returns WHALLOC_BITNESS. Can be used in applications to assert that
       they are linked against the proper whalloc library. Liking against
       one with a different bitness will result in undefined behaviour
       (been there, done that).
    */
    uint8_t WHALLOC_API(bitness)();

    /** @internal @deprecated

        Dumps debugging info about self to the given file. This can be used
        to see which hashtable nodes are linked to what.
    */
    int WHALLOC_API(ht_dump_debug)( WHALLOC_API(ht) const * const self, FILE * out );

    typedef enum {
        /**
           The length of the WHALLOC_API(bt)::bits::cache member, in bytes.
           It must be a positive multiple of 2. To enable it, set it
           to some multiple of (WHALLOC_BITNESS/2).  To disable use of
           this cache (reducing the sizeof(WHALLOC_API(bt)) a bit), set it
           to 0.

           Each byte of increase enables WHALLOC_API(bt) to hold tables
           of 4 entries larger. Thus 8 bytes allows 32 more entries
           before WHALLOC_API(bt) will reserve space from the client
           memory.
        */
    WHALLOC_API(bt_CacheLength) = (2*WHALLOC_BITNESS)
    } WHALLOC_API(config_options);
    
    /**
       Similar to WHALLOC_API(ht) but uses a different internal structure
       for memory management, which generally uses up less of the
       reserved memory than WHALLOC_API(ht) does.

       This class is intended to be used identically to WHALLOC_API(ht),
       but it internally uses a much different storage mechanism
       memory management data. Whereas WHALLOC_API(ht) builds a hashtable
       internally, this class builds up a bitmap of data requiring
       only 2 bits per memory block it manages (plus 2 padding bytes
       for internal reasons).

       A WHALLOC_API(bt) instance must not be used for allocation until
       WHALLOC_API(bt_init)() has succeeded on it.
       
       In theory this memory manager performs identically to
       WHALLOC_API(ht), as all of the underlying algorithms are the
       same. However, the internals of this API open it up to certain
       potential/future optimizations which aren't possible in
       WHALLOC_API(ht), such as checking multiple blocks for
       used/linked-ness via one bitmask operation.
       
       Many, many thanks go to Amir "Ashran" Mohammadkhani for his
       help on this. He came over to my place to discuss the
       WHALLOC_API(ht) implementation with me, and he had the insight that
       the allocator doesn't really need to remember the size of
       allocated blocks - it only needs to know if a given
       (re)allocation is within a block boundary. He combined that
       with a different block-linking mechanism and came up with the
       2-bits-per-block method to replace the WHALLOC_API(ht)'s hashtable.

       Here's an overview of how this memory manager works using
       only two bits of memory per managed memory block:

       First see the documentation for WHALLOC_API(bt_init)(). That
       explains how the managed memory is sliced up into blocks (which
       can be as small as 1 byte for certain pool
       sizes). Understanding that stuff...

       When the maximum number of blocks is known, we can calculate a
       bitmask which, when applied to any memory address in the
       managed range, will uniquely identify it with a hash value.
       The hash value of any pointer within that range is the index of
       a logical block within the managed memory (starting at index
       0), aligned on blockSize boundaries. The exact length of the
       hash mask depends on the maximum number of items the we can
       manage in that memory. The hash mask has a number of bits equal
       to 2^N, where N is smallest number of bits needed to hold the
       value of the number of managed blocks.  e.g. if a memory space
       has 100 blocks (regardless of their size), we need 7 bits
       (2^7=128, whereas 2^6=64 cannot map 100 entries) in the hash
       mask. Any other bits of the address range are irrelevant for
       purposes of uniquely mapping an address to a memory block
       index, and an index back to an address (with blockSize-boundary
       granularity). We also set aside, from the managed memory space,
       enough bytes to hold 2*B (B=block count) _bits_, which are
       explained below. Given any address within our managed range,
       even if it's not aligned at the start of the allocated block,
       will "hash back" to an index in our bit lists. Likewise, we can
       convert such an index index back to the address of its
       corresponding block boundary.

       The internals maintain two bitsets, each with a maximum length
       (in bits) equal to the number of managed blocks. e.g. if the
       pool has 100 blocks, it will reserve enough memory for 200 bits
       (plus potentially a padding byte). These bitsets hold two
       pieces of information:

       - The "is-in-use" flag tells us whether a given block is
       allocated or not.

       - The "is-linked" flag tells us if this block is part
       of an allocation chain. Each block which is followed
       by another block is marked as linked. The last block
       in a chain is not linked.

       Those two bits contain all the metadata for a memory block, and
       two bits gives us the following four possible states for any
       given memory block:

       0) !in-use and !is-linked: the block is available for
       allocation.

       1) in-use and is-linked: it is the start of a multi-block
       allocation chain.

       2) in-use and !is-linked: (2a) the only block in a single-block
       allocation, or (2b) this is final link in an allocation chain.

       3) !in-use and is-linked: this is a non-terminal link in an
       allocation chain.

       (Again, thanks to Amir for providing that insight.)

       When traversing block chains to see if we can allocate a given
       range, we must linearly scan each block by simply accessing the
       next bit in the in-use bitset. If a used/linked item is found
       in our proposed range, we move up the list and try again until
       we can find no range we can fit it. The bitsets are normally
       very small (e.g. pool size of 8000 with 16-byte blocks uses
       about 124 bytes for its bitsets).
       
       When traversing block chains to free them up, we can detect a
       mis-free by checking for the appropriate states. Given the
       address to free, we can hash that in O(1) time to find the
       index of the associated data block (including bounds/error
       checking, of course). On deallocation, at the start of a chain
       we require states (1) or (2a). Then we crawl the chain, looking
       for states (2b) or (3). Any other state at any time is an
       error, signaling an internal state error (probably corruption
       via buggy modification of interal state), which would cause
       WHALLOC_API(bt_free)() to return an error code and possibly
       emit a debugging/logging message via WHALLOC_API(bt)::base::log
       (if set). If built in debugging mode, it may assert() on a
       failed free() operation, as free(3) often does if passed an
       invalid address.
       
       The amount of space which we must reserve for the internal bits
       is most strongly affected by the block size. A block size of 1
       might work for relatively small pools (up to up to
       2^(WHAlLOC_BITNESS-1) in size), but it has a high overhead and
       not all blocks will be allocable if they are doled out in
       one-byte increments. Selecting a block size value involves a
       making trade-offs for the specific use case. As a general rule,
       try to set the block size as big as your average object size,
       because single-block de/allocation always out-performs
       multi-block, sometimes by several factors.
    */
    struct WHALLOC_API(bt)
    {
        /** Holds the "base-most" allocator data, which is common to multiple allocator
            implementations. */
        WHALLOC_API(allocator_base) base;
        /**
           Bitsets holding block metadata (they live within mem,
           before uspace).
        */
        struct WHALLOC_API(bt_bitset)
        {
            /**
               The bitset holding the is-used flags.
            */
            unsigned char * usage;
            /**
               The bitset holding the is-linked flags.
            */
            unsigned char * links;
            /**
               The number of bits used in each of the 'usage' and
               'links' members. i don't remember why we store this
               separately (it seems to always be the same as
               base.blockCount), and we may be able to remove this
               from the API (with appropriate changes in the impl
               code).
            */
            WHALLOC_API(size_t) end;
            /**
               The number of bytes from mem reserved for use by the
               in-use and is-linked bitsets. It will be 0 if
               the cache member is used for storing the bitsets.
            */
            WHALLOC_API(size_t) byteCount;
            /**
               If the bit cache can fit in this memory, it will be
               used instead of reserving memory from the pool. When
               this is the case, the full amount given by the client
               (minus perhaps a partial block at the end) will be
               available for allocation.
            */
            unsigned char cache[(WHALLOC_API(bt_CacheLength))
                                ?(WHALLOC_API(bt_CacheLength)+3)
                                /*^^^^^ reminder: +3 to pad the buffer
                                with 0s to avoid chain walks from
                                overrunning. The final +1 is a kludge
                                for the internal calculation when
                                we've got enough elements to get within 8 bits of over-filling
                                this cache, so that we can hold a couple
                                more elements before falling back to
                                using the client's memory.

                                Reminder #2: since we moved the bitsets to the
                                end of the managed memory we can get rid of the
                                second padding byte and we need to move
                                the 'usage' member up one byte.
                                */
                                :1];
        } bits;
    };
    typedef struct WHALLOC_API(bt) WHALLOC_API(bt);
    /**
       An empty WHALLOC_API(bt) initialialization object.
    */
    extern const WHALLOC_API(bt) WHALLOC_API(bt_empty);
    /** @def whalloc_bt_empty_m
       An empty WHALLOC_API(bt) initialialization object.
    */
#define whalloc_bt_empty_m {                                          \
        whalloc_allocator_base_empty_m,                                     \
            {/*bits*/ 0/*usage*/,0/*links*/,0/*end*/,0/*byteCount*/,{0/*cache*/}/*,0 endOfCache*/}, \
        }

    /**
       Works very similarly to WHALLOC_API(ht_init)(), but works
       on a WHALLOC_API(bt) storage manager.

       self must be an empty-initialized object (e.g assign it
       from WHALLOC_API(bt_empty) to do this).

       mem is pointer to size bytes of memory. The blockSize parameter
       defines how big each managed memory block is. size must be at
       least (2*blockSize) and blockSize may be any value from 1 to
       something smaller than size. A value of 0 causes some
       relatively small default value to be used (e.g. 8 bytes). A
       value equal to or larger than size causes WHALLOC_API(rc).ArgError
       to be returned. The mem parameter is owned by the caller but
       its contents should only be manipulated through pointers
       allocated with WHALLOC_API(bt_alloc)(). Any other access to that
       memory region while self is alive will lead to undefined
       behaviour.

       The blockSize parameter specifies how large each managed such
       of memory can be. If 0 is passed, a default value of 8 is used.
       The size and blockSize determine maximum number number of items
       which can be active in the allocator. Not all combinations will work.
       If a combination doesn't work, try adjusting the blockSize
       by a point or two in either direction. i'm still working on getting
       the calculation working properly :/.
       
       A portion of mem will be reserved by self for use in its memory
       management. Specifically, this needs 2 bits (not bytes) per
       managed block. In the worst case (blockSize==1), this will
       "reappropriate" about 18-19% of mem for internal management
       details. For larger block sizes, the percentage of memory
       dedicated to the internals drops rapidly: blockSize=2=(~11%),
       4=(~6%), 8=(~3%), ... 64=(~0.4%), 128=(~0.2%). Doubling the
       block size approximately halves the percentage of memory
       reserved for internal purposes. This also means, however, that
       by increasing blockSize, the maximum number of objects which
       can be allocated will be reduced, since there are fewer overall
       blocks. self->bits.end holds the maximum number of items the
       allocator can manage, which is roughly (size/blockSize), minus
       whatever memory we need for internal management.
       
       On success:

       WHALLOC_API(rc).OK is returned. mem is owned by the caller but is
       managed by self, and mem must outlive self.

       On error:

       A non-0 value is returned and self will be in an undefined
       state. self should not be used for allocation until
       WHALLOC_API(bt_init)() has succeeded on it.

       Note that self does not own any dynamic resources, so it does
       not explicitly need to be cleaned up. If the caller allocates
       the mem buffer using malloc(), he must free that up after he is
       done using the WHALLOC_API(bt) object associated with it.


       The init routine double-checks its lookup table creation process
       to ensure that all hashcodes it generates are unique and that
       it does not generate too many (which would cause us to step out
       of bounds later on). Because of this consistency checking (A)
       subsequent operations can skimp on range checking (making them
       faster) and (B) the initialization is basically O(N), where N
       is the number of blocks.

       To re-use the allocator, use WHALLOC_API(bt_drain)() to clear out
       the internal state, or call WHALLOC_API(bt_init)() again to
       completely re-build the internals (slower, but necessary if the
       memory or block sizes change).
       
       Example:

       @code
       enum { BufSize 1024 * 8 };
       unsigned char buf[BufSize];
       WHALLOC_API(bt) bm = WHALLOC_API(bt_empty);
       WHALLOC_API(size_t) blockSize = 4;
       // bm.base.log = printf; // generates tons of debugging/tracing messages.
       int rc = WHALLOC_API(bt_init)( &bm, buf, BufSize, blockSize );
       if( WHALLOC_API(rc).OK != rc ) { ... error ... }
       MyType * m = WHALLOC_API(bt_alloc)( &bm, sizeof(MyType) );
       // ^^^ the returned memory lives inside of buf
       ...
       WHALLOC_API(bt_free)(&bm, m);
       @endcode


       Regarding aligment of pointers allocated by the self object:

       If mem is properly aligned and blockSize is a multiple of the
       platform's alignment then pointers allocated via the self
       object are guaranteed (as of version 20100304) to be properly
       aligned. This function does not do any magic to ensure
       alignment - if mem is not aligned or if blockSize is not a
       multiple of the alignment then some or all returned objects
       will not be "properly" aligned.  All that said, x86 platforms
       apparently don't care about alignment (or at least don't crap
       out if a specific alignment is not used).
    */
    int WHALLOC_API(bt_init)( WHALLOC_API(bt) * const self, void * mem, WHALLOC_API(size_t) size, WHALLOC_API(size_t) blockSize );

    /**
       Tries to allocate n bytes from self's pool. On success it returns
       the memory address, which will abstractly be n bytes but may in fact
       be larger (depending on self->base.blockSize). On error it returns
       null.

       If self->base.fallback.alloc AND self->base.fallback.free are set,
       and self cannot fulfill the allocation, the result of calling
       self->base.fallback.alloc(n) will be returned.

       If self was initialized with a "properly" aligned memory buffer
       and a block size which is a multiple of the platform's
       alignment, the returned pointer will be "properly" aligned.
    */
    void * WHALLOC_API(bt_alloc)( WHALLOC_API(bt) * const self, WHALLOC_API(size_t) n  );

    /**
       Semantically equivalent to realloc(), but uses the given
       allocator to manage the underlying storage.

       If !m then this is equivalent to WHALLOC_API(bt_alloc)(self,n). If
       size is 0 and m is not NULL this is equivalent to
       WHALLOC_API(bt_free)(self,m) except that it returns NULL on success
       and m on error.

       If m does not refer to memory managed by self AND
       self->fallback is set up, then the fallback routine is used,
       otherwise 0 is returned and an assertion may be triggered (in
       debug builds).

       If the memory block(s) allocated to m is/are already large
       enough to hold n then the m will be returned but the internal
       size reserved for it may be reduced if fewer blocks are needed
       for the new size.

       m may have to be relocated for the reallocation, and calling
       this invalidates all previously-stored pointers to m.

       On success, a pointer to the newly-(re)allocated memory is
       returned, which must be freed using WHALLOC_API(bt_free)(),
       WHALLOC_API(bt_realloc)(self,mem,0), or WHALLOC_API(bt_drain)().  As with
       realloc(), do not directly assign the return value to the same
       pointer passed as the m argument: if realloc fails that would
       overwrite the m pointer with 0, effectively "losing" the
       pointer to that memory.

       Example usage:

       @code
       void * re = WHALLOC_API(bt_realloc)(&mybt, myMemory, 12);
       if( ! re ) { ... error ... }
       else { myMemory = re; }
       @endcode
    */
    void *  WHALLOC_API(bt_realloc)( WHALLOC_API(bt) * const self, void * m, WHALLOC_API(size_t) n );

    /**
       Deallocates memory from self allocated via WHALLOC_API(bt_alloc)().

       On success it returns WHALLOC_API(rc).OK, else it returns some
       other value described for the whalloc_rc object.

       If self->base.fallback.alloc AND self->base.fallback.free are
       set AND m is not in the address space managed by self,
       self->base.fallback.free(m) is called and 0 is returned.  If m
       is outside of self's managed memory and neither
       self->base.fallback.alloc nor self->base.fallback.free are set,
       an assertion may be triggered (if the library was built with
       them enabled) or a non-zero error code will be returned.
    */
    int WHALLOC_API(bt_free)( WHALLOC_API(bt) * const self, void * m );


    /**
       If neither b nor a are NULL then a is modified such that further
       calls to a->realloc() will use b as the memory source. If the client
       modifies either a->realloc or a->allocState after this call returns,
       undefined behaviour will result.

       On error (either b or a are NULL) it returns non-zero.
    */
    int WHALLOC_API(bt_allocator)( WHALLOC_API(bt) * b, WHALLOC_API(allocator) * a );

    /**
       Cleans up the contents of self, such that:

       - Pointers which were fetched via WHALLOC_API(bt_alloc)() are
       considered to be invalidated.

       - May be used with WHALLOC_API(bt_alloc)() after calling this,
       re-using any memory it may have previously doled out.

       It will only fail (returning non-zero) if !self or if the mutex
       locking is enabled but fails to lock.
    */
    int WHALLOC_API(bt_drain)( WHALLOC_API(bt) * const self );

    /** @internal

       Internal debuggering tool which dumps info about self to the
       given stream.
    */
    int WHALLOC_API(bt_dump_debug)( WHALLOC_API(bt) const * const self, FILE * out );    


    /**
       Calculates a hash mask for a memory block containing the given
       number of logical elements (i.e. data blocks).

       The number parameter is the number for which to calculate a
       hash mask, and should be the maximum possible number of items
       for which a hash value is needed. bits must be a non-null
       pointer to a uint8_t. mask may optionally be null.

       This function basically determines how many bits of information
       we need in order to be able to store the given number. This
       info is used for creating hashcodes for the various whalloc
       allocator implementations.

       On success, WHALLOC_API(rc).OK is returned and:

       - bits is set to the number of bits needed to hold the number
       "size".  If (bits > (WHALLOC_BITNESS-1)) then
       WHALLOC_API(rc).RangeError is returned.

       - if mask is not null then it is set to a bitmask where the lowest N bits
       are set, where N is the value assigned to the bits argument.

       On error, a non-OK value is returned describing the nature of
       the problem and none of the output parameters are modified.
    */
    int whalloc_calc_mask( WHALLOC_API(size_t) number,
                           uint8_t * bits,
                           WHALLOC_API(size_t) * mask );

    /**
       Works like whalloc_calc_mask(), but takes a memory buffer
       size and a logical block size. If size is not evenly dividable
       by blockSize then this function discards the "overflow" for purposes
       of the calculation.

       On success, the same behaviour as whalloc_calc_mask() applies,
       but additionally:

       - if blocks is non-null then it will be assigned to the number
       of logical blocks which can be managed using the given size and blockSize.

    */
    int whalloc_calc_mask2( WHALLOC_API(size_t) size,
                            WHALLOC_API(size_t) blockSize,
                            uint8_t * bits,
                            WHALLOC_API(size_t) * mask, 
                            WHALLOC_API(size_t) *blocks );


    /**
       A simple memory region allocator class. It supports only
       allocation, not deallocation, of individual areas. It does not
       manage blocks of memory, but simply doles out the next n bytes
       of memory on each subsequent request.  The only way to "free"
       the allocated items for re-use is to re-set the region.

       @see WHALLOC_API(region_init)()
       @see WHALLOC_API(region_alloc)()
       @see WHALLOC_API(region_free)()
    */
    struct WHALLOC_API(region)
    {
        /** Pointer to the managed memory. */
        unsigned char * mem;
        /** Current allocation position. */
        unsigned char * pos;
        /** One-past-the-end of the memory reason. */
        unsigned char * end;
    };
    /** Convenience typedef. */
    typedef struct WHALLOC_API(region) WHALLOC_API(region);
    /** Empty-initialized WHALLOC_API(region) object. */
    extern const WHALLOC_API(region) WHALLOC_API(region_empty);

    /**
       Initializes r to use length bytes of mem for memory allocation
       wipes all bytes of mem to 0. Technically, ownership of mem is
       not transfered, but semantically it is given to r. Modifying
       mem it from outside this API (aside from modifying via pointers
       allocated by it) may corrupt the expected state.

       Returns 0 on success, non-zero on error. The only error conditions are
       if !r, !m, or !length.

       If mem is properly aligned for the host platform AND all
       allocations are a multiple of the alignment, then the memory
       allocated via the r object will be properly aligned, otherwise
       there are no alignment guarantees. Note that when using
       allocation sizes which come directly from sizeof(), the result
       will (except in the case of char arrays) be guaranteed to be a
       multiple of the alignment IF the platform pads its structs to
       such alignments.

       TODO:

       - Consider adding an option to the region class which tells it
       to round all allocation requests to the next multiple of the
       alignment value.
    */
    int WHALLOC_API(region_init)( WHALLOC_API(region) * r, void * mem, WHALLOC_API(size_t) length );

    /**
       Tries to allocate n bytes from r. On success returns the new
       pointer, which lives in memory managed by r. On error (!r or
       not enough bytes left) NULL is returned.
    */
    void * WHALLOC_API(region_alloc)( WHALLOC_API(region) * r, WHALLOC_API(size_t) n );

    /**
       "Frees" all memory in r by re-setting the allocation pointer
       and memsetting all bytes to 0.  Any objects allocated by
       WHALLOC_API(region_alloc)() are semantically freed by this, and
       future calls to WHALLOC_API(region_alloc)() may return memory
       overloapping with previously-allocated objects.

       Returns 0 on success, and the only error condition is if
       r is NULL.

       Note that this function does not actually free r itself, as r's
       destruction depends on how it was created (e.g., on the stack,
       malloc(), or via one of the other whalloc allocators).
    */
    int WHALLOC_API(region_free)( WHALLOC_API(region) * r );
    
    /** @def WHALLOC_USE_ALIGN

        No longer used. Will go away.
    */


    /** @def WHALLOC_ENABLE_CONVENIENCE_API

        If WHALLOC_ENABLE_CONVENIENCE_API is defined to a true value
        before including this header, macros are installed which
        provide a "shorthand" form of the core whalloc API.

        Namely, the functions named whalloc_XX_func() are macroized
        to wha_XX_func(), where XX is one of (bt,ht).

        Additionally, the whalloc_XX types are typedef'd to wha_XX
        and whalloc_XX_empty is defined to to wha_XX_empty.

        And... WHALLOC_API(bt_XXX) is macroized to wha_XXX, since
        WHALLOC_API(bt) implementation is considered to be a better (more
        efficient) allocator than WHALLOC_API(ht), and should be the
        default choice.
    */
#if !defined(WHALLOC_ENABLE_CONVENIENCE_API)
#  define WHALLOC_ENABLE_CONVENIENCE_API 0
#endif
#if WHALLOC_ENABLE_CONVENIENCE_API
#  define wha_rc whalloc_rc
    typedef WHALLOC_API(bt) wha_b;
    static const wha_b wha_b_empty = whalloc_bt_empty_m;
#  define wha_b_init WHALLOC_API(bt_init)
#  define wha_b_alloc WHALLOC_API(bt_alloc)
#  define wha_b_realloc WHALLOC_API(bt_realloc)
#  define wha_b_free WHALLOC_API(bt_free)
#  define wha_b_drain WHALLOC_API(bt_drain)
#  define wha_b_dump WHALLOC_API(bt_dump_debug)
    typedef WHALLOC_API(ht) wha_h;
    static const wha_h wha_h_empty = whalloc_ht_empty_m;
#  define wha_h_empty_m whalloc_ht_empty_m
#  define wha_h_init WHALLOC_API(ht_init)
#  define wha_h_alloc WHALLOC_API(ht_alloc)
#  define wha_h_free WHALLOC_API(ht_free)
#  define wha_h_drain WHALLOC_API(ht_drain)
#  define wha_h_dump WHALLOC_API(ht_dump_debug)

    typedef WHALLOC_API(bt) wha_a;
    static const wha_a wha_a_empty = whalloc_bt_empty_m;
#  define wha_empty wha_b_empty_m
#  define wha_init wha_b_init
#  define wha_alloc wha_b_alloc
#  define wha_realloc wha_b_realloc
#  define wha_free wha_b_free
#  define wha_drain wha_b_drain
#  define wha_dump wha_b_dump

#endif /* WHALLOC_ENABLE_CONVENIENCE_API */
#undef WHALLOC_ENABLE_CONVENIENCE_API /* we don't need this anymore */


#define WHALLOC_USE_ALIGN 0
#if WHALLOC_USE_ALIGN
    /** @internal */
    enum whalloc_align_enum {
    WHALLOC_ALIGN_ENUM
    };

    /** @internal */
    struct whalloc_align_struct {
        char pad;
        double type;
    };

    /** @internal */
    union whalloc_align_max {
#if 0
        char char_;
        short int short_;
        int int_;
        long int long_;
        float float_;
        double double_;
        long double long_double_;
#else
        uint8_t u8_;
        uint16_t u16_;
        uint32_t u32_;
        uint64_t u64_;
        double double_;
        long double long_double_;
#endif
        void* ptr_;
        void* (*fptr_) (void*);
        enum whalloc_align_enum enum_;
        struct whalloc_align_struct struct_;
        size_t size_t_;
        ptrdiff_t ptrdiff_t;
    };

#  define WHALLOC_ALIGN_OF(mp_type)             \
    offsetof(                                   \
             struct {                           \
                 char pad_WHALLOC_ALIGN_OF;     \
                 mp_type type_WHALLOC_ALIGN_OF; \
             },                                 \
             type_WHALLOC_ALIGN_OF              \
             )

#  define WHALLOC_ALIGN_MAX WHALLOC_ALIGN_OF(union whalloc_align_max)

#  define WHALLOC_ALIGN_UP(mp_ptr, mp_align)            \
    ((void*)(                                           \
             (((uintptr_t)(mp_ptr)) + ((mp_align) - 1)) \
             & ~(((mp_align) - 1))                      \
             ))


#  define WHALLOC_ALIGN_ASSERT(mp_ptr, mp_align)                \
    (((void*)(mp_ptr)) == WHALLOC_ALIGN_UP(mp_ptr, mp_align))

#else/*!WHALLOC_USE_ALIGN*/

#  define WHALLOC_ALIGN_OF(mp_type) 0
#  define WHALLOC_ALIGN_UP(mp_ptr, mp_align) ((void*)(mp_ptr))
#  define WHALLOC_ALIGN_ASSERT(mp_ptr, mp_align) 1
#if 8 == WHALLOC_BITNESS
#  define WHALLOC_ALIGN_MAX 4
#elif 16 == WHALLOC_BITNESS
#  define WHALLOC_ALIGN_MAX 4
#elif 32 == WHALLOC_BITNESS
#  define WHALLOC_ALIGN_MAX 4
#elif 64 == WHALLOC_BITNESS
#  define WHALLOC_ALIGN_MAX 8
#else
#  error "WHALLOC_BITNESS must be one of (8,16,32,64)!"
#endif

#endif /*WHALLOC_USE_ALIGN*/
#ifdef __cplusplus
} /* extern "C" */
#endif
#endif /* WANDERINGHORSE_NET_WHALLOC_POOL_H_INCLUDED */
/* end file whalloc.h */
/* begin file whalloc_pager.h */
#if !defined(WANDERINGHORSE_NET_WHALLOC_PAGER_H_INCLUDED)
#define WANDERINGHORSE_NET_WHALLOC_PAGER_H_INCLUDED 1
/** @page whalloc_pager whalloc_page API

   A page-based memory allocation manager for C.

   Author: Stephan Beal (http://wanderinghorse.net/home/stephan/

   License: Public Domain

   Features:

   - Allocation of same-sized objects via a page-based memory pool,
   where each page manages a number of equal-sized memory chunks and
   can only dole out individual chunks (as opposed to blocks larger
   than one chunks).

   - The "book" class internally manages any number of pages,
   providing a simple memory de/allocation interface.

   - Allows the client to define how books and pages are allocated.
   e.g. a memory book and its pages can use WHALLOC_API(bt) for storage.

   - The book class optionally supports a mutex to lock all
   access. The page class does not because it is intended to be used
   within a book, and the page class is already fat enough as it is.

   Misfeatures:

   - This is not a general-purpose allocator. It is intended
   specifically for cases which allocate many of the same types of
   objects and wants to recycle the memory to avoid the overhead of
   malloc(). (The original use case was allocating 12-byte structs
   to record record locking information, where we have to create
   and destroy arbitrary numbers of them.)

*/

#ifdef __cplusplus
extern "C" {
#endif
    

/**
   A class representing a "page" of memory blocks
   of equal size. The related API is responsible
   for managing the "allocation".

   This class is intended for "indirect" client use via the
   WHALLOC_API(book) class, but it can also be used as the basis for
   book-like classes which manage memory pages.

   This class is structured like a doubly-linked list to facilitate
   traversal and manipulation of multiple pages in page-managing
   algorithms. Whether or not the links may be circular depends
   on the managing class and its algorithms (the book class does
   not create a circular list, though it arguably should).

   These objects are created (indirectly) via the WHALLOC_API(book)
   API or directly by calling WHALLOC_API(page_new)(). They are freed
   using WHALLOC_API(page_finalize)().  Use WHALLOC_API(page_alloc)()
   WHALLOC_API(page_free)() to allocate and deallocate invididual
   objects within a page.

   TODOs:

   In the interest of memory use...
   
   - Consider removing the useCount member. i think we can do without
   it by relying on nextFree. It's only used as an optimization to
   figure out if the list is full.

   - Consider removing one of the page link pointers (prev/next
   members). i think the book class can get by with a singly-linked
   list just as well (except that it makes re-organization of the list
   more difficult).
*/
struct WHALLOC_API(page)
{
    /**
       The number of memory chunks for which this page reserves
       space. i.e.  the maximum number of objects it may
       allocate. This is set at initialization and must not be changed
       afterwards.
     */
    uint16_t length;

    /**
       The size of each memory chunk. This is set at initialization
       and must not be changed afterwards.
    */
    uint16_t chunkSize;

    /**
       The current number of "used" (allocated to the client)
       entries. This is modified by the de/allocation routines, and
       must not be modified by client code.

       It is primarily a performance optimization for checking
       is-the-page-empty. We could theoretically get rid of this and
       simply check if nextFree>=length for that case. Something to
       try.
    */
    uint16_t useCount;

    /** @internal

       Internal hint to speed up allocation - the index of the next
       (suspected) free chunk. A value here does not guaranty that
       that position is actually free - this is only a hint as to
       where to start looking for a free chunk. This is modified by
       the de/allocation routines, and is always set to be the
       lowest-offset free chunk.

       Setting this from client code can cause a page to allocate
       more slowly or even skip unused memory chunks (treating them
       as used though they are not). Don't do it.
    */
    uint16_t nextFree;

    /** @internal

        A number of flag bytes (enough to hold thisObject->length
        bits). Each chunk in the page requires one bit in this memory
        for marking the chunk as used or unused.

        Do not use this from client code.
        
        Maintenance reminder: this is (unsigned char*) instead of
       (void*) to facilitate access to specific offsets via addition.
    */
    unsigned char * flags;

    /** @internal

       Objects allocated in this page are stored somewhere in here.
       This space is off limits to client code. All access to the
       memory should be via WHALLOC_API(page_alloc)().

       Maintenance reminder: this is (unsigned char*) instead of
       (void*) to facilitate access to specific offsets via addition.
    */
    unsigned char * pool;

    /**
       A pointer to the next page in the list.
    */
    struct WHALLOC_API(page) * next;

    /**
       A pointer to the previous page in the list.
    */
    struct WHALLOC_API(page) * prev;

    /**
       If set to have non-null values during initialization, this
       object is used to allocate the page instance. In
       WHALLOC_API(page_finalize)(), this routine is used to free the
       object.

       This member must comply strictly to the WHALLOC_API(allocator)
       interface.

       A default implementation is used if the does not provide one to
       WHALLOC_API(page_new)(). alloc.realloc must not be NULL and
       must not change addresses after initialization.
    */
    WHALLOC_API(allocator) alloc;
};

/** Convenience typedef. */
typedef struct WHALLOC_API(page) WHALLOC_API(page);

/**
   Empty-initialized WHALLOC_API(page) object.
*/
extern const WHALLOC_API(page) WHALLOC_API(page_empty);

/**
   A book is a management object for a collection of memory page
   objects (see WHALLOC_API(page)). Each book manages pages of a
   certain length and memory chunks of a certain size. The number of
   pages is dynamic, and may grow or shrink over time.
*/
struct WHALLOC_API(book)
{
    /**
       The number of objects allocated per page. Must not be changed
       after initialization.
     */
    uint16_t pageLength;

    /**
       The size of each allocation unit. Must not be changed after
       initialization.
    */
    uint16_t chunkSize;

    /** @internal
        Internal state flags.
    */
    int8_t flags;
    
    /**
       The first page in the memory page list. The API may reorganize
       the list throughout the life of this object, so there is no
       guaranty that this pointer remains stable (in fact, it is
       guaranteed to be unstable if any de/allocation is done which
       when the book has more than one page).
    */
    WHALLOC_API(page) * page;
    /**
       Optional logging/debugging function. Set this to non-null
       to intercept debugging messages. Only used if built in
       debugging mode.
    */
    WHALLOC_API(log_f) log;

    /**
       If set to contain non-null values during initialization, this
       routine is used to de/allocate this book (but not its pages:
       see the pageAlloc member). e.g. WHALLOC_API(book_close)() uses
       routine to free the object.

       This member must comply strictly to the
       WHALLOC_API(allocator)() interface, must not have a NULL
       realloc member, and the members must not change addresses after
       initialization.

       WHALLOC_API(book_open)() assigns a default implementation if
       given a NULL allocator function. The default simply uses
       realloc(3).
    */
    WHALLOC_API(allocator) alloc;
    /**
       If set to contain non-null values during initialization, this
       routine is used to de/allocate this book's pages (but not the
       book itself: see the alloc member).

       This member must comply strictly to the
       WHALLOC_API(allocator)() interface, must not have a NULL
       realloc member, and the members must not change addresses after
       initialization.

       WHALLOC_API(book_open)() assigns a default implementation if
       give a NULL allocator function. The default simply uses
       realloc(3).
    */
    WHALLOC_API(allocator) pageAlloc;
    /**
       An optional mutex which should be used by this object
       to lock/unlock during all operations. It is used as
       described in the docs for the WHALLOC_API(mutex) type.
       If it contains NULL values then locking will not be
       used.

       Pedantic note: if the pageAlloc member uses the same underlying
       native mutex as this object then the mutex must be capable of
       recursive locks. If a book and allocator share a non-recursive
       mutex, allocating new pages in the book may cause a deadlock
       because the allocation must be locked from the book (because it
       uses book members) and then the allocator itself will trigger
       another lock.
    */
    WHALLOC_API(mutex) mutex;
};

/** Convenience typedef. */
typedef struct WHALLOC_API(book) WHALLOC_API(book);

/**
   Empty-initialized WHALLOC_API(book) object.
*/
extern const WHALLOC_API(book) WHALLOC_API(book_empty);

/**
   For a given number of objects (n) of a given size (chunkSize), this
   function returns the size of the memory needed to store a
   WHALLOC_API(page) object created with WHALLOC_API(page_new)() using
   those same parameters.

   If either value is 0 then 0 is returned.

   When using a custom allocator for page objects, this can be helpful
   in sizing the memory blocks of the custom allocator (so they can
   have the same size as the page objects they will host, for an
   optimum use of space).
*/
unsigned int WHALLOC_API(page_calc_size)( uint16_t n, uint16_t chunkSize );

/** @def WHALLOC_API_PAGE_CALC_SIZE

    WHALLOC_API_PAGE_CALC_SIZE is equivalent to the function
    WHALLOC_API(page_calc_size)(), but is provided because this value
    is sometimes required as a compile-time constant. (While C++ will
    let us initialize static const objects from function return
    values, C does not.)

    N is the number of objects to be stored in the page and ChunkSize
    is the size of each object. If either is 0 then this macro
    evaluates to 0 (which is not a legal page size).

    @see WHALLOC_API(page_calc_size)
*/
#define WHALLOC_API_PAGE_CALC_SIZE(N,ChunkSize) ((!(N) || !(ChunkSize)) ? 0 : (sizeof(WHALLOC_API(page)) + (/*pool*/(N) * (ChunkSize) + (N/8+1)/*flags*/)))


    /**
       Allocates a page object along with enough space to hold
       n objects of chunkSize bytes each.

       On success it returns a new book object which is owned by the
       caller and must eventually be cleaned up using
       WHALLOC_API(page_finalize)(). On error NULL is returned.

       The alloc parameter specifies an allocation routine which should be
       used to allocate and destroy the page object's memory. It may be
       null, in which case a realloc(3)-compatible implementation is used
       which ignores the 3rd argument
       
       The allocState parameter is used as the 3rd argument to the alloc()
       argument. It may be NULL if alloc is NULL or if the alloc
       implementation needs no private state (or the state is encapsulated
       with the alloc function itself).

       To succeed, this function has to be able to allocate
       WHALLOC_API(page_calc_size)(n,chunkSize) bytes using a single call to
       alloc() (or the default implementation, if the alloc argument is
       NULL).

       TODO (or to consider): ensure that the memory segment used for
       doling out objects is generically aligned. Currently there are no
       alignment guarantees. Even if we guaranty the initial position, a
       non-multiple-of-alignment chunkSize would ensure that all (or most)
       other allocations were not aligned. We could fudge that by rounding
       up chunkSize to a multiple of the max alignment. Hmmm.

       @see WHALLOC_API(page_new2)()
    */
WHALLOC_API(page) * WHALLOC_API(page_new)( uint16_t n, uint16_t chunkSize,
                                           WHALLOC_API(realloc_f) alloc, void * allocState);


/**
   Equivalent to WHALLOC_API(page_new)() but takes its allocator
   argument in a different form. See WHALLOC_API(page_new)() for
   the full details, and below for the differences...

   If alloc is NULL or alloc->realloc is NULL then a default allocator
   which uses realloc(3) is used in its place.

   If the allocator object is not NULL, is is SHALLOWLY COPIED for
   future use. Thus the alloc pointer itself may legally change after
   this call, but the alloc->state and alloc->realloc values must stay
   valid for the life of the returned object.

   @see WHALLOC_API(page_new)()
   @see WHALLOC_API(page_finalize)()
*/
WHALLOC_API(page) * WHALLOC_API(page_new2)( uint16_t n, uint16_t chunkSize,
                                            WHALLOC_API(allocator) const * alloc );



/**
   Frees all memory associated with p, invalidating p and any
   pointers to memory which were allocated via p. The function
   p->alloc.realloc() is used to do the actual deallocation.

   If p is NULL then this function is a no-op.

   If p is managed by a higher-level structure
   (e.g. WHALLOC_API(book)) then do not use
   WHALLOC_API(page_finalize)() on that page! Doing so may invalidate
   pointers used by the management structure.
*/
void WHALLOC_API(page_finalize)( WHALLOC_API(page) * p );

/**
   Returns the amount of memory which was initially allocated for p
   (assuming p was allocated via WHALLOC_API(page_new)), and is
   equivalent to WHALLOC_API(page_calc_size)(p->length,p->chunkSize).
   Note that this returns the _requested_ allocation size, and the
   underlying allocator might have allocated more (but that space is
   considered unusable).

   Returns 0 if !p.
 */
unsigned int WHALLOC_API(page_sizeof)( WHALLOC_API(page) const * p );

/**
   Searches for the next free memory chunk in p and
   returns it, or returns NULL on error (!p) or
   if p is full.

   Performance notes:

   This implementation performs O(1) for the average case, where
   objects are deallocated in reverse order of their allocation.
   The worst-case scenario is O(N), where N is slightly less than
   p->length, but hitting that case would require some really unusual
   de/allocation patterns.
*/
void * WHALLOC_API(page_alloc)( WHALLOC_API(page) * p );

/**
   Returns non-zero (true) if m is in the bounds managed by p (that
   is, if it appears that m was (or could become) allocated from
   p). Else it returns 0 (false).

   This is an O(1) operation.
*/
char WHALLOC_API(page_owns_mem)( WHALLOC_API(page) const * p, void const * m );

/**
   Semantically equivalent to free(mem), this returns ownership of
   mem, which must have been allocated by WHALLOC_API(page_alloc)(p),
   to p. Returns 0 on success or non-zero error( !p, !mem, or mem is
   not owned by p).

   This routine is O(1): it only has to perform a couple of
   address comparisons and potentially set a byte.

   To free the p object itself, use WHALLOC_API(page_finalize)().
   If the page object itself is managed by a higher-level structure
   (e.g. WHALLOC_API(book)) then do not use WHALLOC_API(page_finalize)()!
*/
int WHALLOC_API(page_free)( WHALLOC_API(page) * p, void * mem );

/**
   Erases the chunk-allocation state of p, such that all memory chunks
   in it are considered unused and ready for re-allocation. Any
   pointers to memory which were allocated via p are semantically
   invalidated by this call (and if used they might clobber or be
   clobbered by a future re-allocation of the chunk).

   p->next and p->prev are not changed.

   Returns 0 on success, non-zero on error. The only error condition
   is !p.


   This operation has effectively O(N) performance, where N is
   approximately (1+(p->length/8)) and is the number of bytes in the
   internal bitset. (Those bytes must be memset()'d to 0.)
*/
int WHALLOC_API(page_erase)( WHALLOC_API(page) * p );

/**
   Returns 0 (false) if p has more chunks available to allocate, else
   it returns non-zero (true).

   This is an O(1) operation.
*/
char WHALLOC_API(page_is_full)( WHALLOC_API(page) const * p );

/**
   Inserts p as after->next, re-linking after->next if necessary.

   Returns 0 on success or non-zero if:

   - !p or !after

   - Either of p->prev or p->next is non-NULL (use
   WHALLOC_API(page_snip) to remove it from a chain if you need to).
*/
int WHALLOC_API(page_insert_after)( WHALLOC_API(page) * p, WHALLOC_API(page) * after );


/**
   Identical to PAGE(page_insert_after), but inserts p before the
   second argument. It has the same error conditions and return codes
   as that function.
*/
int WHALLOC_API(page_insert_before)( WHALLOC_API(page) * p, WHALLOC_API(page) * before );

/**
   Snips p from its prev/next neighbors (if any) and links the
   neighbors together. On error (!p) it returns NULL, else it returns
   p->next (if it was set) or p->prev (if p->next is NULL). That is,
   it tries to return the right-side neighbor, but returns the left
   neighbor if there is nobody on the right. If there are no
   neighbors, NULL is returned (but this is not an error).

   On success, ownership of p is given to the caller. Ownership of the
   returned object does not change.
*/
WHALLOC_API(page)* WHALLOC_API(page_snip)( WHALLOC_API(page) * p );

/**
   Moves page p one step to the right in its chain. On success then 0
   is returned. If !p then non-zero (error) is returned. The case
   of !p->next is treated as a no-op success.
*/
int WHALLOC_API(page_move_right)( WHALLOC_API(page) * p );

/**
   The left-side counterpart to WHALLOC_API(page_move_right), this moves
   p one step to the left in its chain. It has the same error
   conditions and return codes as WHALLOC_API(page_move_right).
*/    
int WHALLOC_API(page_move_left)( WHALLOC_API(page) * p );

/**
   Allocates a book which serves memory in chunks of exactly chunkSize
   bytes. The n parameter is the number of chunks to store in each
   internal memory page (see WHALLOC_API(page)). Pages are added to
   the book as needed when allocation is requested.

   No pages are initially allocated - they are allocated on demand or
   via WHALLOC_API(book_add_page).

   The alloc parameter specifies an allocation routine which should be
   used to allocate and destroy the book object's memory. It may be
   null, in which case a realloc(3)-compatible implementation is used
   which ignores the 3rd argument.
   
   The allocState parameter is used as the 3rd argument to the alloc()
   argument. It may be NULL if alloc is NULL or if the alloc
   implementation needs no private state.

   The pageAlloc and pageAllocState parameters define the allocator
   data for pages allocated via the book, in the same way that th
   ealloc and allocState parameters define it for the book
   itself. pageAlloc may be NULL, in which case the same default
   allocator is used as described above for the book
   object. pageAllocState may or may not be allowed to be NULL,
   depending on the requirements of pageAlloc (the default
   implementation ignores the pageAllocState argument).
   pageAlloc/pageAllocState may be the same values as
   alloc/allocState unless the documentation for those functions
   prohibit it.

   On success it returns a new book object which is owned by the
   caller and must eventually be cleaned up using
   WHALLOC_API(book_close)(). On error NULL is returned.

   Why use two different allocators for the book and the pages? Most
   client cases would use the same for both. i have, however, a highly
   memory-optimized library where i can press out a hundred bytes or
   so by allocating the book from the general-purpose allocator and
   the pages from a page-size-optimized allocator. Pages are much
   larger (bigger allocated size) than books, so allocating pages from
   the GP allocator causes lots of memory block spans in the allocator
   (i.e. worse de/alloc performance). Likewise, allocating the book
   from a page-optimized allocator means the book allocation takes up
   way more slack space than it needs to. Pages have a runtime-defined
   size, which complicates pool size optimization a tiny
   bit. Anyway...


   @see WHALLOC_API(book_open2)()
   @see WHALLOC_API(book_close)()
*/
WHALLOC_API(book) * WHALLOC_API(book_open)( uint16_t n, uint16_t chunkSize,
                                            WHALLOC_API(realloc_f) alloc, void * allocState,
                                            WHALLOC_API(realloc_f) pageAlloc, void * pageAllocState
                                            );

/**
   Equivalent to WHALLOC_API(book_open)() but takes its allocator
   arguments in a different form. See WHALLOC_API(book_open)() for
   the full details, and below for the differences...

   If alloc or pageAlloc are NULL, a default allocator which uses
   realloc(3) is used in its place.

   alloc and pageAlloc may be the same object if the allocator's rules
   do not prohibit it. (e.g. WHALLOC_API(book_open_alloc_reuse)()
   explicitly prohibits it.)

   If the allocator objects are not NULL, they are SHALLOWLY COPIED
   for future use. Thus the alloc/pageAlloc pointers themselves may
   legally change after this call, but the alloc/pageAlloc->state and
   alloc/pageAlloc->realloc values must stay valid for the life of the
   returned book.

   @see WHALLOC_API(book_open)()
   @see WHALLOC_API(book_close)()
*/
WHALLOC_API(book) * WHALLOC_API(book_open2)( uint16_t n, uint16_t chunkSize,
                                             WHALLOC_API(allocator) const * alloc,
                                             WHALLOC_API(allocator) const * pageAlloc );

    
/**
   Implements WHALLOC_API(realloc_f)() in a highly unconventional
   manner:

   If n is not 0 (an allocation request) then allocState is
   returned. If n is 0 (a free() operation) then NULL is returned. In
   no case is any memory actually allocated or deallocated, and only
   the n parameter is actually evaluated.

   Why?

   This can be used as the book allocator parameter (NOT the page
   allocator parameter!) to WHALLOC_API(book_open)(), passing a
   pointer to an allocated WHALLOC_API(book) object as the allocator
   state parameter.  That will cause WHALLOC_API(book_open)() to use
   the client-supplied object. WHALLOC_API(book_close)() will then
   free the pages but not the book (we assume the client will clean it
   up, or that it was stack allocated and needs no further cleaning).

   BIG FAT HAIRY ACHTUNG: do NOT use this as the page allocation
   parameter to WHALLOC_API(book_open)()!!!! Doing so WILL corrupt
   memory!
*/
void * WHALLOC_API(book_open_alloc_reuse)( void * m, unsigned int n, void * allocState );

    
/**
   Frees the memory associated with b, which must have been allocated
   using WHALLOC_API(book_open)(), including all pages in the book. This
   of course invalidates any pointers which refer to memory inside the
   book.

   If b is NULL then this function is a no-op.

   Returs non-zero on error if !b or if mutex locking fails.  On
   success, b is invalidated by this call. On error b is not modified.
*/
int WHALLOC_API(book_close)( WHALLOC_API(book) * b );

/**
   Adds a new page to b. Returns the new page, which is owned by b, on
   success. On error it returns NULL. The page is allocated using
   b->pageAlloc(), and will be deallocated by the book when the time
   comes. Thus, do not hold a pointer to the returned object, as the
   book may free it at any time during the alloc/dealloc routines.

   It is not normally necessary for client code to use this, as
   WHALLOC_API(book_alloc)() adds new pages on demand. The client can
   use this, however, to pre-allocate pages.

   The interface does not specify at what position of the internal
   page list the page must be added, and the implementation is free to
   place it anywhere in the page chain. Having said that: this
   implementation puts it at the start of the chain, since the general
   API policy is to move the least-full pages to the front to speed up
   allocation.
*/
WHALLOC_API(page) * WHALLOC_API(book_add_page)( WHALLOC_API(book) * b );

/**
   Allocates the next available memory slot from b.  On success it
   returns a pointer to that block, which should be treated as being
   b->chunkSize bytes long. On error NULL is returned.

   There is no guaranty whatsoever that objects returned from
   subsequent calls lie in adjecent memory, and the returned value
   should never be used as an array pointer.

   This function adds pages to b as needed, using
   WHALLOC_API(book_add_page)() to allocate the pages. It also may
   re-structure the internal list for (perceived) performance reasons.
   
   Note that re-ordering the internal page list does not actually
   change any addresses within a page, and therefore does not
   invalidate pointers allocated via a page in the book. It often
   does, however, invalidate any pointers to b->page, so _never_ hold
   a pointer to that member.

   Performance notes:

   Allocation is, for the average case, almost (but not quite) O(1).
   When a book de/allocates a block, it may re-position the containing
   page in its internal page list. The book class tries to keep the
   pages with the most free blocks at the front of the list, to help
   ensure fast allocation. The down-side of this is that it can (but
   doesn't necessarily) lead to the opposite effect for deallocation
   (which could become slower, but that depends on the exact de/alloc
   counts and orderings). When an object is deallocated (via
   WHALLOC_API(book_free)()) the book has to ask each page if it
   owns the memory.

   The more pages a book has, the slower average de/allocation
   performance will theoretically be, as the book has to ask each page
   if it owns a given memory block. The exact performance
   characteristics depend largely on the orderings of the individual
   de/allocations and the pageLength/chunkSize.

   Regarding allocation (but not deallocation):

   Since less-used pages are moved to the front, allocation
   performance is (generally) only affected when the front-most page
   fills up (which only happens if all other pages are full or one
   entry away from being full). In this case, the book has to iterate
   over each page (all of which are full now) in order to figure out
   that it is full.

   For peformance, a few long pages are better than more short
   pages, but client requirements may call for allocation in smaller
   chunks, and in such a case more, but smaller, pages might be more
   appropriate. Keep in mind that the memory allocated for a page via
   WHALLOC_API(page_new)() is larger than
   sizeof(WHALLOC_API(page)), as it also allocates memory for the
   paged objects.
*/
void * WHALLOC_API(book_alloc)( WHALLOC_API(book) * b );

/**
   Returns mem, which must have been allocated from b using
   WHALLOC_API(book_alloc)(), to b. Returns 0 on success, non-zero on
   error.

   Performance notes:

   Performance is theoretically O(N), where N is a function of the
   number of pages in b. This is because the book has to ask each page
   if it owns mem. The deallocation itself, once the owning page is
   found, is O(1). Because the internal page list gets moved around to
   optimize allocation speed, it is not possible to calculate the
   exact performance without knowing the exact de/allocation patterns
   used by the client of the book.
*/
int WHALLOC_API(book_free)( WHALLOC_API(book) * b, void * mem );

/**
   De-allocates any pages in b which no longer host any allocated
   items.

   Vacuuming is not a guaranty that any pages _will_ be released,
   because it is possible to have a situation where every page has at
   least one allocated chunk.
   
   If auto-vacuuming is on (see WHALLOC_API(book_vacuum_auto)()) then
   this function need never be called, but if a high chunk recycling
   rate is desired for b then auto-vacuuming is better left off.

   Returns the number of pages removed from b, or 0 if !b.

   This operation is essentially O(N)+O(M), where:

   N is the total number of pages (we have to query each to see if it
   is empty) and M the number of empty pages (which require
   deallocation, and therefore more time). The relative cost of one
   empty page is higher than a non-empty by an unspecified factor
   (performance relies on the underlying deallocator).
*/
unsigned int WHALLOC_API(book_vacuum)( WHALLOC_API(book) * b );

/**
   If autoVac is non-zero (true) then auto-vacuum mode is enabled for
   b, otherwise auto-vacuum is disabled. Autovacuuming means when a
   given page in b deallocates its last chunk, b will automatically
   deallocate the page.

   Returns 0 on success, non-zero on error. The only error cases are
   if !b or locking of b's mutex fails.

   In terms of performance, turning this option on is faster than
   periodically calling WHALLOC_API(book_vacuum)(), but should
   arguably be turned off unless know you won't be recycling most of
   the allocations.

   This is an O(1) operation (not counting the potential mutex lock)
   and does not trigger an immediate vacuum.

   TODO: allow this function to take a threshold value, meaning to
   vacuum if the given number of pages are empty. The problem with
   that is that it increases de/allocation time considerably (at least
   O(N), N=page count) because we would have to check all pages on
   each de/alloc (unless we add more optimizations to the book's
   internals to keep track of the page used/unused counts in the book
   itself). We do not currently have such optimizations because
   changes made to a book from outside of this API would immediately
   invalidate the accounting data.
*/
int WHALLOC_API(book_vacuum_auto)( WHALLOC_API(book) * b, char autoVac );
    
/**
   Erases the chunk-allocation state of b, such that all memory pages
   in it are considered empty and ready for re-allocation. Any
   pointers to memory which were allocated via b (or any of its pages)
   are invalidated by this call.

   Returns 0 on success, non-zero on error. The only error condition
   is !p.

   If alsoDeallocPages is non-zero (true) then all pages in b are
   deallocated, otherwise they are simply erased (see
   WHALLOC_API(page_erase)()) but not deallocated (and not
   deallocated regardless of auto-vacuum setting (see
   WHALLOC_API(book_vacuum_auto)())).
   
   This routine essentially has O(N)*M performance, where N is the
   number of pages in the book and M is the performance of
   WHALLOC_BOOK(page_erase)().
*/
int WHALLOC_API(book_erase)( WHALLOC_API(book) * p, char alsoDeallocPages );
    
    
#ifdef __cplusplus
} /* extern "C" */
#endif


#endif /* WANDERINGHORSE_NET_WHALLOC_PAGER_H_INCLUDED */
/* end file whalloc_pager.h */
/* end file include/wh/whalloc_amalgamation.h */
/* begin file include/wh/whglob.h */
#if !defined(WANDERINGHORSE_NET_WHGLOB_H_INCLUDED)
#define WANDERINGHORSE_NET_WHGLOB_H_INCLUDED 1
/** @page whglob_page_main whglob Globbing Functions
   
    This is a small API for doing string matching using glob or SQL
    LIKE patterns. The code was originally part of the sqlite3
    (http://sqlite.org) project but was found to be easy to extract
    and genericize, so here it is. They are encapsulated in the
    whglob_matches() and whglob_matches_like() functions.

*/
#ifdef __cplusplus
extern "C" {
#endif

    /**
       Checks str to see if it matches the given pattern, which is
       assumed to follow standard globbing pattern rules. On success,
       non-0 is returned.

       Example:

       @code
       if( whglob_matches( "*.c", __FILE__ ) ) {
           puts("This is a .c file!");
       }
       @endcode

       Globbing rules:

       - '*' Matches any sequence of zero or more characters.
       - '?' Matches exactly one character.
       - [...] Matches one character from the enclosed list of characters.
       - [^...]  Matches one character not in the enclosed list.

       With the [...] and [^...] matching, a ']' character can be
       included in the list by making it the first character after '['
       or '^'.  A range of characters can be specified using '-'.
       Example: "[a-z]" matches any single lower-case letter.  To
       match a '-', make it the last character in the list.

       This routine is usually quick, but can be N**2 in the worst case.

       Hints: to match '*' or '?', put them in "[]".  Like this:

        abc[*]xyz        Matches "abc*xyz" only
    */
    int whglob_matches( char const * pattern, char const * str );

    /**
       Checks str to see if it matches the given pattern, which must
       follow SQL's LIKE pattern rules (where the wildcard character
       is a percent sign). On success, non-0 is returned. If
       caseSensitive is non-0 then a case-sensitive search is done
       (ANSI SQL-92 specifies that LIKE is case-insensitive).

       @code
       if( whglob_matches_like( "%.c", __FILE__ ) ) {
           puts("This is a .c file!");
       }
       @endcode

    */
    int whglob_matches_like( char const * pattern, char const * str, char caseSensitive );

#ifdef __cplusplus
} /* extern "C" */
#endif


#endif
/* end file include/wh/whglob.h */
/* begin file include/wh/whio/whio_config.h */
#ifndef WANDERINGHORSE_NET_WHIO_CONFIG_H_INCLUDED
#define WANDERINGHORSE_NET_WHIO_CONFIG_H_INCLUDED 1
/*
  Common configuration options for libwhio. Parts of the
  library can be changed/configured by editing this file.

  Author: Stephan Beal (http://wanderinghorse.net/home/stephan/)

  License: Public Domain
*/

#include <stdint.h> /* uintXX_t */
#if defined(__cplusplus) && !defined(__STDC_FORMAT_MACROS)
/* inttypes.h needs this for the PRI* and SCN* macros in C++ mode. */
#  define __STDC_FORMAT_MACROS
#endif
#include <inttypes.h> /* PRIuXX macros */
#include <sys/types.h> /* off_t on Linux */

#ifndef __cplusplus
/* Try to find a usable bool, or make one up ... */
#  ifndef WHIO_HAVE_STDBOOL
#    define WHIO_HAVE_STDBOOL 1
#  endif
#  if defined(WHIO_HAVE_STDBOOL) && !(WHIO_HAVE_STDBOOL)
#    if !defined(bool)
#      define bool char
#    endif
#    if !defined(true)
#      define true 1
#    endif
#    if !defined(false)
#      define false 0
#    endif
#  else /* aha! stdbool.h! C99. */
#    include <stdbool.h>
#  endif /* WHIO_HAVE_STDBOOL */
#endif /* __cplusplus */

/** @def WHIO_CONFIG_USE_FCNTL

If the library is built with WHIO_CONFIG_USE_FCNTL set to a true
value, the whio_dev implementations which deal with files may enable
fcntl()-style locking via their whio_dev::ioctl() implemenations.
*/
#if !defined(WHIO_CONFIG_USE_FCNTL)
#  if defined(WIN32)
#    define WHIO_CONFIG_USE_FCNTL 0
#  else
#    define WHIO_CONFIG_USE_FCNTL 1
#  endif
#endif

/** @def WHIO_CONFIG_ENABLE_ZLIB

If set to true then the APIs which use libz functionality are
enabled, else they are disabled.

*/
#if !defined(WHIO_CONFIG_ENABLE_ZLIB)
#  if defined(WIN32)
#    define WHIO_CONFIG_ENABLE_ZLIB 0
#  else
#    define WHIO_CONFIG_ENABLE_ZLIB 1
#  endif
#endif

#ifdef __cplusplus
#  if !defined(restrict)
#    define restrict
#  endif
extern "C" {
#endif

#if !defined(WHIO_CONFIG_ENABLE_DEBUG)
#  define WHIO_CONFIG_ENABLE_DEBUG 0
#endif

/** @def WHIO_DEBUG

  WHIO_DEBUG is a printf-like macro which is used for internal debugging
  of the whio library. If compiled with WHIO_CONFIG_ENABLE_DEBUG set to 0 then
  all debuggering output is disabled.
*/
#if WHIO_CONFIG_ENABLE_DEBUG
#  include <stdio.h> /*printf()*/
#  define WHIO_DEBUG if(WHIO_CONFIG_ENABLE_DEBUG) printf("WHIO_DEBUG: %s:%d:%s():\t",__FILE__,__LINE__,__func__); if(WHIO_CONFIG_ENABLE_DEBUG) printf
#else
   extern void whio_noop_printf(char const * fmt, ...);
#  define WHIO_DEBUG if(0) whio_noop_printf
#endif


/** @def WHIO_CONFIG_ENABLE_STATIC_MALLOC

   Don't use WHIO_CONFIG_ENABLE_STATIC_MALLOC any more. The newer
   whio_allocator/whio_memory_source API (added 20100301) allows the
   client to specify a memory source for the whio_dev and whio_stream
   APIs, which is both safer and more generic than what
   WHIO_CONFIG_ENABLE_STATIC_MALLOC enables. If
   WHIO_CONFIG_ENABLE_STATIC_MALLOC is used in conjunction with the
   whio_memory_source then the static allocators will be used before
   falling back to whio_alloc() and friends.

   That said...
   
   Changing this only has an effect when building this library
   or when building extensions which want to follow these
   conventions...

   If WHIO_CONFIG_ENABLE_STATIC_MALLOC is true then certain operations
   which are normally done via malloc() and free() are instead done
   first via a static list of pre-allocated objects and then (if the
   list is all used up) fall back malloc()/free().  This i not
   strictly thread-safe, but for some use cases that isn't
   significant.

   When using this we might not actually save much dynamic memory
   (e.g.  whio_dev is only 20 bytes per object on 32-bit platforms),
   but we potentially save many calls to malloc(). That depends on the
   application, of course, but this idea was implemented for libwhefs,
   where keeping mallocs down is a goal and we create an unusually
   high number of whio_dev objects. In that lib, we were able to cut a
   typical use case from 19 whio-related mallocs down to 1 (and that
   one happened in fopen(), beneath the whio_dev FILE handler, so we
   couldn't avoid it).

   Note that this approach to allocation is inherently not
   thread-safe, so if you need to create/destroy whio_dev objects from
   multiple threads, do not build with this option turned on. If you
   only create and destroy whio_dev objects within a single thread,
   this option can potentially save many calls to malloc() (and should
   perform much better).
*/
#if !defined(WHIO_CONFIG_ENABLE_STATIC_MALLOC)
#  define WHIO_CONFIG_ENABLE_STATIC_MALLOC 0
#endif

#if defined(WHIO_SIZE_T_BITS)
# error "WHIO_SIZE_T_BITS must not be defined before including this file! Edit this file instead!"
#endif

/** @def WHIO_SIZE_T_BITS

    WHIO_SIZE_T_BITS defines the number of bits used by whio's primary
    unsigned interger type. This is configurable so that certain
    client code (*cough* libwhefs *cough*) can use whio without having
    to fudge certain numeric types.

    This value must be one of (8,16,32,64), though values lower than
    32 may or may not work with any given component of the library.
    Most of the higher-level classes (like whio_udb, whio_vlbm,
    whio_ht) cannot function in 8-bit mode.
*/
#define WHIO_SIZE_T_BITS 32

/** @def WHIO_SIZE_T_PFMT

    Is is a printf-style specifier, minus the '%' prefix, for
    use with whio_size_t arguments. It can be used like this:

    @code
    whio_size_t x = 42;
    printf("The value of x is %"WHIO_SIZE_T_PFMT".", x );
    @endcode

    Using this constant ensures that the printf-style commands
    work when whio_size_t is of varying sizes.

    @see WHIO_SIZE_T_SFMT
*/

/** @def WHIO_SIZE_T_SFMT

WHIO_SIZE_T_SFMT is the scanf counterpart of WHIO_SIZE_T_PFMT.

@see WHIO_SIZE_T_PFMT
@see WHIO_SIZE_T_SFMT
*/

/** @def WHIO_SIZE_T_PFMTX

WHIO_SIZE_T_PFMTX is the hexidecimal counterpart of WHIO_SIZE_T_PFMT.

@see WHIO_SIZE_T_PFMT
*/

    
/** @def WHIO_SIZE_T_SFMTX

WHIO_SIZE_T_SFMTX is the hexidecimal counterpart to WHIO_SIZE_T_SFMT.

@see WHIO_SIZE_T_PFMT
@see WHIO_SIZE_T_SFMT
*/

/** @def WHIO_OFF_T_PFMT

WHIO_OFF_T_PFMT is the whio_off_t equivalent WHIO_SIZE_T_PFMT.

@see WHIO_SIZE_T_PFMT
@see WHIO_SIZE_T_SFMT
*/

/** @def WHIO_OFF_T_PFMTX

WHIO_OFF_T_PFMTX is the whio_off_t equivalent WHIO_SIZE_T_PFMTX.

@see WHIO_SIZE_T_PFMT
@see WHIO_SIZE_T_SFMT
*/

/** typedef some_unsigned_int_type_which_is_WHIO_SIZE_T_BITS_long whio_size_t

whio_size_t is a configurable unsigned integer type specifying the
ranges used by this library. Its exact type depends on the value of
WHIO_SIZE_T_BITS: it will be uintXX_t, where XX is the value of
WHIO_SIZE_T_BITS (8, 16, 32, or 64).

We use a fixed-size numeric type, instead of relying on a standard
type with an unspecified size (e.g. size_t) to help avoid nasty
surprises when porting to machines with different size_t
sizes. (Initial versions of this library used size_t, but i had all
sorts of headaches with it when i finally got access to a 64-bit
machine to try it on.)
*/

/** typedef some_signed_int_type whio_off_t

whio_off_t is a signed integer type used by i/o routines which need
to be able to specify coordinates relative to a certain position.

The size of whio_off_t is determined by the WHIO_SIZE_T_BITS
parameter, and is always (except in 64-bit mode) a signed integer type
one step larger than whio_size_t.  e.g. 32-bit whio_size_t has a
64-bit whio_off_t. This is to allow the full range of whio_size_t to
be used as an offset. If they had the same bitness, whio_off_t could
only cover half of the whio_size_t range (and on 64-bit builds that is
still the case).
*/
    
#if WHIO_SIZE_T_BITS == 8
#  warning "You're insane! You're just ASKING for overflows!"
#  define WHIO_SIZE_T_PFMT PRIu8
#  define WHIO_SIZE_T_PFMTX PRIx8
#  define WHIO_SIZE_T_SFMT SCNu8
#  define WHIO_SIZE_T_SFMTX SCNx8
#  define WHIO_OFF_T_PFMT PRIi16
#  define WHIO_OFF_T_PFMTX PRIx16
    typedef uint8_t whio_size_t;
    typedef int16_t whio_off_t;
#elif WHIO_SIZE_T_BITS == 16
#  define WHIO_SIZE_T_PFMT PRIu16
#  define WHIO_SIZE_T_PFMTX PRIx16
#  define WHIO_SIZE_T_SFMT SCNu16
#  define WHIO_SIZE_T_SFMTX SCNx16
#  define WHIO_OFF_T_PFMT PRIi32
#  define WHIO_OFF_T_PFMTX PRIx32
    typedef uint16_t whio_size_t;
    typedef int32_t whio_off_t;
#elif WHIO_SIZE_T_BITS == 32
#  define WHIO_SIZE_T_PFMT PRIu32
#  define WHIO_SIZE_T_PFMTX PRIx32
#  define WHIO_SIZE_T_SFMT SCNu32
#  define WHIO_SIZE_T_SFMTX SCNx32
#  define WHIO_OFF_T_PFMT PRIi64 /* yes, 64! FIXME: 'll' isn't legal in c89 */
#  define WHIO_OFF_T_PFMTX PRIx64 /* yes, 64! FIXME: 'll' isn't legal in c89 */
    typedef uint32_t whio_size_t;
    typedef int64_t whio_off_t;
#elif WHIO_SIZE_T_BITS == 64
#  define WHIO_SIZE_T_PFMT PRIu64
#  define WHIO_SIZE_T_PFMTX PRIx64
#  define WHIO_SIZE_T_SFMT SCNu64
#  define WHIO_SIZE_T_SFMTX SCNx64
#  define WHIO_OFF_T_PFMT PRIi64
#  define WHIO_OFF_T_PFMTX PRIx64
    typedef uint64_t whio_size_t;
    typedef int64_t whio_off_t;
#else
#  error "WHIO_SIZE_T_BITS must be one of: 8, 16, 32, 64"
#endif

/** @def WHIO_VOID_PTR_ADD()
   WHIO_VOID_PTR_ADD() is a workaround for gcc's -pedantic mode
   and other compilers which warn when void pointers are used
   in addition.
*/
#  define WHIO_VOID_PTR_ADD(VP,PLUS) ((void*)((unsigned char *)(VP)+(PLUS)))
/** @def WHIO_VOID_CPTR_ADD()
   Equivalent to WHIO_VOID_PTR_ADD() but applies to a const void
   pointer.
*/
#  define WHIO_VOID_CPTR_ADD(VP,PLUS) ((void const*)((unsigned char const *)(VP)+(PLUS)))

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* WANDERINGHORSE_NET_WHIO_CONFIG_H_INCLUDED */
/* end file include/wh/whio/whio_config.h */
/* begin file include/wh/whio/whio_common.h */
#ifndef WANDERINGHORSE_NET_WHIO_COMMON_H_INCLUDED
#define WANDERINGHORSE_NET_WHIO_COMMON_H_INCLUDED
/** @file whio_common.h
  Common API declarations for the whio API.

  Author: Stephan Beal (http://wanderinghorse.net/home/stephan/)

  License: Public Domain
*/

/** @page page_whio_conventions whio API Conventions

<b>Naming Conventions:</b>

whio uses the following naming conventions:

All library symbols (classes (C structures), functions, and enums)
start with the prefix "whio_".  Macros and library-wide enum values
typically are written in upper case, but there are exceptions to that
guideline. The public API uses lower_case_with_underscores except for
upper-case enum and macro values, which use
UPPER_CASE_WITH_UNDERSCORES. Some internal struct members use
camelCase, and such usage is a hint to the user that they should not
touch those members.

Any C++ code in the library is in the namespace whio.

Functions are named in the form whio_NOUN_VERB()
(e.g. whio_sometype_read()) instead of the more conventional
whio_VERB_NOUN() (e.g. whio_read_sometype()). The reasons for this
are:

- When using documentation generation tools to generate docs for this
code (e.g. doxygen), related functions can be grouped together by
sorting them. This makes finding related functionality easier for the
reader.

- The library is very object-oriented, and this convention is closer to
OO-style calling conventions, e.g. whio::sometype::read().


The overall object model used by this library is described in detail
in a separate article:

http://wanderinghorse.net/wh/computing/papers/#oo_c


<b>Empty Objects</b>

All public classes in the library provide empty-initialized objects
which can (and damned well should!) be used to initialize a newly-created
object of that type, be it on the heap, the stack, or vis a custom allocator.
The empty objects have two forms: a macro (for inlined initialization of
members in _other_ classes) and a const shared object.

The macro forms are always named CLASSNAME_empty_m, where "m" means
"macro" to distinguish from the non-macro form CLASSNAME_empty (the
const shared instance).

Note that the "empty" objects may contain non-NULL/non-0 values for
any given data member, so they should always be used to initialize new
objects. Using memset() (or similar) is not recommended because it
explicitly zeroes all bytes, whereas the empty-object approach allows
the library to set default initial values where it makes sense to do
so.

In the abstract, they are used like this:

@code
// Inlined initialization:

struct Foo {
    whio_ht ht;
    ...
} = {
    whio_ht_empty_m,
    ...
};

// Stack allocation:
whio_ht ht = whio_ht_empty;

// Heap- or custom allocation:
whio_ht * ht = (whio_ht*)malloc(sizeof(whio_ht));
*ht = whio_ht_empty;
@endcode
*/
       
#include <stdarg.h> /* va_list */

#ifdef __cplusplus
extern "C" {
#endif

    /**
       This enum houses various read/write mode flags which
       are used by certain i/o functions.

       Maintenance reminder: keep these at 1 byte or change
       whio_epfs_handle::iomode to suit.
    */
    enum whio_iomodes {
    /** An invalid/sentry mode. */
    WHIO_MODE_INVALID = 0,
    /** An unknown/not-yet-determined mode. */
    WHIO_MODE_UNKNOWN = 0x01,
    /** Signifies read mode. */
    WHIO_MODE_READ = 0x02,
    /** Signifies write mode. */
    WHIO_MODE_WRITE = 0x04,
    /** Mask for "only" modes (r/o, w/o). */
    WHIO_MODE_FLAG_ONLY = 0x08,
    /** Signifies read-only mode. */
    WHIO_MODE_RO = WHIO_MODE_READ | WHIO_MODE_FLAG_ONLY,
    /** Signifies read/write mode. */
    WHIO_MODE_RW = WHIO_MODE_READ | WHIO_MODE_WRITE,
    /** Signifies write-only mode. */
    WHIO_MODE_WO = WHIO_MODE_WRITE | WHIO_MODE_FLAG_ONLY,
    /**
       When masked with WHIO_MODE_WRITE, is semantically equivalent to
       to open(2)'s O_CREAT flag (except that we add the missing 'E').
    */
    WHIO_MODE_FLAG_CREATE = 0x10,
    /**
       Convenience equivalent of (WHIO_MODE_RW | WHIO_MODE_FLAG_CREATE).
    */
    WHIO_MODE_RWC = WHIO_MODE_RW | WHIO_MODE_FLAG_CREATE,
    /**
       Semantically equivalent to O_EXCL used by open(2).
    */
    WHIO_MODE_FLAG_FAIL_IF_EXISTS = 0x20,
    /**
       Signifies that the device should be truncated to 0 bytes after
       opening. Only applicable in write mode, as truncating a
       read-only device would leave one with nothing left to read.
    */
    WHIO_MODE_FLAG_TRUNCATE = 0x40,
    /**
       Equivalent to WHIO_MODE_FLAG_FAIL_IF_EXISTS
    */
    WHIO_MODE_FLAG_EXCL = WHIO_MODE_FLAG_FAIL_IF_EXISTS,
    /**
       Not yet used. Devices which support an "append" mode
       (like via fopen()) may support this.
    */
    WHIO_MODE_FLAG_APPEND = 0x80

    };
    typedef enum whio_iomodes whio_iomodes;


    /**
       A marker type for functions which take or return a mask of
       whio_imodes flags. Using whio_iomodes in such signatures is a
       "conversion to int" for C++ and causes a compile-time error.
     */
    typedef unsigned char whio_iomode_mask;

    
/** @struct whio_rc_t

   Functions in the whio api which return an int almost always return
   a value from the whio_rc object. All members of this type must have
   a non-zero value, except for:

   - The OK member, which must be 0.

   - SizeTError, which is defined as (whio_size_t)-1

   - This class does not use the integer value -1 for any error code,
   to avoid potential confusion with SizeTError. This incidentally
   also helps avoid collisions with many system-level i/o routines
   (which some whio_dev implementations proxy), which return -1 and
   set errno on error.

   The exact numeric values for all error codes are unspecified except
   as described above.

   Clients are not intended to use this type directly, but are
   expected to use the shared whio_rc object.
*/
typedef struct whio_rc_t
{
    /*
      Maintenance reminder: if the members are re-ordered, update the
      comments in the definition of whio_rc in whio.c!
    */

    /**
       The non-error value, always equals 0.
    */
    int OK;

    /**
       Error in argument handling (e.g. unexpected arg type, count,
       etc.).
     */
    int ArgError;

    /**
       Read or write error.
    */
    int IOError;

    /**
       Memory allocation error.
    */
    int AllocError;

    /**
       An internal error in the API.
    */
    int InternalError;

    /**
       An out-of-range error. e.g. wrong size or value.
    */
    int RangeError;

    /**
       Indicates that an operation was interrupted by a signal, or
       possibly by a routine provided for the purpose of interrupting
       a long-running action.
    */
    int InterruptedError;
    
    /**
       A requested resource could not be accessed, or write
       permissions are required but denied.
    */
    int AccessError;

    /**
       A data consistency error (or a bug makes the data look
       corrupted even though it is not).
    */
    int ConsistencyError;

    /**
       Indicates that the called routine is not yet implemented.
    */
    int NYIError;

    /**
       Indicates that the requested option or operation is not
       supported.
    */
    int UnsupportedError;

    /**
       Indicates some form of type mismatch or an unexpected type.
    */
    int TypeError;
    /**
       Indicates that some device-specific operation has determined
       that the device is full and cannot take more input.
    */
    int DeviceFullError;

    /**
       Indicates some form of device-specific locking error, for
       devices which support locking.
    */
    int LockingError;

    /**
       Indicates some form of device-specific hashing-related error.
    */
    int HashingError;

    /**
       Indicates some resource could not be found.
    */
    int NotFoundError;

    /**
       A specialized case of LockingError which specifies that a
       device was modified by a conncurrent thread. Note that this
       support must explicitly be built in to a device, so do not
       expect most library routines to ever return this unless they
       document it.
    */
    int ConcurrentModificationError;
    
    /**
       The catch-all "nobody really knows what happened" error.
    */
    int WTFError;

    /**
       This is equivalent to (whio_size_t)-1, and is used by routines which
       need an error value for a whio_size_t object.
    */
    whio_size_t SizeTError;
} whio_rc_t;

/** @var whio_rc
   A shared instance of whio_rc_t which contains the "official" values
   of the common error codes for the whio API.
*/
extern const whio_rc_t whio_rc;

/**
   When passed one of the integer values from the whio_rc object
   this function returns a string in the form "whio_rc.ErrorName".
   If rc is not a known error value then NULL is returned.

   The returned string is static.
*/
char const * whio_rc_string( int rc );
    
/** @struct whio_client_data

whio_client_data is an abstraction for tying client-specific data to a
whio_dev or whio_stream object. The data is not used by the public
whio_dev/whio_stream API with one exception: when
whio_dev_api::close() or whio_stream_api::close() is called, the
implementation must clean up this data IFF the dtor member is not
0. For example:

  @code
  if( my->client.dtor ) {
    my->client.dtor( my->client.data );
    my->client = whio_client_data_empty; // zero it out
  }
  @endcode
   
*/
struct whio_client_data
{
    /**
       Arbitrary data associated with an i/o device or stream.

       This data is for sole use by whio_dev and whio_stream clients,
       with one important exception: if dtor is not 0 then device
       implementations take that as a hint to destroy this object
       using that function.

       The object pointed to by client.data should not do any i/o on
       this stream or any stream/device during its destructor. Since
       client.data can point to arbitrary objects, it is impossible
       for this API to ensure that they are destroyed in a kosher
       order.  Thus it is the client's responsibility to use
       client.data wisely and carefully. A good use would be for a
       client-side buffer, e.g.  to implement buffered readahead. A
       bad use would be using it to store links to other i/o devices,
       as the destructor would presumably then close or flush them and
       they might not be live at that point. Device implementors should
       use whio_impl_data to store "more private" data.
    */
    void * data;
    /**
       If this function is not 0 then whio_dev implementations
       MUST call this function, passing the data member to it,
       in their cleanup routines. If it is 0 then they must
       ignore the data member.
    */
    void (*dtor)( void * );
};

typedef struct whio_client_data whio_client_data;
/**
   Static initializer for whio_client_data objects.
*/
#define whio_client_data_empty_m {0/*data*/,0/*dtor*/}

/**
   An empty whio_client_data object for use in initialization
   of whio_client_data objects.
*/
extern const whio_client_data whio_client_data_empty;

/**
   Holds private implementation details for whio_dev and whio_stream
   and whio_dev instances. Each instance may (and in practice always
   does) store instance-specific data here. These data are for use
   only by the functions related to this implementation and must be
   cleaned up via whio_dev::close() or whio_stream::close().
*/
struct whio_impl_data
{
    /**
       data is SOLELY for use by concrete implementations of
       whio_stream and whio_dev, and not by clients of those types.
       
       This field can be used to store private data required by the
       implementation functions. Each instance may have its own
       information (which should be cleaned up via the close() member
       function, assuming the object owns the data).

       This data should be freed in the owning object's close()
       routine.
    */
    void * data;

    /**
       A type identifier for use solely by whio_dev and whio_stream
       implementations, not client code. If the implementation uses
       this (it is an optional component), it must be set by the
       whio_dev/whio_stream initialization routine (typically a
       factory function).

       This mechanism works by assigning some arbitrary opaque value
       to all instances of a specific whio_dev implementation. The
       implementation funcs can then use that to ensure that they are
       passed the correct type. The typeID need not be public, but may
       be so if it should be used by third parties to confirm that
       whio_dev/whio_stream objects passed to them are of the proper
       type.

       Note also that the typeID need not be (and normally is not)
       persistant across application sessions. It may change between
       executions of an application.
    */
    void const * typeID;
};
/**
   Static initializer for whio_impl_data objects.
*/
#define whio_impl_data_empty_m {0/*data*/,0/*dtor*/}
/** Convenience typedef. */
typedef struct whio_impl_data whio_impl_data;
/**
   Empty initializer object for whio_impl_data.
*/
extern const whio_impl_data whio_impl_data_empty;

/**
   Tries to convert an fopen()-compatible mode string to a number
   compatible with whio_dev::iomode() and whio_stream::iomode().

   On error WHIO_MODE_INVALID is returned, BUT this function does no
   validation checking on the input string. It simply searches for
   characters used by fopen(), e.g. 'r', 'w', 'a', and '+'.  Thus if
   passed the invalid mode "rwa" then it would return
   read/write/append flags.
   
   This function is intended for use with whio_dev/whio_stream
   factories which use an fopen()-like mode string.
*/
whio_iomode_mask whio_mode_to_iomode( char const * mode );

/**
   whio_realloc_f is a typedef for de/re/allocation routines
   semantically compatible to realloc(), but with the addition of a
   third parameter which can be used to pass allocator-specific state.
   This interface is used by whio to genericize how memory is
   de/re/allocated, to allow us to replace the underlying allocation
   routines for special cases where we want control over the
   allocation source.

   This interface is internally used for allocating most memory within
   the whio API. (The only exception is the memory-based i/o devices,
   which use malloc()/realloc()/free() because they may grow arbitrary
   large.)

   The first two parameters must be semantically compatible with the
   equivalent call to realloc(3).
   
   The state parameter should hold any state needed for the custom
   de/re/allocation algorithm. Ownership of that state object is
   completely dependent on the allocator and its rules, but it is
   typically a pointer to an allocator object with arbitrary
   allocator-internal data. Any custom allocator which can support the
   overall realloc(3) interface/semantics will suffice.

   By default, most of the API which uses this type uses a default
   implementation of this interface which simply forwards all calls to
   realloc(3) and ignores the third argument.

   Rules for implementations:

   1) If passed (NULL,non-0,anything) they must behave like a malloc()
   request, returning at least the given number of bytes on success
   and NULL on error.

   2) If passed (anything,0,anything) they must behave like free() and
   return void. It may legally assert() (or similar) if passed memory
   it does not own/manage (this is common behaviour in standard
   free(3) implementations). Implementations are required to
   gracefully handle a NULL for the first argument (i.e. ignore it).

   3) If passed (non-NULL,non-0,anything), they have the following
   options:

   3a) If they support a realloc operation, it must be semantically
   compatible with realloc(3). That implies that conditions (1) and
   (2) are met.

   3b) If they do not support a realloc operation, they have two
   options:

   3b1) If the allocator knows that the new size does not require
   moving the memory (i.e. is equal to or smaller than the original
   size, or does not grow enough to move it into a new memory block),
   it may legally return the original pointer.

   3b2) Return NULL (failing the realloc).

   Provided that the third argument (allocState) is ignored,
   realloc(3) is considered a compliant implementation (indeed, it is
   the reference implementation) for all operations, meeting
   requirements 1, 2, and (implicitly) 3a.
   
   An interesting ACHTUNG: realloc( someObject, 0 ) is apparently not
   guaranteed to return NULL, but may also return "some value suitable
   for passing to free()." Thus it is philosophically impossible to
   know if realloc(obj,0) ever really succeeds in freeing the memory
   because we have no constant to compare the return value against
   except NULL. Anyway... just something to be aware of.
*/
typedef void * (*whio_realloc_f)( void * m, unsigned int n, void * state );

/**
   An abstract interface for memory de/re/allocator classes.
*/
struct whio_allocator
{
    /**
       The de/re/allocator function. See whio_realloc_f for the rules
       imposed on implementations.
    */
    whio_realloc_f realloc;
    /**
       Implementation-specific state data for the realloc member, to
       be passed as the third argument to that function.
    */
    void * state;
};
/** Convenience typedef. */
typedef struct whio_allocator whio_allocator;
/** An empty-initialized whio_allocator object, for use when static/inline
    initialization is required.
*/
#define whio_allocator_empty_m { NULL/*realloc*/,NULL/*state*/ }

/**
   An EXPERIMENTAL memory source for use by the whio library.  If this
   object is to be configured by client code, it MUST be done before
   ANY objects are created by this library. Note that it is only
   possible to guaranty that setup can be done in time at the
   application level, not the library level. It is also not possible
   to guaranty (at all) if an application is compiled as C++, because
   C++ allows static object initialization to trigger arbitrary
   functions and constructors, which could themselves instantiate whio
   objects.

   Never, ever, ever set its realloc member to NULL. NOT EVER!

   Never, ever, ever change its realloc OR state members after any
   whio resources have been created (i.e. opening any devices or
   streams). NOT EVER!

   If allocation must be safe across threads, make sure your realloc
   implementation supports it.

   Thus: don't use this unless you are 100% sure you know what you're
   doing. And then, only do it as soon as possible after main() is
   entered. And then pray that your code doesn't someday mutate in
   such as way as to unwittingly violate this object's rules.

   (The only reason this object is in the public API is so that i can
   make use of it in a few apps where i'm using custom allocators
   to squeeze out every malloc() i can.)
*/
extern whio_allocator whio_memory_source;

/**
   A whio_allocator instance which simply acts as a proxy for
   realloc(3).
*/
extern const whio_allocator whio_allocator_stdalloc;

/**
   Semantically compatible with realloc(3), and by default it simply
   is a proxy for realloc(), but it may be configured to use a memory
   source other than the standard allocator.

   This function should be used by the internal whio API as well as
   concrete whio_dev/whio_stream implementations which need small
   amounts of memory for the object-private state. It should _not_ be
   used by general client code, nor by device implementations which
   need large amounts of memory (e.g. storage for an in-memory
   device), as it may be configured to a custom memory source which is
   sized for whio's needs (very frugal) but not general client-side
   needs (arbitrarily large). By "small amounts" of memory we mean "up
   to about 200 bytes", but that is a very arbitrary guideline. The
   amount of memory allocated from it only (might) play a role if the
   library is configured to use an alternative memory source and that
   source is not arbitrarily large (via modifying the
   whio_memory_source object).

   Internal notes: this is simply a public interface for
   whio_memory_source.realloc(m,n,whio_memory_source.state). However,
   because whio_memory_source is experimental and might go away,
   this function should be used instead of using that object directly.
*/
void * whio_realloc( void * m, unsigned int n );

/**
   Returns whio_realloc( NULL, n ).
*/
void * whio_malloc( unsigned int n );

/**
   If m is not NULL then it calls whio_realloc( m, 0 ). There is in
   general no way to know if a free() operation fails unless the
   underlying cleanup routine asserts (or similar) on error (which is
   the normal behaviour when using GNU libc, and possibly other libc
   implementations).

   It is legal (a no-op) to pass NULL.
*/
void whio_free( void * m );


/**
   A mutex class for use with specific whio devices.

   To activate the mutex for a class which contains one of these
   objects, assign all of the members to appropriate values.
   You must either set neither or both of the lock() and unlock()
   members. The state member may be null if the lock/unlock functions
   do not use it.
*/
struct whio_mutex
{
    /**
       Intended to lock a mutex. This interface does not require
       that it be a recursive lock, but it may need to be so if
       the client uses the same mutex for outer-level locking
       regarding a given allocator. It is passed the state member
       as its only parameter.

       Must return 0 on success, non-zero on error.

       API routines which support a mutex should return an
       implementation-specific error code if the mutex cannot be
       locked.
    */
    int (*lock)( void * );
    /**
       Intended to unlock the mutex locked by lock(). It is passed
       the state member as its only parameter.

       If lock is non-null then unluck must also be non-null and
       complementary to the lock function.

       Must return 0 on success, non-zero on error.
    */
    int (*unlock)( void * );
    /** Arbitrary state data which should be passed to lock() and unlock(),
        e.g. a platform-specific mutex type.
    */
    void * state;
};
/** Convenience typedef. */
typedef struct whio_mutex whio_mutex;
/** Empty-initialized whio_mutex object. */
#define whio_mutex_empty_m { NULL/*lock*/,NULL/*unlock*/,NULL/*state*/}
/** Empty-initialized whio_mutex object. */
extern const whio_mutex whio_mutex_empty;

/**
   A generic buffer class.

   They can be used like this:

   @code
   whio_buffer b = whio_buffer_empty;
   int rc = whio_buffer_reserve( &buf, 100 );
   if( 0 != rc ) { ... allocation error ... }
   ... use buf.mem ...
   ... then free it up ...
   whio_buffer_reserve( &buf, 0 );
   @endcode
*/
struct whio_buffer
{
    /**
       The number of bytes allocated for this object.
       Use whio_buffer_reserve() to change its value.
     */
    whio_size_t capacity;
    /**
       The number of bytes "used" by this object. It is not needed for
       all use cases, and management of this value (if needed) is up
       to the client. The whio_buffer public API does not use this
       member. The intention is that this can be used to track the
       length of strings which are allocated via whio_buffer, since
       they need an explicit length and/or null terminator.
     */
    whio_size_t used;

    /**
       This is a debugging/metric-counting value
       intended to help certain malloc()-conscious
       clients tweak their memory reservation sizes.
       Each time whio_buffer_reserve() expands the
       buffer, it increments this value by 1.
    */
    whio_size_t timesExpanded;

    /**
       The memory allocated for and owned by this buffer.
       Use whio_buffer_reserve() to change its size or
       free it.
    */
    void * mem;
};
/** Convenience typedef. */
typedef struct whio_buffer whio_buffer;

/** An empty-initialized whio_buffer object. */
#define whio_buffer_empty_m {0/*capacity*/,0/*used*/,0/*timesExpanded*/,NULL/*mem*/}
/** An empty-initialized whio_buffer object. */
extern const whio_buffer whio_buffer_empty;

/**
   Reserves the given amount of memory for the given buffer object.

   If n is 0 then buf->mem is freed and its state is set to
   NULL/0 values.

   If buf->capacity is less than or equal to n then 0 is returned and
   buf is not modified.

   If n is larger than buf->capacity then buf->mem is (re)allocated
   and buf->capacity contains the new length.

   On success 0 is returned. On error non-0 is returned and buf is not
   modified.

   buf->mem is owned by buf and must eventually be freed by passing an
   n value of 0 to this function.

   buf->used is never modified by this function.

   Pedantic notes:

   This routine uses realloc() for memory allocation, rather than
   whio_realloc(), because the latter is intended for allocation of
   relatively small amounts of data and may have a bounded size,
   whereas the buffer should be able to grow as much as the system
   will allow it to.
*/
int whio_buffer_reserve( whio_buffer * buf, whio_size_t n );

/**
   Fills all bytes of the given buffer with the given character.
   Returns the number of bytes set (buf->capacity), or 0 if
   !buf or buf has no memory allocated to it.
*/
whio_size_t whio_buffer_fill( whio_buffer * buf, char c );

/**
   Works like whprintfv(), but all output is appended to the given
   buffer (expanding it as needed). This function uses buf->used to
   determine the starting point for appending the bytes, and
   increments buf->used as data is added to the output. Thus clients
   can check buf->used to find the length of the formatted string, and
   can append to an existing buffer by ensuring that buf->used is
   pointing to its logical end offset. This function of course
   NULL-terminates the string, but that NULL is not counted in the
   buf->used bytes (i.e. it behaves like strlen() in that regard).

   Returns 0 on success or an unspecified non-0 value on error.  (It
   is unspecified due partially to conflicts in the return value
   conventions between whio and whprintf().)
*/
int whio_buffer_vprintf( whio_buffer * buf, char const * fmt, va_list vargs );

/**
   Identical to whio_buffer_vprintf(), but takes elipsis arguments
   instead of a va_list.
*/
int whio_buffer_printf( whio_buffer * buf, char const * fmt, ... );


#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* WANDERINGHORSE_NET_WHIO_COMMON_H_INCLUDED */
/* end file include/wh/whio/whio_common.h */
/* begin file include/wh/whio/whio_dev.h */
#ifndef WANDERINGHORSE_NET_WHIO_DEV_H_INCLUDED
#define WANDERINGHORSE_NET_WHIO_DEV_H_INCLUDED


#include <stdio.h> /* FILE */
#include <stdint.h> /* uint32_t */
#include <stdarg.h> /* va_list */
#include <stddef.h> /* ??? */
#include <stdarg.h> /* va_list */

/*
   This file contains declarations and documentation for the generic
   whio_dev API. The specific iodevice implementations are declared
   in whio_devs.h.
*/

/** @page page_whio_dev whio_dev I/O API

   Author: Stephan Beal (http://wanderinghorse.net/home/stephan/)

   License: Public Domain

   whio encapsulates an i/o device API. It originally developed as
   parts of two other libraries, but the parts were found to be generic
   enough (and complementary enough) to fork out into a single library.

   The API provides interfaces for working with random-access devices
   (via the whio_dev interface) and sequential streams (via the
   whio_stream interface).

   Features:

   - Easy to use - modelled after the standard FILE API.

   - Comes with back-end implementations supporting FILE handles,
   dynamic memory buffers (with the option to expand on demand),
   and client-specified memory ranges (similar to mmap()).

   - Utility functions for doing common things, such as finding the
   size of a device, encoding/decoding certain basic types, and doing
   printf-style formatted output to devices.

   - An ioctl-like interface to perform some device-specific operations
   (for those times when genericness just won't do the job).


   Requirements:

   - C99's stdint.h is required for fixed-size integers and their
   portable printf/scanf specifiers (e.g. PRIu32 and friends).

   - It unfortunately needs fileno() in one place. fileno() is not
   specified by C89, but is found in most (all?) UNIX environments and
   is specified by POSIX. (It is apparently impossible to truncate a
   file without either the file's name or file handle number, as
   opposed to via a FILE handle.)

   This code has been shown to compile and pass basic sanity checks on:

   - Linux x86/32 with gcc 4.3.x and tcc
   - Linux x86/64 with gcc 4.2.x and tcc
   - Solaris 10 on sparcv9 (v240) with gcc 3.4.3 and SunStudio 12

   Example:
@code
char const * fname = "myfile.out";
whio_dev * dev = whio_dev_for_filename( fname, "r+" );
dev->api->write( dev, "hi, world!\n", 11 ); // 11 = size of the data bytes
dev->api->finalize( dev ); // flush and close device

// Now read it back:
dev = whio_dev_for_filename( fname, "r" );
enum { bufSize = 1024 };
char buf[bufSize]; // input buffer
whio_size_t n = 0;
while( 0 != (n = dev->api->read( dev, buf, bufSize ) ) )
{
    printf("Read %"WHIO_SIZE_T_PFMT" bytes\n", n );
}
dev->api->finalize(dev);
@endcode

Note the use of WHIO_SIZE_T_PFMT instead of "%%u", in the printf call,
so that the code will work correctly with varying sizes of
whio_size_t.
*/

#ifdef __cplusplus
extern "C" {
#endif


struct whio_dev;

/**
   whio_dev_api defines the functions for the whio_dev interface.
   Set the documentation for whio_dev for why this was abstracted
   into a separate class from whio_dev.

   Each whio_dev object has an associated whio_dev_api object. In
   practice, all instances of a specific class of whio_dev share a
   single instance of this class as their 'api' member.

   This type is not intended to be instantiated and used by client
   code.
*/
struct whio_dev_api
{
    /**
       Reads, at most, n bytes from the underlying device and writes
       them to dest. The read number of bytes is returned, or 0 at
       EOF. A short read normally indicates EOF was reached, but can
       also be the result of an i/o error.

       On a non-i/o error (e.g. !dev or !dest), implementations should
       return 0.
    */
    whio_size_t (*read)( struct whio_dev * dev, void * dest, whio_size_t n );

    /**
       Writes n bytes from src to dev, returning the number of
       bytes written. On error, the return value will differ from
       n.

       On a non-i/o error (e.g. !dev or !dest), implementations should
       return 0.
    */
    whio_size_t (*write)( struct whio_dev * dev, void const * src, whio_size_t n );

    /**
       Must close the i/o device, such that reading and writing are
       no longer possible. It is not generically possible to re-open
       a closed device.

       This routine should also deallocate any resources associated
       with the device (but not dev itself). If this routine does not
       (i.e., it defers that to finalize()) then stack-allocated
       whio_dev objects cannot be cleaned up uniformly.

       If dev->client.dtor is not null then this routine must call
       that function and pass it dev->client.data. If it is null then
       dev->client.data must not be modified (the lack of a destructor
       function is a signal that the client owns the object).

       This interface requires that close() must be called from the
       finalize() member and that close() must flush the device (if
       needed), so client code normally does not need to call
       close(). It is provided so that whio_dev objects which are
       created on the stack (which would be unusual but possibly
       useful for some cases) can be properly cleaned up.

       Ownership of the underlying native device is defined by the
       factory function (or similar) which creates the whio_dev
       wrapper.

       This function must return true if it could close the device
       or false if it cannot (e.g. if !dev or it was not opened).
     */
    bool (*close)( struct whio_dev * dev );

    /**
       Must call close() and then free dev. After calling this, dev is
       no longer a valid object.  If passed null, the results are
       undefined (but implementations are incouraged to ignore it,
       possibly emiting a debugging message).
    */
    void (*finalize)( struct whio_dev * dev );

    /**
       Returns 0 if the device is in a good state, else it returns
       an implementation-defined non-zero value. Implementations
       are encourage to use the symbolic values from whio_rc_t,
       but some implementations may be able to return exact
       error codes from the underlying device (e.g. a file handler
       could return a value from ferror() or an errno value related
       to it).
    */
    int (*error)( struct whio_dev * dev );

    /**
       Should clear any error state and return whio_rc.OK on success.
       If this function returns an error (an implementation-defined
       non-zero value), the error state should be assumed
       unrecoverable and the device should not be used.

       For compatibility with the standard FILE API (in particular,
       clearerr()), this routine should be used to clear any
       end-of-file flag (if necessary), though that is not all
       implementations have such a flag to clear.
    */
    int (*clear_error)( struct whio_dev * dev );

    /**
       Returns an implementation-defined non-zero value at eof or 0 at
       not-eof.
     */
    int (*eof)( struct whio_dev * dev );

    /**
       Returns the current position of the device, or
       whio_rc.SizeTError on error. An an example of an error, calling
       truncate() to truncate a device may leave its cursor out of
       bounds, which may be considered an error by the underlying
       implementation (though some allow arbitrary placement but may
       fail to be able to read/write from/to the given position).

       On a non-i/o error (e.g. !dev), whio_rc.SizeTError is returned.

       This function can normally be implemented by calling
       seek(dev,0,SEEK_CUR), but many custom i/o device types know
       their current location and can return it more quickly than
       checking a seek() request.
    */
    whio_size_t (*tell)( struct whio_dev * dev );

    /**
       Sets the current position within the stream, following the same
       semantics as fseek() except that:

       - the return value is the new position.

       - If the seek would move the cursor out of bounds, it MAY be
       kept in bounds instead (i.e. at 0 or EOF). This is
       implementation-dependent (e.g. an in-memory back-end may not be
       able to grow). As a general rule, seek() is unbounded, and a
       validity check on the position is deferred until the next read
       or write.

       - Implementations MAY return whio_rc.SizeTError for the
       following cases:

       - !dev
       - whence==SEEK_SET and pos is negative.
       - whence is not one of SEEK_SET, SEEK_CUR, or SEEK_END.
       - seek fails in some other way.

       Alternately, implementations may rely on (largely undocumented)
       behaviour of the underlying implementation. e.g. fseek() does
       not document what happens on SEEK_SET with a negative value, but
       we can hope that it fails in that case.
    */
    whio_size_t (*seek)( struct whio_dev * dev, whio_off_t pos, int whence );

    /**
       Flushes the underying stream (not all streams support/need
       this). On success it must return whio_rc.OK. On error it
       returns an implementation-defined non-zero value. Devices
       which do not use flushing should return 0.
    */
    int (*flush)( struct whio_dev * dev );

    /**
       Changes the size of the device to the new size. On success,
       whio_rc.OK is returned, otherwise an implementation-specified
       non-0 value is returned.

       Whether or not it is possible to increase the size of a device
       using this function is unfortunately implementation-specified.
       See the Linux man pages for ftruncate() for interesting
       details.

       The underlying cursor position must not be changed by calling
       this function.
    */
    int (*truncate)( struct whio_dev * dev, whio_off_t size );

    /**
       ioctl() is a "back door" to give access to certain
       implementation-specific features. Devices need not support
       this, in which case they should return
       whio_rc.UnsupportedError. The second argument specifies the
       requested device-specific operation, which will normally be
       some common enum or macro value. The remaining arguments depend
       100% on the operation, and must be specified in the
       documentation for that operation.

       If the requested operation is supported then whio_rc.OK should
       be returned on success, else some error value OTHER than
       whio_rc.UnsupportedError should be returned. When passing on an
       underlying error code, there may be a code collision with
       whio_rc.UnsupportedError - that is unfortunate but unavoidable
       and we won't lose any sleep over it.

       To pass elipsis-style arguments, use whio_dev_ioctl() (and see
       that function's docs for why this one takes a va_list).
    */
    int (*ioctl)( struct whio_dev * dev, int operation, va_list args );

    /**
       This function must return a mask of whio_iomodes values which
       represent its read/write mode. If it cannot determine the mode
       the it should return WHIO_MODE_UNKNOWN. If the dev pointer is
       invalid or not of the correct type then WHIO_MODE_INVALID
       should be returned.
    */
    whio_iomode_mask (*iomode)( struct whio_dev * dev );
};
typedef struct whio_dev_api whio_dev_api;

/**
   whio_dev is an interface for communicating with an underlying
   random access data store. It is modelled after the
   POSIX-standard FILE API, and it "should" be able to act as a
   wrapper for any stream type for which we can implement the
   appropriate operations. The most significant limitation is that the
   underlying device type must support random read/write access (if it
   does not, not all operations of this type will be meaningful).

   There is no "default" whio_dev implementation - each underlying
   data store needs a different implementation. This type defines the
   conventions of the interface as specifically as possible, however.

   The member functions of this struct are abstracted into the
   whio_dev_api class (via the 'api' member of this class). The
   primary reason for this is because all instances of a certain class
   of whio_devices, in practice, share a single set of implementation
   functions. By referencing the functions this way we save
   (sizeof(whio_dev_api) - sizeof(whio_dev_api*)) bytes on each instance
   of whio_dev, and in its place we have a single shared (and static)
   instance of the implementation's API object.

   Thread safety: it is never legal to use any given whio_dev instance
   from more than one thread at a single time, and doing so will
   almost certainly corrupt the internal state of the stream. e.g. its
   read/write position may be moved by another thread, causing a read
   or write to go somewhere other than desired. It is in theory not
   problematic for multiple threads to share one whio_dev instance as
   long as access to the device is strictly serialized via a
   marshaller and device positioning operations are implemented taking
   that into account.
*/
typedef struct whio_dev
{
    /**
       Holds all "member functions" of this interface.  It is never
       legal for api to be NULL, and if a device with a NULL api
       member is used with the whio API then a segfault will certainly
       quickly result.
    */
    whio_dev_api const * api;

    /**
       Holds instance-specific, implementation-dependent
       information. Not for use by client code. The
       implementation-specific close() method should free up this
       memory.
    */
    whio_impl_data impl;

    /**
       This data is for sole use by whio_dev clients, with one
       important exception: see the docs for whio_client_data for
       details.
    */
    whio_client_data client;
} whio_dev;

/**
    Empty whio_dev object for clean initialization.
*/
#define whio_dev_empty_m {0/*api*/, whio_impl_data_empty_m, whio_client_data_empty_m }
/**
   Empty whio_dev object for clean initialization.
*/
extern const whio_dev whio_dev_empty;

/**
   Works like malloc(), but beware...

   Creates an empty, non-functional whio_dev object and returns it.
   The object must be populated by the caller and must eventually
   be destroyed by calling whio_dev_free() AFTER the private parts
   of the object are cleaned up (see whio_dev_free() for details).

   Clients of whio_dev objects SHOULD NOT use this routine - it is
   intended for use by whio_dev factory/initialization routines for
   reasons explained below.

   The default implementation simply returns the result of calling
   malloc(sizeof(whio_dev)), but the interface allows it to use
   an alternate memory source and have other side effects.

   A side effect of the undefined allocation rules is that devices
   returned from this function may not be valid if used after
   main() exits (e.g. via an atexit() handler) because the underlying
   allocation mechanism might have been cleaned up already.

   Why this function exists:

   As part of a related project i am looking to avoid using malloc()
   when necessary. For that project i would like to provide my own
   allocation pool for whio_dev objects (which are allocated
   relatively often in that framework). So, to that end, the i/o
   device implementations which come with whio use this routine to
   allocate their objects.

   @see whio_dev_free()
*/
whio_dev * whio_dev_alloc();

/**
   BIG FAT HAIRY WARNING:

   - This function must ONLY be passed objects allocated via
   whio_dev_alloc().

   - This function DOES NOT call dev->api->finalize(dev) or
   dev->api->close(dev). Instead, this function is intended to be
   called from one of those routines after the device's private data
   has been cleaned up.

   This function effectively passes the given object to free(), but
   the implementation is free to use a different alloc/dealloc
   method. In any case, clients should treat dev as invalid after this
   call.

   @see whio_dev_alloc()
*/
void whio_dev_free( whio_dev * dev );

/**
   This function is a bit of a workaround for the whio_dev::ioctl()
   interface.

   The public ioctl() function on Linux looks like:

   @code
   int ioctl( int descriptor, int operation, ... );
   @endcode

   But if we give whio_dev::ioctl() that interface, passing a va_list
   instead of elipsis, it becomes problematic to pass on those
   arguments to the underlying ioctl() function (or do equivalent
   operations). So we provide the elipsis form here and the va_list
   form in the whio_dev::ioctl() interface.
*/
int whio_dev_ioctl( whio_dev * dev, int operation, ... );

/**
   Returns the size of the given device.

   It first tries the whio_dev_ioctl_GENERAL_size ioctl. If that works
   then its value is returned. As a fallback, this routine seeks to
   end position of the device (seek() returns the position (=the
   size)). It then re-positions the cursor to its pre-call position.
   If one of the seek()s fails then whio_rc.SizeTError is returned.

   As a general rule, concrete whio_dev implementations shipped with
   this library which _can_ internally support an optimized
   (non-seeking) method for getting their size _do_ support the
   whio_dev_ioctl_GENERAL_size ioctl.
*/
whio_size_t whio_dev_size( whio_dev * dev );

/**
   Equivalent to dev->api->set( dev, 0, SEEK_SET ), but returns whio_rc.OK
   on success.
*/
int whio_dev_rewind( whio_dev * dev );

/**
   Equivalent to dev->api->write( dev, data, n ).
*/
whio_size_t whio_dev_write( whio_dev * dev, void const * data, whio_size_t n );

/**
   Positions dev to pos and then writes n bytes from data to it. May
   return either whio_rc.SizeTError (if the seek fails) or the result
   of calling dev->api->write( dev, data, n ). On success it will
   return n.

   After writing, the new cursor position is one after the last write
   position.
*/
whio_size_t whio_dev_writeat( whio_dev * dev, whio_size_t pos, void const * data, whio_size_t n );

/**
   The read() counterpart of whio_dev_writeat().
*/
whio_size_t whio_dev_readat( whio_dev * dev, whio_size_t pos, void * data, whio_size_t n );

/**
   Copies all of src, from the beginning to EOF, to dest, starting
   at dest's current position. Returns whio_rc.OK on success.
*/
int whio_dev_copy( whio_dev * src, whio_dev * dest );

/**
   UNTESTED!

   Copies n bytes from src to dest, using the current cursor position
   for both devices.

   The data is copied internally, using an unspecified buffer size, to
   shovel the data between the two devices.

   If outCount is not NULL then it will be set to the total number
   of bytes writte, which equals n on success.
   
   Returns 0 on success, non-0 on error. If 0==n then this function
   has no side effects and returns whio_rc.RangeError.  If either src
   or dest are NULL then whio_rc.ArgError is returned (even if 0==n).
   If dest does not report itself as writable, whio_rc.AccessError is
   returned.

   On error, dest may have been partially written to.
*/
int whio_dev_copy_n( whio_dev * src, whio_size_t n, whio_dev * dest, whio_size_t * outCount );

/**
   Similar to printf() and friends, this writes a formatted string
   to the given output device. Returns the number of bytes written.
   In the general case it is not possible to know if a given conversion
   fails, so it is not possible to say how many bytes *should* have
   been written.

   The formatted data is not copied, but is instead sent (via proxy
   functions) to the destination device directly, so it may be
   arbitrarily large without any copy penalty. Nonetheless, as with
   most formatted writing, this routine has an extremely high overhead
   compared to unformatted writes.
*/
size_t whio_dev_writefv( whio_dev * dev, const char *fmt, va_list ap );

/**
   Equivalent to whio_dev_writefv() except that it takes an elipsis list
   instead of a va_list.
*/
size_t whio_dev_writef( whio_dev * dev, const char *fmt, ... );

/**
  This is the collection of "known" ioctl values for use as the second
  argument to whio_dev::ioctl(). The documentation for each entry
  explains what the third and subsuquent arguments to ioctl() must be.
  Type mismatches will lead to undefined results, very possibly
  crashes or memory corruption.

  This enum is updated as new whio_dev implementations are created or
  new ioctl commands are added.

  Here's an example which works with whio_dev objects created
  via whio_dev_for_memmap_XXX() and whio_dev_membuf(), to reveal
  the size of their associated memory buffer:

  @code
  whio_size_t sz = 0;
  int rc = whio_dev_ioctl(dev, whio_dev_ioctl_BUFFER_size, &sz );
  if( whio_rc.OK == rc ) {
    printf("Buffer size = %u\n", sz );
  }
  @endcode

   Conventions:

   The xxx_mask_yyy entries, which represent categories of ioctls,
   should all have bits set only in the top 16 bits. The lower 16 bits
   are for definining specific ioctls within a givin category.  Note
   that ISO C limits enumerators to the same range as (int), so the
   top (sign) bit cannot be used.

   The library reserves values where the top bits are 0 for client
   use. Thus the client may define his own 16-bit integral values for
   use as ioctls without concern about conflicting with this library.

   Concrete ioctl values should not use the top byte and should
   instead mask their value against one of the masking entries. This
   assists in documentation, by making it clear which category an
   ioctl command belongs to.
*/
enum whio_dev_ioctls {

whio_dev_ioctl_mask_GENERAL = 0x010000,

/** @var whio_dev_ioctl_GENERAL_size
   whio_dev_file() finds a device's size by calling seek()
   to get to the EOF. While this is generic, it potentially
   requires i/o. Some devices must record their length and
   therefor have constant-time access to it. Such devices should
   support this ioctl.

   The third argument to whio_dev::ioctl() MUST be a pointer
   to a whio_size_t, to which the size is written.

   Implementations which support this ioctl but enounter an error
   should return a non-0 return code OTHER than
   whio_rc.UnsupportedError.
*/
whio_dev_ioctl_GENERAL_size = whio_dev_ioctl_mask_GENERAL | 0x01,

/** @var whio_dev_ioctl_GENERAL_name
   Some devices may be able to report a name associated with the
   device. The second parameter must be a (char const **). The pointer
   will be assigned to the name of the device. The string's ownership
   is not generically defined, but will typically be owned by the
   one who opened the device or by the device itself (if it copies the
   name it was opened with). In any case, if the caller wants to keep
   the name, he should copy it immediately after fetching it.
*/
whio_dev_ioctl_GENERAL_name = whio_dev_ioctl_mask_GENERAL | 0x02,

/**
   ioctl's for FILE devices should have this mask.
*/
whio_dev_ioctl_mask_FILE =   0x020000,

/** @var whio_dev_ioctl_FILE_fd

   A FILE-based whio_dev can use this ioctl to return the underlying
   file descriptor number. The third argument to ioctl() MUST be a
   pointer to a signed integer, in which the file descriptor is
   written.
*/
whio_dev_ioctl_FILE_fd = whio_dev_ioctl_mask_FILE | 0x01,

/**
   Devices which support this ioctl should call ignore all arguments
   and call remove(3) (or equivalent) to remove the device's
   underlying handle. They should only return 0 if the remove actually
   works. Note that platforms which support hard linking of files are
   only required to unlink(2) one time, not to actually force the
   deletion of the multi-linked object (if that's even generically
   possible).

   If removal fails, implementations are requested to find a whio_rc
   error code which closely (or, worst case, remotely) matches the
   OS' reported error. If using remove(3) then erro can be used.
*/
whio_dev_ioctl_FILE_REMOVE = whio_dev_ioctl_mask_FILE | 0x2,

/**
   ioctl's for in-memory device buffers should have this mask.
*/
whio_dev_ioctl_mask_BUFFER = 0x040000,


/** @var whio_dev_ioctl_BUFFER_size

   Some whio_dev implementations use a buffer. Some of those can also
   report the buffer size using this ioctl.

   The 3rd parameter to the ioctl call MUST be a pointer to a whio_size_t
   object, in which the size of the buffer is stored.

   The exact meaning of the buffer is implementation dependent. e.g
   the FILE wrapper uses no buffer (though the underlying
   implementation probably does), but the membuf and memmap
   implementations do (but use them in slightly different ways).

   A growable membuf implementation returns the current allocated size
   of the buffer (which may be larger than its reported device size
   and may be changed by write or truncate operations). A non-growable
   membuf will return the fixed allocated size, which does not change
   during the life of the device.

   The memmap device wrapper will return the size of the memory range
   pointed to by the device. This number does not change during the
   life of the device.
*/
whio_dev_ioctl_BUFFER_size = whio_dev_ioctl_mask_BUFFER | 0x01,

/**
   Devices which store an internal memory buffer *might* want to expose it,
   for performance/access reasons, to the client. The argument to this ioctl
   must be a (unsigned char const **), which will be set to the start of the
   buffer's address. However, a memory buffer might be reallocated and the
   address invalidated, so it should not be stored.

   Example:

   @code
   unsigned char const * buf = 0;
   int rc = whio_dev_ioctl( dev, whio_dev_ioctl_BUFFER_uchar_ptr, &buf );
   if( whio_rc.OK == rc )
   {
       ... Use buf. It is valid until the next write() or truncate() on dev...
       ... It MIGHT be valid longer but it might be moved through reallocation...
   }
   @endcode
*/
whio_dev_ioctl_BUFFER_uchar_ptr = whio_dev_ioctl_mask_BUFFER | 0x02,



/**
   ioctl's for sub-device operations should have this mask.
*/
whio_dev_ioctl_mask_SUBDEV = 0x80000,

/** @var whio_dev_ioctl_SUBDEV_parent_dev

   Sub-device whio_dev devices interpret this as "return the parent device
   pointer through the third argument", where the third argument must
   be a (whio_dev**).
*/
whio_dev_ioctl_SUBDEV_parent_dev = whio_dev_ioctl_mask_SUBDEV | 0x01,

/** @var whio_dev_ioctl_SUBDEV_bounds_get

   Sub-device whio_dev devices interpret this as "return the
   lower/upper bounds range, relative to the parent device, through
   the third and fourth arguments, respectively", where the third and
   fourth arguments must be a (whio_size_t*). Either may be NULL, in which
   case that argument is ignored.
*/
whio_dev_ioctl_SUBDEV_bounds_get = whio_dev_ioctl_mask_SUBDEV | 0x02,

/**
   ioctl's for locking-related operations should have this mask.
*/
whio_dev_ioctl_mask_LOCKING = 0x100000,

/**
   ioctl's compatile with fcntl() should have this mask.

   Implementations which support this family of ioctls should return
   accept this mask as a separate ioctl. If they do, they should
   return 0 from the ioctl call and ignore all arguments if this value
   is passed as the command.  This provides a way of determining of
   locking is enabled without actually attempting a lock.

   If an implementation determines that existing locks prevent
   locking, it should return whio_rc.LockingError. For other error
   conditions, it may return an implementation-specified error code
   other than whio_rc.LockingError.

   @see whio_dev_ioctl_FCNTL_lock_nowait
   @see whio_dev_ioctl_FCNTL_lock_wait
   @see whio_dev_ioctl_FCNTL_lock_get

*/
whio_dev_ioctl_mask_FCNTL_LOCKING = whio_dev_ioctl_mask_LOCKING | 0x200000,


/** @var whio_dev_ioctl_FCNTL_lock_nowait

   Devices which support locking via fcntl() (or semantically
   compatible) may support this ioctl (and the related ones).
   
   The third argument to the ioctl() call MUST be a non-const (struct
   flock *) which describes the lock/unlock operation.

   whio_dev_ioctl_FCNTL_lock requests a fcntl() non-blocking lock
   (F_SETLK).

   On success the ioctl() will return 0. On error, it may return one
   of the whio_rc errors or a value specified by the fcntl()
   interface. Since fcntl() uses the global errno to report the actual
   error, it is possible to distinguish between the two. fcntl()
   supposedly only returns -1 for errors, and if that's true then
   there can be no error code collision because whio_rc has no integer
   values which have a value of -1 (which is reserved for
   whio_rc.SizeTError, which is of type whio_size_t).

   @see whio_dev_ioctl_mask_FCNTL_LOCKING
   @see whio_dev_ioctl_FCNTL_lock_wait
   @see whio_dev_ioctl_FCNTL_lock_get
*/
whio_dev_ioctl_FCNTL_lock_nowait = whio_dev_ioctl_mask_FCNTL_LOCKING | 0x01,

/** @var whio_dev_ioctl_FCNTL_lock_wait

   whio_dev_ioctl_FCNTL_lock_wait requests a fcntl() blocking lock
   (F_SETLKW).

   @see whio_dev_ioctl_mask_FCNTL_LOCKING
   @see whio_dev_ioctl_FCNTL_lock_nowait
   @see whio_dev_ioctl_FCNTL_lock_get
*/
whio_dev_ioctl_FCNTL_lock_wait = whio_dev_ioctl_mask_FCNTL_LOCKING | 0x02,

/** @var whio_dev_ioctl_FCNTL_lock_get

   whio_dev_ioctl_FCNTL_lock_get requests an fcntl() F_GETLK
   operation.

   @see whio_dev_ioctl_mask_FCNTL_LOCKING
   @see whio_dev_ioctl_FCNTL_lock_nowait
   @see whio_dev_ioctl_FCNTL_lock_wait

*/
whio_dev_ioctl_FCNTL_lock_get = whio_dev_ioctl_mask_FCNTL_LOCKING | 0x04,

/**
   ioctl's compatible with whio_lock_request-style locking should have
   this mask.

   Implementations which support this family of ioctls should return
   accept this mask as a separate ioctl. If they do, they should
   return 0 from the ioctl call and ignore all arguments if this value
   is passed as the command.  This provides a way of determining of
   locking is enabled without actually attempting a lock.

   If an implementation determines that existing locks prevent
   locking, it should return whio_rc.LockingError. For other error
   conditions, it may return an implementation-specified error code
   other than whio_rc.LockingError.

   @see whio_dev_ioctl_WHIO_LOCK
*/
whio_dev_ioctl_mask_WHIO_LOCKING = whio_dev_ioctl_mask_LOCKING | 0x400000,


/** @var whio_dev_ioctl_WHIO_LOCK

   For devices which support whio_lock_request-style locking. The
   third argument to whio_dev_ioctl() MUST be a non-const
   (whio_lock_request *), and the ioctl call may change the passed-in
   object to reflect the "real" request (if the device modifies it for
   some reason).


   Subdevices, and other device implementations which proxy parts of
   a parent device, are encouraged to trim lock requests to fit only
   within the managed bounds.

   @see whio_dev_ioctl_mask_WHIO_LOCKING
*/
whio_dev_ioctl_WHIO_LOCK = whio_dev_ioctl_mask_WHIO_LOCKING | 0x01,

/**
   Reserved for use by the libwhio whio_epfs extension.
*/
whio_dev_ioctl_mask_WHIO_EPFS = 0x1000000,

/** Reserved for future use. */
whio_dev_ioctl_mask_RESERVED_1 = 0x2000000,
/** Reserved for future use. */
whio_dev_ioctl_mask_RESERVED_2 = 0x4000000,
/** Reserved for future use. */
whio_dev_ioctl_mask_RESERVED_3 = 0x8000000,

/**
   Reserved for client use are any ioctl values where all but the
   bottom-most 16 bits are 0.
*/
whio_dev_ioctl_mask_CLIENT = 0x00000000

};


/**
   Equivalent to dev->api->read(...). If !dev, 0 is returned.
 */
whio_size_t whio_dev_read( whio_dev * dev, void * dest, whio_size_t n );

/**
   Equivalent to dev->api->write(...). If !dev, 0 is returned.
 */
whio_size_t whio_dev_write( whio_dev * dev, void const * src, whio_size_t n );

/**
   Equivalent to dev->api->eof(...). If !dev, whio_rc.ArgError  is returned.
 */
int whio_dev_eof( whio_dev * dev );

/**
   Equivalent to dev->api->tell(...). If !dev, whio_rc.SizeTError is returned.
 */
whio_size_t whio_dev_tell( whio_dev * dev );

/**
   Equivalent to dev->api->seek(...). If !dev, whio_rc.SizeTError is returned.
 */
whio_size_t whio_dev_seek( whio_dev * dev, whio_off_t pos, int whence );

/**
   Equivalent to dev->api->flush(...). If !dev, whio_rc.ArgError  is returned.
 */
int whio_dev_flush( whio_dev * dev );

/**
   Equivalent to dev->api->truncate(...). If !dev, whio_rc.ArgError is returned.
 */
int whio_dev_truncate( whio_dev * dev, whio_off_t size );

/**
   Equivalent to dev->api->finalize(...). If !dev, this function does nothing.
 */
void whio_dev_finalize( whio_dev * dev );

/**
   Equivalent to dev->api->close(...). If !dev, this function returns false.
 */
bool whio_dev_close( whio_dev * dev );


/**
   Result type for whio_dev_fetch(). It is a workaround to enable some
   auto-generated script bindings to use the read() API.  See
   whio_dev_fetch() for details.
*/
typedef struct whio_fetch_result
{
    /**
       malloc()'d memory will be placed here by whio_dev_fetch() and
       whio_dev_fetch_r().  It must be freed by calling
       whio_dev_fetch_free() (if this object is heap-allocated), or by
       passing the data member to free() (if this object is
       stack-allocated).

       It is (char *), as opposed to (void*) or (unsigned char *)
       because SWIG likes it that way.
    */
    char * data;
    /**
       Number of bytes requested in the corresponding
       whio_dev_fetch().
    */
    whio_size_t requested;
    /**
       Number of bytes actually read in the corresponding
       whio_dev_fetch().
    */
    whio_size_t read;
    /**
       Number of bytes allocated to the data member.
     */
    whio_size_t alloced;
} whio_fetch_result;

/**
   This function is a workaround to allow us to use SWIG to
   generate scriptable functions for the whio_dev::read()
   interface. It works like so:

   - it allocates a new whio_fetch_result object.
   - it allocates n bytes of memory.
   - it calls dev->api->read() to fill the memory.

   The returned object contains referneces to the allocated memory,
   the size of the request (the n parameter), the number of bytes
   actually read, and the amount of memory allocated in the obj->data
   member.

   The returned object must be passed to whio_dev_fetch_free(), or
   free(obj->data) and free(obj) must be called (in that order!).

   @see whio_dev_fetch_r()
   @see whio_dev_fetch_free()
   @see whio_dev_fetch_free_data()
*/
whio_fetch_result * whio_dev_fetch( whio_dev * dev, whio_size_t n );

/**
   Similar to whio_dev_fetch(), but the results are written to the tgt
   object (which may not be 0) and the memory buffer of that object is
   re-used if possible (or reallocated, if n is bigger than
   tgt->alloced). On success, whio_rc.OK is returned and tgt is updated.
   On error, tgt may still be updated, and still needs to be freed
   as explained in whio_dev_fetch(), and non-whio_rc.OK is returned:

   - whio_rc.ArgError = !dev or !tgt

   - whio_rc.AllocError = (re)allocation of the memory() buffer
   failed.  tgt->data might still be valid (and need to be freed), but
   could not be expanded to n bytes.

   If tgt comes from C code (as opposed to SWIG-generated script
   bindings) and is a stack-allocated object (not via malloc()), then
   the caller MUST NOT call whio_dev_fetch_free() and must instead
   call free(tgt->data) to free any allocated memory.

   PS: the '_r' suffix on this function name is for "re-use".

   @see whio_dev_fetch()
   @see whio_dev_fetch_free()
   @see whio_dev_fetch_free_data()
*/
int whio_dev_fetch_r( whio_dev * dev, whio_size_t n, whio_fetch_result * tgt );

/**
   Calls free(r->data) then free(r). DO NOT pass this a stack-allocated
   object. To clean up such an object, simply call free(obj->data)
   or call whio_dev_fetch_free_data().

   @see whio_dev_fetch()
   @see whio_dev_fetch_r()
   @see whio_dev_fetch_free_data()
*/
int whio_dev_fetch_free( whio_fetch_result * r );

/**
   Similar to whio_dev_fetch_free(), except that r->data i freed and
   r->alloced set to 0, but r is not deleted. Thus this is legal
   for stack-allocated objects, whereas whio_dev_fetch_free() is not.

   When using the fetch API from scripted code, one needs to be
   careful how the whio_fetch_results are cleaned up. Here's an
   example (in Python) which demonstrates the two ways to handle it:

   @code
import whio
fname = 'bogo.out';
f = whio.whio_dev_for_filename( fname, "w" )
sz = whio.whio_dev_write( f, "Hi, world!", 10 )
whio.whio_dev_finalize(f)
f = whio.whio_dev_for_filename( fname, "r" )
if f is None:
    raise Exception("Could not open "+fname+" for reading!")
# Approach #1: use whio_dev_fetch() to allocate an object:
frc = whio.whio_dev_fetch(f, 5);
if frc is None:
    raise Exception("Fetch failed!")
print('sizes:', frc.requested, frc.read, frc.alloced);
print('data:',frc.data);
# Now clean up the object:
whio.whio_dev_fetch_free(frc);
# Or there's a second approach:
frc = whio.whio_fetch_result(); # allocated new object
rc = whio.whio_dev_fetch_r( f, 30, frc );
rc = whio.whio_dev_fetch_free_data(frc); # note the different cleanup function!
print('fetch_free rc=',rc);
whio.whio_dev_finalize(f)
   @endcode

*/
int whio_dev_fetch_free_data( whio_fetch_result * r );

/**
   The whio_lock_types enum describes lock types
   used with the whio_lock_request class.
*/
enum whio_lock_types
{
    /**
       A sentry/placeholder value.
    */
    whio_lock_TYPE_INVALID = 0,
    /**
       This represents a read lock (non-exclusive) request.

       Analog to F_RDLCK.
    */
    whio_lock_TYPE_READ,
    /**
       This represents an unlock request.

       Analog to F_UNLCK.
    */
    whio_lock_TYPE_UNLOCK,
    /**
       This represents a write lock (exclusive) request.

       Analog to F_WRLCK.
    */
    whio_lock_TYPE_WRITE
};
typedef enum whio_lock_types whio_lock_types;
/**
   The whio_lock_types enum describes lock commands
   used with the whio_lock_request class.
*/
enum whio_lock_commands
{
    /**
       A sentry/placeholder value.
    */
    whio_lock_CMD_INVALID = 0,
/**
   Specifies that the attempt to get a lock should not block, but
   should return if conflicting lock prohibits us from immediately
   obtaining a lock.

   Analog to F_SETLK.
*/
    whio_lock_CMD_SET_NOWAIT,
/**
   Specifies that the attempt to get a lock should block until the
   lock can be obtained or it is interrupted by a signal or some such.
   Whether or not an implementation re-tries the lock after being
   interrupted by a signal is implementation-defined.
   
   Analog to F_SETLKW.
*/
    whio_lock_CMD_SET_WAIT,
/**
   Specifies that the lock request is just a test. It describes a lock
   we would _like_ to place, but it is not actually set. If a conflicting
   lock prohibits access, the locking request will fail.

   This is analog to F_GETLK except that the success of the test is
   checked differently: see whio_lock_CMD_TEST_PASSED.
*/
whio_lock_CMD_TEST,
/**
   ioctl implementations which honor whio_lock_CMD_TEST should, on
   success, re-assign the whio_lock_request::command field of the lock
   request object to whio_lock_CMD_TEST_PASSED. This is analog to how
   fcntl()'s F_GETLK notifies the caller by re-assigning the
   flock::l_type value to F_UNLCK.  The fcntl() docs are unclear as to
   whether fcntl() _returns_ success or error if such a lock test
   fails, but seem to imply that it returns success but modifies the
   lock request to report info about the conflicting lock.
*/
whio_lock_CMD_TEST_PASSED
};
typedef enum whio_lock_commands whio_lock_commands;

/**
   The whio_lock_request class is part of an ioctl-accessible
   interface for implementing device-specific locking features.

   It is modelled closely after fcntl()-style locking:

   - It uses slightly different approaches for specifying an unlock
   and for testing whether a lock is possible. (i personally find
   the fcntl() approaches unintuitive and difficult to remember.)

   - This API has no way to report certain lock info back to the
   caller (e.g.  the PID of another process holding a conflicting
   lock). This is not likely to be added to the interface because such
   information is too device-specific.  e.g., we might at some point
   wish to add locking to memory-based devices, and they would have
   difference concerns (they'd want to know what C-side object/mutex
   owns the lock, not which process).

   This class is an abstraction around the concept of byte-range
   locking, and does not specifically imply that the back-end is a
   file. In practice, locking is only implemented for file-backed
   devices, but in theory non-file devices may be implemented to
   support some form of locking.

   Layered device implementations, like subdevices, probably want to
   pass locking requests to their lower-level device.
*/
struct whio_lock_request
{
    /**
       Type of locking request: read, write, or unlock.
    */
    whio_lock_types type;

    /**
       The locking command: set-immediately-or-fail, set-and-wait,
       or test.

       ioctl implementations which respect whio_lock_CMD_TEST are supposed,
       on a successful lock test, to re-assign this member to the value
       whio_lock_CMD_TEST_PASSED, as a way of notifying the caller that
       the test succeeded.

       ioctl implementations are requested (very humbly) to check if
       the device is read-write before attempting to set (or even test
       for) a write lock. They should return whio_rc.AccessError if a
       write lock is requested on a non-writable device.
    */
    whio_lock_commands command;

    /**
       Semantically identical to the whence argument used by
       fseek() and fcntl() locking. It must be one of SEEK_SET,
       SEEK_CUR, SEEK_END.

    */
    int8_t whence;
    
    /**
       The start position of the lock, relative to the location
       specified by the whence parameter.

       Implementations are not required to support a negative start
       position in combination with SEEK_SET.

    */
    whio_off_t start;

    /**
       The length of the lock, in bytes.

       Devices should (if possible) interpret 0 as "until the
       end of the device, regardless of whether its size changes
       later" (for compatibility with fcntl() locking).

       Devices may, but are not required to, support a negative
       length.
       
       Implementations may, but need not, shorten the length to stay
       in bounds if they are acting as a fence for a parent
       device. This allowance is primarily for whio_dev subdevices,
       which philosophically should not allow locking past their upper
       bound (this could cause buggy locking in some use cases, namely
       in whio_epfs).
    */
    whio_off_t length;
};
/**
   An empty-initialized whio_lock_request object.
*/
#define whio_lock_request_empty_m { \
        whio_lock_TYPE_INVALID/* type */,            \
        whio_lock_CMD_INVALID/* command */,        \
        SEEK_SET/*whence*/,\
        0 /* start */,\
        0 /* length */ \
}
/**
   Convenience typedef.
*/
typedef struct whio_lock_request whio_lock_request;

/**
   An empty-initialized whio_lock_request object.
*/
extern const whio_lock_request whio_lock_request_empty;
/**
   A whio_lock_request initialization object with command=TEST, type=TEST,
   start=0, length=1.
*/
extern const whio_lock_request whio_lock_request_test_r;

/**
   A whio_lock_request initialization object with command=TEST,
   type=WRITE, start=0, length=1.
*/
extern const whio_lock_request whio_lock_request_test_w;

/**
   A whio_lock_request initialization object with command=SET_NOWAIT,
   type=READ.
*/
extern const whio_lock_request whio_lock_request_set_r;

/**
   A whio_lock_request initialization object with command=SET_NOWAIT,
   type=WRITE.
*/
extern const whio_lock_request whio_lock_request_set_w;

/**
   A whio_lock_request initialization object with command=SET_WAIT,
   type=READ.
*/
extern const whio_lock_request whio_lock_request_setw_r;

/**
   A whio_lock_request initialization object with command=SET_WAIT,
   type=WRITE.
*/
extern const whio_lock_request whio_lock_request_setw_w;

/**
   A whio_lock_request initialization object with command=SET_NOWAIT,
   type=UNLOCK.
*/
extern const whio_lock_request whio_lock_request_set_u;
/**
   A whio_lock_request initialization object with command=SET_WAIT,
   type=UNLOCK.
*/
extern const whio_lock_request whio_lock_request_setw_u;

/**
   Almost equivalent to:

   @code
   whio_dev_ioctl( dev, whio_dev_ioctl_WHIO_LOCK, lock )
   @endcode

   Except that:

   a) It's  a bit easier on the eyes.

   b) This routine ensures that if (lock->type==whio_lock_TYPE_WRITE)
   then dev must not be read-only. If the i/o mode is not writable and
   a write lock is requested, whio_rc.AccessError is returned.

   Returns whio_rc.ArgError if either dev or lock are NULL.
   lock may be modified by this call, but ownership does not
   change.
*/
int whio_dev_lock( whio_dev * dev, whio_lock_request * lock );

/**
   Writes the given character n times to the given device, starting at
   its current cursor position. The writes are not done per-character,
   but using an internal buffer of an unspecified size.

   Returns 0 on success, non-0 on error. Errors include:

   !dev = whio_rc.ArgError

   !n = whio_rc.RangeError

   dev does not report itself as writable: whio_rc.AccessError

   
   If writing fails, whio_rc.IOError is returned and the device may
   have been partially written to.
*/
int whio_dev_fill( whio_dev * dev, unsigned char ch, whio_size_t n );

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* WANDERINGHORSE_NET_WHIO_DEV_H_INCLUDED */
/* end file include/wh/whio/whio_dev.h */
/* begin file include/wh/whio/whio_devs.h */
#ifndef WANDERINGHORSE_NET_WHIO_DEVS_H_INCLUDED
#define WANDERINGHORSE_NET_WHIO_DEVS_H_INCLUDED

/*
   This file contains declarations and documentation for the concrete
   whio_dev implementations. The generic iodevice API is declared in
   whio_dev.h.
*/
#include <stdio.h> /* FILE */
#include <stdint.h> /* uint32_t */
#include <stdarg.h> /* va_list */

#ifdef __cplusplus
extern "C" {
#endif


/**
   Creates a whio_dev object which will use the underlying FILE
   handle. On success, ownership of f is defined by the takeOwnership
   argument (see below) and the returned object must eventually be finalized with
   dev->api->finalize(dev).

   For purposes of the whio_dev interface, any parts which have
   implementation-specified behaviour will behave as they do
   for the local FILE-related API. e.g. ftruncate() may or may
   not be able to extend a file, depending on the platform
   and even the underlying filesystem type.

   The takeOwnership argument determines the ownerhsip of f: if the
   function succeeds and takeOwnership is true then f's ownership is
   transfered to the returned object. In all other cases ownership is
   not changed. If the device owns f then closing the device
   will also close f. If the device does not own f then f must
   outlive the returned device.

   Peculiarities of this whio_dev implementation:

   - See the docs for whio_dev_ioctl_FILE_fd for how to fetch the
   underlying file descriptor.

   - IFF takeOwnership is false then it is legal for the whio_dev::client.data
   member to point to the passed-in file and for whio_dev::client.dtor to
   close/free that file. If takeOwnership is true then behaviour is undefined
   if the client data field is set up to destroy the file handle.
   
   - The iomode() member will initially return WHIO_MODE_UNKNOWN
   (indicating an unknown r/w state) because it cannot know (without
   trying to write) if f is writeable. If the device ever successfully
   reads or writes then the i/o mode will be adjusted to reflect that
   it is readable and/or writable.
   
   - It supports the whio_dev_ioctl_FCNTL_lock_wait,
   whio_dev_ioctl_FCNTL_lock_nowait, and whio_dev_ioctl_FCNTL_lock_get
   ioctls (from the whio_dev_ioctls enum). This is only enabled
   if the library is compiled with WHIO_CONFIG_USE_FCNTL set to a true
   value.

   - It supports the whio_dev_ioctl_WHIO_LOCK ioctl, simply
   translating it into a corresponding whio_dev_ioctl_FCNTL request.
   When a request of type whio_lock_CMD_TEST passes, the
   whio_lock_request::command field will be set to
   whio_lock_CMD_TEST_PASSED to signify that the test lock _could_
   have been placed but wasn't.

   - If the ioctl command is whio_dev_ioctl_mask_WHIO_LOCKING or
   whio_dev_ioctl_mask_FCNTL_LOCKING (note the "mask" parts), it is
   treated as the question "is locking support fundamentally enabled?" 
   but does not actually attempt to lock anything and all arguments
   are ignored. If locking is enabled, zero is returned. Clients can
   use this to query whether locking can or cannot be used at all
   before trying to use locking.

   - If a lock request is interrupted by a signal, the implementation
   will attempt the lock again. This behaviour is however arguable
   and needs to be made configurable (yet another ioctl).
   
   @see whio_dev_for_filename()
*/
whio_dev * whio_dev_for_FILE( FILE * f, bool takeOwnership );

/**
   Similar to whio_dev_for_FILE(), but takes a filename and an
   access mode specifier in the same format expected by fopen().
   In addition, the returned object internally uses the lower-level
   read(), write(), lseek(), etc. API instead of fread(), fwrite(),
   fseek(), etc. This is, for some use cases, more performant, and is
   compatible with fcntl()-style locking.

   It is ill advised to mix use of the POSIX file API and the
   lower-level APIs. The returned object uses the lower-level APIs for
   all i/o operations, using the fopen() and fclose() API only for
   opening and closing the file (because fopen()'s mode arguments are
   easier to manage).


   Peculiarities of this whio_dev implementation:
   
   - Because the lower-level I/O API doesn't have direct equivalents
   of feof(), ferror(), and clearerr(), devices created this way may
   behave slightly differently in some cases (involving error
   reporting) than devices created using whio_dev_for_FILE() (but
   should nonetheless behave as expected).

   - The whio_dev_ioctl_FILE_fd ioctl is supported to fetch the
   underlying file descriptor.

   - It also supports the whio_dev_ioctl_GENERAL_name ioctl() to
   report the name passed to this function. As of version 20100309,
   the name is copied when the object is opened, and need not be
   static. (In previous versions, this ioctl was only safe if the
   filename pointer was still in scope when this ioctl was used.)

   - It supports the whio_dev_ioctl_FCNTL_xxx and
   whio_dev_ioctl_WHIO_LOCK family of ioctls in the exact same manner
   as described for whio_dev_for_FILE().
   
   - The iomode() member will return a value appropriate for the given
   mode string, as determined by whio_mode_to_iomode().

   - It is illegal for the whio_dev::client.data member of the
   returned object to refer to the given file descriptor (whether
   indirectly or not) if whio_dev::client.dtor is set up to close/free
   the client data. If the dtor does not close/free the resource then
   the client.data member may refer to the file.

   - The whio_dev_ioctl_FILE_REMOVE ioctl is supported, and it tries
   to report the error code as accurately as the remove(3)
   documentation allows for.

   Maintenance reminder: we have two impls of this function, one using
   the file descriptor proxy and one using the FILE proxy. These docs
   describe the file descriptor variant. If we ever switch the impl to
   the other one then the above description of the returned object
   will change (mildly incompatibly). In particular regarding the
   legality of the client.data member referring to the underlying
   device.

   @see whio_dev_for_FILE()
   @see whio_dev_for_fileno()
   @see whio_dev_posix_open2()

*/
whio_dev * whio_dev_for_filename( char const * fname, char const * mode );

/**
   This function creates a whio_dev instance which is a proxy for a
   file descriptor opened using open(2). Arguments 2-4 similar to
   those accepted by open(2):

   - fname is the name of the file to open.

   - flags is a bitmask of whio_iomodes flags specifying how to open
   the file (read/write, etc.). It must be a mask of values from the
   whio_iomodes enum, and NOT the O_xxx values used by open(2). (The
   reason for this is to avoid forcing the client to include fcntl.h
   to get the O_xxx values!)

   - filePerms is the permissions flags with which a file should be
   created.  This is only used if WHIO_MODE_FLAG_CREATE is in the
   flags and only if this function actually creates the file. In all
   other cases this flag is ignored. If (0==mode) then a default of
   0644 (rw-r--r--) is used.

   The first argument:

   - May be a pointer to NULL (i.e. *tgt == NULL), in which case this
   routine allocates the device for the user.

   - May point to a user-allocated object, in which case this routine
   assumes it is empty-initialized and uses it. It must still allocate
   its internal data but then replaces *tgt's contents with its
   own. Make SURE that *tgt is not an opened device, or this WILL
   lose its state and cause a leak!

   On success:

   - 0 is returned.

   - *tgt contains the new device. If this function alloced it, the
   caller must free it using (*tgt)->api->finalize(*tgt) . If the
   client allocated it himself he must clean it using
   (*tgt)->api->close(*tgt) and then free the tgt memory using the
   method complementary to its allocation.

   On error, non-zero is returned and *tgt (if not NULL) will be
   cleaned up. The caller must still free its memory if he allocated
   *tgt. This function tries to map the errno values reported by
   open(2) to the semantically closest error code from whio_rc.

   ACHTUNG: because the O_xxx values need by open(2) require that the
   client include fcntl.h (or other system-specific headers), the
   flags field does NOT accept the O_xxx values. Instead use the
   values from the whio_imodes enum!!!!
   
   The primary advantage of this function over whio_dev_for_filename()
   is that this one allows a richer set of flags for specifying how a
   file should (or should not) be opened. The down-side is the
   added complexity of those flags.
   
   Example:

   @code
   whio_dev * dev = NULL;
   int rc = whio_dev_posix_open2( &dev, "myfile.txt", WHIO_MODE_RWC, 0 );
   if( rc ) { ... error ... }
   else {
       ... use dev, then clean it up...

       // IFF we passed a pointer to NULL to whio_dev_posix_open2()
       // then do:
       dev->api->finalize(dev);

       // ELSE do:
       dev->api->close(dev); // cleans up internal state but does not dealloc dev
       ... then free dev if needed (if it is not stack-allocated) ...
   }
   @endcode
   
   @see whio_dev_for_FILE()
   @see whio_dev_for_fileno()
*/
int whio_dev_posix_open2( whio_dev ** tgt, char const * fname, whio_iomode_mask flags, short filePerms );
    
/**
   Equivalent to whio_dev_for_filename(), but takes an opened file
   descriptor and calls fdopen() on it.

   PLEASE read your local man pages for fdopen() regarding caveats in
   the setting of the mode parameter and the close()
   handling. e.g. destroying the returned device will close it, so the
   descriptor should not be used by client code after that. Likewise,
   client code should not close the descriptor as long as the returned
   device is alive. Thus ownership of the handle is effectively passed
   to the returned object, and there is no way to relinquish it.

   My local man pages say:

   @code
   The fdopen() function associates a stream with the existing file
   descriptor, fd.  The mode of the stream (one of the values "r",
   "r+", "w", "w+", "a", "a+") must be compatible with the mode of the
   file descriptor.  The file position indicator of the new stream is
   set to that belonging to fd, and the error and end-of-file
   indicators are cleared.  Modes "w" or "w+" do not cause truncation
   of the file.  The file descriptor is not dup()'ed, and will be
   closed when the stream created by fdopen() is closed.  The result
   of applying fdopen() to a shared memory object is undefined.
   @endcode

   The returned device is identical to one returned by
   whio_dev_for_filename(), except that:

   - the ioctl() whio_dev_ioctl_GENERAL_name will return NULL but
   will succeed without an error.

   - The whio_dev_ioctl_FILE_REMOVE ioctl is not supported because
   removal requires a name.

   @see whio_dev_posix_open2()
   @see whio_dev_for_filename()
*/
whio_dev * whio_dev_for_fileno( int filedescriptor, char const * mode );


/**
   Creates a new whio_dev object which wraps an in-memory buffer. The
   initial memory allocated by the buffer is allocated by this call,
   and this size represents its initial buffer capacity (its virtual
   size starts at 0). Whether or not the buffer is allowed to be
   expanded by write() operations is defined by the remaining
   parameters.

   The expFactor specifies a growth expansion value, as follows. If
   expFactor is less than 1.0 then the buffer will never be allowed to
   expand more than the original size. If it is equal to or greater
   than 1.0, then it will be made expandable (that is, write() may
   cause it to grow). Every time its size grows, it will grow by a
   factor of expFactor (or to exactly the requested amount, for a
   factor of 1.0). e.g. 1.5 means grow by 1.5 times (a common growth
   factor for dynamic memory allocation). Likewise, when a buffer
   shrinks (via truncate()), it will be reallocated if
   (currentSize/expFactor) is greater than the number of bytes being
   used. For example, if a buffer of 1024 bytes with an expFactor of
   1.5 is being shrunk, it will not release the allocated memory
   unless doing so will drop it below ((1024/1.5)=682) bytes. A very
   large expFactor (more than 2.0) is not disallowed, but may not be
   good for your sanity.

   For purposes of the following text, a membuf device with an
   expFactor of equal to or greater than 1.0 is said to be "growable".

   If the buffer is growable then calling write() when we are at (or
   past) EOF will cause the buffer to try to expand to accommodate.
   If it cannot, or if the buffer is not growable, the write operation
   will write as much as it can fit in existing memory, then return a
   short write result.

   It not enough memory can be allocated for the intitial buffer then
   this function returns 0. On success, the caller owns the returned
   object and must eventually destroy it by calling
   dev->api->finalize(dev).

   The returned object supports all of the whio_dev interface, with
   the caveat that write() calls will not be allowed to expand out of
   bounds if the device is not growable.

   Regardless of the expansion policies, the truncate() member of the
   returned object can be used to expand the buffer. See below for
   more details.

   Note that the memory buffer explicitly uses malloc(), realloc(),
   and free() for the memory management of its internal buffer but
   uses whio_malloc() (and friends) to manage its own memory (which is
   very small). (TODO: add a whio_allocator to the interface to allow
   the client to specify the allocator.)
   
   Peculiarities of this whio_dev implementation:

   - Whether or not the device is growable (as explained above), seeks
   past EOF are always allowed as long as the range is
   positive. Non-growable buffers will not write there, but growable
   ones will try to expand at the next write. Non-growable buffers
   *can* be expanded by manually calling truncate() on them.

   - truncate() ignores the growth policy! That is by design, to allow
   us to (optionally) manually control the growth without allowing
   rogue seek/write combinations to take up all our memory.

   - When truncate() shrinks a growable buffer: memory may or may not
   be immediately released, depending on the magnitude of the
   change. A truncate() to a size of 0 will always release the memory
   immediately.

   - When truncate() shrinks a non-growable buffer: the memory is not
   released at all because the buffer could then not be expanded
   later. When truncating a non-expanding buffer to a smaller size,
   writes() made past new EOF will cause it to expand, but only up to
   the original size given to this function. e.g. if we have a non-growable
   buffer with 1024 bytes, we can truncate() it to 10 bytes, then write
   (expanding the size) up until we reach 1024 bytes, at which point
   we cannot write any more.

   - seek() will only fail if the offset would cause the position
   counter to overflow its numeric range or would set it before the
   start of the buffer. seek() does not change the object's size, and
   writing after an out of bounds seek will cause the object to grow
   starting at that new position (if it is growable) or it will fail
   (if the buffer is not growable or cannot grow).

   - flush() is a harmless no-op.

   - ioctl(): all of the ictl operations listed in the whio_dev_ioctls
   enum and marked with whio_dev_ioctl_mask_BUFFER are supported, as
   documented in that enum. The whio_dev_ioctl_GENERAL_size ioctl is
   also supported (from the whio_dev_ioctls enum), but it returns the
   size vis-a-vis the virtual EOF (highest position we have written
   to, perhaps modified by shrinking truncate()s), whereas
   whio_dev_ioctl_BUFFER_size returns the allocated size of the
   buffer. Unlike the cursor position, the "virtual EOF" can be
   changed by truncate() operations.

   - iomode() will always indicate that the device is writable.
*/
whio_dev * whio_dev_for_membuf( whio_size_t size, float expFactor );

/**
   Creates a new read/write whio_dev wrapper for an existing memory
   range. For read-only access, use whio_dev_for_memmap_ro() instead.

   The arguments:

   - mem = the read/write memory the device will wrap. Ownership is
   not changed.  May not be 0. If mem's address changes during the
   lifetime of the returned object (e.g. via a realloc), results are
   undefined and almost certainly ruinous. If you want this device to
   free the memory when it is destroyed, set dev->client.data to the
   mem parameter and set dev->client.dtor to an appropriate destructor
   function (free() would suffice for memory allocated via alloc()).
   Depending on the specific use case, it may or may not be legal to
   modify mem, except via the returned object, for the life of the
   returned object.

   - size = the size of the mem buffer. It may not be 0. It is the
   caller's responsibility to ensure that the buffer is at least that
   long. This object will not allow i/o operations outside of that
   bound. It is good practice to ensure that the memory is zeroed out
   before passing it here, to avoid unpredictable artifacts.

   On success a new whio_dev is returned. On error (invalid
   arguments or allocation error), 0 is returned.

   Peculiarities of the memmap whio_dev wrapper:

   - truncate() operations will work, but only up to the size passed
   to this function.  That is, one can "shrink" the device by
   truncating it, then grow it back, but never larger than the
   original size.  Shrinking does not actually free any memory but
   changes the virtual EOF.

   - seek() accepts past-EOF ranges, but will return
   whio_rc.SizeTError on a numeric over/underflow. Writing past EOF
   range will of course not be allowed. Seeking before the start
   is also not allowed.

   - write() on a read-only memory buffer returns 0.

   - Supports the ioctl()s whio_dev_ioctl_BUFFER_size, which returns
   the allocated size of the buffer (as passed to the factory
   function). The whio_dev_ioctl_GENERAL_size ioctl returns the
   position of the virtual EOF. The whio_dev_ioctl_BUFFER_uchar_ptr
   ioctl returns a const pointer to the memory.

   - iomode() always indicates that the device is writable.

   @see whio_dev_for_memmap_ro()
   @see whio_dev_for_membuf()
*/
whio_dev * whio_dev_for_memmap_rw( void * mem, whio_size_t size );

/**
   If dev was created via whio_dev_for_memmap_rw() or
   whio_dev_for_memmap_ro(), this function will "re-map" it to point
   to use the given memory range.  If dev is NULL, whio_rc.ArgError is
   returned. If dev was not created using whio_dev_for_memmap_rw() or
   whio_dev_for_memmap_ro(), then whio_rc.TypeError is returned.

   If the memory device should be read-only, set rw=NULL and
   ro=MEMORY_TO_USE. To make it read-write there are two equivalent
   options:

   - Pass (rw=MEMORY,ro=NULL)

   - Pass (rw=MEMORY,ro=MEMORY)

   If both ro AND rw are set then they must have the same value. If
   both are non-NULL and (rw!=ro) then whio_rc.RangeError is returned.

   It is legal for both rw and ro to be NULL, in which case the device
   cannot be used for i/o until it is re-mapped again (using this
   function). If both are NULL then the size argument is ignored.

   It is legal, using this function, to change a r/o memory device to
   a r/w memory device, or the other way around.

   rw and ro, if not NULL, must be at least @a size bytes long.
   
   Ownership of dev and rw are not modified. rw and ro (if not NULL)
   must outlive dev.

   Returns 0 on success, in which case dev is now a proxy for the
   given memory block.

   Uses for this function:

   - It was originally implemented so that i could use it in
   conjunction with the whio_udb API for writing out key/value
   information into a fixed buffer. i didn't want to re-allocate a new
   device for my various buffering needs, so this function was added
   to allow re-initialization of an allocated memory device.  The
   point of using the memory device class in such a way is that the
   class does all the range checking, leaving me only to check the
   return values for my read()/write() calls.

   - This might be useful as an eccentric substitute for sprintf(),
   when used on conjunction with whio_dev_writef().

   - Or as an even more eccentric substitute for memcpy().
*/
int whio_dev_memmap_remap( whio_dev * dev, void * rw, void const * ro, whio_size_t size );
    
/**
   This is nearly identical to whio_dev_for_memmap_rw() except that it
   creates a read-only device and ownership of mem is not changed by
   calling this function.

   In addition to the description for whio_dev objects returned from
   whio_dev_for_memmap_rw(), these notes apply:

   - iomode() always indicates that the device is read-only.

   @see whio_dev_for_memmap_rw()
   @see whio_dev_for_membuf()
*/
whio_dev * whio_dev_for_memmap_ro( const void * mem, whio_size_t size );

/**
   This object is the whio_dev::api member used by whio_dev instances
   returned by whio_dev_for_memmap_rw() and
   whio_dev_for_memmap_ro(). It is in the public interface because
   there are some interesting use-cases where we want to override
   parts of the API to do custom handling.

   The address of this object is also used as the
   whio_dev::impl::typeID value for memmap devices.
*/
extern const whio_dev_api whio_dev_api_memmap;

/**
   This object is the whio_dev::api member used by whio_dev instances
   returned by whio_dev_for_membuf(). It is in the public interface
   because there are some interesting use-cases where we want to
   override parts of the API to do custom handling.

   The address of this object is also used as the
   whio_dev::impl::typeID value for membuf devices.
*/
extern const whio_dev_api whio_dev_api_membuf;


/**
   Creates a new whio_dev object which acts as a proxy for a specified
   range of another device (that is, the object acts as a
   "subdevice"). All read/write/seek/tell operations on the returned
   object act on a range which is relative to the parent object. The
   object will not allow read/write operations outside of the given
   range.

   The arguments are:

   - parent = the parent i/o device. It must outlive the returned
   object, and ownership of parent is not changed by calling this
   function.

   - lowerBound is the logical begining-of-file for the returned
   device, relative to the coordinates of the parent.

   - upperBound is the logical "hard" EOF for the returned device -
   the one-past-the-end position. Writes will not be allowed at or
   past this point. If 0 is passed it is treated as
   "unlimited". upperBound must be 0 or it must be greater than
   lowerBound.

   The bounds are not checked when the subdevice is created, as most
   devices will allow one to write past EOF to extend them. If the
   bounds are not legal at read/write time then the error will be
   triggered there.  If parent is ever sized such that the given
   bounds are not longer legal, read/write errors may occur.

   Subdevices can be used to partition a larger underlying device into
   smaller pieces. By writing to/reading from the subdevices, one can
   be assured that each logical block remains separate and that any
   operation in one block will not affect any other subdevices which
   have their own blocks (barring any bugs in this code or overlapping
   byte ranges). Results are of course unpredictable if multiple
   devices map overlapping ranges in the parent device (then again,
   maybe that's what you want, e.g. as a communication channel).

   Most operations are proxied directly through the parent device,
   with some offsets added to accomodate for the bounds defined, so
   the returned object will inherit any peculiarities of the parent
   implementation (e.g. flush() requirements).

   On success a new whio_dev object is returned, which must eventually
   be destroyed by calling dev->api->finalize(dev).

   On error 0 is returned.

   Peculiarities of this whio_dev implementation:

   - read() and write() will reposition the parent cursor to the
   subdevice's position before reading/writing and re-set it when
   complete. Thus other code using the parent device need not worry
   about the subdevice hosing the cursor position. reads/writes do of
   course track the internal cursor used by the subdevice, so (for
   example) one need not manually reposition the cursor when doing
   sequential reads or writes. Likewise, seek() and tell() work independently
   of the parent device (with one exception, described below).

   - The behaviour of seek(dev,n,SEEK_END) depends partially on
   upperBound. If upperBound==0 (i.e. "no bounds") then SEEK_END will
   use the EOF of the parent device, not the subdevice. In any case,
   the value returned from tell() or seek() will be relative to the
   subdevice. FIXME: the SEEK_END behaviour is arguably broken in
   combination with unbounded subdevices (upperBound==0) which are
   themselves not at the end of a device chain.  i.e. an unbounded
   subdevice laying before another subdevice in the same parent will
   arguably have "wrong" results for SEEK_END. Then again, such a use
   case is fundamentally broken if the user is expanding the first
   subdevice in the chain, overflowing into another device. But we
   also potentially have a problem here if the parent device itself is
   an unbounded subdevice.  Hmmm.

   - truncate() is very limited. If the given size is less than its
   upper bounds, or if its upper bounds are unlimited, then it returns
   0 without actually truncating anything (because doing so would be
   disastrous when multiple levels of subdevices wrap a larger
   device). Any other value causes whio_rc.UnsupportedError to be
   returned.

   - Some calls (e.g. flush(), clear_error()) are simply passed on to
   the parent device. Though it is not philosophically/pedantically
   correct to do so in all cases.

   - close() does not, contrary to normal conventions, flush() the
   device because in practice this causes lifetime- and mutex-related
   issues. Because all writes are proxied to a parent, and the parent
   must outlive this device, it is assumed that flush()ing on the
   parent will happen properly through its normal lifetime.  (Before
   20110826 subdevices _did_ flush the parent but this was not
   explicitly documented.)

   - iomode() returns the same as the parent device does.

   - A subdevice can have another subdevice as its parent.

   - ioctl(): this type accepts ioctls described in the
   whio_dev_ioctls enum having the name prefix
   whio_dev_ioctl_SUBDEV_. See those docs for details.

   - If compiled with WHIO_CONFIG_USE_FCNTL then ioctls of types
   whio_dev_ioctl_FCNTL_lock_nowait, whio_dev_ioctl_FCNTL_lock_wait,
   and whio_dev_ioctl_FCNTL_lock_get will be adjusted for the
   subdevice's position and passed on to the parent device. Locking
   offsets "should" behave as expected, even when subdevices are
   embedded within one another, but one particularly fuzzy case is
   when SEEK_END is used as the locking position and the subdevice has
   been created with a length of 0. In that case, the virtual lock
   start position is NOT adjusted and SEEK_END is passed directly to
   the parent device. The third argument to whio_dev_ioctl() must be a
   non-const flock structure and it will be modified by this call to
   adjust for the embedded position of the subdevice. The flock
   object's value when this function returns will be changed to
   contain the "real" flock values, i.e. adjusted to contain a
   different start position and SEEK_CUR requests get translated to a
   SEEK_SET. In no case will locking be allowed before the start of
   the subdevice (returns whio_rc.RangeError), but locking past the
   end is legal - see the notes below for more details.

   - It supports the whio_dev_ictol_WHIO_LOCK ioctl, translating the
   coordinates before passing it on to the parent device. The
   whio_lock_request object passed to this ioctl is modified by the
   call to set the new position. Subdevives translate SEEK_CUR and
   SEEK_END positions to SEEK_SET (because the positioning is relative
   to the subdevice coordinates) before being passed on to the
   parent. SEEK_END is slightly special (unfortunately): a bounded
   subdevices will translate the request into SEEK_SET because it
   knows the position of EOF. Unbounded subdevices must pass the
   SEEK_END request directly to the parent, without any form of
   adjustment. It is unfortunately possible for the lock request to
   run outside of the subdevice's bound range, meaning it could lock
   bytes in a neighboring (sub)device. This class may be changed in
   the future to trim the requests to the bounded subrange.

   - All ioctls not described above are passed to the parent device
   (for better or for worse - not all ioctls make sense, or may cause
   some confusion, in a subdevice context).

   - It is not recommended that one use whio_dev_subdev_rebound() in
   conjunction with devices being locked via the locking ioctls, as it
   could easily lead to confusion about where locks have been placed.

   Example:


   @code
    char const * fname = "subdev.iodev";
    whio_dev * parent = whio_dev_for_filename( fname, "w+" );
    assert(parent);
    parent->api->write( parent, "!", 1 );
    parent->api->seek( parent, 99, SEEK_SET );
    parent->api->write( parent, "!", 1 );
    // parent is now 100 bytes long.
    whio_dev * sub = whio_dev_subdev_create( parent, 10, 43 );
    assert(sub);
    printf("Subdevice in place for file [%s]...\n", fname );

    size_t i = 0;
    whio_size_t szrc = 0;
    for( ; i < 5; ++i )
    {
        szrc = sub->api->write( sub, "0123456789", 10 );
        printf("Write length = %"WHIO_SIZE_T_PFMT"\n", szrc );
        if( szrc != 10 ) break;
    }
    sub->api->finalize(sub);
    parent->api->finalize(parent);
    // Now bytes in the inclusive range 10..42 (not 43 - that's sub's
    // one-past-the-end) will be filled with whatever was written to sub.
   @endcode

   
   Bugs/Questionable Features:

   - This function SHOULD take the numeric arguments as
   (offset,length) instead of (lowerOffset,upperOffset). Changing that
   would break a good deal of my client code, though, and would
   require a good amount of adjustment in this class' internals.
   
   - Regarding FCNTL ioctls (does not apply to WHIO_LOCK ioctls):

   Whether or not the l_len member of the passed-in flock structure
   may be negative is not specified by this interface. POSIX defines
   it as an allowed, but not required, feature. Thus it will depend on
   whether the underlying platform supports it.
   
   If the lock length runs past the subdevice EOF, that condition is
   allowed by this code, which means that the subdevice may lock bytes
   in in the parent device past the subdevice's managed range. This is
   primarily for compatibility with fcntl(), which allows bytes past
   EOF (but not before the first byte) to be locked. We could
   alternately adjust the length of the lock request if it would run
   out of bounds, but this code currently doesn't do that (the
   (flock::l_len==0) handling gets philosophically tricky for
   subdevices). i would like to change this behaviour to fence off
   l_len, but it adds more complexity to the implementation than i'm
   feeling up to at the moment. Thus: for the sake of sanity, it is probably
   best to avoid using (fcntl::whence==SEEK_EOF) in conjunction with
   locking of subdevices. Prefer SEEK_SET or SEEK_CUR options instead,
   and bound their lengths to ensure they don't escape the subdevice.
*/
whio_dev * whio_dev_subdev_create( whio_dev * parent, whio_size_t lowerBound, whio_size_t upperBound );


/**
   This routine only works on devices created with
   whio_dev_subdev_create() (or equivalent). It re-sets the lower and
   upper bounds of the subdevice (as described in
   whio_dev_subdev_create()) and re-sets the cursor to the new lower bound.

   This routine does no bounds checking on the parent device.

   On success, whio_rc.OK is returned, otherwise:

   - whio_rc.ArgError = !dev or upperBound is not 0 but is less than lowerBound.

   - whio_rc.TypeError = dev's type-id does not match (it is not a subdev device).

   - whio_rc.InternalError = dev is not mapped to a parent device (this theoretically
   cannot happen unless client code muddles with dev->impl.data).

   @see whio_dev_subdev_create()
*/
int whio_dev_subdev_rebound( whio_dev * dev, whio_size_t lowerBound, whio_size_t upperBound );

/**
   Works like whio_dev_subdev_rebound(), but also reparents the subdevice (dev)
   to the new parent object.
*/
int whio_dev_subdev_rebound2( whio_dev * dev, whio_dev * parent, whio_size_t lowerBound, whio_size_t upperBound );
    
/**
   Returns true if dev appears to be a subdevice (as opened by
   whio_dev_subdev_create()), else it returns false.
*/
bool whio_dev_isa_subdev( whio_dev const * dev );

/** @struct whio_blockdev

   whio_blockdev is a helper intended to assist in
   partitioning of a larger i/o device. It is intended to
   be used in conjunction with a "master" i/o device
   which has logical partitions made up of fixed-sized
   records. Instead of providing a low-level i/o API, its
   API works at the "record" level, where each record
   is a block of a size specified when the object
   is initialized.

   whio_blockdev objects are initialized via whio_blockdev_setup()
   and cleaned up (depending on how they were created) using
   whio_blockdev_cleanup() or whio_blockdev_free().

   Though this type's internals are publically viewable,
   they should not be used by client code. Use the
   whio_blockdev family of functions instead.

   @see whio_blockdev_alloc()
   whio_blockdev_setup()
   whio_blockdev_cleanup()
   whio_blockdev_free()
   whio_blockdev_in_range()
   whio_blockdev_write()
   whio_blockdev_read()
   whio_blockdev_wipe()
*/
typedef struct whio_blockdev
{
    /**
       Info about the blocks this object manages.
    */
    struct blocks
    {
	/**
	   Size of each block. MUST NOT be changed after setting up
	   this object, and doing so may lead to errors.
	*/
	whio_size_t size;
	/**
	   Number of blocks. MUST NOT be changed after setting up
	   this object, and doing so may lead to errors.
	*/
	whio_size_t count;
	/**
	   Must be null or valid memory at least 'size' bytes
	   long. When a block is "wiped", this memory is copied over
	   that block.

	   The contents may be changed after setting up this object,
	   so long as the address stays valid (or is changed to
	   accommodate) and stays at least 'size' bytes long.
	*/
	void const * prototype;
    } blocks;
    /**
       Implementation details which the client should neither touch
       nor look at.
    */
    struct impl
    {
	/**
	   This object's i/o device. It is created via
	   whio_blockdev_setup() and cleaned up by
	   whio_blockdev_cleanup(). It is a whio_dev subdevice
	   which fences i/o operations on the parent device
	   to the range defined by whio_blockdev_setup().
	*/
	whio_dev * fence;
    } impl;
} whio_blockdev;

/**
   A whio_blockdev object for cases where static initialization is necessary
   (e.g. member whio_blockdev objects).
*/
#define whio_blockdev_empty_m {\
	{ /* blocks */ \
	    0 /*size*/,\
	    0 /*count*/,\
	    NULL /*prototype*/\
	},\
	{ /* impl */ \
	    NULL /*fence*/ \
	}\
    }

/**
   Empty initialization object.
*/
extern const whio_blockdev whio_blockdev_empty;


/**
   Allocates and returns a new whio_blockdev, which the caller owns,
   or 0 on OOM.  Because this function might be configured to use a
   memory source other than malloc, the object must be destroyed using
   whio_blockdev_free() instead of free().

   @see whio_blockdev_free()
*/
whio_blockdev * whio_blockdev_alloc();

/**
   Initializes the given whio_blockdev object, which must have been
   allocated using whio_blockdev_alloc() or created on the stack and
   initialized using whio_blockdev_empty or whio_blockdev_empty_m.

   bdev will use parent_store as its storage device, but will only
   access the device range [parent_offset,(block_size *
   block_count)). None of the parameters may be 0 except for
   parent_offset and prototype. If prototype is not null then it must
   be valid memory at least block_size bytes long. When a block is
   "wiped" (see whio_blockdev_wipe()), this prototype object is
   written to it.

   The parent_store object must outlive bdev. Performing any i/o on
   bdev after the parent i/o device is invalidated will lead to
   undefined results.

   On success, a call to whio_blockdev_cleanup() or
   whio_blockdev_free() must eventually be made for bdev to free up
   the internally allocated resources. See those functions for details
   on which to use.

   If bdev is passed to this function multiple times without a
   corresponding call to whio_blockdev_cleanup() betwean each setup,
   it will leak resources.

   Returns whio_rc.OK on success, some other value on error:

   - whio_rc.AllocError if allocation of a subdevice fails.

   - whio_rc.ArgError if any of bdev, parent_store, block_size, or
   block_count are 0.

   @see whio_blockdev_setup2()
   @see whio_blockdev_free()
   @see whio_blockdev_cleanup()
*/
int whio_blockdev_setup( whio_blockdev * bdev, whio_dev * parent_store, whio_size_t parent_offset,
			 whio_size_t block_size, whio_size_t block_count, void const * prototype );
/**
   Works similarly to whio_blockdev_setup(), but it uses the whole
   parent device and does not place an upper limit on the number of
   blocks it may write.

   parent may be any API-compliant device, including a subdevice.
   parent must outlive bdev. All i/o on the parent device starts at
   offset 0 and happens in blocks of block_size.

   whio_blockdev_in_range() will always return true for a blockdev
   initialized this way.

   Returns whio_rc.OK on success or whio_rc.ArgError if
   !bdev, !parent, or !block_size.

   Unlike whio_blockdev_setup(), this routine does not allocate any
   memory, but see whio_blockdev_setup() for the allocation and
   cleanup requirements of bdev.

   @see whio_blockdev_setup()
   @see whio_blockdev_free()
   @see whio_blockdev_cleanup()
*/
int whio_blockdev_setup2( whio_blockdev * bdev, whio_dev * parent, whio_size_t block_size, void const * prototype );

/**
   Cleans up internal memory owned by bdev but does not free bdev
   itself. After this, bdev may be passed to whio_blockdev_setup() to
   re-initialize it if needed.

   Returns true on success, false on error.

   If bdev is a default-initialized object then this function will
   likely attempt to free memory from an undefined memory region,
   leading to undefined behaviour.

   @see whio_blockdev_free()
   @see whio_blockdev_setup()
   @see whio_blockdev_setup2()
*/
bool whio_blockdev_cleanup( whio_blockdev * bdev );

/**
   Destroys bdev and any internal memory it owns. ONLY pass this
   object created using whio_blockdev_alloc(). DO NOT pass this an
   object which was created on the stack, as that will lead to a
   segfault. For stack-allocated objects use whio_blockdev_cleanup()
   instead.

   @see whio_blockdev_cleanup()
   @see whio_blockdev_alloc()
*/
void whio_blockdev_free( whio_blockdev * bdev );

/**
   Returns true if id is a valid block ID for bdev, else false.

   If bdev was initialized with whio_blockdev_setup2() then this
   function will always return true, with the assumption that the
   underlying device can indeed be grown if needed.
*/
bool whio_blockdev_in_range( whio_blockdev const * bdev, whio_size_t id );

/**
   Writes the contents of src to bdev at the underlying device
   position corresponding to the given block id.  On success it
   returns whio_rc.OK. It returns an error code if bdev or src are
   null, id is not in bounds, or on an i/o error. src must be valid
   memory at least bdev->blocks.size bytes long.

   Error conditions:

   - If !bdev or !src: whio_rc.ArgError is returned.

   - If whio_blockdev_in_range(bdev,id) returns false,
   whio_rc.RangeError is returned.
  
   - If writing fails, whio_rc.IOError is returned.
*/
int whio_blockdev_write( whio_blockdev * bdev, whio_size_t id, void const * src );

/**
   Reads bdev->blocks.size bytes of memory from the block with the
   given id from bdev and copies it to dest. dest must be valid memory
   at least bdev->blocks.size bytes long. Returns whio_rc.OK on success.
*/
int whio_blockdev_read( whio_blockdev * bdev, whio_size_t id, void * dest );

/**
   This is equivalent to whio_blockdev_write(bdev,id,bdev->blocks.prototype),
   but returns whio_rc.ArgError if either bdev or bdev->blocks.prototype
   are NULL.
*/
int whio_blockdev_wipe( whio_blockdev * bdev, whio_size_t id );

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* WANDERINGHORSE_NET_WHIO_DEVS_H_INCLUDED */
/* end file include/wh/whio/whio_devs.h */
/* begin file include/wh/whio/whio_stream.h */
#ifndef WANDERINGHORSE_NET_WHIO_STREAM_H_INCLUDED
#define WANDERINGHORSE_NET_WHIO_STREAM_H_INCLUDED 1

/*
   This file contains declarations and documentation for the generic
   whio_stream API. The specific stream implementations are declared
   in whio_streams.h.
*/

/** @page page_whio_stream whio_stream C Stream API

  The whio_stream API provides an abstract interface for sequential
  streams which are either read-only or write-only. In practice, this
  type of stream is often the only type an application has access to
  for certain operations (as opposed to a full-fledged i/o device with
  random access, as modelled by the whio_dev API). This API is similar
  to that of whio_dev, but is somewhat smaller (because sequential
  streams have fewer requirements than random-access streams do).

   Author: Stephan Beal (http://wanderinghorse.net/home/stephan/)

   License: Public Domain

 */
#include <stdarg.h> /* va_list */

#ifdef __cplusplus
extern "C" {
#endif

struct whio_stream;
/** @struct whio_stream_api

   whio_stream_api defines the "member functions" of the whio_stream
   class. It is an abstract interface for sequential streams.

   @see whio_stream
*/
struct whio_stream_api
{
    /**
       read() must read (at most) count bytes from its underlying
       source and write them to dest. It may read more than count
       (e.g. buffering) but must not write more than count bytes to
       dest, nor may it actually consume more bytes than that.

       It must return the number of bytes read, or 0 on EOF or error.
    */
    whio_size_t (*read)( struct whio_stream * self, void * dest, whio_size_t count );

    /**
       write() tries to write count bytes from src to its underlying
       destination. Returns the number of bytes written, 0 if it cannot
       write, or a number smaller than count on error.       
    */
    whio_size_t (*write)( struct whio_stream * self, void const * src, whio_size_t count );

    /**
       Close must close the stream, such that further reads or writes will
       fail. It must also free any resources owned by the instance, but must
       not free the self object.

       The interface requires that finalize() call close(), so normally
       client code does not need to call this. It is provided to allow
       for stack-allocated stream objects which otherwise could not
       be cleaned up uniformly.

       If dev->client.dtor is not null then this routine must call
       that function and pass it dev->client.data. If it is null then
       dev->client.data must not be modified (the lack of a destructor
       function is a signal that the client owns the object).

       This function should returned false if !self or if the stream is
       not opened.
    */
    bool (*close)( struct whio_stream * self );

    /**
       finalize() must call close() and then free the self object.
       After finalize() returns, self is not a valid
       object.

       The proper way to destroy a whio_stream object is:

       @code
       theStream->api->finalize(theStream);
       @endcode

       Implementations of this function must ensure that they meet
       that expectation.

       DO NOT call this on a stack-allocated object - use close()
       instead (which is provided primarily for stack-allocated
       objects).
    */
    void (*finalize)( struct whio_stream * self );

    /**
       Flushes the write buffer (for write streams). On success it
       must return whio_rc.OK. On error it returns an
       implementation-defined non-zero value.
    */
    int (*flush)( struct whio_stream * self );

    /**
       isgood() returns whether or not self is in a valid use state.
       It should return true on eof, as eof is not strictly an error.
       To report EOF it should return 0 from the read()
       implementation.
    */
    bool (*isgood)( struct whio_stream * self );

    /**
       This function must return a mask of whio_iomodes values which
       represent its read/write mode. If it cannot determine the mode
       the it should return WHIO_MODE_UNKNOWN. If the dev pointer is
       invalid or not of the correct type then WHIO_MODE_INVALID
       should be returned.
    */
    whio_iomode_mask (*iomode)( struct whio_stream * dev );
};

typedef struct whio_stream_api whio_stream_api;

/** @struct whio_stream

   whio_stream is an abstract interface for sequential streams. There
   is no default implementation - custom implementations must be
   provided which can handle specific stream types, e.g. FILE handles,
   an in-memory buffer, or a socket.

   The proper way to create any stream instance is from a factory
   function. The function may take any arguments necessary for
   constructing a new stream (or connecting to an existing one). For
   example, to create a stream for a FILE handle we might do:

   @code
   whio_stream * theStream = whio_stream_for_FILE(stdin,false);
   @endcode

   The public API of a stream object is accessed like:

   @code
   theStream->api->write( theStream, ... );
   @endcode

   (The first parameter as the equivalent of a "this" pointer,
   so we can get at instance-specific data.)

   For an explanation of why the "extra" api member exists, see the
   documentation for the whio_dev interface, which uses this same
   technique.

   The proper way to destroy a whio_stream object is:

   @code
   theStream->api->finalize(theStream);
   @endcode

   Implementations are responsible for properly implementing the
   finalize() member. Ownership of the underlying native stream is
   defined by the factory function which creates the stream.

   For examples of creating concrete implementations of this type,
   see the files whio_stream_FILE.c and whio_stream_dev.c.
*/
struct whio_stream
{
    /**
       Holds all "member functions" of this interface.  It is never
       legal for api to be NULL, and if a device with a NULL api
       member is used with the whio API then a segfault will certainly
       quickly result.
    */
    const whio_stream_api * api;
    /**
       Holds instance-specific, implementation-dependent
       information. Not for use by client code. The
       implementation-specific close() method should free up this
       memory.
    */
    whio_impl_data impl;
    /**
       This data is for sole use by whio_dev clients, with one
       important exception: see the docs for whio_client_data for
       details.
    */
    whio_client_data client;
};
/**
   Convenience typedef.
*/
typedef struct whio_stream whio_stream;

/**
   An initializer macro for use in whio_stream subclass struct
   initializers.
*/
#define whio_stream_empty_m { 0/*api*/, whio_impl_data_empty_m, whio_client_data_empty_m}

/**
   Empty initialization object for whio_streams.
*/
extern const whio_stream whio_stream_empty;

/**
   Equivalent to whio_dev_writefv() except that it takes a whio_stream
   object instead of a whio_dev.
*/
whio_size_t whio_stream_writefv(whio_stream * stream, char const * fmt, va_list args );

/**
   Equivalent to whio_stream_writefv() except that it takes an (...) 
   elipses list instead of a va_list.
*/
whio_size_t whio_stream_writef( whio_stream * stream, char const * fmt, ... );

/**
   Convenience function to read the next character from a whio_stream. If tgt
   is not 0 then it is assigned to the value of the character.
   Returns true if it reads a character, else false.

   Example:

   @code
   char x = 0;
   if( whio_stream_getchar( myStream, &x ) ) {  ... }
   @endcode
*/
bool whio_stream_getchar( whio_stream * stream, char * tgt );

/**
   Copies all data from istr to ostr, stopping only when
   istr->api->read() returns fewer bytes than requested. On success
   whio_rc.OK is returned, on error some other value.  On error this
   function unfortunately cannot report whether the failure was at the
   read or write level.

   The data is copied in chunks of some unspecified static size (hint: a few kb).
*/
int whio_stream_copy( whio_stream * istr, whio_stream * ostr );


/**
   Consumes stream to the first \\n character.  It appends that data, minus the newline,
   to dest. Returns the number of characters appended to dest, or 0 at EOF or on a read
   error.

   Note that the stream is consumed and the trailing newline character
   (if any) is effectively lost.

   whio_size_t whio_stream_readln_membuf(whio_stream * stream, struct memblob * dest );
*/

/**
   Functionally identical to whio_stream_readln_membuf() except that the
   line is returned as a null-termined string which the caller must
   clean up using free(). On error or EOF 0 is returned.

   char * whio_stream_readln(whio_stream * stream);
*/

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* WANDERINGHORSE_NET_WHIO_STREAM_H_INCLUDED */
/* end file include/wh/whio/whio_stream.h */
/* begin file include/wh/whio/whio_streams.h */
#ifndef WANDERINGHORSE_NET_WHIO_STREAMS_H_INCLUDED
#define WANDERINGHORSE_NET_WHIO_STREAMS_H_INCLUDED 1
/*
  Author: Stephan Beal (http://wanderinghorse.net/home/stephan/)

  License: Public Domain
*/


/*
   This file contains declarations and documentation for the concrete
   whio_stream implementations. The generic stream API is declared in
   whio_stream.h.
*/
#ifdef __cplusplus
extern "C" {
#endif

/**
   Creates a stream object which wraps the given whio_dev object.
   If takeOwnership is true then ownership of dev is passed to the
   new object. dev must outlive the returned object or results
   are undefined.

   Returns 0 if !dev or on an alloc error, otherwise it returns
   a new object which the caller must eventually free using
   str->api->finalize(str). If the stream owns dev then dev will be
   destroyed at that point, too.

   Whether the returned stream is write-capable is not specified here
   - write operations will simply fail if the device is not writable.

   The returned object's iomode() member may not return an accurate
   value, as the interpretation of iomode is slightly different for
   whio_dev devices. In short, its return value cannot be trusted. In
   order to know whether the returned stream can read or write (or
   both) you'll simply have to try it. Note that the stream and
   wrapped device share the same cursor position, so writing _and_
   reading via the same stream may produce confusing results unless
   the cursor placement of dev is carefully managed.
   
   Pedantic note: if takeOwnership is true then it is not legal for
   the whio_stream::client.data member of the returned object to refer
   to dev, as doing so may cause dev to be destructed before the
   owning stream object tries to close it. The
   whio_stream::client.dtor function may legaly make use of the stream
   and/or device but must never destroy the stream and must not
   destroy the device if takeOwnership=true was passed to this
   function.
*/
whio_stream * whio_stream_for_dev( whio_dev * dev, bool takeOwnership );

/**
   Creates a whio_stream wrapper around the given FILE handle. If fp
   was opened in read mode, it is illegal to use the stream in a write
   context (but this routine cannot check that). Likewise, if it was
   open for write mode, it is illegal to use the stream in a read
   context (again, this code cannot check that).

   The takeOwnership argument determines the ownerhsip of fp: if the
   function succeeds and takeOwnership is true then fp's ownership is
   transfered to the returned object. In all other cases ownership is
   not changed.

   The returned stream object must be destroyed by calling
   stream->destroy(stream). If the stream owns the FILE handle then
   that will close the FILE handle.

   If you want to write to stdout, simply use:

   @code
   whio_stream * out = whio_stream_for_FILE(stdout, false);
   @endcode

   And similar for stdin or stderr.
*/
whio_stream * whio_stream_for_FILE( FILE * fp, bool takeOwnership );

/**
   Works like whio_stream_for_FILE(), except that it accepts a
   filename and a file open mode argument (the same as expected by
   fopen()), and the stream takes over ownership of the underlying
   FILE handle.

   If allocation of the new stream or fopen() fails then 0 is returned.

   For output streams, for mode you will normally want mode "a" (if
   you want to keep the old contents) or "w" (if you want to lose the
   old contents). For input streams, use mode "r". Optionally, you can
   append the letter 'b' to the mode string for platforms which treat
   binary and text streams differently (POSIX platforms don't and
   probably ignore the 'b').

   The returned stream object is owned by the caller and must be
   destroyed by calling stream->api->finalize(stream).
*/
whio_stream * whio_stream_for_filename( char const * src, char const * mode );

/**
   Similar to whio_stream_for_FILE() but it takes an existing/open
   file handle number and uses fdopen() to try to open it. On success,
   a new whio_stream object is returned which wraps that FILE
   object. On error (fdopen() or a malloc() fails) 0 is returned.

   See the man page for fdopen() for details of how this might or might not
   behave the exact same as opening a FILE handle.

   The man pages say that the open mode (e.g "r", "r+", "w+", etc.) 
   "must be compatible with" the one used for opening the file
   descriptor in the first place. They do not say what "compatible"
   means, though (e.g. are "w" and "w+" compatible?). Because of this,
   this function may or may not be able to associate a FILE handle
   with the descriptor, as we cannot know the exact flags used to open
   that stream.
*/
whio_stream * whio_stream_for_fileno( int fileno, bool writeMode );

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* WANDERINGHORSE_NET_WHIO_STREAMS_H_INCLUDED */
/* end file include/wh/whio/whio_streams.h */
/* auto-generated on Fri Aug 26 20:59:39 CEST 2011. Do not edit! */
#if !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200112L /* needed for ftello() and friends */
#endif
/* begin file include/wh/whio/whio_zlib.h */
#if !defined(WANDERINGHORSE_NET_WHIO_ZLIB_H_INCLUDED)
#define WANDERINGHORSE_NET_WHIO_ZLIB_H_INCLUDED 1

#if ! defined(WHIO_CONFIG_ENABLE_ZLIB)
#  define WHIO_CONFIG_ENABLE_ZLIB 0
#endif

#ifdef __cplusplus
extern "C" {
#endif

/**
   Compresses src to dest using gzip compression of the level specified
   by the level parameter (3 is an often-used choice). zlib provides
   several constants for this value:

   Z_NO_COMPRESSION, Z_BEST_SPEED, Z_BEST_COMPRESSION, and
   Z_DEFAULT_COMPRESSION.

   If level is not in the bounds defined by those constants, it will
   be adjusted up (if too low) or down (if too high) to the minimum or
   maximum compression level.

   src must be a readable stream and dest must be writeable. They may
   not be the same object.

   If whio is not compiled with WHIO_CONFIG_ENABLE_ZLIB defined to a true value,
   this function does nothing and returned whio_rc.UnsupportedError.

   Returns whio_rc.OK on success, else some error value from one of
   zlib routines (a non-zero error code defined in zlib.h). If
   !src or !dest or (src==dest) then whio_rc.ArgError is returned.

   The compressed data is decompressable by gzip-compatible tools.

   Note that because a whio_stream instance can be created for any
   whio_dev device (see whio_stream_for_dev()), it is possible to use
   this routine to compress any i/o device to another.  However,
   random access with transparent compression/decompression is not
   supported (very few people have every managed to code that).

   On error, any number of bytes may or may not have been read from src
   or written to dest.

   @see whio_stream_gunzip()
   @see whio_stream_for_dev()
 */
int whio_stream_gzip( whio_stream * src, whio_stream * dest, int level );

/**
   Assumes src contains gzipped data and decompresses it to dest.

   src must be a readable stream and dest must be writeable. They may
   not be the same object.

   If whio is not compiled with WHIO_CONFIG_ENABLE_ZLIB defined to a true value,
   this function does nothing and returned whio_rc.UnsupportedError.

   Returns whio_rc.OK on success, else some error value from one of
   zlib routines (a non-zero error code defined in zlib.h). If !src or
   !dest or (src==dest) then whio_rc.ArgError is returned.

   On error, any number of bytes may or may not have been read from src
   or written to dest.

   @see whio_stream_gzip()
   @see whio_stream_for_dev()
*/
int whio_stream_gunzip( whio_stream * src, whio_stream * dest );

#ifdef __cplusplus
} /* extern "C" */
#endif


#endif /* WANDERINGHORSE_NET_WHIO_ZLIB_H_INCLUDED */
/* end file include/wh/whio/whio_zlib.h */
/* begin file include/wh/whio/whio_encode.h */
#if !defined(WANDERINGHORSE_NET_WHIO_ENCODE_H_INCLUDED)
#define WANDERINGHORSE_NET_WHIO_ENCODE_H_INCLUDED 1
/*
  Author: Stephan Beal (http://wanderinghorse.net/home/stephan/

  License: Public Domain
*/

#include <stddef.h> /* size_t on my box */
/** @file whio_encode.h

   This file contains an API for encoding/decoding binary data to/from
   memory buffers and i/o devices.
*/

#ifdef __cplusplus
extern "C" {
#endif

/**
   This enum defines some on-disk sizes for the utility routines
   which encode/decode data to/from whio_dev objects.
*/
enum whio_sizeof_encoded {

/** @var whio_sizeof_encoded_uint64

   whio_sizeof_encoded_uint64 is the length (in bytes) of an encoded uint64 value.
   It is 9: 1 tag byte + 8 data bytes.

   @see whio_decode_uint64()
   @see whio_encode_uint64()
*/
whio_sizeof_encoded_uint64 = 9,
whio_sizeof_encoded_int64 = whio_sizeof_encoded_uint64,
/** @var whio_sizeof_encoded_uint32

   whio_sizeof_encoded_uint32 is the length (in bytes) of an encoded uint32 value.
   It is 5: 1 tag byte + 4 data bytes.

   @see whio_decode_uint32()
   @see whio_encode_uint32()
*/
whio_sizeof_encoded_uint32 = 5,
whio_sizeof_encoded_int32 = whio_sizeof_encoded_uint32,

/** @var whio_sizeof_encoded_uint16

   whio_sizeof_encoded_uint16 is the length (in bytes) of an encoded uint16 value.
   It is 3: 1 tag byte + 2 data bytes.

   @see whio_decode_uint16()
   @see whio_encode_uint16()
*/
whio_sizeof_encoded_uint16 = 3,
whio_sizeof_encoded_int16 = whio_sizeof_encoded_uint16,

/** @var whio_sizeof_encoded_uint8

   whio_sizeof_encoded_uint8 is the length (in bytes) of an encoded uint8 value.
   It is 2: 1 tag byte + 1 data byte.

   @see whio_decode_uint8()
   @see whio_encode_uint8()
*/
whio_sizeof_encoded_uint8 = 2,
whio_sizeof_encoded_int8 = whio_sizeof_encoded_uint8,

/** @var whio_size_cstring

   whio_size_cstring is the encoded length of a C-style string,
   NOT INCLUDING the actual string bytes. i.e. this is the header
   size.

   @see whio_decode_cstring()
   @see whio_encode_cstring()
*/
whio_sizeof_encoded_cstring = 1 + whio_sizeof_encoded_uint32,

/**
   The encoded size of a whio_size_t object. Its size depends
   on the value of WHIO_SIZE_T_BITS.
*/
whio_sizeof_encoded_size_t =
#if WHIO_SIZE_T_BITS == 64
    whio_sizeof_encoded_uint64
#elif WHIO_SIZE_T_BITS == 32
    whio_sizeof_encoded_uint32
#elif WHIO_SIZE_T_BITS == 16
    whio_sizeof_encoded_uint16
#elif WHIO_SIZE_T_BITS == 8
    whio_sizeof_encoded_uint8
#else
#error "WHIO_SIZE_T_BITS is not a supported value. Try one of (8,16,32,64)!"
#endif
,

/**
   The encoded size of a whio_off_t object. Its size depends
   on the value of WHIO_SIZE_T_BITS.
*/
whio_sizeof_encoded_off_t =
#if WHIO_SIZE_T_BITS == 64
    whio_sizeof_encoded_uint64
#elif WHIO_SIZE_T_BITS == 32
    whio_sizeof_encoded_uint64
#elif WHIO_SIZE_T_BITS == 16
    whio_sizeof_encoded_uint32
#elif WHIO_SIZE_T_BITS == 8
    whio_sizeof_encoded_uint16
#else
#error "WHIO_SIZE_T_BITS is not a supported value. Try one of (8,16,32,64)!"
#endif
,

/**
 */
whio_sizeof_encode_pack_overhead = (1 + whio_sizeof_encoded_uint8)

};

   
/**
   Encodes a 32-bit integer value into 5 bytes - a leading tag/check
   byte, then the 4 bytes of the number, in big-endian format. Returns
   the number of bytes written, which will be equal to
   whio_sizeof_encoded_uint32 on success.

   dest must be valid memory at least whio_sizeof_encoded_uint32 bytes long.

   @see whio_decode_uint32()
*/
whio_size_t whio_encode_uint32( unsigned char * dest, uint32_t i );
/**
   The signed counterpart of whio_encode_uint32().
*/
whio_size_t whio_encode_int32( unsigned char * dest, int32_t i );

/**
   The converse of whio_encode_uint32(), this tries to read an
   encoded 32-bit value from the given memory. On success it returns
   whio_rc.OK and sets tgt (if not null) to that value. On error it
   returns some other value from whio_rc and does not modify tgt.

   src must be valid memory at least whio_sizeof_encoded_uint32 bytes
   long.

   Error values include:

   - whio_rc.ArgError = !src

   - whio_rc.ConsistencyError = the bytes at the current location
   were not encoded with whio_encode_uint32().

   @see whio_encode_uint32()

*/
int whio_decode_uint32( unsigned char const * src, uint32_t * tgt );
/**
   The signed counterpart of whio_decode_uint32().
*/
int whio_decode_int32( unsigned char const * src, int32_t * tgt );

/**
   Similar to whio_encode_uint32(), with the same conventions, but
   works on 16-bit numbers. Returns the number of bytes written, which
   will be equal to whio_sizeof_encoded_uint16 on success.

   dest must be valid memory at least whio_sizeof_encoded_uint16
   bytes long.

   @see whio_decode_uint16()
*/
whio_size_t whio_encode_uint16( unsigned char * dest, uint16_t i );
/**
   The signed counterpart of whio_encode_uint16().
*/
whio_size_t whio_encode_int16( unsigned char * dest, int16_t i );

/**
   Similar to whio_decode_uint32(), with the same conventions and
   error codes, but works on 16-bit numbers.  On success it returns
   whio_rc.OK and sets target to that value. On error it returns some
   other value from whio_rc and does not modify tgt.

   src must be valid memory at least whio_sizeof_encoded_uint16 bytes
   long.


   @see whio_encode_uint16()
*/

int whio_decode_uint16( unsigned char const * src, uint16_t * tgt );
/**
   The signed counterpart of whio_decode_uint16().
*/
int whio_decode_int16( unsigned char const * src, int16_t * tgt );

/**
   The uint8 counterpart of whio_encode_uint16(). Returns
   whio_sizeof_encoded_uint8 on success and 0 on error. The only
   error condition is that dest is null.

   dest must be valid memory at least whio_sizeof_encoded_uint8 bytes
   long.

*/
whio_size_t whio_encode_uint8( unsigned char * dest, uint8_t i );
/**
   The signed counterpart of whio_encode_uint8().
*/
whio_size_t whio_encode_int8( unsigned char * dest, int8_t i );

/**
   The uint8 counterpart of whio_decode_uint16(). Returns whio_rc.OK
   on success. If !src then whio_rc.ArgError is returned. If src
   does not appear to be an encoded value then whio_rc.ConsistencyError
   is returned.

   src must be valid memory at least whio_sizeof_encoded_uint8 bytes
   long.
*/
int whio_decode_uint8( unsigned char const * src, uint8_t * tgt );
/**
   The signed counterpart of whio_decode_uint8().
*/
int whio_decode_int8( unsigned char const * src, int8_t * tgt );


/**
   Encodes v to dest. This is just a proxy for one of:
   whio_encode_uint8(), whio_encode_uint16(), whio_encode_uint32() or
   whio_encode_uint64(), depending on the value of WHIO_SIZE_T_BITS.

   dest must be valid memory at least whio_sizeof_encoded_size_t bytes
   long.

*/
whio_size_t whio_encode_size_t( unsigned char * dest, whio_size_t v );

/**
   Decodes v from src. This is just a proxy for one of:
   whio_decode_uint8(), whio_decode_uint16(), whio_decode_uint32() or
   whio_decode_uint64(), depending on the value of WHIO_SIZE_T_BITS.
*/
int whio_decode_size_t( unsigned char const * src, whio_size_t * v );


/**
   Encodes v to dest. This is just a proxy for one of:
   whio_encode_int16(), whio_encode_int32() or whio_encode_int64(),
   depending on the value of WHIO_SIZE_T_BITS.

   dest must be valid memory at least whio_sizeof_encoded_off_t bytes
   long. Returns whio_sizeof_encoded_off_t on success.
*/
whio_size_t whio_encode_off_t( unsigned char * dest, whio_off_t v );

/**
   Decodes v from src. This is just a proxy for one of:
   whio_decode_int16(), whio_decode_int32() or whio_decode_int64(),
   depending on the value of WHIO_SIZE_T_BITS. Returns 0 on success.
*/
int whio_decode_off_t( unsigned char const * src, whio_off_t * v );

    
/**
   Encodes v to dev using whio_size_t_encode().
   Returns whio_sizeof_encoded_size_t on success.
*/
whio_size_t whio_dev_encode_size_t( whio_dev * dev, whio_size_t v );

/**
   Decodes a whio_size_t object from dev. On success whio_rc.OK is returned
   and tgt (if not null) is modified, otherwise tgt is not modified.
*/
int whio_dev_decode_size_t( whio_dev * dev, whio_size_t * tgt );

/**
   The 64-bit variant of whio_encode_uint32(). Follows the same
   conventions as that function but handles a uint64_t value instead
   of uint32_t.

   dest must be valid memory at least whio_sizeof_encoded_uint64 bytes
   long.
   
   @see whio_encode_uint16()
   whio_encode_uint32()
   whio_decode_uint64()
*/
whio_size_t whio_encode_uint64( unsigned char * dest, uint64_t i );
/**
   The signed counterpart of whio_encode_uint64().
*/
whio_size_t whio_encode_int64( unsigned char * dest, int64_t i );

/**
   The 64-bit variant of whio_decode_uint32(). Follows the same
   conventions as that function but handles a uint64_t value instead
   of uint32_t.

   src must be valid memory at least whio_sizeof_encoded_uint64 bytes
   long.
   
   @see whio_decode_uint16()
   whio_decode_uint32()
   whio_encode_uint64()
*/
int whio_decode_uint64( unsigned char const * src, uint64_t * tgt );
/**
   The signed counterpart of whio_decode_uint64().
*/
int whio_decode_int64( unsigned char const * src, int64_t * tgt );

/**
   Uses whio_encode_uint32() to write n elements from the given
   array to dev.  Returns whio_rc.OK on success. Returns the number of
   items written.

   @see whio_encode_uint32()
*/
whio_size_t whio_encode_uint32_array( unsigned char * dest, whio_size_t n, uint32_t const * list );

/**
   Reads n consecutive numbers from src, populating list (which must
   point to at least n uint32_t objects) with the results. Returns the
   number of items read, which will be less than n on error.

   @see whio_decode_uint32()
*/
whio_size_t whio_decode_uint32_array( unsigned char const * src, whio_size_t n, uint32_t * list );

/**
   Encodes a C string into the destination by writing a tag byte, the length of
   the string, and then the string bytes. If n is 0 then n is equivalent to
   strlen(s). Zero is also legal string length.

   Returns the number of bytes written, which will be (n +
   whio_sizeof_encoded_cstring) on success, 0 if !dev or !s.

   dest must be at least (n + whio_sizeof_encoded_cstring) bytes long,
   and on success exactly that many bytes will be written. The null
   terminator (if any) is not stored and not counted in the length.
   s may contain null characters.

   @see whio_decode_cstring()
*/
whio_size_t whio_encode_cstring( unsigned char * dest, char const * s, uint32_t n );

/**
   The converse of whio_encode_cstring(), this routine tries to
   decode a string from the given source memory.

   src must contain at least (whio_sizeof_encoded_cstring + N) bytes,
   where N is the number which is encoded in the first part of the data.
   On success exactly that many bytes will be read from src. The null
   terminator (if any) is not stored and not counted in the length.
   s may contain null characters.

   On success, tgt is assigned to the new (null-terminated) string
   (allocated via calloc()) and length (if it is not null) is set to
   the length of the string (not counting the terminating null). The
   caller must free the string using free(). If the string has a
   length of 0 then tgt is set to 0, not "", and no memory is
   allocated.

   Neither dev nor tgt may be 0, but length may be 0.

   Returns whio_rc.OK on success.

   On error, neither tgt nor length are modified and some non-OK value
   is returned:

   - whio_rc.ArgError = dev or tgt are 0.

   - whio_rc.ConsistencyError = src does not contain a string written
   by whio_encode_cstring().

   Example:

@code
char * str = 0;
size_t len = 0;
int rc = whio_decode_cstring( mySource, &str, &len );
if( whio_rc.OK != rc ) ... error ...
... use str ...
free(str);
@endcode

   @see whio_encode_cstring()
*/
int whio_decode_cstring( unsigned char const * src, char ** tgt, whio_size_t * length );


/**
   Encodes a 32-bit integer value into 5 bytes - a leading tag/check
   byte, then the 4 bytes of the number, in big-endian format. Returns
   the number of bytes written, which will be equal to
   whio_dev_sizeof_uint32 on success.

   @see whio_dev_decode_uint32()
*/
whio_size_t whio_dev_encode_uint32( whio_dev * dev, uint32_t i );

/**
   The converse of whio_dev_encode_uint32(), this tries to read an encoded
   32-bit value from the current position of dev. On success it returns
   whio_rc.OK and sets target to that value. On error it returns some
   other value from whio_rc and does not modify tgt.

   Error values include:

   - whio_rc.ArgError = !dev or !tgt

   - whio_rc.IOError = an error while reading the value (couldn't read enough bytes)

   - whio_rc.ConsistencyError = the bytes at the current location were not encoded
   with whio_dev_encode_uint32().

   @see whio_dev_encode_uint32()

*/
int whio_dev_decode_uint32( whio_dev * dev, uint32_t * tgt );

/**
   Similar to whio_dev_encode_uint32(), with the same conventions, but
   works on 16-bit numbers. Returns the number of bytes written, which
   will be equal to whio_dev_sizeof_uint16 on success.

   @see whio_dev_decode_uint16()
*/
whio_size_t whio_dev_encode_uint16( whio_dev * dev, uint16_t i );

/**
   Similar to whio_dev_decode_uint32(), with the same conventions and
   error codes, but works on 16-bit numbers.  On success it returns
   whio_rc.OK and sets target to that value. On error it returns some
   other value from whio_rc and does not modify tgt.

   @see whio_dev_uint16_encode()
*/

int whio_dev_decode_uint16( whio_dev * dev, uint16_t * tgt );


/**
   The 64-bit variant of whio_dev_encode_uint32(). Follows the same
   conventions as that function but handles a uint64_t value instead
   of uint32_t.

   @see whio_dev_uint16_encode()
   @see whio_dev_encode_uint32()
   @see whio_dev_decode_uint64()
*/
whio_size_t whio_dev_encode_uint64( whio_dev * fs, uint64_t i );

/**
   The 64-bit variant of whio_dev_decode_uint32(). Follows the same
   conventions as that function but handles a uint64_t value instead
   of uint32_t.

   @see whio_dev_decode_uint16()
   @see whio_dev_decode_uint32()
   @see whio_dev_uint64_encode()
*/
int whio_dev_decode_uint64( whio_dev * dev, uint64_t * tgt );

/**
   Uses whio_dev_encode_uint32() to write n elements from the given
   array to dev.  Returns whio_rc.OK on success. Returns the number of
   items written.

   @see whio_dev_encode_uint32()
*/
whio_size_t whio_dev_encode_uint32_array( whio_dev * dev, whio_size_t n, uint32_t const * list );

/**
   Reads n consecutive numbers from dev, populating list (which must
   point to at least n uint32_t objects) with the results. Returns the
   number of items read, which will be less than n on error.

   @see whio_dev_decode_uint32()
*/
whio_size_t whio_dev_decode_uint32_array( whio_dev * dev, whio_size_t n, uint32_t * list );



/**
   Encodes a C string into the device by writing a tag byte, the length of
   the string, and then the string bytes. If n is 0 then n is equivalent to
   strlen(s). Zero is also legal string length.

   Returns the number of bytes written, which will be (n +
   whio_dev_size_cstring) on success, 0 if !dev or !s.

   @see whio_dev_decode_cstring()
*/
whio_size_t whio_dev_encode_cstring( whio_dev * dev, char const * s, uint32_t n );

/**
   The converse of whio_dev_encode_cstring(), this routine tries to
   decode a string from the current location in the device.

   On success, tgt is assigned to the new (null-terminated) string
   (allocated via calloc()) and length (if it is not null) is set to
   the length of the string (not counting the terminating null). The
   caller must free the string using free(). If the string has a
   length of 0 then tgt is set to 0, not "", and no memory is
   allocated.

   Neither dev nor tgt may be 0, but length may be 0.

   Returns whio_rc.OK on success.

   On error, neither tgt nor length are modified and some non-OK value
   is returned:

   - whio_rc.ArgError = dev or tgt are 0.

   - whio_rc.ConsistencyError = current position of the device does not
   appear to be an encoded string written by whio_dev_encode_cstring().

   - whio_rc.IOError = some form of IO error.


   Example:

@code
char * str = 0;
size_t len = 0;
int rc = whio_dev_decode_cstring( myDevice, &str, &len );
if( whio_rc.OK != rc ) ... error ...
... use str ...
free(str);
@endcode


   @see whio_dev_encode_cstring()
*/
int whio_dev_decode_cstring( whio_dev * dev, char ** tgt, uint32_t * length );
/**
   Parses fmt in the same manner as whio_encode_pack() and returns
   the number of bytes which would be needed to encode that set
   of data. On error it returns 0, which is never a legal encoding
   length value. If itemCount is not null then it is set to he number
   if objects parsed from the list.

   e.g.

   @code
   whio_size_t itemCount = 0;
   whio_size_t len = whio_encode_pack_calc_size("828",&itemCount);
   // len==24 and itemCount==3
   @endcode

   Note that the encoded length is longer than the actual data because
   each encoded elements gets a consistency-checking byte added to it,
   to allow the decode routines to more safely navigate their input,
   and the number of items in the list is stored in the encoding. The
   size also includes bytes for the packing structure itself, and is
   not a mere accumulation of the types specified in the format
   string.
*/
whio_size_t whio_encode_pack_calc_size( char const * fmt, whio_size_t *itemCount );
    
/**
   Encodes a series of values supported by the various whio_encode_xxx()
   routines as an atomic unit. They can be unpacked by using
   whio_decode_pack().

   fmt must contain only the following characters:

   - '1' means the corresponding (...) arg must be a uint8_t.
   - '2' means the corresponding (...) arg must be a uint16_t.
   - '4' means the corresponding (...) arg must be a uint32_t.
   - '8' means the corresponding (...) arg must be a uint64_t.
   - 'S' means the corresponding (...) arg must be a whio_size_t.
   - '+' or '-' followed by a digit means the following number argument is signed. e.g. -2 or +2 means int16_t.

   
   Returns the result of calling whio_encode_xxx() for each argument,
   where XXX is the type designated by the format specifier.

   If itemsWritten is not null then it is set to the number of items
   successfully written. You can figure out what that number _should_ be
   by using whio_encode_pack_calc_size().
   
   e.g.:

   @code
   whio_size_t count = 0;
   whio_size_t rc = whio_encode_pack( mybuffer, &count,
               "14+4", myUint8, myUInt32, myInt32 );
   // count should be 3 now.
   // rc will be the same as whio_encode_pack_calc_size("14+4",0).
   @endcode

   You can use whio_encode_pack_calc_size() to figure out what the
   return value of whio_encode_pack() _should_ be.
   
   TODOS:

   - Consider adding support for whio_encode_cstring(). The problem
   here is that decoding it requires malloc()ing or some weird
   arg-passing conventions, e.g. fmt="s" requiring two args (char *
   dest,size_t destLen) (which wouldn't be all that bad for the uses i
   have in mind).
*/
whio_size_t whio_encode_pack( void * dest, whio_size_t * itemsWritten, char const * fmt, ... );

/**
   va_list form of whio_encode_pack().
*/
whio_size_t whio_encode_pack_v( void * dest, whio_size_t * itemsWritten, char const * fmt, va_list va );
/**
   This is the converse of whio_encode_pack(), and is used to unpack
   data sets packaged using that function. It takes the same format
   string as whio_encode_pack(), but requires pointers to arguments to
   be passed as the variadic arguments. e.g. fmt "1" requires a
   (uint8_t*) argument and fmt "-8" requires an int64_t.

   Returns whefs_rc.OK on success.

   If itemsRead is not null then it will be set ot the number items
   successfully decoded, whether or not an error code is returned.

   You can use whio_decode_pack_calc_size() to figure out how many
   items _should_ be decoded for the given format string.

   Be aware that a data set saved with whio_encode_pack() must be
   decoded with the exact same formatting string. Differences will
   cause the decoding process to return whio_rc.ConsistencyError.
*/
int whio_decode_pack( void const * src, whio_size_t * itemsRead, char const * fmt, ... );

/**
   va_list form of whio_deencode_pack().
*/
int whio_decode_pack_v( void const * src, whio_size_t * itemsRead, char const * fmt, va_list va );

/**
   Parses a whio_encode_pack()-formatted string and figures out the
   size of the encoded data. If itemCount is not NULL then it is set
   to the number of items parsed from fmt. On error, 0 is returned but
   itemCount will contain the number of values parsed before the
   error.
*/
whio_size_t whio_encode_pack_calc_size( char const * fmt, whio_size_t *itemCount );
    
#ifdef __cplusplus
} /* extern "C" */
#endif


#endif /* WANDERINGHORSE_NET_WHIO_ENCODE_H_INCLUDED */
/* end file include/wh/whio/whio_encode.h */
/* begin file include/wh/whio/whio_udb.h */
#ifndef WANDERINGHORSE_NET_WHIO_UDB_H_INCLUDED
#define WANDERINGHORSE_NET_WHIO_UDB_H_INCLUDED

#include <stdarg.h> /* va_list */
/** @page page_whio_udb whio_udb micro-database

    The whio_udb ("u" as in "micro" and "db" as in "database") API is
    a small database API encapsulating a storage-based hashtable for
    holding records with fixed maximum key and value sizes. When
    working with string records, the strings need not all be the same
    size, but all with have a db-instance-specified _maximum_
    size. When working with binary data, the user must tell the DB how
    to measure the length of the objects.

    The primary class is whio_udb, which uses whio_dev as its storage
    and has only a relatively small collection of functions for
    searching and updating the hashtable.

    All of the major algorithms are amortized O(1):

    - Inserting a new key/value pair.
    - Searching by key.
    - Removal of an entry by key.

    Updating of certain records requires that we also update 0-2
    neighboring records, which adds a small fixed/predictable i/o
    component to some algorithms, but fundamentally the performance is
    independent of the number of entries as long as the hashtable
    length is long enough (i.e. assuming few hash collisions).

    Obviously, longer key/value lengths mean more i/o, but when we say
    O(1) we mean, "constant in relation to another udb with the same
    record length". Most i/o does not require that the db read the
    key/data bytes, and their length plays relatively little role in
    the performance (unless of course they have huge values).

    For "core service"the whio_udb class requires a near-constant amount of
    dynamically-allocated memory. It must internally allocate enough
    memory to store one data record, which means the buffer size is
    determined by the upper bounds of the key/value sizes. The
    whio_udb_search() brings in another level of allocations, but
    they are managed via a page-based allocator.

    The management of the on-storage free-records list is quite
    efficient, and finding the next free record is an O(1)
    operation. The db will add data blocks on demand (also
    O(1)... where 1=(keyLen+dataLen)), but if the db has "too many"
    entries (a number approaching or surpassing its hashtable size)
    then hashcode collisions will slow it down somewhat (theoretically
    O(log n), n=number of collisions?). The db never allocates new
    blocks as long as it has free blocks.

    Primary Features:

    - Excellent performance characteristics. All significant
    operations are amortized O(1) as long as the hash function is good
    and the number of items inserted does not approach or exceed the
    hashtable size.

    - Fairly good throughput. My basic tests showed insert rates of
    around 60000 records per second for total key/data size of 72
    bytes of string data per record.

    - Memory-light. For small record sizes it typically needs only a
    couple kb of memory. It needs proporionately more memory larger
    records (it has to buffer one for encoding purposes).

    - Client-configurable hashtable size. Bbigger = less collisions at
    a price in storage space: whio_udb_sizeof_hashent bytes times
    hashtable size.

    - The collection of hash/comparison/length functions used by a db
    are named, and that name is stored in the db. When a db is opened,
    it loads the functions by their name. This removes the need for an
    opener to specify which functions should be used (provided his
    library has the registered function name) and avoids the
    possibility of function set mismatches.


    Primary Misfeatures:

    - The maximum key and data payload sizes are fixed when a db is
    created and cannot be changed. It only supports variable-length
    records within those upper bounds and only if the key/value
    handling functions support variable-length keys/values. (It
    supports C-string keys out of the box.)
    
    - It currently has no file locking support. That is on the TODO
    list. The framework is in place, i just need to figure out
    where/when to lock, and how to keep two
    same-process/same-file/different-whio_udb-instance cases from
    clobbering each other's locks (i don't think i can do that,
    though, without manually tracking the locks and making them
    globally available).

    - It is not currently safe to use a single whio_udb object, or a
    single udb file via different whio_udb instances, from multiple
    threads. Fixing this requires removing some of the db-instance
    buffering and allocating more often.

    - Each whio_udb instance has a single buffer where most (but not
    all) reads/writes of records go before they are written to or as
    they are read from storage. This is because records are encoded in
    a platform-neutral manner and this requires a buffer. Having that
    buffer interferes with the lifetime of certain return values.  The
    public API is _mostly_ blind to this, but there is some room for
    error there internally. i'm working on this.

    - It is designed to be able to work with strings or binary keys
    and data.

    - It currently has no mechanism for shrinking the storage by
    removing unused records. That requires some fairly intensive
    rebuilding of the tables, and there are internal
    buffering/allocation problems which have to be resolved before
    this can be handled properly. A simple workaround is to copy the
    data into another, newly-created db instance by using
    whio_udb_foreach_entry().

    The more significant TODOs:

    - The paging allocator is overkill for this API. Replace it with a
    simpler allocator which simply stores the last (e.g.) 3-5
    deallocations for later re-use. In practice we generally only need
    one record in memory at a time, and the paging allocator uses up
    much more space than that.
    
    - Add device locking. Its absence doesn't stop this from being
    used with non-file storage (or pseudo-file storage, like
    whio_epfs).

    - Add a vacuum feature to remove unused blocks. This requires
    moving records around, and therefore potentially re-linking
    objects. Workaround: use whio_udb_foreach_entry() to copy the data into
    a new db instance. That will inherently lose the free blocks.
    
    - Experiment with how we can use the free-item chain approach to
    serve data with purely variable key/value sizes. This would seem
    to force the find-next-free-block algo to be O(N) (N=number of
    free blocks), though, since we can only re-use blocks of the right
    size.  This also may pose a problem with db growth if we have no
    vacuum functionality.

    - Consider how... shit, i forgot. (Hours later...) Ah, right...
    adding encode/decode functions for the key/value data for
    marshalling their conversion to/from storage. Without this we
    cannot platform-portably store, e.g., integer keys as binary data
    (but must first encode them to a string). Doh... but then we have
    to account for different key- and encoded-key lengths, for
    example. i'd rather let the client deal with that bit.
*/

/** @page whio_udb_threading whio_udb and threading

ACHTUNG: threading support is not well tested!

General threading guidelines:

- A db may optionally have a mutex, set must be set with whio_udb_mutex_set()
before concurrent access to the object becomes possible (e.g. right after
opening or formatting it).

- Concurrent multi-threaded access without a compliant mutex in place
WILL eventually cause corruption in a db's internal state, and
possibly in the db contents.

- The mutex does not need to be capable of recursive locks.


The following API functions honor the mutex:


- whio_udb_flush()
- whio_udb_remove()
- whio_udb_insert_with_length()
- whio_udb_insert()
- whio_udb_reap_free_records()
- whio_udb_reap_free_records_mode()
- whio_udb_record_alloc()
- whio_udb_record_free()
- whio_udb_foreach_entry() locks for the duration of the loop.
- whio_udb_foreach_matching_glob(), whio_udb_foreach_matching_globs(),
whio_udb_foreach_matching_like(), and whio_udb_foreach_matching_likes()
are simply small wrappers around whio_udb_foreach_entry(), and lock for
the duration of the loop.

Routines which honer the mutex will fail if locking fails (returning
whio_rc.LockingError, or NULL, depending on their return type).
However, the udb code assumes that if locking succeeds then unlocking
will always succeed. The code does not check the unlock errors because
by the time an unlock happens there is no way to undo everything which
(except for the unlock error) seems to have suceeded until that point.
Thus unlocking errors (if any) are silently ignored.

Places where mutex support cannot or will not be added:

- The various whio_udb_record_XXX() functions which do NOT take a
whio_udb parameter cannot lock because they have no pointer back to
their db. That said, there is no direct reason for them to lock: they
work solely on private data of the record.

- whio_udb_close() function behaves safely if called from two
threads concurrently, but future use of the db object is of course
undefined after it is closed, no matter which thread it is used from.

- whio_udb_free() has the same limitations as whio_udb_close()

- None of the internal routines will lock unless they need to. Most of
the locking happens directly via public interfaces.

- Routines which read unchanging db state (e.g. its options
values or its i/o mode) do not honor the mutex. This includes
whio_udb_key_length() and whio_udb_data_length().

- whio_udb_insert_keyf() and whio_udb_insert_dataf() internally change
only local data but access 1 nummeric piece of immutable db data to
figure out how to size their buffer. They indirectly lock (via
whio_udb_insert_with_length()) after they have formatted the key/value.

- whio_udb_funcs_search(), whio_udb_funcs_register(), and
whio_udb_funcs_parse() use no db-private state and therefore cannot
lock it. search() and register() do use shared private/internal state
which is NOT mutex-locked, but whio_udb_funcs_register() is intended
only to be used very early in application initialization (if at all).
whio_udb_funcs_search() is safe as long as whio_udb_funcs_register()
is not called while whio_udb_funcs_search() is running.



Threading vis-a-vis Freeing/Closing a whio_udb:

Because, for example, records are allocated and deallocated by the
client, and those records become invalidated if the db object is
cleaned up, it is illegal to whio_udb_close() or whio_udb_free()
database while it still has active threads/sessions. Maybe we can add
a way for the db to keep a count its sessions, treat them as reference
counts, and don't actually close the db until all sessions are over.

*/
#ifdef __cplusplus
extern "C" {
#endif

    /** @def WHIO_UDB_ENABLE_METRICS

    If set to 1 the library is build to include certain
    metrics, otherwise they are removed. They do not
    drastically impact performance, but they do about
    double sizeof(whio_udb). These do not change
    the format of the database storage.
    */
#define WHIO_UDB_ENABLE_METRICS 1
    
    /** @page page_whio_udb_format whio_udb storage format

    All db records are encoded in an endian-neutral format. Key and
    value data is stores as-is, and thus is not platform-neutral
    unless the client so encodes it.

    The storage format broken down into areas of related record types.
    Abstractly it looks a bit like the following:

      MAGIC_BYTES
      --> UDB_OPTIONS
      --> UDB_HINTS
      --> HASH_ENTRY_1 ... HASH_ENTRY_N
      --> RECORD_1 ... RECORD_N ...

      (Despite the "N" suffix, the number of hashtable entries does
      not affect the upper bound on the number of records. The former
      is fixed, the latter grows on demand.)

      The various blocks look like this...
      
      MAGIC_BYTES:

      whio_udb_osz_sizeof_magic bytes:
      
      [WHIO_UDB_MAGIC_STRING][NULL byte]

      The magic bytes are a string composed of various compile-time
      options, e.g. the value of WHIO_SIZE_T_BITS (since changing that
      changes the sizes of internal types and the routines used to
      encode/decode them). The magic bytes of the library must match
      that of a stored db, or it will not be openable.
      
      UDB_OPTIONS:

      whio_udb_sizeof_dbopt bytes at position whio_udb_pos_dbopt:

      [tag char][hashtable size][key length][data length]

      UDB_HINTS:

      whio_udb_sizeof_hints bytes at position whio_udb_pos_hints:

      [tag byte]
      [id of next free record]
      [id of next un-free record]
      [highest record id]


      HASH_ENTRY:

      whio_udb_sizeof_hashent bytes at position whio_udb_pos_hashtable:
      
      [tag byte][data_record_id]

      The number of entries = db->opt.hashSize.

      
      Key/Data RECORD:

      whio_udb_sizeof_record(db) bytes long, starting immediately after the hashtable:
      
      [tag byte][hashcode][id][nextCollisionID]
      [prevFreeID][nextFreeID]
      [key_length][db->opt.keyLength bytes of key][NULL byte]
      [data_length][db->opt.dataLength bytes of data][NULL byte]


      The db starts out with no record entries. They are added
      (unbounded) on demand for read/write databases. Removing
      a key frees the record, and that record will be the next
      one used when the db needs a new record slot. The db never
      adds new blocks as long as it has free blocks available.

      The hashtable can be re-built using the data from the records,
      and i hope to one day use this to allow changing of the
      hashtable's size.
    */

    /** Hashcode type used by the whio_udb API. */
    typedef whio_size_t whio_udb_hash_t;

    /**
       whio_udb_key_cmp_f() is the interface whio_udb uses for
       comparing keys.

       Must compare, at most, len bytes from lhs and rhs and return
       less than 0, 0, or greater than 0 to signify that lhs is less
       than, equivalent to, or greater than rhs.  i.e. it must
       semantically behave like strncmp() and memcmp().

       Note that this is an equivalence, not identity, comparison.
       Implementations may of course check for identity to short-cut
       the check, but the whio_udb API will never (as far as i can
       tell) pass the same pointer as both args to this function.

       A value of NULL should semantically compare less than anything
       but NULL, to which it should compare equal.

       The whio_udb internals are careful not to pass len values
       which are out of range for its key length configuration.

       Maintenance reminder: the third argument is of type size_t,
       instead of whio_size_t, so that we can use memcmp() as an
       implementation. i despise size_t because it has an unspecified
       size and there is no portable printf()/scanf() specifier for
       it. That causes my debug code which uses size_t to throw all
       kinds of compile warnings when switching between 32- and 64-bit
       platforms.
    */
    typedef int (*whio_udb_key_cmp_f)( void const * lhs, void const * rhs, size_t len );

    /**
       whio_udb_key_hash_f() is the interface whio_udb instances use for hashing their
       keys.
    
       Must produce a non-zero hash value for (at most) len bytes from
       obj. The value 0 is reserved as an error code. If the hash
       would indeed be 0, it must return some other constant value.

       How it produces the hash is unimportant, but its mechanism must
       not change after the function has been used in a given db, or
       else an old key may hash to a different value (which would
       throw off the internal hashtable).

       The whio_udb API will call implementations like
       hash_f_impl(key,whio_udb_key_length(db,key)), and it is important that
       hashing implementation and the corresponding key-length
       function (see whio_udb_length_f()) play nicely together in
       order to avoid reading or overwriting memory which does not
       belong to the key.
    */
    typedef whio_udb_hash_t (*whio_udb_key_hash_f)( void const * obj, whio_size_t len );

    /**
       whio_udb_length_f() is the interface used for returning the
       length of whio_udb key and data fields. obj is the key/data
       bytes, and its exact size requirements depend on the
       configuration of the underlying whio_udb object. If using
       variable-sized keys (e.g. strings) then this routine must be
       able to determine where the object ends (e.g. at the NULL
       terminator). For non-string variable-length keys and data, a
       type-specific algorithm is required. For fixed-size records, a
       length function is not required: the db's preconfigured length
       is used in that case, and all key resp. value pointers passed
       in by the client damned well better respect that size.

       Implementations must return 0 if passed NULL. That said, the
       udb library tries not to pass NULL to any client-specified
       functions.
    */
    typedef whio_size_t (*whio_udb_length_f)( void const * obj );

    /**
       A whio_udb_key_hash_f() implementation which creates a hash
       using some unspecified hashing algorithim on the first n bytes
       of obj.  (The aglorithm is supposedly quite good, in particular
       for strings, according to the guy i got it from.) obj MUST be
       at least n bytes long.
    */
    whio_udb_hash_t whio_udb_hash_default( void const * obj, whio_size_t n );

    /**
       A whio_udb_key_hash_f() implementation which creates a hash
       from UP TO len bytes of str, stopping at the first NULL
       character. While i'm no expert on the topic, the hashing
       algorithm it uses is reported very good for "short" strings in
       particular.
    */
    whio_udb_hash_t whio_udb_hash_str( void const * str, whio_size_t len );

    /**
       A whio_udb_key_hash_f() implementation which creates a hash
       using the same algorithm as whio_udb_hash_str(), but in a
       case-insenstive manner. Thus "aaa", "AaA", and "aAa" would all
       have the same hashcode.
    */
    whio_udb_hash_t whio_udb_hash_str_nocase( void const * str, whio_size_t len );

    /**
       A whio_udb_length_f() implementation which takes it on faith
       that obj is a NULL-terminated string, and it acts like
       strlen(obj) (except that it returns 0 if obj is NULL, instead
       of crashing).
    */
    whio_size_t whio_udb_length_str( void const * obj );

    /**
       A whio_udb_key_cmp_f() implementation which treats s1 and s2 as
       strings and compares them using strncmp(3). It follows the
       whio_udb_key_cmp_f() guidelines regarding NULL values for s1
       and s2.
    */
    int whio_udb_key_cmp_str( void const * s1, void const * s2, size_t len );

    /**
       A whio_udb_key_cmp_f() implementation which treats s1 and s2 as
       strings and compares them case-insensitively. It follows the
       whio_udb_key_cmp_f() guidelines regarding NULL values for s1
       and s2.    
    */
    int whio_udb_key_cmp_str_nocase( void const * s1, void const * s2, size_t len );

    /** @internal
       @def WHIO_UDB_MAGIC_STRING_BIT_INFO

    WHIO_UDB_MAGIC_STRING_BIT_INFO is an internal string
    whose value depends on the value of WHIO_SIZE_T_BITS.
    This string becomes part of WHIO_UDB_MAGIC_STRING.

    The string value is a 4-byte hex representation of
    WHIO_SIZE_T_BITS' value. It's hex so that the string is the same
    length for all legal values of WHIO_SIZE_T_BITS. ("08" isn't
    decimal, and i don't want that confusion in there.)
    */
#if 8 == WHIO_SIZE_T_BITS
#  define WHIO_UDB_MAGIC_STRING_BIT_INFO "0x08"
#elif 16 == WHIO_SIZE_T_BITS
#  define WHIO_UDB_MAGIC_STRING_BIT_INFO "0x0F"
#elif 32 == WHIO_SIZE_T_BITS
#  define WHIO_UDB_MAGIC_STRING_BIT_INFO "0x20"
#elif 64 == WHIO_SIZE_T_BITS
#  define WHIO_UDB_MAGIC_STRING_BIT_INFO "0x40"
#else
#error "Invalid value for WHIO_SIZE_T_BITS!"
#endif

    /**
       The version string for the overall whio_udb data format.
    */
#define WHIO_UDB_FORMAT_VERSION "20100315"
    /**
       WHIO_UDB_MAGIC_STRING is the "magic bytes" string for a whio_udb
       data device.
    */
#define WHIO_UDB_MAGIC_STRING "whio_udb:format version="WHIO_UDB_FORMAT_VERSION":WHIO_SIZE_T_BITS="WHIO_UDB_MAGIC_STRING_BIT_INFO

    /**
       The whio_udb_funcs encapsulates the various client-specified
       functions required by whio_udb instances.

       @see whio_udb_funcs_parse()
       @see whio_udb_funcs_register()
       @see whio_udb_funcs_search()
    */
    struct whio_udb_funcs
    {
        /**
           Comparison function for db keys. See the whio_udb_key_cmp_f()
           docs for details.
        */
        whio_udb_key_cmp_f keycmp;

        /**
           A function which, which passed bytes for a db key, return
           the length of that key.  This may be less than
           whio_udb_key_length(db,NULL) in the case of string-like
           keys, but for all others it should return exactly keyLen.

           If this member is NULL then a whio_udb will use its
           keyLength as the key length for all keys, and all keys
           damned well better be that many bytes long.  DO NOT set
           this to null if using variable-sized keys.
        */
        whio_udb_length_f keylen;

        /**
           A function which, which passed bytes for a db data record,
           return the length of that data.  This may be less than
           whio_udb_data_length(db,NULL) in the case of string-like
           data, but for all others it should return exactly
           db->opt.dataLen.

           If this member is NULL then a whio_udb will use it's
           dataLength as key length, and all data damned well better
           be that many bytes long.  DO NOT set this to null if using
           variable-sized data.
        */
        whio_udb_length_f datalen;

        /**
           A hash function for keys.
        */
        whio_udb_key_hash_f hash;
    };
    /** Convenience typedef. */
    typedef struct whio_udb_funcs whio_udb_funcs;
    /** Empty-initialized whio_udb_funcs object. */
#define whio_udb_funcs_empty_m {                  \
        NULL/*keycmp*/,NULL/*keylen*/,NULL/*datalen*/,NULL/*hash*/}
    /**
       whio_udb_funcs object initialized with functions suitable
       for string-like keys and data.
    */
#define whio_udb_funcs_strings_m {              \
        whio_udb_key_cmp_str/*keycmp*/,\
        whio_udb_length_str/*keylen*/,\
        whio_udb_length_str/*datalen*/,      \
        whio_udb_hash_str/*hash*/}

    /**
       whio_udb_funcs object initialized with functions suitable
       for case-insensitive string-like keys and data.
    */
#define whio_udb_funcs_strings_nocase_m {              \
        whio_udb_key_cmp_str_nocase/*keycmp*/,\
        whio_udb_length_str/*keylen*/,\
        whio_udb_length_str/*datalen*/,      \
        whio_udb_hash_str_nocase/*hash*/}

    /** Empty-initialized object. */
    extern const whio_udb_funcs whio_udb_funcs_empty;

    /**
       Object initialized with functions suitable
       for string-like keys and data.
    */
    extern const whio_udb_funcs whio_udb_funcs_strings;

    /**
       Object initialized with functions suitable
       for case-insensitive string-like keys and data.
    */
    extern const whio_udb_funcs whio_udb_funcs_strings;

    /**
       This class encapsulates whio_udb options which
       become inherent properties of databases created
       using these properties

       @see whio_udb_dev_format()
    */
    struct whio_udb_opt
    {
        /**
           Maximum number of entries in the db's hashtable. Should,
           for purposes of hashing, be a prime number.

           As the number of entries in the table approaches this
           number, the chance of hash collisions increases (eventually
           to 100%). That won't break the db but will hurt search
           performance.

           The number of _records_ in the db is theoretically bounded
           only by the limits of whio_size_t. That doesn't mean we can
           store that many records, but that the underlying storage
           "should" be able to grow to those limits.

           Increasing the hashSize in small increments does not
           appreciably change the required size of the storage: each
           hashtable entry takes up whio_udb_sizeof_hashcode bytes on
           the storage.
        */
        whio_size_t hashSize;

        /**
           The maximum length, in bytes, of record keys.

           This value must be at least 1.
        */
        whio_size_t keyLen;

        /**
           The maximum length, in bytes, of record data.

           This value must be at least 1.
        */
        whio_size_t dataLen;
    };
    /** Convenience typedef. */
    typedef struct whio_udb_opt whio_udb_opt;

    /** Empty-initialized whio_udb_opt object. */
#define whio_udb_opt_empty_m {0/*hashSize*/, 0/*keyLen*/, 0/*dataLen*/}
    /** Macro for statically initializing a whio_udb_opt object. */
#define whio_udb_opt_static(HashSize,KeyLen,DataLen) { (HashSize), (KeyLen), (DataLen) }

    /** Empty-initialized object. */
    extern const whio_udb_opt whio_udb_opt_empty;


    /**
       A holder for internal hints used by whio_udb objects.
    */
    struct whio_udb_hints
    {
        /** ID of the next free record in the free-list. */
        whio_size_t freeList;
        /** Not yet used.

            ID of the next free record in the not-free-list.
        */
        whio_size_t usedList;
        /**
           ID of the highest-used internal table index. This is used
           to determine whether or not we have to add a block in order
           to satisfy an insert request.
        */
        whio_size_t highestID;

    };
    /** Convenience typedef. */
    typedef struct whio_udb_hints whio_udb_hints;
    /** Empty-initialized whio_udb_hints object. */
#define whio_udb_hints_empty_m {0/*nextFree*/,0/*usedList*/,0/*highestID*/}
    /** Empty-initialized object. */
    extern const whio_udb_hints whio_udb_hints_empty;


    /**
       Internally used for tracking whio_udb statistics. If this code
       is compiled with WHIO_UDB_ENABLE_METRICS set to a false value
       then this class contains only one meaningless placeholder
       member.
    */
    struct whio_udb_metrics
    {
#if WHIO_UDB_ENABLE_METRICS
        /** Number of non-replacing inserts performed. */
        uint32_t inserts;
        /** Number of insert-with-replace performed, where a replacement was really made.
         */
        uint32_t replacements;
        /** Number of succesful removals. */
        uint32_t removals;
        /** Number of searches requested. */
        uint32_t searches;
        /** Number of searches which found a match. */
        uint32_t searchHits;
        /** Number of searches which found no match. */
        uint32_t searchMisses;
        /** Number of times a record was read during hash code collision resolution. */
        uint32_t collisionTraversals;
        /** Number of times a record was added to the free-list. */
        uint32_t freeListAdd;
        /** Number of times a record was removed from the free-list. */
        uint32_t freeListRemove;
        /** Number of "short" record writes - only the record metadata. */
        uint32_t recordWritesShort;
        /** Number of "medium" record writes - the record metadata + key data. */
        uint32_t recordWritesMed;
        /** Number of "long" record writes - metadata, key, and data. */
        uint32_t recordWritesLong;
        /** Number of "short" record reads - only the record metadata. */
        uint32_t recordReadsShort;
        /** Number of "medium" record reads - the record metadata + key data. */
        uint32_t recordReadsMed;
        /** Number of "long" record reads - metadata, key, and data. */
        uint32_t recordReadsLong;
        /** Number of times a hashtable entry was read. */
        uint32_t hashReads;
        /** Number of times a hashtable entry was written. */
        uint32_t hashWrites;
        /** The total number of records allocated during the session. */
        uint32_t recordAllocs;
        /** The number of records allocated at the moment this metric is read. */
        uint32_t recordAllocsNow;
        /** The maximum number of records which were ever allocated concurrently. */
        uint32_t recordAllocsMaxConcurrent;
        /** The number of times records were deallocated. Ideally==recordAllocs. */
        uint32_t recordDeallocs;
        /** The number of times whio_udb_flush() was called. */
        uint32_t flushes;
        /** The number of times the db had to write its "hints" data
            (namely the free-list value). Each time an on-storage
            record is newly allocated or newly freed, this number is
            incremented.
        */
        uint32_t hintWrites;
#else
        /**
           A meaningless placeholder value which is this class' only
           content if the library is built without
           WHIO_UDB_ENABLE_METRICS.
         */
        uint8_t placeholder;
#endif
    };
    /** Convenience typedef. */
    typedef struct whio_udb_metrics whio_udb_metrics;
#if WHIO_UDB_ENABLE_METRICS
    /** Empty-initialized whio_udb_metrics object. */
#define whio_udb_metrics_empty_m { \
        0/*inserts*/,                                   \
            0/*replacements*/,                              \
            0/*removals*/,                              \
            0/*searches*/,                              \
            0/*searchHits*/,                            \
            0/*searchMisses*/,                          \
            0/*collisionTraversals*/,                   \
            0/*freeListAdd*/,                           \
            0/*freeListRemove*/,                        \
            0/*recordWritesShort*/,                          \
            0/*recordWritesMed*/,                          \
            0/*recordWritesLong*/,                                      \
            0/*recordReadsShort*/,                          \
            0/*recordReadsMed*/,                          \
            0/*recordReadsLong*/,                                      \
            0/*hashReads*/,                                         \
            0/*hashWrites*/,                            \
            0/*recordAllocs*/,                          \
            0/*recordAllocsNow*/,                         \
            0/*recordAllocsMaxConcurrent*/,                         \
            0/*recordDeallocs*/,                         \
            0/*flushes*/,                                \
            0/*hintWrites*/,                                \
            }
#else
#define whio_udb_metrics_empty_m { 0/*placeholder*/ }
#endif /* WHIO_UDB_ENABLE_METRICS */    
    /** Empty-initialized whio_udb_metrics object. */
    extern const whio_udb_metrics whio_udb_metrics_empty;

    /** @struct whio_udb_record

       whio_udb_record is the internal record type used for client
       data storage in a whio_udb. It used by clients via the
       whio_udb_search() and whio_udb_foreach_entry() interfaces.

       These objects are opaque to client code. Clients can
       use the various functions like whio_udb_record_key()
       and whio_udb_record_data() to fetch their data.

       @see whio_udb_record_key()
       @see whio_udb_record_data()
    */
    struct whio_udb_record;
    /** Convenience typedef. */
    typedef struct whio_udb_record whio_udb_record;

    
    /**
       On-storage sizes and positions of various whio_udb record types
       which have fixed sizes.
    */
    enum whio_udb_sizes_and_positions {
    /**
       Encoded size of the whio_udb core magic bytes, including a
       trailing NULL byte.
    */
    whio_udb_sizeof_magic = sizeof(WHIO_UDB_MAGIC_STRING)/*includes NULL byte*/,

    /**
       Encoded size of a hashcode field.
    */
    whio_udb_sizeof_hashcode = whio_sizeof_encoded_size_t,
    /**
       Encoded size of a hashtable entry.
    */
    whio_udb_sizeof_hashent = 1/*tag byte*/
    + whio_udb_sizeof_hashcode/*ID of data record*/
    ,

    /** Storage position of whio_udb::opt. */
    whio_udb_pos_dbopt = whio_udb_sizeof_magic,

    /**
       Size of encoded whio_udb_opt options.

       They are stored at position whio_udb_pos_dbopt in the storage.
    */
    whio_udb_sizeof_dbopt = 1 /*tag byte*/
    + whio_sizeof_encoded_size_t /* hashSize */
    + whio_sizeof_encoded_size_t /* keyLen */
    + whio_sizeof_encoded_size_t /* dataLen */
    ,
    /** Encoded size of internal hints. They live at
        position whio_udb_pos_hints of the db storage.
    */
    whio_udb_sizeof_hints = 1 /*tag byte*/
    + whio_sizeof_encoded_size_t /* whio_udb_hints::freeList */
    + whio_sizeof_encoded_size_t /* whio_udb_hints::usedList */
    + whio_sizeof_encoded_size_t /* whio_udb_hints::highestID */
    ,

    /** Storage position for whio_udb::hints. */
    whio_udb_pos_hints = whio_udb_pos_dbopt
    + whio_udb_sizeof_dbopt
    ,

    /**
       The maximum length of a "function set" name, not including a
       null terminator. This is stored at position
       whio_udb_pos_funcs_label in the whio_udb storage.
    */
    whio_udb_funcs_name_length = 48/*almost arbitrary!*/,
    /**
       The maximum length of a "function set" name,
       including a null terminator.
    */
    whio_udb_sizeof_funcs_label =
    1/*tag byte*/
    + whio_udb_funcs_name_length/*string bytes*/
    +1 /*trailing NULL*/
    ,
    /**
       On-storage position of the "function label"
       used by whio_udb to try to load the proper functions
       when it is opened.
    */
    whio_udb_pos_funcs_label = whio_udb_pos_hints
    + whio_udb_sizeof_hints
    ,
    /** Storage position for whio_udb's internal hashtable. */
    whio_udb_pos_hashtable = whio_udb_pos_funcs_label
    + whio_udb_sizeof_funcs_label
    ,
    /**
       The on-storage size of the header part of a whio_udb_record
       data record.  This does not include the space needed for the
       db-dependent key and value bytes.
    */
    whio_udb_sizeof_record_header = 1/*tag byte*/
    + whio_sizeof_encoded_size_t /* hash */
    + whio_sizeof_encoded_size_t /* id */
    + whio_sizeof_encoded_size_t /* nextCollision */
    + whio_sizeof_encoded_size_t /* prevFree */
    + whio_sizeof_encoded_size_t /* nextFree */
    + whio_sizeof_encoded_size_t /* keyLen */
    + whio_sizeof_encoded_size_t /* dataLen */
    };

    /** @internal

       Internal array index values used by in the whio_udb private
       API. Each entry is an array index in whio_udb::osz, and the
       value at that index described a certain static component of the
       database storage (e.g. the storage position or size of a given
       record type).
     */
    enum whio_udb_osz_indexes
    {
    /** Encoded size of udb magic bytes. */
    whio_udb_osz_sizeof_magic = 0,
    /** Encoded size of one hashtable entry. */
    whio_udb_osz_sizeof_hashent,
    /** Encoded size of one data record. */
    whio_udb_osz_sizeof_record,
    /** Encoded size of index hashtable entry. */
    whio_udb_osz_sizeof_ht,
    /** Encoded size of persistant db options. */
    whio_udb_osz_sizeof_dbopt,
    /** Encoded size of persistant db hints. */
    whio_udb_osz_sizeof_hints,
    /** Device-relative position of persistant db options. */
    whio_udb_osz_pos_dbopt,
    /** Device-relative position of persistant db hints. */
    whio_udb_osz_pos_hints,
    /** Device-relative position of special next-free record. */
    whio_udb_osz_pos_free,
    /** Device-relative position of index hashtable. */
    whio_udb_osz_pos_ht,
    /** Device-relative position of data records table. */
    whio_udb_osz_pos_data,
    /** Internal size of records in the whio_udb_record page-based
        allocator. The value at this index is the number of bytes
        needed to allocate the following data structure bundle:

        1) a whio_udb_record entry
        2) +whio_udb_sizeof_record_header bytes
        3) + keyLen + dataLen of the db
        4) +2 bytes (padding NULLs for the key/data)

    */
    whio_udb_osz_sizeof_page_line,
    /** Placeholder entry - must be last. */
    whio_udb_osz_enum_length
    };


    struct whalloc_book;/* internal detail, defined elsewhere */
    /**
       A whio_udb object encapsulates a single "micro-database"
       ("uDB"). It uses the whio_dev interface for storage and can
       therefore work using any compliant storage implementations
       provided for that interface.

       All members of this class must be considered private, and the
       implementation of the class is only visible in the public API
       to allow clients to stack-allocate (or custom-allocate) them.

       @see whio_udb_dev_format()
       @see whio_udb_dev_open()
       @see whio_udb_close()
       @see whio_udb_insert()
       @see whio_udb_search()
       @see whio_udb_foreach_entry()
       @see whio_dev_is_udb()
    */
    struct whio_udb
    {
        /**
           whio_dev::iomode()-compliant value. Will mostly be
           the same as dev->api->iomode(dev).
        */
        whio_iomodes iomode;
        /**
           Not yet used.

           Indicates storage locking mode:

           (<0) = don't yet know
           (0) = don't use locking
           (>0) = use locking
        */
        short lockMode;
        /** An internal error flag.
            
        Used mainly by cleanup routines to skip certain bits if the db
        is in an error state (e.g. flushing the db hints to disk).
        */
        int err;

        /** Device used for db storage. */
        whio_dev * dev;

        /**
           Internal DB options.
        */
        whio_udb_opt opt;
        /**
           The key/data function set used by the db.
        */
        whio_udb_funcs funcs;
        /** Internal hints for the data device. */
        whio_udb_hints hints;
        /**
           Internal buffer for decoding/encoding reads/writes of
           records from/to the storage.
        */
        whio_udb_record * rbuf;
        /**
           Not yet consistently used.
        */
        whio_mutex mutex;
        /**
           Holds various object sizes and device offsets, as described
           in the whio_udb_osz_indexes enum.
        */
        whio_size_t osz[whio_udb_osz_enum_length];
        /**
           A page-based memory allocator for whio_udb_record
           object and their key/data memory.
        */
        struct whalloc_book * recordBook;
        /** Various db metric. */
        struct whio_udb_metrics metrics;
    };
    /** Convenience typedef. */
    typedef struct whio_udb whio_udb;
    /** Empty-initialized whio_udb object. */
#define whio_udb_empty_m {\
        WHIO_MODE_INVALID/*iomode*/,\
        -1/*lockMode*/,\
        0/*err*/,\
        NULL/*dev*/,\
        whio_udb_opt_empty_m/*opt*/,\
        whio_udb_funcs_empty_m/*funcs*/,                                \
        whio_udb_hints_empty_m/*hints*/, \
        NULL/*rbuf*/,                   \
        whio_mutex_empty_m/*mutex*/,    \
        {/*osz*/0},                         \
        NULL/*recordBook*/,             \
        whio_udb_metrics_empty_m /*metrics*/ \
}
    /** Empty-initialized object. */
    extern const whio_udb whio_udb_empty;

    /**
       Allocates a new whio_udb object using an unspecified memory
       source. Ownership is given to the caller, who must eventually
       free the object using whio_udb_free().  Returns NULL on error.
    */
    whio_udb * whio_udb_alloc();

    /**
       Calls whio_udb_close(db) (if needed) then frees db. Returns 0
       on success, or non-zero if !db.

       Because of how records are allocated, any records created via
       whio_udb_record_alloc() or whio_udb_search() (and friends) will
       be invalidated (and deallocated) by this call. Calling
       whio_udb_record_free() on such records after the db is closed
       will result in undefined behaviour, very possibly dereferencing
       a NULL pointer. That said: please treat record pointers as
       "normal memory", and stay in the habit of cleaning them up as
       one would any other objects.
    */
    int whio_udb_free( whio_udb * db );

    /**
       Tries to open a whio_dev object which has previously been
       formatted as a udb.

       db must be either a pointer to NULL or a pointer to
       an empty-initialized client-allocated object. In the former
       case this function allocates the db object. In the latter
       the caller is assumed to have allocated (possibly on the stack)
       the db object.

       Returns 0 on success. On error, if the client passed in his own
       db object then he must free it up if it was dynamically
       allocated. If it was stack allocated, then there is nothing
       to clean up except the dev object (see below) if this function fails.

       dev must be an opened device which contains compatible
       udb-formatted data.  If dev does not appear to be formatted as
       a udb then this routine will fail with whio_rc.TypeError. The
       read/write mode of db will be determined by the i/o mode of
       dev.  On success ownership of dev is passed to *db. On error
       ownership of the device is not changed, and the owner must
       eventually free it. Because of how the ownership/destruction
       works, dev must be dynamically allocated (but i/o devices, in
       practice, always are).

       Example:
       
       @code
       whio_udb * db = NULL;
       whio_dev * dev = whio_dev_for_filename("my.udb","w+");
       int rc = whio_udb_dev_open( &db, dev );
       if( rc ) { // ... error ...
           dev->api->finalize(dev);
           return rc;
       }
       //... use db ...
       // Finalize db (also finalizes dev):
       whio_udb_free(db);
       @endcode

       @see whio_udb_dev_format()
       @see whio_udb_close()
    */
    int whio_udb_dev_open( whio_udb ** db, whio_dev * dev );
    
    /**
       Closes db and frees its internal resources, but does not
       free db itself.

       If db has a mutex (see whio_udb_mutex_set()) then it is illegal
       to close the db while multiple threads are using it. It must
       not be closed until all threads using it have stopped doing so.

       @see whio_udb_free()
    */
    int whio_udb_close( whio_udb * db );

    /**
       Formats a device for use as a whio_udb storage, destroying all
       data on that device, and creates a whio_udb object to manage
       the device.

       The opt object specifies the general options for the db.
       The dev object must be a writeable device.

       db should be a pointer to a NULL-initialized pointer to a db
       (see below for an example).  On success, *db is assigned to the
       new db, which must be destroyed using whio_udb_free().

       Alternately, db may be a pointer to non-NULL, in which case
       this function assumes that *db was freshly allocated and
       proceeds to use it.

       A third option: if db is NULL then internally this function allocates
       a whio_udb object for purposes of formatting, but discards it before
       returning and does not change ownership of the devs object.
       

       The various options:
       
       opt->hashSize:

       When creating a new db, opt->hashSize is the size of the
       internal hash table. It "should" be a prime number, but that is
       not a rule. Storage for all hash entries is allocated when the
       db is "formatted," but data blocks are added as needed. There
       is no inherent upper bound on the number of data entries, but
       as the number approaches opt->hashSize, the chances of a
       collision go up (eventually to 100%), which means poorer
       overall db performance. This number cannot be directly changed
       after the db is initialized, but it is possible to grow a db by
       creating a new copy with a higher hashSize, and then copying
       the data into the new object.  When opening an existing db,
       opt->hashSize will be set to the value from the db being
       opened.
       
       opt->keyLen:

       If creating a new db, opt->keyLen must be the maximum length,
       in bytes, of a db key. When opening an existing db this value
       is set to the value stored in the db device.

       opt->dataLen:

       If creating a new db, opt->dataLen must be the maximum length,
       in bytes, of a db data entry. When opening an existing db this
       value is set to the value stored in the db device.

       The dev parameter is described in whio_udb_dev_open(), and
       are treated identically here except that this routine
       overwrites its contents immediately.

       funcSetName must specify a name a function set for the
       hashtable.  The function set name must be resolvable via
       whio_udb_funcs_parse(). The function set name is required so
       that when opening the db, the correct function set can be
       loaded. If we allow the client to specify the functions at
       open-time, there is a very real possibility of a mis-match.  To
       define your own function set, pass it to
       whio_udb_funcs_register() before formatting or opening a DB
       which needs that set.

       On success, *db takes over ownership of dev, and will destroy
       the device when the db is closed. Ownership of dev is never
       changed on error.

       On error, any internally-allocated db object will be freed. If
       *db started out as non-NULL (i.e. the user allocated it) then
       this routine will, on error, close it (freeing its internal
       resources) but not deallocate it. In that case the caller must
       free *db using the complement to its allocation method
       (e.g. free() if it was allocated via malloc(), or do nothing if
       it is stack-allocated).

       This function will fail if dev supports byte range locking
       but this function cannot get an immediate write lock
       on the device. This is to avoid that the format overwrites
       an in-use db or that it waits for an in-use db to be closed
       before hosing it (presumably it's still useful if something
       had it opened). If dev does not support locking then no
       storage locking is done.
       
       Example:
       
       @code
       whio_udb * db = NULL;
       whio_dev * dev = whio_dev_for_filename("my.udb","w+");
       whio_udb_opt opt = whio_udb_opt_empty;
       {
           opt.hashSize = 71;
           opt.keyLen = 16;
           opt.dataLen = 128;
       }
       int rc = whio_udb_dev_format( &db, dev, &opt, "string=string" );
       if( rc ) { // ... Error! So we still own dev ...
           dev->api->finalize(dev);
           return rc;
       }
       //... use db ...
       // Finalize db (also finalizes dev):
       whio_udb_free(db);
       @endcode
       

       TODO: add a client-specified text string to the db files so
       that the client can tag a db. This could be used by the client
       to help ensure they're using the proper db for a given
       application.

       TODO: add a way for the client to disable locking support, as
       locking performance _really_ sucks on some network filesystems.
       
       @see whio_udb_dev_open()
       @see whio_udb_funcs_parse()
    */
    int whio_udb_dev_format( whio_udb ** db,
                             whio_dev * dev,
                             whio_udb_opt const * opt,
                             char const * funcSetName );

    /**
       Returns true if dev is not NULL and appears to be a whio_udb
       data container, else false. It performs only a minimal check,
       checking only the "magic bytes" at the start of the device.  If
       the device turns out (later) not to be a properly-formatted udb
       then future operations may fail with error code
       whio_rc.ConsistencyError (a sign that decoding of stored data
       failed).
    */
    bool whio_dev_is_udb( whio_dev * dev );

    /**
       Flushes db's storage device. Returns 0 on success, or a
       device-specific error code on failure. If !db then
       whio_rc.ArgError is returned. A read-only db will return
       whio_rc.AccessError.
    */
    int whio_udb_flush( whio_udb * db );
    
    /**
       Returns the whio_udb-internal size of a record block which has
       the given (maximum) key and data lengths.

       For a given whio_udb instance, the record block size of that db
       is whio_udb_record_buffer_size(db->opt.keyLen,db->opt.dataLen).

       Note that accidentally swapping the order of the arguments does
       not change the result.

       Returns 0 (which is an illegal record size) if either parameter
       is 0.

       This number is of potential interest to clients only because it
       is the amount of dynamic memory which a udb object has to
       allocate for each record buffer. However, the db allocates them
       in pages of an unspecified length, so this number cannot be
       used to 100% accurately predict a db's memory usage (but can
       give a good ballpark figure).


       Rambling notes...

       If all compilers supported C99 variable-length arrays we
       wouldn't need to dynamically allocate our encoding/decoding
       buffers for most cases. The db allocates one for itself, but
       internally we try to avoid using it so as to not introduce more
       points for contention between threads.
    */
    whio_size_t whio_udb_record_buffer_size( whio_size_t keyLen, whio_size_t dataLen );

    /**
       Equivalent to whio_udb_record_buffer_size(db->opt.keyLen,db->opt.dataLen),
       but returns 0 if !db.
    */
    whio_size_t whio_udb_sizeof_record( whio_udb const * db );

    /**
       Registers a whio_udb_funcs collection with a specific name,
       such that whio_udb_funcs_search(n) will return a copy of that
       object.

       The library only has internal space for a static number of
       entries, but the interface guarantees that at least 10 will be
       available for client use. The library does not use this
       registration table for its own purposes (it uses
       whio_udb_funcs_parse() instead), so all slots are free for
       client use and any registered entries are guaranteed to have
       come from client code.

       This routine is not thread-safe and should only be used as
       early in the application as possibly (ideally early on in
       main(), but for single-threaded apps it doesn't matter).

       On success (all parameters are in order and there is enough
       space to fill the request), a pointer to the now-registered
       _copy_ of f is returned, that copy being a static/shared object
       owned by the library. In general it is not necessary to hold
       this pointer, as the API internally copies whio_udb_funcs
       rather than hold pointers to them.

       Returns NULL on error:

       - Arguments are null

       - f->keycmp or f->hash are NULL (f->keylen and f->datalen may
       legally be NULL only for dbs with absolute record sizes).

       - n is longer than whio_udb_funcs_name_length, not including
       the NULL terminator.

       - The internal table is full.

       - An entry is already registered with that name.
       
       The function whio_udb_funcs_parse() is related, but can
       "create" function sets using a formatted name string. For set
       names which it can parse, whio_udb_funcs_register() need not be
       used.
       
       @see whio_udb_funcs_search()
       @see whio_udb_funcs_parse()
    */
    whio_udb_funcs const * whio_udb_funcs_register( char const * n, whio_udb_funcs const * f );

    /**
       Returns a function set registered via
       whio_udb_funcs_register(), or NULL if no set is found with the
       given name.

       See whio_udb_funcs_register() for the list of pre-defined
       function set names.

       @see whio_udb_funcs_register()
       @see whio_udb_funcs_parse()
    */
    whio_udb_funcs const * whio_udb_funcs_search( char const * n );


    /**
       whio_udb_funcs_parse() constructs a whio_udb_funcs set from a
       key which follows a simple naming convention. This function
       includes the functionality of whio_udb_funcs_search(), but also
       allows one to create certain combinations of sets on the fly.
       Explicitly registered function sets take precedence over
       "constructed" sets, and this function always prefers a
       registered set over constructing one on its own.

       key must be either:

       - A string usable by whio_udb_funcs_search() (i.e. the name of
       a registered function set).

       - A string in the form "KEY_TYPE=VALUE_TYPE". Where the valid
       values of KEY_TYPE and VALUE_TYPE are listed below...

       The supported key/value type tokens are:

       - "string", for C-string-like keys/values.

       - "string:nocase", like "string", but for case-insensitive
       keys.  This means searching for key "a" will also match a key
       named "A", and that you cannot insert keys which differ only in
       case (you can of course replace the first entry with a new one,
       but they cannot co-exist). This is only supported by the KEY
       field, not the VALUE field, because the db never compares value
       fields.

       - "int8_t*", "int16_t*", "int32_t*", "int64_t*"

       - "uint8_t*", "uint16_t*", "uint32_t*", "uint64_t*"

       -"whio_size_t*"

       ("size_t*" is NOT supported because size_t has an unspecified size,
       making it unportable for our purposes.)
       
       Note that all of these strings are case- and
       whitespace-sensitive.

       Example: "int16_t*=string" represents a function set for
       (int16_t*) keys and C-string values.
       
       On success 0 is returned and tgt is modified to contain the values
       appropriate for the given key/value type combination.

       On error non-0 is returned and tgt is in an unspecified
       state. (If the first token is valid but the second isn't, tgt
       will be half-populated).

       If either key or tgt are NULL, or !*key, whio_rc.ArgError is
       returned.

       The various error codes one can expect:

       - whio_rc.ArgError: either (!key, !*key, or !tgt), or key is not
       properly formatted.

       - whio_rc.RangeError: key is longer than
       whio_udb_funcs_name_length.

       - whio_rc.NotFoundError: either the KEY or VALUE part of the
       key parameter could not be mapped to a known type (see the list
       above).

       This operation is effectively linear, taking up to O(R+(2*T))
       time. R=number of slots in set registration table, T=number
       known type tokens listed above.
       
       @see whio_udb_funcs_register()
       @see whio_udb_funcs_search()
    */
    int whio_udb_funcs_parse( char const * key, whio_udb_funcs * tgt );

    
    /**
        Dynamically allocates a new in-memory record object for db. It
        does not modify the storage or associate the object with any
        storage.

        Returns NULL if !db or on out-of-memory errors.

        On success, the returned object's key and data members
        are pointed to memory which is allocated as part of the
        record. That memory is long enough to hold the key resp.
        value data for a db record.    

        The bytes owned by the returned object are valid until either
        db is closed or until it is passed to whio_udb_record_free().

        The db manages allocation of records using a custom allocator
        which allocates in "pages" of records and recycles individual
        entries as they are freed (vis whio_udb_record_free()).

        @see whio_udb_record_free()
    */
     whio_udb_record * whio_udb_record_alloc( whio_udb * db );

    /**
       This is the converse of whio_udb_record_alloc(), and it must
       only be passed record objects which were allocated by that
       function. Passing it a record allocated using any other
       mechanism invokes undefined behaviour.

       All records allocated via whio_udb_record_alloc() should
       eventually be passed to this function. That said, when
       a db is closed, its custom allocator is cleaned up and
       any allocated records go with it.
       
       @see whio_udb_record_free()
    */
    int whio_udb_record_free( whio_udb * db, whio_udb_record * r );

    /**
       This is a special-case function which is not normally needed
       in client code...

       This function tells the underlying record allocation pager to
       remove any empty pages (pages which contain only unallocated
       records).
       
       If whio_udb_reap_free_records_mode() is called to enable
       auto-vacuuming, this function need never be used. (There are
       terribly minor performance tradeoffs, however.)
       
       Returns 0 on success. Only returns non-0 if !db.

       Note that this function only affects the memory
       allocator, and not on-storage records.
       
       @see whio_udb_reap_free_records_mode()
    */
    int whio_udb_reap_free_records( whio_udb * db );

    /**
       Enabled or disables "auto-reap" mode for the internal record
       allocator. This function only affects the memory allocator, and
       not on-storage records.
    
       To avoid having to allocate memory too often, the database
       manages records in a page-based system which allocates groups
       of records and then lets us de/allocate those individual items
       from the pager. By default, the db keeps keeps as much
       record-allocator memory around as the user ever _concurrently_
       allocated (and does so in pages of several records). That is
       called non-auto-reap mode, and is the mode enabled if this
       function is passed false as its second value. In auto-reap
       mode, pages are released from memory as soon as a page becomes
       empty (all records in it have been deallocated).

       This option should normally be left off, but one might want to
       turn it on for the following cases:

       - When keeping large numbers records active concurrently.

       - When using very large records. ("Large" is of course relative
       to your environment and your target memory goals.)

       The db internally keeps one record open for its general-purpose
       encoding/decoding buffer, so at least one page of records is
       always allocated as long as the db is alive.
       
       Returns 0 on success. Only returns non-0 if !db or db has not
       been properly initialized.
    */
    int whio_udb_reap_free_records_mode( whio_udb * db, bool doAutoReap );
    
    /**
       Searches db for the given key. If the key is not found the NULL
       is returned, else the return value depends on dest...

       If dest is non-null then it MUST be a properly-initialized
       record object with key/data members pointing to memory long
       enough to hold whio_udb_key_length(db,NULL)
       resp. whio_udb_data_length(db,NULL) bytes.

       If dest is NULL then this function allocates a new record using
       whio_udb_record_alloc().  (It must allocate even for most
       mismatch cases because it needs a private buffer for decoding
       the record data, which it has to do before it can find out if a
       match is really made.)

       Results are undefined if dest is non-NULL and dest was not
       allocated from db using either whio_udb_record_alloc() or by
       passing NULL as the final argument to this function (which
       causes whio_udb_record_alloc() to be used).
       
       On error:

       - NULL is returned.

       - dest, if not null, contains undefined data because its memory
       may be used for encoding/decoding multiple objects while performing
       the search. Do not rely on its contents, and do not rely on
       its internal state being consistent - it might contain a mix
       of data from multiple records.
       
       On success:

       - If dest was not NULL then dest is modified to contain the
       state for the found record and dest is returned.

       - If dest was NULL then the newly-allocated record is
       returned. Its memory is valid as long as db is opened, and must
       be freed using whio_udb_record_free().

       If dest is allocated from whio_udb_record_alloc() (or by
       passing (dest=NULL) to this function, which is equivalent),
       then the object carries with it all the memory it needs for
       encoding/decoding during i/o. That memory can be re-used via
       subsequent calls to this function, but eventually must be freed
       using whio_udb_record_free().

       The proper/safe ways to guaranty proper lifetime of the
       returned record data are:

       1) Allocate dest with whio_udb_record_alloc() before calling
       this function.

       or:
       
       2) Pass NULL to this function and let it allocate the object.

       If you try to "do it differently" then "you're on your own" and
       don't say that i didn't warn you. (Now that the class is
       opaque, clients can't do it any other way without importing the
       private API.)

       Examples:

       Single-use records:
       
       @code
       whio_udb_record * R = whio_udb_search(db,"hi",NULL);
       if( R ) { ... result found ...
           ...
           whio_udb_record_free(db,R);
       }
       @endcode

       Recycling records:
       
       @code
       whio_udb_record * R1 = whio_udb_record_alloc(db);
       while( ... something ... ) {
           whio_udb_record * r2 = whio_udb_search(db,"hi", R1);
           if( r2 ) { ... result found ...
               ... r2 _IS_ R1, but contains new contents on
               ... each search iteration
               ... Do not deallocate r2 here.
           }
       }
       whio_udb_record_free(db,R1);
       @endcode

       Note that it is legal to allocate a record at an arbitrary
       times (e.g. during intialization, for use as a buffer later
       on). Philosophically speaking, the record must be freed before
       the db is closed (and it must NEVER be freed _after_ the db is
       closed), but ... the internal paging allocator will indirectly
       free all open records when the db is closed. Thus it is not
       _strictly_ necessary to free them before the db is closed.
       (But, again, freeing them after it is closed will result in
       undefined behaviour.)
    */
    whio_udb_record * whio_udb_search( whio_udb * db,
                                       void const * key,
                                       whio_udb_record * dest );
        
    /**
       If db or key are NULL then non-zero (error) is returned, else...

       This function tries to insert a record with the given key and
       value into the database. If a matching record exists and
       replaceIfExists is true then the record is replaced, otherwise
       whio_rc.AccessError is returned.

       key must be valid memory at least keyLen bytes in length, and
       keyLen may not be more than whio_udb_key_length(db,NULL).

       val must be NULL or must be valid memory at least valLen bytes
       long. valLen may not exceed whio_udb_data_length(db,NULL) bytes
       in length. If val is NULL and valLen is not 0 then whio_rc.RangeError
       is returned. If val is NULL and valLen is 0 then an empty value
       is stored.

       If either keyLen or valLen are too long for db then
       whio_rc.RangeError is returned, else.

       On success 0 is returned. Some of the error codes one might
       theoretically encounter:

       - whio_rc.ArgError normally indicates that db or key are NULL,
       or that some deeper internal function was passed incorrect
       arguments (indicative of a bug/internal error).

       - whio_rc.AccessError means either that db is not writable,
       or that the key exists and replaceIfExists is false.

       - whio_rc.RangeError is possible, but can come from several
       internal sources, so having this code does not definitively
       describe the problem. If keyLen or valLen are out of range,
       you'll get this error code.

       - whio_rc.ConsistencyError and whio_rc.InternalError: if you
       ever see these then db should not be used. These errors only
       happen when the db has seen something it really didn't
       like. e.g.  unexpected (possibly corrupt) internal state or
       storage state. (If you see such a thing, please consider
       reporting it to this code's maintainer!)
    */
    int whio_udb_insert_with_length( whio_udb * db, void const * key, whio_size_t keyLen,
                                     void const * val, whio_size_t valLen, bool replaceIfExists );


    
    /**
       whio_udb_insert() is essentially the short-hand form of:

       @code
       whio_udb_insert_with_length( db, key, key ? whio_udb_key_length(db,key) : 0,
                                    val, val ? whio_udb_data_length(db,val) : 0,
                                    replaceIfExists );
       @endcode

       That is, it inserts key and val using the db-defined length-counting
       functions to determine the length of the key and value. If either of
       the key/data length-counting functions is NULL then the db's fixed key/data
       lengths is used in thier places, with these exceptions:

       - key NULL is not permitted.

       - val NULL is permitted, in which case the associated record is
       stored with an empty value (intuitively enough).

       If key or val are non-NULL then they MUST be able to be legally
       length-counted via whio_udb_key_length()
       resp. whio_udb_data_length(), or undefined results will ensue.

       Reminder: length-counting is only problematic when one or both
       of the key/data fields contains binary data of variable length.
       For string-based databases, length-counting is not a problem as
       long as all strings are properly NULL-terminated.
    */
    int whio_udb_insert( whio_udb * db, void const * key, void const * val, bool replaceIfExists );

    
    /**
       Removes the given record from the database. Returns 0 on
       success.  Note that not finding a record is treated as an error
       (whio_rc.NotFoundError), and client code can safely ignore that
       error code if they like.

       If you must know if it existed before removing it, call
       whio_udb_search().

       Design note:

       i really pondered as to whether a remove should fail if the
       object doesn't exist, and finally came to the conclusion that
       it's "the correct thing to do." That said, we don't normally
       care about removal failures.

    */
    int whio_udb_remove( whio_udb * db, void const * key );

    /** Returns true only if db is not null and is opened for
        read/write.
    */
    bool whio_udb_is_rw( whio_udb const * db );
    
    /**
       If db is NULL then 0 is returned, else...

       If key is NULL then db->keyLen is returned.

       Else if db->funcs.keylen is not NULL, the return value
       of db->funcs.keylen(key) is used.

       Else if db->funcs.keylen is NULL then db->opt.keyLen
       is returned.

       Got that?

       @see whio_udb_data_length()
    */
    whio_size_t whio_udb_key_length( whio_udb const * db, void const * key );

    /**
       If db  is NULL then 0 is returned, else...

       If data is NULL then db->dataLen is returned.

       Else if db->funcs.datalen is not NULL, the return value
       of db->funcs.datalen(data) is used.

       Else if db->funcs.datalen is NULL then db->opt.dataLen
       is returned.

       Got that?

       @see whio_udb_key_length()
    */
    whio_size_t whio_udb_data_length( whio_udb const * db, void const * data );
    
    /**
       A callback interface for use with whio_udb_foreach_entry(). It
       is called by that function and must behave thusly:

       All memory of the r object is owned by db and is invalidated as
       soon as the callback returns OR if the callback performs any
       operations on the db which require a non-const db pointer. The
       callback may copy the key/value data, print it out, or
       whatever, but must not keep a pointer to it.

       Callbacks can distinguish used from unused entries by checking
       if the record's keyLen member is 0. If it is, then that record
       is (or should be!) in the free-list.
       
       The callbackData parameter is passed as the final argument ot
       whio_udb_foreach_entry(), which simply passes it here so that
       the client has a way to pass his own state to the callback.

       whio_udb_foreach_entry() will never pass a NULL value to the
       callback for the db or r parameters, and implementations may,
       with good conscience, skimp on related error checking.
       
       The callback must return 0 on success. If it returns non-zero,
       that error code is returned via whio_udb_foreach_entry().
    */
    typedef int (*whio_udb_foreach_f)( whio_udb const * db, whio_udb_record const * r, void * callbackData );

    /**
       For each entry in the db, this routine calls callback(db,
       entry, callbackData). If the callback returns non-zero (error),
       iteration is stopped and that error code is returned.

       The whichOnes parameter describes which entries are passed
       to the callback:

       - (whichOnes>0) = all entries.

       - (whichOnes==0) = only free-list entries.

       - (whichOnes<0) = only in-use entries.
       
       Returns 0 on success, but success does not mean that the
       callback was ever called.

       The order of the calls to the callback has nothing to do with
       the order of the records in the hashtable. The order is
       arbitrary except in one special case: if (whichOnes==0) then
       only blocks in the free-list are traversed and they are
       traversed in their list order. (There is no "un-free" list,
       so there is no such optimization for (whichOnes<0).)

       This is of course an O(N) operation, where N is the number of
       records we end up having to traverse.

       Mutex locking: in order to try to keep the list from changing
       during the loop (which could lead to double visits and skipped
       entries) the mutex is locked for the duration of the loop.
       
       Design notes:

       A for-each approach was choses for iteration, instead of an
       iterator class, for a couple reasons:

       A) Requires much less code in the library. It normally requires
       more code in the client (a separate function instead of a
       loop), but so far i've liked how to modularizes my client code.

       B) This approach allows the db to better control locking during
       iteration, compared to iterator-style iteration.

       C) Lifetime and ownership issues regarding iterators do not
       come into play, eliminating a potential point for leaks via
       mis-use.
       

       TODOs:

       - Considering locking the db storage, but not the mutex, for
       the duration of the foreach. If another process modifies the table
       during foreach, we could end up calling the callback more than
       once for a given record and skipping others entirely.
    */
    int whio_udb_foreach_entry( whio_udb * db, short whichOnes, whio_udb_foreach_f callback, void * callbackData );

    /**
       A variant of whio_udb_foreach_entry() which calls the callback
       only for entries which match any of the given "glob" patterns.

       ACHTUNG: this function has undefined results if db is not
       configured for string-like keys.

       globs must be an array of at least n items long, each element a
       globbing string pattern.

       The glob parser recognizes most common globbing patterns, e.g.
       '*' and '?', and character ranges in the form '[a-z]', but does
       not support regex-like ranges in the form '{n,m}' nor bash-like
       string "creation" in the form 'x{a,b,c}'.

       The only argument which may legally be 0 is
       callbackData. Passing 0 for any other argument causes
       whio_rc.ArgError to be returned.

       Example:
       @code
       char const * pattern = "[a-zA-Z]*";
       whio_udb_foreach_matching_globs( db, &pattern, 1, my_callback, NULL );
       @endcode

       This function only calls the callback one time per entry, and stops
       checking for a match if any patterns apply. This is, the result
       set will never contain the same record twice unless the db is
       modified during the foreach loop _and_ those modifications just
       happened to re-order the block chain such as to repeat an old
       result.

    */
    int whio_udb_foreach_matching_globs( whio_udb * db, char const * const * globs, unsigned int n,
                                         whio_udb_foreach_f callback, void * callbackData );
    /**
       Equivalent to whio_udb_foreach_matching_globs(db,&globs,1,callback,callbackData).
    */
    int whio_udb_foreach_matching_glob( whio_udb * db, char const * glob, whio_udb_foreach_f callback,
                                        void * callbackData );

    /**
       Works identically to whio_udb_foreach_matching_globs() but the
       patterns it takes are matches like SQL patterns. e.g. the
       wildcard "a*" and the LIKE pattern "a%%" (note: the percent
       sign is only doubled there to please doxygen). If caseSensitive
       is true is is a case-sensitive match, otherwise it is
       case-insensitive (like SQL-92).
    */
    int whio_udb_foreach_matching_likes( whio_udb * db, char const * const * likes, unsigned int n,
                                         bool caseSensitive, whio_udb_foreach_f callback, void * callbackData );
    /**
       Equivalent to whio_udb_foreach_matching_likes(db,&like,1,caseSensitive,callback,callbackData).
    */
    int whio_udb_foreach_matching_like( whio_udb * db, char const * like, bool caseSensitive,
                                        whio_udb_foreach_f callback, void * callbackData );
    
    /**
       Returns the length of db's hashtable, or 0 if !db.

       This is an O(1) operation.
    */
    whio_size_t whio_udb_hashtable_length( whio_udb const * db );

    /**
       Adds n empty records to db. It is not normally necessary to do
       this, as records are created on demand. If you want to
       pre-allocate records, however, this is the way to do it. All
       such records start out their lives in the free-list and may be
       allocated by future insertions in the db.

       This is an O(n) operation (literally).
    */
    whio_size_t whio_udb_add_empty_records( whio_udb * db, whio_size_t n );


    /**
       A variation of whio_udb_insert() with a very unusual argument ordering
       to accomodate variadic function conventions...

       This function tries to insert a key formatting using the given
       printf-compatible format string and va_list. If the formatted
       result is smaller than whio_udb_key_length(db,NULL) then the
       result of calling
       whio_udb_insert(db,formattedKey,val,replaceIfExists) is
       returned.

       If the formatted string evaluates to empty or would be longer than
       whio_udb_key_length(db,NULL) then whio_rc.RangeError is returned.

       On success 0 is returned (unlike printf() and friends, which
       return the number of bytes written).

       Be very aware that the val argument comes _before_ the key
       argument. This is unfortunate, but a requirement of the rules
       for variadic functions.
       
       Minor Achtungen:

       - This function relies on C99 Variable-length Arrays. If db's keyLen
       is way too large then... well, i don't know what will happen.

       - For compilers without VLA support there is a compile toggle
       in whio_udb.c which will cause malloc()/free() to be used
       instead of a VLA. e.g. The TinyC compiler doesn't yet do VLAs
       :(, and for that compiler the malloc() toggle is automatically
       selected.
    */
    int whio_udb_insert_keyfv(whio_udb * db, void const * val, bool replaceIfExists, char const * fmt, va_list vargs );

    /**
       Equivalent to whio_udb_insert_keyfv(), but takes elipsis arguments.
    */
    int whio_udb_insert_keyf(whio_udb * db, void const * val, bool replaceIfExists, char const * fmt, ... );

    /**
       The counterpart of whio_udb_insert_keyfv(), this function takes
       an unformatted key and inserts a formatted value. The behaviour
       and return value are the same as for whio_udb_insert_keyfv()
       except that the ranges apply to whio_udb_data_length(db,NULL)
       instead of whio_udb_key_length(db,NULL).

       Beware: if db's dataLen is "too big" (i don't know what that
       really means), i don't know how your C platform will behave in
       the face of very large VLA objects. If VLAs do not appear to be
       available on the build platform then this function calls back
       to malloc() for its formatting needs.
    */
    int whio_udb_insert_datafv(whio_udb * db, void const * key, bool replaceIfExists, char const * fmt, va_list vargs );

    /**
       Equivalent to whio_udb_insert_datafv(), but takes elipsis arguments.
    */
    int whio_udb_insert_dataf(whio_udb * db, void const * key, bool replaceIfExists, char const * fmt, ... );

    /**
       The public interface for fetching a record's key bytes. If
       length is not NULL then the key's length (in bytes) is written
       to it.

       Results are undefined if r is not the result of a whio_udb_search()
       operation.

       The contents of the returned memory are valid until the record
       is destroyed or until it is passed as the final argument to
       whio_udb_search() (or a similar function which recycles a record).
       
       The member returned will never be NULL unless there is some
       major bug in the internal API. While the logical length of the
       key is the value assigned to the length output parameter, the
       memory returned will always be exactly the length of the
       underlying database's maximum key length plus 1 byte which
       contains a trailing NULL. Thus string-based databases need
       not account for the trailing NULL when fetching records where (length)
       is exactly the same as the db's maximum.
       
       @see whio_udb_record_data()
    */
    void const * whio_udb_record_key( whio_udb_record const * r, whio_size_t * length );

    /**
       The public interface for fetching a record's data (value)
       bytes. If length is not NULL then the data's length (in bytes)
       is written to it.

       Results are undefined if r is not the result of a
       whio_udb_search() operation.

       The contents of the returned memory are valid until the record
       is destroyed or until it is passed as the final argument to
       whio_udb_search() (or a similar function which recycles a record).
       
       The member returned will never be NULL unless there is some
       major bug in the internal API. While the logical length of the
       data is the value assigned to the length output parameter, the
       memory returned will always be exactly the length of the
       underlying database's maximum data length plus 1 byte which
       contains a trailing NULL.
       
       @see whio_udb_record_key()
    */
    void const * whio_udb_record_data( whio_udb_record const * r, whio_size_t * length );

    /**
       Returns the unique (within its own udb) ID of the given record.
       The ID is stable and valid until:

       a) The record is removed using whio_udb_remove().

       b) A vaccuuming feature is added to UDB and the UDB is
       vaccuumed, in which case the IDs can change.
    */
    whio_size_t whio_udb_record_id( whio_udb_record const * r );

    /**
       This is a low-level routine which tries to read a UDB record by
       its internal ID.

       db is the UDB to read from. id is the record ID, and it must correspond
       to an existing record (in use or not).

       tgt must be a pointer to NULL or a pointer to a record object
       allocated with whio_udb_record_alloc(db). If the record can be
       read then 0 is returned and tgt is populated with its contents.
       If *tgt is NULL then this function allocates a new record,
       which the caller must eventually free with
       whio_udb_record_free(). If the caller allocated it, he must of
       course eventually free it as well. If this function calls and
       the caller allocated the *tgt object, its contents are
       unspecified (this is a side-effect of how record
       reading/decoding is done - *tgt's contents might have been
       partially overwritten). If this function fails and this
       function allocates *tgt then *tgt is guaranteed not to be
       modified by this call (i.e. it will be NULL when this function
       returns).

       On error non-0 is returned:

       - If !db or !tgt: whio_rc.ArgError

       - Various errors can happen during the actual read,
       e.g. whio_rc.IOError, whio_rc.LockingError, or
       whio_rc.ConsistencyError (if the UDB appears to be corrupt).

       - If allocation of a new record fails: whio_rc.AllocError.
     */
    int whio_udb_record_read_by_id( whio_udb * db, whio_size_t id, whio_udb_record ** tgt );
    
    /**
       Tries to assign m to be db's mutex. m is bitwise copied
       and need not outlive db (but its contents must be valid
       as long as db is alive).

       The given mutex is used to lock/unlock the database object.

       Concurrent, multi-threaded access to the db object without a
       compliant mutex will eventually cause corruption of the
       internal state and possibly the on-storage state.
       
       If m is NULL then db's mutex is removed.
       
       Returns 0 on success, or:

       - whio_rc.ArgError: !db

       - whio_rc.RangeError: one of m.lock or m.unlock is NULL but the
       other is not NULL.

       ACHTUNG: This function, if used, MUST be called before
       concurent access to db is possible and it MUST NOT be changed
       later on with one exception: it may be set to an empty mutex to
       clear out the mutex (e.g. by passing NULL or
       <tt>&whio_mutex_empty</tt>).

       BUGS: all of the code assumes that if a lock succeeds,
       its unlock will also succeed. It does not catch unlocking
       errors because by that time it is too late to undo any
       changes the locked operation might have implemented.
    */
    int whio_udb_mutex_set( whio_udb * db, whio_mutex const * m );
    /**
       Copies the current internal metrics of db into dest.

       Returns 0 on success. Only fails (with whio_rc.ArgError) if
       either arg is NULL.
       
       @see whio_udb_metrics_get_ptr()
       @see whio_udb_metrics_reset()
    */
    int whio_udb_metrics_get( whio_udb const * db, whio_udb_metrics * dest );

    /**
       Returns a pointer to the db's metrics, or NULL if !db.
       The pointer is valid as long as db itself is. This variant is
       provided for applications which want to monitor metrics from a
       different thread. This one multi-threaded usage of db is legal
       as long as the returned pointer cannot be used after db is
       destroyed in the other thread.

       @see whio_udb_metrics_get()
       @see whio_udb_metrics_reset()
    */
    whio_udb_metrics const * whio_udb_metrics_get_ptr( whio_udb const * db );
    
    /**
       Re-sets the metrics counter for db. Returns 0 on success
       or whio_rc.ArgError if !db.

       This routine locks db's mutex, by the way, so it may have to
       wait to return.
       
       @see whio_udb_metrics_get()
       @see whio_udb_metrics_get_ptr()
    */
    int whio_udb_metrics_reset( whio_udb * db );

    /**
       whio_udb_keycmp_ptr_NUMERIC_TYPE() is a placeholder/documentation-point
       function for several declarations of concrete
       whio_udb_keycmp_f() implementations declared via macros. All of
       the functions follow this naming pattern:

       whio_udb_keycmp_ptr_TYPENAME(), where TYPENAME is one of the following:

       - int8_t, int16_t, int32_t, int64_t, unsigned variants (with a
       'u' prefix) of the same.

       - whio_size_t, but NOT size_t (which the library tries to avoid
       because of its unpredictable size.

       In all cases, the lhs and rhs pointers MUST be const-pointers
       to the corresponding TYPENAME.  Thus
       whio_udb_keycmp_ptr_uint32_t() requires that the arguments be
       (uint32_t [const] *).

       The pointers are (if not NULL) dereferenced and compared
       numerically.

       These functions all ignore their len parameter.
       
       Do not bother searching for a variant of this API which takes a
       real (size_t) pointer - there isn't one. They cannot be used
       portably for this purpose because they have indeterminate
       sizes. That means storing on one machine and loading on another
       might have different results.
      
       @see whio_udb_hash_ptr_NUMERIC_TYPE()
    */
    int whio_udb_keycmp_ptr_NUMERIC_TYPE( void const * lhs, void const * rhs, size_t len );
    /**
       whio_udb_hash_ptr_NUMERIC_TYPE() is a placeholder/documentation-point
       function for several declarations of concrete
       whio_udb_key_hash_f() implementations declared via macros. All
       of the functions follow this naming pattern:

       whio_udb_hash_ptr_TYPENAME(), where TYPENAME is one of the following:

       - int8_t, int16_t, int32_t, int64_t, and unsigned variants (with a 'u'
       prefix) of the same.

       - whio_size_t, but NOT size_t (which libwhio tries to avoid
       because of its unpredictable size).

       In all cases, the obj ptr MUST be const-pointers to the
       corresponding TYPENAME.  Thus whio_udb_hash_ptr_uint32_t()
       requires that obj be (uint32_t [const] *).

       The hashcode is calculated using the following extremely
       complex formula:

       @code
       return (whio_udb_hash_t) (obj ? *((TYPENAME const *)obj) : 0)
       @endcode

       That is, the numeric values are their own hashcode. The
       hashcode value 0 is reserved for use as an error code, and
       should not be used in this context.

       These functions all ignore their len parameter.

       Do not bother searching for a variant of this API which takes a
       real (size_t) pointer - there isn't one. They cannot be used
       portably for this purpose because they have indeterminate
       sizes. That means storing on one machine and loading on another
       might have different results.
       
       @see whio_udb_keycmp_ptr_NUMERIC_TYPE()
    */
    whio_udb_hash_t whio_udb_hash_ptr_NUMERIC_TYPE( void const * obj, whio_size_t len );    

    /** Short-lived helper macro to declare whio_udb_keycmp_ptr_NUMERIC_TYPE(). */
#define KEYCMP(Suffix)                                                  \
    /** See whio_udb_keycmp_ptr_NUMERIC_TYPE(). */                               \
    int whio_udb_keycmp_ptr_##Suffix( void const * lhs, void const * rhs, size_t len )
    /** Short-lived helper macro to declare whio_udb_hash_ptr_NUMERIC_TYPE(). */
#define HASHFUNC(Suffix)                                                \
    /** See whio_udb_hash_ptr_NUMERIC_TYPE(). */                                 \
    whio_udb_hash_t whio_udb_hash_ptr_##Suffix( void const * obj, whio_size_t len )

    /** Short-lived interal macro to simplify declarations of whio_udb_hash_ptr_NUMERIC_TYPE() and whio_udb_keycmp_ptr_NUMERIC_TYPE() variants.*/
#define HASH_KEYCMP(T) /** Short-lived helper macro to declare whio_udb_hash_ptr_NUMERIC_TYPE(). */ HASHFUNC(T); \
    /** Short-lived helper macro to declare whio_udb_keycmp_ptr_NUMERIC_TYPE(). */ KEYCMP(T)
    HASH_KEYCMP(uint64_t);
    HASH_KEYCMP(uint32_t);
    HASH_KEYCMP(uint16_t);
    HASH_KEYCMP(uint8_t);
    HASH_KEYCMP(int64_t);
    HASH_KEYCMP(int32_t);
    HASH_KEYCMP(int16_t);
    HASH_KEYCMP(int8_t);
    HASH_KEYCMP(size_t);
#undef HASH_KEYCMP
#undef HASHFUNC
#undef KEYCMP

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* WANDERINGHORSE_NET_WHIO_UDB_H_INCLUDED */
/* end file include/wh/whio/whio_udb.h */
/* begin file include/wh/whio/whio_vlbm.h */
#if !defined(WANDERINGHORSE_NET_WHIO_VLBM_H_INCLUDED)
#define WANDERINGHORSE_NET_WHIO_VLBM_H_INCLUDED 1
/** @page page_whio_vlbm whio_vlbm API

whio_vlbm encapsulates a whio_dev-based "Variable-Length Block Manager". That is,
it acts as a pseudo-database of variable-length blocks. It does not maintain a database,
in the sense that one cannot search for blocks by a key, but only provides a repository
of blocks. It is up to the client to somehow map the blocks it doles out to lookup keys
appropriate to their application.

Author: Stephan Beal (http://wanderinghorse.net/home/stephan/

License: Public Domain

The VLBM maintains two lists: used blocks and free blocks. Each used block
may contain any amount of user-supplied data up to its defined size. Free blocks
are doled out as records are freed and new ones allocated, and the blocks list
grows on demand.

Primary features:

- Manages a list of arbitrarily-sized on-storage blocks for a client. (The client
is responsible for mapping the block IDs provided by the library to
client-specific data.)

- Database metadata is all encoded in a platform-agnostic manner,
so it will work in varying bitnesses and endianesses.

- Can use any interface-compliant whio_dev class for its back-end
storage.

- TINY memory footprint: far under 1kb of dynamically-allocated memory
for a typical use case. (This doesn't count the size of any data
buffers a client might allocate in conjunction with using the
library.)  Its API is designed to allow the client to custom-allocate
the internally-used structures, allowing for further memory use
optimizations.

- Relatively decent performance. Adding new blocks is effectively
O(1), as is accessing blocks by ID. Allocating a new block is
O(N), where N is the number of marked-as-free blocks which we have to
check before allocating a new block. Removal of blocks is O(N) with
a very small N.

- It provides several approaches to getting data into and out of a
record, including directly from/to memory, insertion/extraction via
whio_stream/whio_dev objects, and insertion/extraction using a
caller-defined callback (e.g. to send to/from a custom data
sink/source). This gives the client nearly complete control over
memory usage. It also provides random access to block data via
the whio_dev API.

- Fairly well documented. No public API members are undocumented.


Primary Misfeatures:

- Very young (born on 20101008). Only lightly tested.

- The client application is responsible for mapping the library-defined
block IDs to a separate client key, if needed. e.g. a DB-like application
might map unique DB keys to block IDs.

- No support for locking, neither threading nor storage. whio_dev
supports byte-range (inter-process) locking, but this library does not
yet use it.

- When allocating blocks from the free-block list it uses a
non-optimal-fit algorithm (in the interest of reasonable speed), and
is thus subject to suboptimal storage usage if large blocks are
allocated, deallocated, and then small blocks are allocated (since the
larger blocks may be re-used for small data). When re-allocating freed
blocks, the kernel tries to ensure that it is not waste "too much"
space, however.

- Has no "vaccuum" feature, meaning that it never truly frees up
the storage for freed blocks. They are marked as deleted but
never truly relinquished.

- Its data storage model is not optimal for tiny data amounts, e.g.
storing only numbers or very small strings (less than 50 bytes or so).
This is because each on-storage record has
(whio_vlbm_sizeof_encoded_block) bytes of metadata (ahem... overhead)
associated with it.


More than you could possibly want to know...

Storage layout:

[internal table][data blocks 1..N]

The internal bookkeeping data looks like:

[tag byte (stored for constency checking only)]
[data format version]
[freeListBlockID]
[usedListBlockID]
[EOF position]

The freeList/UsedBlockID fields are used in list management,
described below.

The data blocks are in the form:

[tag byte (stored for constency checking only)]
[id (stored for constency checking only)]
[client-specified flags]
[nextBlockID]
[prevBlockID]
[capacityInBytes]
[usedByteCount]

A VLBM manages blocks in two "chains" (doubly-linked lists), the
used-blocks and free-blocks lists. It stores only the IDs of one item
in each list (the head of the list), and from there can reach any
other in that chain. When a block is freed it is made the head of the
free-list. Allocated blocks are taken from the free-list chain (if
they are big enough to satisfy a request) or allocated at the end of
the storage on demand.
     
*/

#ifdef __cplusplus
extern "C" {
#endif
/**
   Holds the metadata associated with VLBM blocks. It does not hold
   the client data associated with each block - that is never held in
   memory by this library.

   All its members must be considered private, and they are only in
   the public API to allow client-side custom allocation (e.g. stack
   allocation) of these object.
*/
struct whio_vlbm_block
{
    /**
       Unique ID. Offset from the start of the parent storage.
       The value of 0 is reserved for "not a block."
     */
    whio_size_t id;
    /**
       Client-specified flags. This library does nothing with them
       except set them.
     */
    uint32_t clientFlags;
    /**
       ID of the previous block in this object's chain,
       or 0 for "no link."
     */
    whio_size_t prevBlock;
    /**
       ID of the next block in this object's chain,
       or 0 for "no link."
     */
    whio_size_t nextBlock;
    /**
       The length of the client data portion of the block,
       not including internal metadata.

       Changing this after block creation will likely corrupt the VLBM
       (and _certainly_ will if capacity is _increased_).
     */
    whio_size_t capacity;

    /**
       The number of bytes currently used by client-provided data.
     */
    whio_size_t usedByteCount;
};

/** Convenience typedef. */
typedef struct whio_vlbm_block whio_vlbm_block;

/**
   An empty-initialized whio_vlbm_block object.
*/
#define whio_vlbm_block_empty_m {0,0,0,0,0,0}

/**
   Equivalent to whio_vlbm_block_empty_m.
*/
extern const whio_vlbm_block whio_vlbm_block_empty;

/**
   Returns the value of WHIO_VLBM_FORMAT_VERSION which
   this library was compiled against. Different versions
   are not compatible with one-another.
 */      
uint32_t whio_vlbm_format_version();


/**
   Identifiers referring to the various VLBM-internal
   lists.
*/
enum whio_vlbm_list {
/**
   The free-block list.
*/
WHIO_VLBM_LIST_FREE = 0,
/**
   The used-block list.
*/
WHIO_VLBM_LIST_USED = 1,
/**
   A "non-list" list. These blocks are not linked to
   directly by a VLBM, and it is up to the client
   to manage any links.
 */
WHIO_VLBM_LIST_ORPHANED = 3
};
/**
   Convenience typedef.
*/
typedef enum whio_vlbm_list whio_vlbm_list;

/**
   Holds several constant values used by the VLBM API.
*/
enum whio_vlbm_misc_constants {
    /**
       The version number of the library's file format. Changes in
       this version make older files unreadable.

       The data version is based on two variables:

       - Year/month/day of the format change.
       - The size of whio_size_t
    */
    WHIO_VLBM_FORMAT_VERSION = ((101203/*YYMMDD*/<<8)|sizeof(whio_size_t))/*must be uint32_t-compatible!*/,

    /**
       On-storage size of whio_vlbm_block metadata, not counting the client-data bits.
    */
    whio_vlbm_sizeof_encoded_block =
    1 /*tag byte*/
    + whio_sizeof_encoded_size_t/*id*/
    + whio_sizeof_encoded_uint32/*clientFlags*/
    + whio_sizeof_encoded_size_t/*nextBlock*/
    + whio_sizeof_encoded_size_t/*prevBlock*/
    + whio_sizeof_encoded_size_t/*capacity*/
    + whio_sizeof_encoded_size_t/*usedByteCount*/
    ,
    /**
       On-storage size of whio_vlbm_table metadata.
    */
    whio_vlbm_sizeof_encoded_table =
    1 /*tag byte*/
    + whio_sizeof_encoded_uint32/*version*/
    + whio_sizeof_encoded_size_t/*freeList*/
    + whio_sizeof_encoded_size_t/*usedList*/
    + whio_sizeof_encoded_size_t/*clientBlock*/
    + whio_sizeof_encoded_size_t/*eofPos*/
};
    
/**
   Holds internal metadata used for managing a VLBM.

   All its members must be considered private, and they are only in
   the public API to allow client-side custom allocation (e.g. stack
   allocation) of these object (as part of a whio_vlbm object).
*/
struct whio_vlbm_table
{
    /**
       Data format version.
     */
    uint32_t version;
    /**
       ID of the first block in the free-block list.
     */
    whio_size_t freeList;
    /**
       ID of the first block in the used-block list.
     */
    whio_size_t usedList;
    /**
       ID of the "client metadata" block. That block is an optional
       area for clients to store metadata about their VLBM. e.g.  a
       hashtable implementation could use it to store internal
       metadata for a hashtable which has its data stored in other
       VLBM blocks.
     */
    whio_size_t clientBlock;
    /**
       The logical EOF position of the database. It might not match up
       identically with the real EOF, for several reasons. The db manages
       its own record of its logical EOF so that:

       a) it can play nicely with whio_dev subdevices. We don't need to use
       truncate(), for example.

       b) It does not have to write out empty block data when adding
       new blocks to the end of the file. It writes out only its block
       metadata and not the (arbitrarily large/small) area after that
       (it will be written via whio_vlbm_data_write() and friends).

    */
    whio_size_t eofPos;
};

/** Convenience typedef. */
typedef struct whio_vlbm_table whio_vlbm_table;

/**
   An empty-initialized whio_vlbm_table object.
*/
#define whio_vlbm_table_empty_m { \
        WHIO_VLBM_FORMAT_VERSION/*version*/,    \
            0/*freeList*/,\
            0/*usedList*/,\
            0/*clientBlock*/,\
            whio_vlbm_sizeof_encoded_table \
            }
/**
   Equivalent to whio_vlbm_table_empty_m.
*/
extern const whio_vlbm_table whio_vlbm_table_empty;


/**
   This class contains the management details for a given VLBM
   database. Each instance is associated with a whio_dev I/O device
   which it uses for its back-end storage.

   The internals of this class are considered private, and must not be
   relied upon by client code. They are only opaque to facilitate
   stack- or custom allocation of these objects.

   @see whio_vlbm_format()
   @see whio_vlbm_open()
*/
struct whio_vlbm
{
    /**
       Back-end storage for the database.
     */
    whio_dev * dev;
    /**
       Internal non-persistent flags.
     */
    uint8_t flags;
    /**
       whio_dev subdevice for bounding record data reads and writes.

       This object initialy seems like overkill, but it has a nice
       side-effect: when looping over larger blocks when streaming
       data in or out, the subdevice can help avoid problems in
       positioning of the parent device if that device is used from
       other subdevices which themselves manage other parts of that
       parent device. For example, a whio_vlbm hosted in whio_epfs
       pseudofile, which is itself hosted in a larger whio_dev
       instance. Read/write ops via the subdevice will re-place
       the cursor where it needs to be.

       That said, except for the above-described cases, the fence only
       serves to provide a bit of seek() overhead which we otherwise
       would not have.
    */
    whio_dev * fence;

    /**
       Internal stamp to simplify certain memory management issues.
       This is used as a flag to tell whio_vlbm_close() whether or not
       it should deallocate the VLBM instance. We could probably do this
       via the flags member, instead of having an extra field for it,
       but this seems less problematic in the long term.
     */
    void const * allocStamp;

    /**
       The persistent DB metadata. It is regularly flushed to storage
       as blocks are de/re/allocated.
    */
    whio_vlbm_table table;
};

/**
   Convenience typedef.
*/
typedef struct whio_vlbm whio_vlbm;

/**
   Empty-initialized whio_vlbm object.
*/
#define whio_vlbm_empty_m {                     \
        NULL/*dev*/,                            \
            0/*flags*/,                         \
            NULL/*fence*/,                      \
            NULL/*allocStamp*/,                 \
            whio_vlbm_table_empty_m \
            }
/**
   Equivalent to whio_vlbm_empty_m.
*/
extern const whio_vlbm whio_vlbm_empty;

/**
   A callback function type used by whio_vlbm_foreach_block().

   Its arguments are:

   - bm is the VLBM being visited.

   - whichList identifies which list of blocks being visited.
   
   - bl is the block being visited.

   - clientData is the last argument passed to whio_vlbm_foreach_block().
   Its meaning is client-dependent.

   If the callback returns non-0 then for-each loop stops and returns
   that value to the caller for whio_vlbm_foreach_block().
   
   See whio_vlbm_foreach_block() for important details.
*/
typedef int (*whio_vlbm_foreach_block_f)( whio_vlbm * bm,
                                          whio_vlbm_list whichList,
                                          whio_vlbm_block const * bl,
                                          void * clientData );

/**

Visits a list of blocks in bm, the exact set of which is restricted by
the value of the 'which' parameter, and calls a callback for each one.

The 'which' parameter specifies which blocks are traversed:

- WHIO_VLBM_LIST_FREE = only the free-list blocks.

- WHIO_VLBM_LIST_USED = only the used blocks.

Note that orphaned blocks are not traversible, as the VLBM has no
direct way of finding them.

For each visited block, callback(bm, block, clientData) is called. If
that function returns non-0 then looping stops and that code is
returned to the caller of this function.

On success 0 is returned and an arbitrary number of blocks (possibly
0) are travered. On error non-zero is returned. Any error codes
returned from this library will be one of the whio_rc codes, so
clients are encouraged to use their own error codes from the callback
function if they need to know whether for-each was aborted because of
a library-level error or callback-level error.

The order the blocks are traversed is unspecified. The contents of
unused blocks is unspecified, except that their id and length values
will be valid.

Do not modify bm while looping, or undefined results may occur.

This is an O(N) operation, plus whatever time the callback function
takes.
*/
int whio_vlbm_foreach_block( whio_vlbm * bm, whio_vlbm_list which,
                             whio_vlbm_foreach_block_f callback, void * clientData );
    
/**
   Allocates a whio_vlbm on the heap, initializes its memory with internal
   defaults, and returns it. Returns NULL on allocation error.
*/
whio_vlbm * whio_vlbm_alloc();
/**
    Like whio_vlbm_alloc(), but allocates allocates the new block on
    the given list. None of the pointer arguments may be NULL.  toList
    must be one of WHIO_VLBM_LIST_USED or WHIO_VLBM_LIST_ORPHANED, or
    whio_rc.ArgError is returned.

    Returns 0 on success, and populates dest as documented for
    whio_vlbm_block_alloc().

    The primary difference between this and
    whio_vlbm_block_add_new_to() is that the latter function
    unconditionally allocates a new block, whereas this one will try
    to re-use free blocks.
*/
int whio_vlbm_block_alloc_to( whio_vlbm * bm, whio_size_t blockSize,
                              whio_vlbm_block * dest, whio_vlbm_list toList  );

/**
   Frees an object which was allocated with whio_vlbm_alloc().
*/
void whio_vlbm_free( whio_vlbm * bm );

/**
   "Formats" the given parent as a VLBM table (destroying any existing
   contents), initializes a whio_vlbm object to manage its state, and
   optionally transfers ownership of the parent device to the new
   object.

   tgt must be a pointer to NULL or a pointer to an empty-initialized
   whio_vlbm object (e.g. stack-allocated). If it is a pointer to NULL
   then this function allocates a new object on the heap, otherwise
   the caller is assumed to have allocated it himself
   (e.g. stack-allocated or using malloc() or a custom allocator).

   parent must be a pointer to an opened, valid whio_dev object. If
   parent reports itself as read-only then formatting will fail. This
   function will effectively destroy the contents of the parent
   device! If parent's I/O mode is indeterminate (its iomode() member
   returns WHIO_MODE_UNKNOWN) then this function optimistically assumes
   read-write mode but will fail on writes if the underlying device
   cannot write (which will show up as a whio_rc.IOError).

   If takeDeviceOnSuccess is true then on success, ownership of parent is
   transfered to the new VLBM, otherwise ownership is not changed.  If
   takeDeviceOnSuccess is true then parent will be closed when
   whio_vlbm_close() is passed the resulting VLBM object.

   Use whio_vlbm_open() to open a previously-formatted VLBM.
   
   IN NO CASE is it legal to close the device before VLBM has been
   closed. It is also illegal to modify the VLBM via the storage
   device's API, and doing so will almost certainly corrupt it. Reads
   via the parent's API in a separate thread will also likely lead to
   corruption. In short: the VLBM owns the parent device for the
   VLBM's lifetime, and parent must neither be used (read NOR written)
   by other code during that time.

   On success 0 is returned and:

   - tgt is initialized and ready for further operations.

   - The caller must eventually call whio_vlbm_close() to close the
   VLBM and free its internal resources. If the VLBM owns the parent
   device, it will clean that up, too. If it does not, the caller must
   free the parent device using either parent->api->close(parent) or
   parent->api->finalize(parent), depending on how it was allocated
   (see the docs for the function used to open the parent device).

   On error non-zero is returned and:

   - If this function allocated the VLBM then it is deallocated.

   - Ownership of parent never changes on error, regardless of the
   value of takeDeviceOnSuccess.

   Example:

   @code
   whio_dev * dev = whio_dev_for_filename("my.vlbm","w+");
   if( ! dev ) { ... error ... }
   whio_vlbm * bm = NULL;
   int rc = whio_vlbm_format( &bm, dev, true );
   if( 0 != rc ) { ... error ... }

   ... use bm ...

   whio_vlbm_close( bm ); // Also closes dev.
   @endcode

   If you want to avoid dynamically allocating the bm object, you
   can use a stack-allocated one like this:

   @code
   whio_vlbm BM = whio_vlbm_empty;
   whio_vlbm * bm = &BM;
   int rc = whio_vlbm_format( &bm, dev, true );
   ...
   whio_vlbm_close( bm );
   @endcode

   Note that bm internally manages a small amount of
   dynamically-allocated memory, so it DOES need to be closed even if
   it is "allocated" using a stack-based object. (We say
   "stack-based", but the object could be allocated via an arbitrary
   mechanism.)
   
   @see whio_vlbm_open()
*/
int whio_vlbm_format( whio_vlbm ** tgt, whio_dev * parent, bool takeDeviceOnSuccess );

/**
   Opens an previously-formatted VLBM. The arguments and their
   semantics are identical to those of whio_vlbm_format(), so see that
   function for the full details.

   The only functional (as it were) difference is that this function
   will fail if parent was not previously formatted as a VLBM.

   @code
   whio_dev * dev = whio_dev_for_filename("my.vlbm","r+");
   if( ! dev ) { ... error ... }
   whio_vlbm * bm = NULL;
   int rc = whio_vlbm_open( &bm, dev, true );
   if( 0 != rc ) { ... error ... }

   ... use bm ...

   whio_vlbm_close( bm ); // Also closes dev.
   @endcode

   @see whio_vlbm_format()

*/
int whio_vlbm_open( whio_vlbm ** tgt, whio_dev * parent, bool takeDeviceOnSuccess );

/**
   Closes bm, which must have been opened using either whio_vlbm_open() or
   whio_vlbm_format(). If bm was allocated by this library then this function
   also frees it, otherwise this function cleans up any internals owned by bm,
   clears its state, and does not deallocate bm.

   Returns 0 on success, non-zero on error. The only error case is
   when !bm.
*/
int whio_vlbm_close( whio_vlbm * bm );

/**
   Returns true if bm is not null and its storage reports itself as
   not being in read-only mode. Indeterminate modes are optimistically
   reported as write-capable.
*/
bool whio_vlbm_is_rw( whio_vlbm const * bm );

/**
   Returns the ID of bl, or 0 if !bl or if bl is not populated
   (i.e. was not read from a VLBM). The block ID 0 is reserved
   for "not a block" or "invalid block".
*/
whio_size_t whio_vlbm_block_id( whio_vlbm_block const * bl );

/**
   Returns the capacity of the given block's data area, or 0 if !bl.
*/
whio_size_t whio_vlbm_block_capacity(whio_vlbm_block const * bl);

/**
   Returns the currently used number of bytes in given block's data area, or 0 if !bl.
*/
whio_size_t whio_vlbm_block_length(whio_vlbm_block const * bl);

/**
  Sets bl's "used length" but does not flush the changes to storage
  (use whio_vlbm_block_write() for that). Returns 0 on success or:

  - invalid arguments: whio_rc.ArgError

  - whio_vlbm_block_id(bl) is 0 or or newLen is greater than
  whio_vlbm_block_capacity(bl): whio_rc.RangeError

  This function is not normally necessary but is provided so that
  clients using the whio_vlbm_block_dev_open() API can re-set the
  "used length" if they need to.
*/
int whio_vlbm_block_length_set(whio_vlbm * bm, whio_vlbm_block * bl, whio_size_t newLen);

/**
   Reads the given block ID from storage and populates dest with its
   metadata contents (not client data).

   Returns 0 on success and a non-zero whio_rc value on error.
*/
int whio_vlbm_block_read( whio_vlbm * bm, whio_size_t id, whio_vlbm_block * dest );

/**
   If bl has a left-hand neighbor then that node is read and stored in
   the given block object. If bl has no left-hand neighbor then the
   dest object is overwritten with an empty state.

   Returns 0 on success and a non-zero whio_rc value on error.

   On success dest holds the new state, and its ID will be 0 if
   bl had no neighbor.

   @see whio_vlbm_block_read_right()
*/
int whio_vlbm_block_read_left( whio_vlbm * bm, whio_vlbm_block const * bl, whio_vlbm_block * dest );

/**
   Identical to whio_vlbm_block_read_left(), but reads the right-hand
   block.

   @see whio_vlbm_block_read_left()
*/
int whio_vlbm_block_read_right( whio_vlbm * bm, whio_vlbm_block const * bl, whio_vlbm_block * right );

/**
    Writes bl, which must be a fully-populated block, to bm.

    This writes only the metadata associated with bl, and not
    its client data.

    It is important that clients not fiddle with bl's data members in
    a way which make them semantically illegal, else the VLBM is
    like to be corrupted by this operation.
    
    Calling this is only necessary if a client changes the logical
    length of the block's contents via whio_vlbm_block_length_set(),
    or makes a similar change to the block metadata.

    Returns 0 on success.
*/
int whio_vlbm_block_write( whio_vlbm * bm, whio_vlbm_block const * bl  );

/**
   Fills the data area of the given block with zeroes. Does not change
   metadata associated with the block, such as its in-use length.

   Returns 0 on success, non-zero on nerror.

   As a special case, this function is a no-op for length-zero blocks.
*/
int whio_vlbm_block_wipe( whio_vlbm * bm, whio_vlbm_block const * bl  );

/** @internal

   Unlinks bl, which must be a properly populated object, from its
   neighbors, if any. If bl is the head of either the free-list or
   used-list then the appropriate list is also updated.

   It flushes the block and neighboring nodes, if any, to storage.

   This operation effectively orphans the block, meaning that the VMBL
   no longer has a way of finding the block again. Thus the caller
   should either remember its ID for later reference or should call
   whio_vlbm_block_free() to put the block in the free-list.
   
   Returns 0 on success.
*/
int whio_vlbm_block_unlink( whio_vlbm * bm, whio_vlbm_block * bl );
    
/**
   Sets the client-defined flags for bl to the given set. These flags
   are stored along with the block, but this library applies no
   meaning to them. They are solely for client use.

   This function does not write the change to storage - use
   whio_vlbm_block_write() for that.

   @see whio_vlbm_block_flags()
*/
int whio_vlbm_block_flags_set(whio_vlbm_block * bl, uint32_t flags );

/**
   Gets the client-defined flags associated with the given block, or 0
   if !block (or if it has no flags).

   @see whio_vlbm_block_flags_set()
*/
uint32_t whio_vlbm_block_flags(whio_vlbm_block const * bl );
    
/**
   Reads the client data associated with src, copying it into dest.
   bl must be a fully-populated block (populated via
   whio_vlbm_block_open() or equivalent). The block's contents are
   streamed from storage to dest, and dest must be at least n bytes
   long. pos specifies a starting offset within the data. If (pos+n)
   are larger than the block's capacity, whio_rc.RangeError is
   returned.

   On success n bytes are copied to dest and 0 is returned. On error,
   non-zero is returned and dest might be partially populated - its
   contents are undefined.
*/
int whio_vlbm_data_read_n_at( whio_vlbm * bm, whio_vlbm_block const * bl, void * dest,
                              whio_size_t n, whio_size_t pos );
/**
   Equivalent to whio_vlbm_data_read_n_at( bm, bl, dest, n, 0 ).
 */
int whio_vlbm_data_read_n( whio_vlbm * bm, whio_vlbm_block const * bl, void * dest, whio_size_t n );

/**
   Equivalent to whio_vlbm_data_read_n_at( bm, bl, dest, whio_vlbm_block_length(bl), 0 ),
 */
int whio_vlbm_data_read( whio_vlbm * bm, whio_vlbm_block const * bl, void * dest );

/**
   Writes n bytes from src to bl's storage.

   src must be at least n bytes of valid memory and n must be less
   than or equal to whio_vlbm_block_capacity(bl).

   Returns 0 on success, non-zero on error. A whio_rc.RangeError
   indicates that n is too large. whio_rc.ArgError indicates that one
   of the arguments is invalid. whio_rc.AccessError indicates that bm
   is read-only. whio_rc.IOError indicates a more serious problem,
   after which the contents of the db are not guaranteed to be
   consistent.

   If whio_vlbm_block_length(bl) is not n then bl will be updated
   with the new length and flushed to storage.
*/
int whio_vlbm_data_write( whio_vlbm * bm, whio_vlbm_block * bl, void const * src, whio_size_t n );

/**
   A callback function type used with
   whio_vlbm_data_write_callback(). This function is called to collect
   data for whio_vlbm_data_write_callback(), to populate a block's
   data area in a streaming manner.

   - dest is the destination memory.

   - n is the number of bytes which the implementation should copy to
   dest.

   - cbData is the client state data passed to
   whio_vlbm_data_write_callback().

   This function may be called an arbitrary number of times for any
   one logical VLBM write operation.
   
   On success it must return n. Any other value is treated as an error
   except for one special case:

   When processing of the record has finished the callback is called
   one time with a NULL dest pointer and an n value of 0. The client
   can use this as an indication that the end was reached and he may
   do any cleanup and whatnot.
*/
typedef whio_size_t (*whio_vlbm_data_source_f)( void * dest, whio_size_t n, void * cbData );

/**
   Populates bl's client data area by fetching n bytes from the given
   callback function.

   On success it fetches exactly n bytes from the callback (possibly
   via multiple calls to it), writes that many bytes to bl's data
   area, and returns 0. On success, bl will be modified to have the
   used-size of n.

   After sending all data to the callback, it will call the callback a
   final time with a value of 0 for the first two arguments. This is a
   signal to the callback that the data writing process is complete,
   so that it may (e.g.) clean up any private resources associated
   with the data source.
   
   On error it returns non-0. Error cases include:

    - Any pointer parameters are NULL: whio_rc.ArgError

    - n is larger than whio_vlbm_block_capacity(bl): whio_rc.RangeError

    - Any number of things can cause a whio_rc.IOError.

    Results are undefined if bl was not populated from bm. Doing so
    will likely corrupt the block chain.
*/
int whio_vlbm_data_write_callback( whio_vlbm * bm, whio_vlbm_block * bl,
                                   whio_vlbm_data_source_f cb, void * cbData,
                                   whio_size_t n );


/**
   A callback for whio_vlbm_data_write_callback(). It requires that cbData be a
   live whio_dev input device, which is used to fetch the record data.
*/
whio_size_t whio_vlbm_data_write_dev_cb( void *dest, whio_size_t n, void * cbData );

/**
   Equivalent to:

   @code
   whio_vlbm_data_write_callback( bm, bl, whio_vlbm_data_write_dev_cb, n, inputStream );
   @endcode
*/
int whio_vlbm_data_write_dev( whio_vlbm * bm, whio_vlbm_block * bl,
                              whio_dev * inputStream, whio_size_t n );


/**
   A callback for whio_vlbm_data_write_callback(). It requires that
   cbData be a live whio_stream input device, which is used to fetch
   the record data.

   Example:

   @code
   whio_vlbm_data_write_callback( bm, block, whio_vlbm_data_write_stream_cb, n, anInputStream );
   @endcode
*/
whio_size_t whio_vlbm_data_write_stream_cb( void *dest, whio_size_t n, void * cbData );

/**
   Equivalent to:

   @code
   whio_vlbm_data_write_callback( bm, bl, whio_vlbm_data_write_stream_cb, n, inputStream );
   @endcode
*/
int whio_vlbm_data_write_stream( whio_vlbm * bm, whio_vlbm_block * bl,
                                 whio_stream * inputStream, whio_size_t n );

/**
   A callback function type used with whio_vlbm_data_read_callback().

   The arguments are:

   - src is a read()-style pointer from which the callback should read n bytes.

   - n is the number of bytes the caller may consume from src.

   - cbData is the client-supplied state data passed to whio_vlbm_data_read_callback().

   On success it must return n. The callback may be called an arbitrary number of times
   during a single execution of whio_vlbm_data_read_callback().

   On the final call to this function, src will be NULL and n will be
   0. See whio_vlbm_data_read_callback() for other important details
   regarding the "final call" to the callback.
*/
typedef whio_size_t (*whio_vlbm_data_sink_f)( void const * src, whio_size_t n, void * cbData );

/**
   Reads the data area of bl and sends the bytes to the client-supplied callback.

   - bm: the VLBM to operate on.

   - A fully-populated VLBM block

   - The callback to call for each group of data bytes (which may be
   (<=n) bytes long).

   - cbData is arbitrary state data to pass to the callback. It may be NULL.

   - n is the maximum number of bytes to read from bl. n must be (<=whio_vlbm_block_capacity()).

   This function may iterate over the block data (if it is too large
   for a single pass) and may call the callback an arbitrary number of
   times. When it is done copying the data it will call the callback
   once more with a NULL buffer pointer and an n value of 0, which the
   callback can optionally use to do any final processing
   (e.g. cleaning up an input source or flushing a destination
   stream).
*/
int whio_vlbm_data_read_callback( whio_vlbm * bm, whio_vlbm_block const * bl,
                                  whio_vlbm_data_sink_f cb, void * cbData,
                                  whio_size_t n );

/**
   A callback for whio_vlbm_data_read_callback(). It requires that
   cbData be a live whio_stream output device, which is used as the
   destination for the fetched record data.

   Example:

   @code
   whio_vlbm_data_read_callback( bm, block, whio_vlbm_data_read_stream_cb, n, anOutputStream );
   @endcode
*/
whio_size_t whio_vlbm_data_read_stream_cb( void const *dest, whio_size_t n, void * cbData );

/**
   Equivalent to:

   @code
   whio_vlbm_data_read_callback( bm, bl, whio_vlbm_data_read_stream_cb, n, outputStream );
   @endcode
*/
int whio_vlbm_data_read_stream( whio_vlbm * bm, whio_vlbm_block const * bl,
                                whio_stream * outputStream, whio_size_t n );

/**
   Equivalent to:

   @code
   whio_vlbm_data_read_callback( bm, bl, whio_vlbm_data_read_dev_cb, n, outputDev );
   @endcode
*/
int whio_vlbm_data_read_dev( whio_vlbm * bm, whio_vlbm_block const * bl,
                             whio_dev * outputDev, whio_size_t n );


/**
   A callback for whio_vlbm_data_read_callback(). It requires that
   cbData be a live whio_dev output device, which is used as the
   destination for the fetched record data.
*/
whio_size_t whio_vlbm_data_read_dev_cb( void const *dest, whio_size_t n, void * cbData );
    
/**
   This adds a new block capable of holding blockSize bytes of client
   data.

   If markAsUsed is true then the block is added to the used-block
   chain, otherwise it is added to the free-block chain (for future
   potential use).

   On success 0 is returned and dest is populated with the block's
   info. On error non-zero is returned and dest is not modified. On
   error, other state of the table _might_ be modified, depending on
   how late the error happened. A worst-case error is corruption of
   one of the block chains.

   A blockSize of 0 is legal but fairly useless. It might be useful as
   a marker-block of some sort, but i can't really see much of a use
   for it.

   This is essentially an O(1) operation, requiring 0-1 reads and 2-3 writes.
*/
int whio_vlbm_block_add_new( whio_vlbm * bm, whio_size_t blockSize,
                             whio_vlbm_block * dest, bool markAsUsed );

/**
   This is a lower-level form of whio_vlbm_block_add_new() which adds a
   new block of the specified size to the internal list specified by
   the whichList parameter. whichList must be one of:

   - WHIO_VLBM_LIST_FREE adds the new block to the free-block list.

   - WHIO_VLBM_LIST_USED adds the new block to the used-block list.

   - WHIO_VLBM_LIST_ORPHANED adds the block to NO list, effectively
   orphaning it. This block will not be accessible later unless the
   client records the ID which gets written to the dest parameter, so
   the client will need to store it somewhere for later
   reference. Calling whio_vlbm_block_free() will "de-orphan" the
   block, moving it to the free-list.

   @see whio_vlbm_block_add_new()
*/
int whio_vlbm_block_add_new_to( whio_vlbm * bm, whio_size_t blockSize,
                                whio_vlbm_block * dest, whio_vlbm_list whichList );


/**
   Finds an unused block with enough space for the given blockSize, or
   allocates a new one (as per whio_vlbm_block_add_new()), and
   populates dest with its data.

   On success 0 is returned, else a non-zero value from the whio_rc
   object. On error dest is not modified but bm _might_ be in an
   undefined state (depending on how far along the error happened).

   This does not allocate any memory, only storage space (unless the
   storage space is an expanding in-memory device).

   A blockSize of 0 is legal, but has no real use other than as
   client-internal markers. However, there is a down-side: a 0-byte
   block which gets deallocated (moved to the free-list) can never
   be re-used (except for other 0-byte requests) and will essentially
   bloat the internal free-list.

   Before allocating a new block the VLBM will search the list of free
   blocks (an O(N) operation, where N is a function of the number free
   blocks), looking for a block which "fits". The meaning of "fits" is
   fairly vague, however. Instead of taking the first free block big
   enough to hold blockSize bytes, it tries to figure out if the size
   makes sense. For example, it will not re-use a 100-byte block for a
   2-byte blockSize, but it might re-use that block for an 80-byte
   request. For relatively small block sizes (some internal hard-coded
   value with an unspecified (small) value), it is "more lenient." 
   e.g. it would recycle a 15-byte block for a 2-byte request,
   depspite the block being 7.5 times larger than the request needs.
   If the free-block list is empty then this request is essentially
   O(1), writing only the new block and updating the head of the
   used-blocks list.
 */       
int whio_vlbm_block_alloc( whio_vlbm * bm, whio_size_t blockSize, whio_vlbm_block * dest );
    
/**
    Moves bl, which must be a fully-populated block object, to the
    free-block list.

    Note that this is the only way to make the VLBM internally aware
    of "orphaned" blocks, and freeing orphaned blocks makes them
    available for future use (but they cannot be re-orphaned).

    Freeing an already-free block is logically a no-op but it does
    have side-effects - the block is moved to the start of the
    free-blocks list.
    
    This is an O(N) with a fairly small N:

    - 1-3 block metadata reads, 1-4 block metadata writes. Best case
    is 0 block reads and 1 block write, but only in one special case
    (when bl is the only block in the whole VLBM).

    - 1 write to the VLBM metadata table.

    All of these writes are small, and the overhead of having to do the
    writes in the first place overwhelms the overhead of the actual
    amount of data written.

    This does not free any RAM memory, nor does it reduce that storage
    size of the VLBM. The block is simply marked as free for future
    re-use.
*/
int whio_vlbm_block_free( whio_vlbm * bm, whio_vlbm_block * bl );

/**
   Returns the on-storage size of bm (in bytes) or 0 if !bm. Results
   are undefined if bm is not fully initialized (i.e. not opened).

   It is possible for bm's storage to be larger than bm itself
   (e.g. if bm is living inside a fixed-size in-memory device), and
   the value returned here is the size of bm's data, as opposed to the
   size of its storage device. It is actually also possible for the
   storage device to be smaller than bm, but only in one case: when a
   new block is added, its data-area is not immediately allocated on
   disk, and it will not be used until another block is allocated or
   data is written to this block. Thus, after adding a block, the
   physical storage might be smaller than the logical size of bm.
*/
whio_size_t whio_vlbm_storage_size( whio_vlbm const * bm );

/**
   Creates a whio_dev device which proxies the given block ID.

   tgt may not be null and must point to NULL or an uninitialized
   pointer. On success this function assigns *tgt to the new device,
   which is owned by the caller and MUST be closed by the caller
   BEFORE bm is closed (by calling whio_dev_finalize(theDevice)).

   On error *tgt is not modified and non-zero is returned (one of the
   whio_rc codes).

   All reads from and writes to the device will operate on the byte
   range associated with the block. The device is a "subdevice", and
   has a few I/O limitations as described for
   whio_dev_subdev_create(). (Namely, its truncate() member will not
   function.)
   
   The device will continue to function if its data block is moved
   between the VLBM-internal lists (e.g. it is freed or allocated),
   since its position on storage does not change. The proxy device
   does not access the block state - it only accesses the "data part"
   of the block (the part where client data is stored).
   
   CAVEATS:

   - The returned device is owned by the caller and MUST be finalized
   BEFORE bm is closed. Use whio_dev_finalize(theDevice). Failing to
   do so leads to undefined behaviour.

   - This function cannot open a zero-length block, and will return
   whio_rc.RangeError if an attempt is made. (This is not an arbitrary
   decision, but a limitation of the subdevice implementation.)
   
   - Each block has a byte capacity and a current length. When writing
   data to the block using the returned i/o device, the current length
   state is not changed. Likewise, there is no way to fetch the "used
   length" of the block using this approach. Thus this approach is
   only usable when clients are using up the whole block contents or
   they have a way within their stored data to know what is real data
   and what is leftover capacity (which might be filled with garbage
   from previous writes). whio_vlbm_block_length_set() can be used to
   explicitly set the used length.

   OTHER POINTS OF INTEREST:

   - This API does not use the whio_dev::client part of the device -
   it can be used by the caller as specified in the whio_client_data
   API docs (but it is not expected that this will be necessary for
   client applications).

   - The returned device has the same read/write mode as bm itself
   has.
 */
int whio_vlbm_block_dev_open( whio_vlbm * bm, whio_size_t blockID, whio_dev ** tgt );

/**
   This function "re-opens" a device which was opened using
   whio_vlbm_block_dev_open() (and has undefined results if dev is a
   subdevice from another source). The main purpose is to recycle a
   device opened by whio_vlbm_block_dev_open(), as opposed to re-allocating
   new devices in, e.g. a looping context.

   The blockID parameter specifies which block of bm which will be proxied
   by dev.

   dev must be a valid pointer to an opened device which was
   initialized via whio_vlbm_block_dev_open().

   On success 0 is returned and dev is now a proxy for the given
   block's contents.  On error non-zero is returned and the state of
   dev retains its initial state.

   Ownership of the bm and dev parameters is not changed by this function.

   Results are undefined if dev comes from a source other than
   whio_vlbm_block_dev_open().
   
*/
int whio_vlbm_block_dev_reopen( whio_vlbm * bm, whio_size_t blockID, whio_dev * dev );

/**
   Reads the so-called "client metadata block" and stores its information
   in dest. dest should be an empty-initialized block, and whio_vlbm_block_client_write()
   must have been previously called (not necessarily during this session)
   to set up the block.

   On success it returns 0 and updates dest's state to contain the block
   information. Returns non-0 on error. Error conditions include:

   - !bm or !dest: whio_rc.ArgError;

   - No client block has been initialized for this VLBM:
   whio_rc.NotFoundError

   The underlying read operations might also produce a whio_rc.IOError
   or whio_rc.ConsistencyError.

   On error, the state of the dest block is undefined: it might be
   partially populated, fully populated, or untouched, depending on
   where the error occurred.
   
   @see whio_vlbm_block_client_write()
*/
int whio_vlbm_block_client_read( whio_vlbm * bm, whio_vlbm_block * dest );

/**
   Sets src to be the VLBM's "client metadata block" and flushes it to
   storage. The block must have been previously allocated using one of
   the block allocation routines (otherwise results are undefined).

   After calling this, future calls to whio_vlbm_block_client_read()
   will read this block.

   The purpose of the "client block" is to give client applications a
   well-known place to store VLBM metadata for their own use. As an
   example, a hashtable implementation which uses VLBM to manage its
   blocks might store block IDs of internally-used blocks (e.g. a
   block holding the hashtable itself, and another holding sizing- and
   hashing-related metadata). Each VLBM has only one dedicated client
   block, but it can of course be used to store IDs which refer to
   other blocks which the client application reserves for its own
   use.

   If this function is called multiple times with different blocks
   (with different IDs), the VLBM's internal table is updated to
   contain the ID of the block most recently passed to this function.

   It is intended that src be an "orphaned" block (see
   whio_vlbm_block_add_new_to()). If it is not, it might get mis-used
   or mis-linked later on.
   
   Returns 0 on success. Error conditions include:

   !bm or !src: whio_rc.ArgError

   !src->id: whio_rc.RangeError

   The underlying write operation(s) can also generate
   whio_rc.IOError, or possibly other codes.
   
   @see whio_vlbm_block_client_read()
*/
int whio_vlbm_block_client_set( whio_vlbm * bm, whio_vlbm_block const * src );

/**
   This is a special-purpose function to give certain downstream
   initialization operations a way to keep control of the underlying
   device in the case that their own initialization fails after they
   have passed ownership of the device to their whio_vlbm. If
   whio_vlbm_format() or whio_vlbm_open() are told to not take over
   ownership of the device, then this is never necessary.

   After this call, bm is functionally useless, and whio_vlbm_close()
   should be the next (and only) function called on it.

   On success the device owned by bm has its ownership transfered to
   the caller. On error (!bm or bm has no device) NULL is returned.
*/
whio_dev * whio_vlbm_take_dev( whio_vlbm * bm );

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* WANDERINGHORSE_NET_WHIO_VLBM_H_INCLUDED */
/* end file include/wh/whio/whio_vlbm.h */
/* begin file include/wh/whio/whio_ht.h */
#if !defined(WANDERINGHORSE_NET_WHIO_HT_H_INCLUDED)
#define WANDERINGHORSE_NET_WHIO_HT_H_INCLUDED 1
/** @page page_whio_ht whio_ht API

Author: Stephan Beal (http://wanderinghorse.net/home/stephan/

License: Public Domain

whio_ht encapsulates an on-storage hashtable. It may use any
full-featured whio_dev implementation as storage.

Primary features:

- An on-storage hashtable of records with variable-length keys
and values. The client supplies the hashtable size and
hashing routines, and default hashing implementations are
provided for strings and generic binary data.

- Can use any whio_dev storage device as its back-end. (The storage
does not require a working truncate() operation, so it will work with
whio_dev subdevices as well.)

- Memory-light. Each hashtable instance requires less than 500 bytes
of dynamically-allocated memory unless exceedingly long keys are used
(more than a few hundred bytes). (It makes up for its frugal memory
usage by taking up a converse amount of storage.) If "really large"
keys are used it may have to allocate a buffer for the key
comparisons, in which case the memory usage is proportional to the
largest key which the hashtable compares against during its lifetime.

- Well-documented.

- Performant. Insertion, search, and removal are all O(1).  Caveat:
for insertion operations, that "1" includes an amount of overhead
propotional to the key/value lengths, since those bytes must be
written to storage. It could thus arguably be called O(N), but the
core insertion operations are O(1).

- Can operate in read-only or read-write mode.

- Pedantic levels of internal consistency/range/error checking.

- Optional locking of a client-supplied mutex.


Primary Misfeatures:

- TODO: Storage-level byte locking. At a minimum, lock the whole
container device.

- Keys must all be able to use the same hash and comparison
functions. e.g. it cannot reliably mix string and integer keys in the
same table.

- Because it does not normally internally allocate memory for keys and
values, fetching values might require a few more lines of code than
would be necessary if it allocated buffers to give to the client. It
transfers data directly between the client and storage, without any
intermediary copying, and this requires that the client first get the
record's key/value sizes, allocate a place to store them, and then ask
whio_ht to copy them to that memory. That said, writing allocating
wrappers around the core functions is easy to do.

- On storage with high seek times and no kernel- or device-level
caching, performance may suck (seek is the most common I/O operation
it performs, due to the multiple internal levels of indirection it
uses).

- Cannot actually free storage for removed items. The storage will be
marked as free/re-usable, but the size of the storage is not
reduced. Shrinking a hashtable requires creating a new one and copying
its values to a new hashtable. (And doing that requires an
iteration mechanism!)

- A poorly timed C signal (e.g. Ctrl-C from the console) during an
update of the hashtable can potentially corrupt its on-storage state.
TODO: add optional signal handler support to block signals during
write ops. In my (limited) experience, installing a SIGINT handler
causes whio_dev::write() to abort with EINTR if Ctrl-C is pressed
during a write. That leaves us in the situation of having to try to
roll back any changes made to that point. We might want to consider
making all updates in new/unmanaged blocks, and re-link them after the
"less atomic" operations are done. That, however, would lead to more
free/unused blocks that i would like to have.

*/

#ifdef __cplusplus
extern "C" {
#endif
    /**
       Type used for hash values.

       Maintenance reminder: it must be an unsigned type for internal
       reasons. If this type changes, the encoding/decoding routines
       for the hash values also need to be tweaked and
       whio_ht_sizeof_encoded_hashent also needs to be changed.
    */
    typedef whio_size_t whio_ht_hash_t;
#define WHIO_HT_HASH_T_PFMT WHIO_SIZE_T_PFMT
#define WHIO_HT_HASH_T_SFMT WHIO_SIZE_T_SFMT
    /**
       A collection of constants used by the whio_ht API.
    */
    enum whio_ht_constants {
    /**
       The version number of the library's file format. Changes in
       this version make older files unreadable.

       The data version is based on two variables:

       - Year/month/day of the format change.
       - The size of whio_size_t

       Maintenance reminders:

       - If the default hash function changes, this value needs to be
       changed.
    */
    WHIO_HT_FORMAT_VERSION =
    ((101205/*YYMMDD*/<<8)|sizeof(whio_size_t))/*must be uint32_t-compatible!*/
    ,

    /**
       On-storage size of a hashtable value.
     */
    whio_ht_sizeof_encoded_hashent =
    1 /* tag byte, for consistency checking */
    + whio_sizeof_encoded_size_t/*hashcode*/
    ,

    /**
       The maximum length of a "function set" name, not including a
       null terminator.

       Reminder to self: this is a static value mainly because of how
       whio_ht_funcset_register() works. For most other purposes we
       could have function set names of arbitrary lengths.
    */
    whio_ht_funcset_name_length = 32/*almost arbitrary!*/
    ,

    /**
       On-storage size of hashtable internal book-keeping information,
       including the function set name string, but not including the
       hashtable itself.
     */
    whio_ht_sizeof_encoded_bookkeeping_info =
    1/*tag byte*/
    + whio_sizeof_encoded_uint32 /* data format version. */
    + whio_sizeof_encoded_size_t /* Hashtable length/number of entries. */
    + whio_sizeof_encoded_size_t /* block ID of hashtable VLBM block. */
    + whio_ht_funcset_name_length /* function set name */
    + 1 /* NULL pad */
    ,

    /**
       On-storage size of the metada associated with a hashtable
       record, not including its raw key and value.
     */
    whio_ht_sizeof_encoded_record =
    1 /*tag char*/
    + whio_sizeof_encoded_size_t /*hash*/
    + whio_sizeof_encoded_size_t /*keyLen*/
    + whio_sizeof_encoded_size_t /*valueLen*/
    };

    /**
       whio_ht_key_cmp_f() is the interface whio_ht uses for
       comparing keys.

       Must compare, at most, len bytes from lhs and rhs and return
       less than 0, 0, or greater than 0 to signify that lhs is less
       than, equivalent to, or greater than rhs.  i.e. it must
       semantically behave like strncmp() and memcmp().

       Note that this is an equivalence, not identity, comparison.
       Implementations may of course check for identity to short-cut
       the check, but the whio_ht API will never (as far as i can
       tell) pass the same pointer as both args to this function.

       A value of NULL should semantically compare less than anything
       but NULL, to which it should compare equal.

       The whio_ht internals are careful not to pass len values
       which are out of range for its key length configuration.

       Note that while this function technically has memcmp()
       semantics, whio_ht is only interested in the equality value, so
       implementations are not required to perform strict ordering.
       That is, whio_ht treats negative (less than) and positive
       (greater than) values equivalently, and treats 0 as a match.
       
       Maintenance reminder: the third argument is of type size_t,
       instead of whio_size_t, so that we can use memcmp() as an
       implementation. i despise size_t because it has an unspecified
       size and there is no portable printf()/scanf() specifier for
       it. That causes my printf code which uses size_t to throw all
       kinds of compile warnings when switching between 32- and 64-bit
       platforms.
    */
    typedef int (*whio_ht_key_cmp_f)( void const * lhs, void const * rhs, size_t len );

    /**
       whio_ht_key_hash_f() is the interface whio_ht instances use
       for hashing their keys.
    
       Must produce a non-zero hash value for (at most) len bytes from
       obj. The value 0 is reserved as an error code. If the hash
       would indeed be 0, it must return some other constant value.

       How it produces the hash is unimportant, but its mechanism must
       not change after the function has been used in a given db, or
       else an old key may hash to a different value (which would
       throw off the internal hashtable).

       The whio_ht API will call implementations like
       hash_f_impl(key,lengthOfKey), and it is important that hashing
       implementation play nicely together with the given length order
       to avoid reading memory which does not belong to the key.
    */
    typedef whio_ht_hash_t (*whio_ht_key_hash_f)( void const * obj, whio_size_t len );

    /**
       A whio_ht_key_hash_f() implementation which creates a hash
       using some unspecified hashing algorithim on the first n bytes
       of obj.  (The aglorithm is supposedly quite good, in particular
       for strings, according to the guy i got it from.) obj MUST be
       at least n bytes long.
    */
    whio_ht_hash_t whio_ht_hash_default( void const * obj, whio_size_t n );

    /**
       A whio_ht_key_hash_f() implementation which creates a hash
       using len bytes of str (which must of course be at least len
       bytes long). While i'm no expert on the topic, the hashing
       algorithm it uses is reported very good for "short" strings in
       particular.
    */
    whio_ht_hash_t whio_ht_hash_str( void const * str, whio_size_t len );

    /**
       A whio_ht_key_hash_f() implementation which creates a hash
       using the same algorithm as whio_ht_hash_str(), but in a
       case-insenstive manner. Thus "aaa", "AaA", and "aAa" would all
       have the same hashcode.
    */
    whio_ht_hash_t whio_ht_hash_str_nocase( void const * str, whio_size_t len );

    /**
       A whio_ht_key_cmp_f() implementation which treats s1 and s2 as
       strings (or raw binary bytes) and compares them using
       memcmp(3). It follows the whio_ht_key_cmp_f() guidelines
       regarding NULL values for s1 and s2.
    */
    int whio_ht_key_cmp_str( void const * s1, void const * s2, size_t len );

    /**
       A whio_ht_key_cmp_f() implementation which treats s1 and s2 as
       strings (do not use raw binary data!) and compares them
       case-insensitively. It follows the whio_ht_key_cmp_f()
       guidelines regarding NULL values for s1 and s2.
    */
    int whio_ht_key_cmp_str_nocase( void const * s1, void const * s2, size_t len );
    
    /**
       The whio_ht_funcset encapsulates the various client-specified
       functions required by whio_ht instances.

       @see whio_ht_funcset_register()
       @see whio_ht_funcset_search()
    */
    struct whio_ht_funcset
    {
        /**
           Comparison function for db keys. See the whio_ht_key_cmp_f()
           docs for details.
        */
        whio_ht_key_cmp_f keycmp;

        /**
           A hash function for keys.
        */
        whio_ht_key_hash_f hash;
    };

    /** Convenience typedef. */
    typedef struct whio_ht_funcset whio_ht_funcset;
    /** Empty-initialized whio_ht_funcset object. */
#define whio_ht_funcset_empty_m {                  \
        NULL/*keycmp*/,NULL/*hash*/}
    /**
       whio_ht_funcset object initialized with functions suitable
       for string-like keys and data.
    */
#define whio_ht_funcset_strings_m {              \
        whio_ht_key_cmp_str/*keycmp*/,\
        whio_ht_hash_str/*hash*/}

    /**
       whio_ht_funcset object initialized with functions suitable
       for case-insensitive string-like keys and data.
    */
#define whio_ht_funcset_strings_nocase_m {              \
        whio_ht_key_cmp_str_nocase/*keycmp*/,\
        whio_ht_hash_str_nocase/*hash*/}

    /** Empty-initialized object. */
    extern const whio_ht_funcset whio_ht_funcset_empty;

    /**
       Object initialized with functions suitable
       for string-like keys and data.
    */
    extern const whio_ht_funcset whio_ht_funcset_strings;

    /**
       Object initialized with functions suitable
       for case-insensitive string-like keys and data.
    */
    extern const whio_ht_funcset whio_ht_funcset_strings;

    /**
       This class encapsulates whio_ht options which
       become inherent properties of databases created
       using these properties

       @see whio_ht_dev_format()
    */
    struct whio_ht_opt
    {
        /**
           Maximum number of entries in the db's hashtable. It should,
           for purposes of hashing, be a prime number.

           As the number of entries in the table approaches this
           number, the chance of hash collisions increases (eventually
           to 100%). That won't break the db but will hurt search and
           insertion performance.

           The number of records in the hashtable is theoretically
           bounded only by the limit of whio_size_t. That doesn't mean
           we can store that many records, but that the underlying
           storage "should" be able to grow to that size.

           Increasing the hashSize in small increments does not
           appreciably change the required size of the storage: each
           hashtable entry takes up whio_ht_sizeof_hashent bytes on
           the storage.
        */
        whio_size_t hashSize;

        /**
           An optional mutex for locking a hashtable. If its lock()
           member is non-NULL then its unlock() member must be the
           unlocking counterpart. If lock() is not NULL but unlock()
           is, results are undefined. The state member may be NULL,
           assuming the lock() and unlock() members require no
           additional state.

           The whio_ht API does not require that locks be recursive.
        */
        whio_mutex mutex;
    };

    /** Convenience typedef. */
    typedef struct whio_ht_opt whio_ht_opt;

    /** Empty-initialized whio_ht_opt object. */
#define whio_ht_opt_empty_m \
    {1987/*hashSize - default value was ALMOST ARBITRARILY CHOSEN (it is the 300th prime number)! (Why 300? THAT was arbitrary.) */, \
    whio_mutex_empty_m/*mutex*/     \
    }

    /** Empty-initialized object. */
    extern const whio_ht_opt whio_ht_opt_empty;

    /**
       A handle for a hashtable record. The internals must be
       considered private/internal, and are not to be accessed
       directly by client code. This type is not opaque so that
       client-side code can stack-allocate them.
    */
    struct whio_ht_record
    {
        /**
           The parent VLBM block.

           Reminders: the block id of a record CAN CHANGE during the
           lifetime of a record, and should not be stored for later
           reference (or one should be very careful about doing
           so). Specifically, when a record's value is replaced after
           initial insertion, the library _might_ need to create
           a new record to hold the data.
        */
        whio_vlbm_block block;
        /**
           Record's hash code.
         */
        whio_ht_hash_t hash;
        /**
           Length, in bytes, of the record's key.
        */
        whio_size_t keyLen;
        /**
           Length, in bytes, of the record's value.
         */
        whio_size_t valueLen;
    };
    /** Convenience typedef. */
    typedef struct whio_ht_record whio_ht_record;

    /** Empty-initialized whio_ht_record object. */
#define whio_ht_record_empty_m { \
whio_vlbm_block_empty_m/*block*/, \
0/*hash*/, 0/*keyLen*/, 0/*valueLen*/\
}

    /** Empty-initialized whio_ht_record object. */
    extern const whio_ht_record whio_ht_record_empty;

    /**
       whio_ht is the core data structure used by the whio_ht API. It
       encapsulates an on-storage hashtable.

       These objects are initialized via whio_ht_open() or
       whio_ht_format(), and cleaned up with whio_ht_close().
    */
    struct whio_ht
    {
        /**
           Hashtable options.
         */
        whio_ht_opt opt;
        /**
           Interal block manager.
        */
        whio_vlbm vlbm;
        struct {
            /**
               Subdevice for wrapping the hashtable block.
            */
            whio_dev * ht;
            /**
               "Transient" subdevice for fetching/setting block-level
               metadata.
            */
            whio_dev * fence;
            /**
               "Transient" subdevice for copying record metadata
               between records (for when we grow a record).
            */
            whio_dev * cloneFence;
        } devs;
        struct
        {
            /**
               VLBM block ID where the core ht metadata is stored.
            */
            whio_size_t meta;
            /**
               VLBM block ID where the internal hashtable is stored.
            */
            whio_size_t ht;
        } blockIDs;

        /**
           The set of hashing/comparison functions associated with
           the hashtable.
        */
        whio_ht_funcset funcs;

        /**
           whio_dev::iomode()-compliant value. Will mostly be
           the same as devs.parent->api->iomode(devs.parent).
        */
        whio_iomode_mask iomode;

        /**
           Internal option flags.
        */
        uint8_t flags;

        /**
           Internal stamp which lets us know whether this API
           allocated this object or not (and, correspondingly, whether
           or not this API should deallocate it).
        */
        void const * allocStamp;

        /**
           Each time a record is inserted or removed, this counter is
           changed. whio_ht_iterator uses this to try to detect
           concurrent modification of the hashtable. i say "try"
           instead of "does" because this approach will fail if the
           hashtable is modified _exactly_ (2^(sizeof(whio_size_t)))
           times between the time the iterator is initialized and the
           time the check is made. i'm going to put that in the
           category of "if that REALLY happens then Gawd wanted it to
           be so" and not consider it a bug.
        */
        whio_size_t writeMarker;
        /**
           Internal buffer used for comparing "long" keys, if
           on-storage key sizes exceed some internally-defined value
           (the size of a particular stack-allocated buffer).

           If a "rougue search" tries a really long key will cause the
           internal buffer to be held (for re-use with future keys)
           until the hashtable is closed. e.g. if you search for a
           10000000-byte key then the buffer will hang around with at
           least that much memory in it.
        */
        whio_buffer buffer;
    };

    /**
       Convenience typedef.
     */
    typedef struct whio_ht whio_ht;

    /** Empty-initialized whio_ht object. */
#define whio_ht_empty_m {                       \
        whio_ht_opt_empty_m,                    \
        whio_vlbm_empty_m,                  \
        {/*devs*/                             \
            NULL/*ht*/,                   \
            NULL/*fence*/,                     \
            NULL/*cloneFence*/                     \
        },                                        \
        {/*blockIDs*/ 0/*meta*/,0/*ht*/},   \
        whio_ht_funcset_empty_m/*funcs*/,               \
        WHIO_MODE_INVALID/*iomode*/,                  \
        0/*flags*/, \
        NULL/*allocStamp*/,        \
        0/*writeMarker*/,      \
        whio_buffer_empty_m \
    }

    /** Empty-initialized whio_ht object. */
    extern const whio_ht whio_ht_empty;

    /**
       Not yet used. Might eventually be used to consolidate
       format/open-related options into a single argument, like we do
       in whio_epfs.
    */
    struct whio_ht_open_opt
    {
        struct
        {
            whio_dev * dev;
            bool takeDevOnSuccess;
            bool enableLocking;
        } storage;
        char const * funcSetName;
    };
    
    /**
       "Formats" the given storage device for use as a whio_ht container.
       All contents of dev are irrevocably destroyed by this operation!

       None of the arguments may be null.

       (*ht) may either point to NULL or to an existing (e.g. custom-
       or stack-allocated) object. If the client allocates the object,
       he should be sure to initialize its state by copying the
       whio_ht_empty object over it. That will ensure that all of the
       internals have a clean (but not necessarily NULL) state.

       dev is the device which will hold the hashtable. On success, ht
       takes over ownership of the device. On error, the caller must
       free the device himself (normally using
       dev->api->finalize(dev)).

       The opt argument contains the hashing-related information and
       an optional mutex object. This function copies the values, so
       opt need not live longer than this function call. It is important
       that opt be initialized to contain both a valid/useful hashtable
       size (opt->hashSize).

       funcSetName is the name of the "function set" (key hash and
       comparison functions) which the hashtable will use. The name
       must be a valid built-in or client-registered function set name
       (see whio_ht_funcset_parse()). That name will be baked into the
       hashtable so that when it is opened later on, the hashtable
       knows which functions to use for hashing and comparing keys.

       On success:

       - 0 is returned.

       - *ht will point to an initialized/ready-to-use object. The
       caller must eventually clean it up using whio_ht_close(). If
       the caller passed a custom-allocated object to this function
       then he must also deallocate the ht object after calling
       whio_ht_close().

       - Ownership of dev is passed on to the ht object. The device
       will be finalized (using dev->api->finalize(dev)) when
       whio_ht_close() is called.

       - Client code must not use the parent device for any other
       purpose (not even a seek() or a flush()!) for the lifetime of
       the whio_ht object. Doing so might invalidate its cursor position
       and cause data to be mis-read or mis-written.

       The contents of the opt and funcSetName parameters are copied,
       and need not live longer than this function call.

       On error:

       - non-0 is returned.

       - Ownership of dev is not changed.
       
       - The contents of dev might be in an undefined state, depending
       on where the error happend. e.g. if dev is read-only then it will
       fail without changing dev's contents.


       Other notes:

       - opt->mutex is NOT locked by this function. If it did, we
       could end up overwriting an opened hashtable once the lock
       became available. That is basically what happens now, and
       locking the mutex does not help us avoid that possibility.
       Thus the client must enforce that concurrent access to the
       hashtable does not become possible until after formatting
       is finished.
       
       Potential TODOs:

       - Add a flag which allows caller to keep ownership of dev.

       - Check for file locking support and abort if a lock cannot be
       immediately obtained, to avoid overwriting an in-use table.

    */
    int whio_ht_format( whio_ht ** ht, whio_dev * dev,
                        whio_ht_opt const * opt, char const * funcSetName );

    /**
       Similar to whio_ht_format(), but opens a pre-formatted hashtable.

       See whio_ht_format() for the semantics of the two parameters
       and the return value.  The only difference in parameter
       semantics between this function and that one is that the
       contents of dev are not directly modified by this call.
       
       If dev is read-only, insert operations will fail (probably with
       the code whio_rc.IOError or whio_rc.AccessError, depending on
       the underlying whio_dev implementation), but read operations
       will work normally.

       Some of the error codes and their potential causes:

       - whio_rc.AllocError: could not allocate ht or some internal
       resource.

       - whio_rc.ConsistencyError: dev was not formatted by
       whio_ht_format(), was formatted by a different version,
       or is otherwise corrupt.

       - whio_rc.IOError: device could not be read.

       That list is not exhaustive. e.g. an IOError can be caused by a
       number of things, and other internal error conditions might
       bubble back to the caller. e.g. a return value of
       whio_rc.InternalError probably indicates a bug in this code or
       other underlying bits (the whio_dev implementation or
       whio_vlbm).
       
       Other notes:

       - By default a hashtable has no mutex to lock. Use
       whio_ht_open_m() if the hashtable needs a mutex during the
       opening phase.

       Potential TODOs:

       - Add a flag which allows caller to keep ownership of dev.

       - Check for file locking support and lock the table.
    */
    int whio_ht_open( whio_ht ** ht, whio_dev * dev );

    /**
       Identical to whio_ht_open(), but also takes a mutex which will
       be used as the hashtable's mutex. On success, ht will use
       the mutex for future operations which require a lock.

       mu may be NULL, in which case this function is equivalent to
       whio_ht_open().

       Returns the same as whio_ht_open(), except for the following
       additional error conditions:

       - If mu->lock is non-null then mu->unlock must also be non-null,
       else whio_rc.ArgError is returned.

       - If mu->lock(mu->state) fails then whio_rc.LockingError
       is returned.
    */
    int whio_ht_open_m( whio_ht ** ht, whio_dev * dev, whio_mutex const * mu );

    /**
       Closes the hashtable, freeing all resources associated with
       it. If ht was allocated by whio_ht_format() or whio_ht_open()
       then this function also frees ht, otherwise it is up to the
       caller to deallocate it in a manner appropriate for however he
       allocated it (e.g. if it was stack-allocated, simply let it go
       out of scope).

       The only error conditions are:

       - !ht: whio_rc.ArgError

       - locking ht's mutex fails: whio_rc.LockingError

       If ht was not opened by whio_ht_open() or whio_ht_format() (or
       equivalent) then calling this function technically invokes
       undefined behaviour (that said, it "should" be safe, but this
       function will not actually deallocate ht in that case).
    */
    int whio_ht_close( whio_ht * ht );

    /**
       Returns non-0 (true) if ht is non-NULL and appears to be
       opened.
    */
    char whio_ht_is_open( whio_ht const * ht );

    /**
       Inserts the given key and value into a new record in the
       hashtable.

       On success, 0 is returned, else non-zero.
       
       Returns whio_rc.AccessError if an identical record already
       exists. (whio_ht_remove() can be used to remove it first.)
    */
    int whio_ht_insert( whio_ht * ht,
                        void const * key, whio_size_t keyLen,
                        void const * value, whio_size_t valueLen );

    /**
       Works just like whio_ht_insert(), but if dest is not NULL then
       on success dest is populated with the record information for
       the inserted entry.
    */
    int whio_ht_insert2( whio_ht * ht,
                         void const * key, whio_size_t keyLen,
                         void const * value, whio_size_t valueLen,
                         whio_ht_record * dest );

    /**
       Not yet implemented.

       Reminder to self: replacing a value might require allocating a
       new record (if their sizes do not match), and we have to
       re-link everyone associated with the replaced block in that
       case. We _could_ re-use the same block if the new value is
       smaller, but then we open ourselves up to having arbitrarily
       large, unused gaps at the end of the value blocks, and i'm not
       too keen on that.
    */
    int whio_ht_replace( whio_ht * ht,
                         void const * key, whio_size_t keyLen,
                         void const * value, whio_size_t valueLen );

    /**
       Removes the given key from ht.

       Returns 0 on success, whio_rc.NotFoundError if the key was not
       found, or some other non-0 value for a "real" error.
    */
    int whio_ht_remove( whio_ht * ht, void const * key, whio_size_t keyLen );

    /**
       This is similar to whio_ht_remove(), but takes a record object
       instead of a search key. rec MUST have been fetched via
       whio_ht_search() (or equivalent), or results are undefined.
       The main difference between whio_ht_remove() and this function
       is that the former requires a search, whereas this one is much
       more efficient if we already have the record from a search we
       just performed. Note, however, that any writes made to the
       hashtable between the search and the call to this function
       might invalidate the record, and such a two-phase search/remove
       is not atomic vis-a-vis the hashtable's mutex.

       Returns 0 on success, non-0 on error. On success rec's internal
       state is cleared, making it invalid for use in other future
       API calls until it is re-initiailized.

     */
    int whio_ht_record_remove( whio_ht * ht, whio_ht_record * rec );

    /**
       Given a record's block ID (an internal value which is not
       guaranteed to stay constant during a record's lifetime), this
       function reads the record and populates rec with it.

       This is a very low-level function, and is only in the public
       API so that some other components of the whio library can do
       some unusually tricky things with the hashtable.

       The block id of a record should be considered volatile. It CAN
       CHANGE during the lifetime of a record, and should generally
       not be stored for later reference (or one should be very
       careful about doing so). Specifically, when a record's value is
       replaced after initial insertion, the library _might_ need to
       create a new record to hold the data. Likewise, if a record
       is removed and another record is later inserted, the new record
       _might_ recycle the old block, meaning that its contents might
       not be what the caller of this function would expect.

       In summary: normal client code should not use this function
       unless it absolutely must, and then only if it has a good
       understanding of how to abuse it properly.
       
       Returns 0 on success, non-zero on error. A return value of
       whio_rc.ConsistencyError likely means that the given block ID
       does not refer to a record.
    */
    int whio_ht_record_read_by_id( whio_ht * ht, whio_size_t blockID, whio_ht_record * rec );
    
    /**
       Searches ht for the given key.

       On success, returns 0 and the record's information is written
       to tgt. On error tgt is not modified.

       If no record is found, but there are no underlying I/O or
       hashing problems, whio_rc.NotFoundError is returned.  Any other
       error code is Bad News (e.g. whio_rc.IOError,
       whio_rc.HashingError, or whio_rc.ConsistencyError).

       tgt may be NULL, in which case this function works like
       whio_ht_contains(), but returns 0 if the item is found.
     */
    int whio_ht_search( whio_ht * ht, void const * key, whio_size_t keyLen, whio_ht_record * tgt );

    /**
       Equivalent to (0==whio_ht_search(...)). Returns true if ht and
       key are non-NULL and the given key can be found in ht.
    */
    bool whio_ht_contains( whio_ht * ht, void const * key, whio_size_t keyLen );

    /**
       Returns the length, in bytes, of the given record's key, or
       0 if !rec.
    */
    whio_size_t whio_ht_key_len( whio_ht_record const * rec );

    /**
       Returns the length, in bytes, of the given record's value, or 0
       if !rec or if it has no value.
    */
    whio_size_t whio_ht_value_len( whio_ht_record const * rec );

    /**
       Copies the value for the given record to dest.

       dest must be at least the lesser of *n or
       whio_ht_value_length(rec). If !n then dest must be at
       least whio_ht_value_length(rec) bytes long.

       On success 0 is returned, X bytes are written to dest, where X
       is the lesser of *n or whio_ht_value_length(rec), and X is
       written to *n (if n is not NULL). Note that an X value of 0 is
       legal, in which case *n is set to 0 but dest is not modified.

       On error non-0 is returned and the contents of dest are
       undefined - it may have been partially populated.

       Remember that the hashtable does not really know if its data
       are conventional strings or binary data, and it does not
       automatically null-terminate them for the caller. Clients must
       be certain to null-terminate the dest memory (and size it to
       accommodate the terminator) if they are using string data.
    */
    int whio_ht_value_get_n( whio_ht * ht, whio_ht_record const * rec,
                             void * dest, whio_size_t * n );
    /**
       Works just like whio_ht_value_get_n(), but operates on the
       'key' part of the given record instead of the 'value' part.

       See whio_ht_value_get_n() for important details about NULL
       termination (or not) of the dest pointer.
       
       @see whio_ht_value_get_n()
    */
    int whio_ht_key_get_n( whio_ht * ht, whio_ht_record const * rec,
                           void * dest, whio_size_t * n );
    /**
       Equivalent to whio_ht_value_get_n(ht,rec,dest,NULL).
    */
    int whio_ht_value_get( whio_ht * ht, whio_ht_record const * rec, void * dest );

    /**
       Equivalent to whio_ht_key_get_n(ht,rec,dest,NULL).
    */
    int whio_ht_key_get( whio_ht * ht, whio_ht_record const * rec, void * dest );

    /**
       Replaces the value part of the given record, which MUST have
       been initialized via a call to whio_ht_search().

       Return 0 on success, non-0 on error.
       
       If the new value is longer than the original record's storage
       capacity then a new block is allocated, the original record is
       removed, and rec is updated to contain the new state.
    */
    int whio_ht_value_set( whio_ht * ht, whio_ht_record * rec,
                           void const * value, whio_size_t valueLen );

    
    /**
       A combination of whio_ht_key_get() and whio_ht_value_get()
       which dynamically allocates space for the key and value.

       Neither of ht nor rec nor key nor val may be NULL.

       This function allocates enough memory to store at least
       whio_ht_key_len(rec) bytes (plus a padding NULL, for sanity's
       sake). Likewise, this function allocates anough space to store
       at least whio_ht_value_len(rec) (plus a NULL) bytes of a value.

       On success:

       - Zero is returned.

       - Ownership of *key and *val are passed to the caller. The
       caller must eventually free *key and *value by calling
       free(*key). The value is allocated as part of the same
       allocation, and is freed by the call to free(key).

       - If keyLen is not NULL then *keyLen is set to the size of
       the key data pointed to by *key.

       - If valLen is not NULL then *valLen is set to the size of
       the value data pointed to by *val.

       - An empty value is returned as (*val == NULL). Empty
       (0-length) keys are not allowed by the hashtable.

       The returned buffers are always NULL-terminated by this
       function, to help simplify usage with string data.
       
       On error non-zero is returned and:

       - *key is not modified

       - *val is not modified

       - All internally-allocated memory is freed.

       On error, the following MIGHT apply, depending on how
       early on the error happened:
       
       - If keyLen is not NULL then *keyLen is set to the record
       key's size.

       - If valLen is not NULL then *valLen is set to the record
       value's size.

       These will be set unless the error was caused by invalid
       arguments being passed to this function (in that case this
       function does not have enough information to set them).


       FIXME: allow NULL for either key or val, to allow selective
       fetching of either one. The main problem problem with this is
       that is complicates freeing the value (the caller as to be sure
       to free either key (if key or both are non-NULL) or val (if key
       was NULL).
    */
    int whio_ht_kv_get_alloc( whio_ht * ht, whio_ht_record const * rec,
                              void ** key, whio_size_t * keyLen,
                              void ** val, whio_size_t * valLen );

    
    /**
       Returns a function set registered via whio_ht_funcs_register(),
       or NULL if no set is found with the given name, if !n, or
       if strlen(n) is larger than whio_ht_funcset_name_length.

       See whio_ht_funcs_register() for the list of pre-defined
       function set names.

       @see whio_ht_funcs_register()
       @see whio_ht_funcs_parse()
    */
    whio_ht_funcset const * whio_ht_funcset_search( char const * n );
    
    /**
       whio_ht_funcs_parse() constructs a whio_ht_funcs set from a
       key which follows a simple naming convention. This function
       includes the functionality of whio_ht_funcs_search(), but also
       allows one to create certain combinations of sets on the fly.
       Explicitly registered function sets take precedence over
       "constructed" sets, and this function always prefers a
       registered set over constructing one on its own.

       key must be either:

       - A string usable by whio_ht_funcs_search() (i.e. the name of
       a registered function set).

       - It must have a maximum length of whio_ht_funcset_name_length,
       not including the terminating NULL.
       
       - A string in the form "KEY_TYPE". Where the valid values of
       KEY_TYPE are listed below...


       The supported key/value type tokens are:

       - "string", for C-string-like keys/values.

       - "string:nocase", like "string", but for case-insensitive
       keys.  This means searching for key "a" will also match a key
       named "A", and that you cannot insert keys which differ only in
       case (you can of course replace the first entry with a new one,
       but they cannot co-exist). This is only supported by the KEY
       field, not the VALUE field, because the db never compares value
       fields.

       - "binary", uses memcmp() for comparison and whio_ht_hash_default()
       for hashing. This also works for with case-sensitive strings.

       - "int8_t*", "int16_t*", "int32_t*", "int64_t*"

       - "uint8_t*", "uint16_t*", "uint32_t*", "uint64_t*"

       -"whio_size_t*"

       ("size_t*" is NOT supported because size_t has an unspecified size,
       making it unportable for our purposes.)
       
       Note that all of these strings are case- and
       whitespace-sensitive.

       Example: "int16_t*" represents a function set for hashing and
       comparing (int16_t*) keys.
       
       On success 0 is returned and tgt is modified to contain the values
       appropriate for the given description.

       On error non-0 is returned and tgt is not modified.

       If either key or tgt are NULL, or !*key, whio_rc.ArgError is
       returned.

       The various error codes one can expect:

       - whio_rc.ArgError: either (!key, !*key, or !tgt).

       - whio_rc.RangeError: key is longer than
       whio_ht_funcset_name_length.

       - whio_rc.NotFoundError: key parameter could not be mapped to a
       known function set (see the list above).

       This operation is effectively linear, taking up to O(R+T)
       time. R=number of slots in set registration table, T=number
       known type tokens listed above.
       
       @see whio_ht_funcs_register()
       @see whio_ht_funcs_search()
    */
    int whio_ht_funcset_parse( char const * key, whio_ht_funcset * tgt );

    /**
       Registers a whio_ht_funcs collection with a specific name, such
       that whio_ht_funcs_search() or whio_ht_funcs_parse() will
       return a copy of that object.

       The library only has internal space for a static number of
       entries, but the interface guarantees that at least 20 will be
       available for client use. The library does not use this
       registration table for its own purposes (it uses
       whio_ht_funcs_parse() instead), so all slots are free for
       client use and any registered entries are guaranteed to have
       come from client code.

       This routine is not thread-safe and should only be used as
       early in the application as possibly (ideally early on in
       main(), but for single-threaded apps it doesn't matter).

       On success (all parameters are in order and there is enough
       space to fill the request), f is copied to the internal table.

       Returns 0 on success. The error conditions and return values
       include:

       - Any arguments are null or f->keycmp or f->hash are NULL: whio_rc.ArgError

       - n is longer than whio_ht_funcset_name_length: whio_rc.RangeError

       - An entry is already registered with that name: whio_rc.AccessError
       
       - The internal table is full: whio_rc.DeviceFullError

       The function whio_ht_funcs_parse() is related, but can
       "create" function sets using a formatted name string. For set
       names which it can parse, whio_ht_funcs_register() need not be
       used.

       @see whio_ht_funcs_search()
       @see whio_ht_funcs_parse()
    */
    int whio_ht_funcset_register( char const * name, whio_ht_funcset const * f );

    /**
       Returns the data format version. Different versions are not
       compatible with one-another.
    */
    uint32_t whio_ht_format_version();

    /**
       Returns the hash code for keyLen bytes of the given key, using
       ht's specified hashing function.

       If ht or key are NULL, or keyLen is 0, then 0 is returned, but
       0 is also a legal hashcode, so it is not generically possible
       to know (without checking the arguments before or after calling
       this) if a return value of 0 indicated an error in the arguments.
    */
    whio_ht_hash_t whio_ht_hash( whio_ht * ht, void const * key, whio_size_t keyLen );
    
    /**
       An iterator type for use in iterating over whio_ht entries.

       Use whio_ht_iterator_begin() to initialize an interator,
       whio_ht_iterator_is_end() to check if it is valid, and
       whio_ht_iterator_next() to increment it. Use the 'record'
       member to fetch key/value data during iteration.

       
       
       @see 
       @see whio_ht_iterator_is_end()
       @see whio_ht_iterator_next()
    */
    struct whio_ht_iterator
    {
        /** @internal The parent hashtable. */
        whio_ht * ht;
        /** @internal

            Current index in the hashtable.

            CLIENT CODE MUST NOT MODIFY THIS, or results are
            undefined.
        */
        whio_size_t index;
        /** @internal

            Used internally to try to figure out if concurrent writes
            have been performed on the hashtable between iterator
            function calls.
        */
        whio_size_t writeMarker;
        /**
           The current record being traversed.
        */
        whio_ht_record record;
    };

    /** Convenience typedef. */
    typedef struct whio_ht_iterator whio_ht_iterator;

    /** Empty-initialized whio_ht_iterator object. */
    extern const whio_ht_iterator whio_ht_iterator_empty;

    /**
       Initializes an iterator to the first item in the hashtable.
       Returns 0 on success. On error the contents of iter are
       unspecified and iter must not be used by the client.

       Note that if it returns 0 (success), the iterator might still
       be the "end" iterator, meaning it might not point to a record
       (this happens when the hashtable is empty). ALWAYS use
       whio_ht_iterator_is_end() to check if the iterator is valid
       before using it!

       It is important to remember that iteration in this manner is
       effectively O(N+R), where N=hashtable size and R=number of
       records in the hashtable. We must traverse each entry in the
       on-storage hashtable to see if it points to a record, so this
       routine has to perform many (minimum=N) small reads.
       
       Example usage:

       @code
       whio_ht_iterator it = whio_ht_iterator_empty;
       int rc = whio_ht_iter_begin( ht, &it );
       if( rc ) ... error ...;
       while( ! whio_ht_iterator_is_end(&it) ) {
           ... use it.record to fetch key/value parts ...
           ... then advance the iterator: ...
           rc = whio_ht_iterator_next( &it );
           if( rc ) ... error ...;
           else continue;
       }
       @endcode

       Iterators have no dynamic resources and need not be cleaned up
       after use.

       Note that the order of objects fetched via iteration is
       unspecified, and they are not sorted in any manner.

       THREADING WARNINGS: concurrent insertions or removals on the
       hashtable can invalidate any opened iterators and leave them in
       a state which is no longer consistent vis-a-vis the new table
       contents. Results when using such an invalidated iterator are
       undefined. whio_ht_iterator_next() checks for this condition
       and returns whio_rc.ConcurrentModificationError if ANY inserts
       or removals have been done on the hashtable since the iterator
       was initialized. We pessimistically assume that any
       modification invalidates all iterators because we have no
       mechanism which allows us to determine whether or not the
       record was modified. We _could_ re-read the record on each
       iteration and compare it to the copy held by the iterator, but
       that seems like a bit of I/O overkill. Note that there is still
       a window of opportunity for concurrent changes between the time
       an iterator is initialized/incremented and the time the client
       uses that iterator to fetch the key/value data.


       TODO: Consider adding whio_ht_mutex_lock() and
       whio_ht_mutex_unlock(), and require that clients lock before
       iteration starts and unlock when they are done. Doh, that can't
       work without recursive-lock-capable mutexes because when they
       fetch data from the iterator, those routines will lock again.
       What do to? i don't think we can improve this significantly
       unless we build support for a specific threading API into the
       hashtable.

       @see whio_ht_iterator_is_end()
       @see whio_ht_iterator_next()
    */
    int whio_ht_iterator_begin( whio_ht * ht, whio_ht_iterator * iter );

    /**
       Returns true if iter is the "one-past-the-end" iterator for its
       hashtable, else false. As a special case, also returns true if
       !iter or if iter has not been initialized via an initial call
       to whio_ht_iterator_begin().

       @see whio_ht_iterator_begin()
       @see whio_ht_iterator_next()
    */
    bool whio_ht_iterator_is_end( whio_ht_iterator const * iter );

    /**
       Advances iter, which must have been initialized using
       whio_ht_iterator_begin(), to the next entry in the hashtable.

       On success 0 is returned and whio_ht_iterator_is_end() should be
       called to see if iter has reached the end of the hashtable.

       To help avoid mis-behaviour caused by changes made to the
       hashtable during the iteration process (e.g. by a separate
       thread), this function tries to detect if the hashtable has
       been modified since the iterator was initialized. If it has
       been then this function returns
       whio_rc.ConcurrentModificationError.
       
       @see whio_ht_iterator_begin()
       @see whio_ht_iterator_is_end()
    */
    int whio_ht_iterator_next( whio_ht_iterator * iter );
    
    /**
       A highly special-case/low-level variant of
       whio_ht_iterator_begin() which iterates only over records with
       the same hashcode (i.e. where hash collisions have
       occurred). To check if the iterator points to a valid record,
       use whio_ht_hash_iterator_is_end(). To advance the iterator to
       the next record use whio_ht_hash_iterator_next().

       DO NOT mix the "other" iterator functions with iterators
       initialized via this functiond, as doing so will lead to
       confusing results.

       Clients can use whio_ht_hash() to ht's hashcode for a given
       key.

       @see whio_ht_hash_iterator_is_end()
       @see whio_ht_hash_iterator_next()
    */
    int whio_ht_hash_iterator_begin( whio_ht * ht, whio_ht_hash_t hash, whio_ht_iterator * iter );

    /**
       Advances iter to the next record which has the same hashtable
       index as the item the iterator currently points to.

       iter is required to have been initialized via
       whio_ht_hash_iterator_begin(), and results are unpredictable if
       iter was initialized with whio_ht_iterator_begin() or
       whio_ht_iterator_next().

       After this returns, use whio_ht_hash_iterator_is_end() to
       determine if the iterator has advanced pasted the end of the
       list.

       @see whio_ht_hash_iterator_begin()
       @see whio_ht_hash_iterator_is_end()
    */
    int whio_ht_hash_iterator_next( whio_ht_iterator * iter );

    /**
       Advances an iterator initialized with
       whio_ht_hash_iterator_begin() or whio_ht_hash_iterator_next().
    
       iter is required to have been initialized using
       whio_ht_hash_iterator_begin() or whio_ht_hash_iterator_next(),
       and results are unpredictable if whio_ht_iterator_begin() or
       whio_ht_iterator_next() were used to initializer iter.

       If iter was initialized "properly" (see above) then this
       function returns true if iter has advanced past the end of the
       elements.

       As a special case, if iter is NULL or it seems to have not been
       properly initialized then true is returned. If it is properly
       initialized and there is another record which we can advance to
       with whio_ht_hash_iterator_next(), then this function returns
       false.

       @see whio_ht_hash_iterator_begin()
       @see whio_ht_hash_iterator_next()
    */
    bool whio_ht_hash_iterator_is_end( whio_ht_iterator const * iter );

    /**
       If value is true then removal operations on ht will zero-out
       the device blocks associated with the removed entry. This slows
       down removal operations but ensures that removed items are no
       longer visible when viewing the raw hashtable data (e.g. via a
       hex dump or similar). By default this option is off.

       Returns 0 on succes, and the only error condition is if ht is
       NULL.
    */
    int whio_ht_opt_set_wipe_on_remove( whio_ht * ht, bool value );
    
#if 0
    /* maybe ... */
#define whio_ht_insert_K_V_decl(K,KSize,V,VSize)                           \
    int whio_ht_insert_##K##_##V( whio_ht * ht, K const * key, V const * value )
#define whio_ht_insert_K_V_impl(K,KSize,V,VSize)                           \
    int whio_ht_insert_##K##_##V( whio_ht * ht, K const * key, V const * value ) \
    { return whio_ht_insert( ht, key, KSize, value, VSize ); }

#define whio_ht_insert_K_decl(K,KSize)                   \
    int whio_ht_insert_##K( whio_ht * ht, K const * key, void const * value, whio_size_t valueLen )
#define whio_ht_insert_K_impl(K,KSize)                   \
    int whio_ht_insert_##K( whio_ht * ht, K const * key, void const * value, whio_size_t valueLen )  \
    { return whio_ht_insert( ht, key, KSize, value, valueLen ); }
#endif

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* WANDERINGHORSE_NET_WHIO_HT_H_INCLUDED */
/* end file include/wh/whio/whio_ht.h */
/* auto-generated on Fri Aug 26 20:59:40 CEST 2011. Do not edit! */
#if !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200112L /* needed for ftello() and friends */
#endif
/* begin file include/wh/whio/whio_epfs_config.h */
#ifndef WANDERINGHORSE_NET_WHIO_EPFS_CONFIG_H_INCLUDED
#define WANDERINGHORSE_NET_WHIO_EPFS_CONFIG_H_INCLUDED
/** @file whio_epfs_config.h

This file contains the compile-time-configurable parts of whio_epfs.
*/
/** @def WHIO_EPFS_CONFIG_ENABLE_MEMPOOL

EXPERIMENTAL!

If WHIO_EPFS_CONFIG_ENABLE_MEMPOOL is a true value then the whio_epfs
class will be capable of installing an internal memory allocator.

The mempool support is not yet considered "trusted", as in
"stable". It has been seen to cause memory corruption in at
least one test.

Reminder to self: with 32-bit WHIO_SIZE_T on a 64-bit platform,
i'm seeing some buggy deallocation in whio_epfs_close(), which
causes an endless loop.
*/
#define WHIO_EPFS_CONFIG_ENABLE_MEMPOOL 0

/** @def WHIO_EPFS_CONFIG_MEMPOOL_BLOCKSIZE
@internal

WHIO_EPFS_CONFIG_MEMPOOL_BLOCKSIZE only applies if
WHIO_EPFS_CONFIG_ENABLE_MEMPOOL is set to true. It defines the memory
block size used by the allocator.

Some numbers to keep in mind:

- Internally, EPFS typically allocates far more whio_epfs_block
objects than all other allocations combined. They're very small (6
bytes on my setup), and they're (re)allocated in arrays, so we can
pack several of them into a mid-sized memory block (about 24-48
bytes). A block chain (allocated as an array, realloced as needed)
will always have at least as many blocks as is necessary to hold its
inode's data. In the general case, smaller EFS block size == more
whio_epfs_blocks needed in memory at one time.

- We allocate only 1 whio_epfs_inode for any given opened inode ID. If
a given ID is opened multiple times, we still only allocate one inode
(and its associated block chain is only loaded once). However...

- We allocate 1 whio_epfs_handle every time any inode ID is opened (contrast
with inode allocations).

- A larger memory block size inherently means fewer entries can be
allocated, so a relatively large size (48+ bytes) is not recommended.

- For growing block chains via re-allocation, the allocator may
temporarily need two copies (if it cannot expand the memory in-place). Thus
the pool always needs some slack space.

Tips for testing OOM conditions:

- First, to use OOM-capable code you must disable the failoverOnOOM
option in the EPFS memory pool. (If using the standard allocators, it is
very, very unlikely that you'll ever seen OOM error.)

- Use a small (e.g. 1200-byte) memory pool on an EFS with 256-byte
blocks, open an inode device and truncate() it to, e.g. 1MB. That will
end up trying to load a block chain of at least (1MB/256B=4000)
entries of sizeof(whio_epfs_block) each.
*/
#define WHIO_EPFS_CONFIG_MEMPOOL_BLOCKSIZE (sizeof(whio_epfs_inode))

/** @def WHIO_EPFS_CONFIG_AUTO_FLUSH_HINTS

    Experimental.

    This will probably go away. i am not sure if it might be needed
    for some future changes.

    If WHIO_EPFS_CONFIG_AUTO_FLUSH_HINTS is a true value
    then certain inode and block operations which update
    internal FS hints will try to write such changes to
    the FS.
*/
#define WHIO_EPFS_CONFIG_AUTO_FLUSH_HINTS 0

/** @def WHIO_EPFS_CONFIG_ENABLE_STORAGE_LOCKING

If WHIO_EPFS_CONFIG_ENABLE_STORAGE_LOCKING is set to a true value then
the library is compiled with some interal support for byte-range
locking of its back-end storage device. It relies on the whio_dev_lock()
API (and friends).

Caveats:

- Locking support is far from complete. Do not rely on it.

- Just because it's enabled at compile-time doesn't mean that it will
actually be used.

- Locking may or may not be implemented for any given back-end storage
device. Only file-based storage supports these operations at all (if
they're compile-time configured for it).
*/
#define WHIO_EPFS_CONFIG_ENABLE_STORAGE_LOCKING ((WHIO_CONFIG_USE_FCNTL) ? 1 : 0)

/** @def WHIO_EPFS_ID_T_BITS

WHIO_EPFS_ID_T_BITS defines the number of bits in an
whio_epfs_id_t object. It must be a multiple of 8, >=16, and
<=WHIO_SIZE_T_BITS.

Changing this value makes this copy of whio_epfs incompatible
with copies using a different value.

In general, an EFS may not have more than 2^WHIO_EPFS_ID_T_BITS
inodes or blocks. The "real" limit is probably a few ticks
lower than that.

A value of 16 is a good compromise, allowing an EFS to contain up to
64k blocks and/or inodes (which is far larger than its envisioned
usages call for) while shaving a few bytes of memory compared to
32-bit IDs.

Changing this number changes the EFS signature.
*/
#define WHIO_EPFS_ID_T_BITS 16

/** @def WHIO_EPFS_CONFIG_LABEL_LENGTH

    WHIO_EPFS_CONFIG_LABEL_LENGTH defines the number of bytes to
    reserve in the EFS for the label field.

    Changing this number changes the EFS signature.
*/
#define WHIO_EPFS_CONFIG_LABEL_LENGTH 64

/**
   WHIO_CONFIG_ENABLE_MMAP is HIGHLY EXPERIMENTAL! DO NOT USE!

   In my basic tests mmap() is giving us no performance at all, and in
   fact costs us a small handful of seek()s, _unless_ we enable async
   mode. When async mmap mode is enabled, it's _much_ faster (about
   2.5x in my over-simplified tests) IF the whio_epfs internals do
   "extra" (superflous) flushing of the storage.  If the internals do
   not do "extraneous" flushes then memmap provides unerwhelmingly
   little benefit (_roughly_ up to 50% in my simple tests). Possibly
   not enough to be worth the extra code.

   In read-only mode mmap() is not used because profiling showed
   it to actually cost performance (apparenly due to duplicate
   copying of data from storage to mmap, then to us).

   This support requires an unduly large amount of code to coddle
   mmap() (largely because the size of the EFS can change), and is
   subject to removal at some point.
*/
#define WHIO_CONFIG_ENABLE_MMAP 0
#define WHIO_CONFIG_ENABLE_MMAP_ASYNC 0

#ifdef __cplusplus
extern "C" {
#endif

    /** @def WHIO_EPFS_ID_T_PFMT

        WHIO_EPFS_ID_T_PFMT is the a printf-compatible format specifier
        for whio_epfs_id_t values.
    */
    /** @def WHIO_EPFS_ID_T_SFMT

        WHIO_EPFS_ID_T_SFMT is the a scanf-compatible format specifier
        for whio_epfs_id_t values.
    */

    /** @def WHIO_EPFS_ID_T_PFMTX

    WHIO_EPFS_ID_T_PFMTX is the hexidecimal counterpart to WHIO_EPFS_ID_T_PFMT.

    @see to WHIO_EPFS_ID_T_PFMT
    */
    
    /** @def WHIO_EPFS_ID_T_SFMTX

    WHIO_EPFS_ID_T_SFMTX is the hexidecimal counterpart to WHIO_EPFS_ID_T_SFMT.

    @see to WHIO_EPFS_ID_T_PFMT
    @see to WHIO_EPFS_ID_T_SFMT
    */

    /** @typedef SOME_UNSIGNED_INTEGER_TYPE whio_epfs_id_t

        whio_epfs_id_t is a fixed-sized unsigned integer type
        whose size is WHIO_EPFS_ID_T_BITS/8 bytes.
    */
#if WHIO_EPFS_ID_T_BITS == 8
    /*
      For very, very limited filesystems. There's lots of room for
      overflows here!  Completely untested!
    */
#  define WHIO_EPFS_ID_T_PFMT PRIu8
#  define WHIO_EPFS_ID_T_PFMTX PRIx8
#  define WHIO_EPFS_ID_T_SFMT SCNu8 /*C89 does not have %hh*/
#  define WHIO_EPFS_ID_T_SFMTX SCNx8
    typedef uint8_t whio_epfs_id_t;
#elif WHIO_EPFS_ID_T_BITS == 16
    /* the most realistic value, IMO. */
#  define WHIO_EPFS_ID_T_PFMT PRIu16
#  define WHIO_EPFS_ID_T_PFMTX PRIx16
#  define WHIO_EPFS_ID_T_SFMT SCNu16
#  define WHIO_EPFS_ID_T_SFMTX SCNx16
    typedef uint16_t whio_epfs_id_t;
#elif WHIO_EPFS_ID_T_BITS == 32
#  define WHIO_EPFS_ID_T_PFMT PRIu32
#  define WHIO_EPFS_ID_T_PFMTX PRIx32
#  define WHIO_EPFS_ID_T_SFMT SCNu32
#  define WHIO_EPFS_ID_T_SFMTX SCNx32
    typedef uint32_t whio_epfs_id_t;
#elif WHIO_EPFS_ID_T_BITS == 64
#  define WHIO_EPFS_ID_T_PFMT PRIu64
#  define WHIO_EPFS_ID_T_PFMTX PRIx64
#  define WHIO_EPFS_ID_T_SFMT SCNu64
#  define WHIO_EPFS_ID_T_SFMTX SCNx64
    typedef uint64_t whio_epfs_id_t;
#else
#  error "WHIO_EPFS_ID_T_BITS must be one of: 16, 32, 64"
#endif

#if WHIO_SIZE_T_BITS < 16
#  error "whio_epfs cannot work with (WHIO_SIZE_T_BITS<16)"
#endif
#if WHIO_EPFS_ID_T_BITS > WHIO_SIZE_T_BITS
#  error "WHIO_EPFS_ID_T_BITS must be <= WHIO_SIZE_T_BITS"
#endif

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* WANDERINGHORSE_NET_WHIO_EPFS_CONFIG_H_INCLUDED */
/* end file include/wh/whio/whio_epfs_config.h */
/* begin file include/wh/whio/whio_epfs.h */
#ifndef WANDERINGHORSE_NET_WHIO_EPFS_H_INCLUDED
#define WANDERINGHORSE_NET_WHIO_EPFS_H_INCLUDED

/** @page page_whio_epfs_main whio_epfs: an embedded pseudo-filesystem

whio_epfs is an embedded filesystem (EFS) library for C. It allows
applications to embed filesystem-like devices in their applications.
It is based off of the whio API (primarily whio_dev), and supports any
underlying storage supported by whio_dev.

<b>Code status:</b> Very Beta, but based mostly off of pre-existing,
fairly well-proven code.

<b>Author:</b> Stephan Beal (http://wanderinghorse.net/home/stephan)

<b>License:</b> This code is released in the Public Domain except in
jurisdictions which do not recognize Public Domain property, in which
case it is released under the MIT license (which is about as close as
Public Domain as a license can get). The MIT license is compatible for
use with GPLd and commercial software.

<b>Primary Features:</b>

- Provides applications with access to an embedded random-access,
read-write data store. We call this an embedded filesystem, or EFS.

- The EFS can contain a number of "inodes" or "pseudofiles", which in turn
can be opened with random read/write or read/only access.

- The pseudofiles within an EFS are manipulated via the whio_dev
interface, so pseudofiles can be used everywhere where other whio_dev
objects can.

- whefs_pfs can use any back-end storage supported (or supportable) by
the whio_dev API. That includes embedding an EFS as a pseudofile
in another EFS.

- Optimized for low memory usage: normal use cases need to allocate
less than 1k of dynamic memory at runtime. Clients may provide it with
their own memory buffer, from which it will "allocate" any memory it
needs. (See whio_epfs_mempool_setup().)

- As of 20100310, the last of the most performance-significant
algorithms (finding the next free block and inode) are O(1), plus a
possible extra write or two to re-link the free-list. The library
overall now performs quite well.

- Fairly well documented.

- The EFS container file is endian/platform-neutral. Clients can store
arbitrary binary data in pseudofiles, and that data may or may not be
endian/platform-dependent.

- Very rigorous internal checking of ranges/consistency/error
conditions.

- It gets run through Valgrind regularly, to help ensure no leaks or
bogus memory access.


<b>Primary Misfeatures:</b>

- Currently no support for flock()-style locking (that is on the TODO
list). The main problem here is that we are sitting a couple levels of
abstraction above the FILE (if any) the EFS lives in.

- No multi-threading support (and it may never come). It is not legal
to use an EFS from more than one thread at a time. Accessing one EFS
in any but the absolute strictest serialized approach will eventually
lead to corruption as one thread moves the device cursor and another
one then mis-writes to that location.

- C signals (or propagated C++ exceptions via callbacks, or similar)
during write operations can potentially corrupt the contents of an
EFS.

- It does not map names to pseudofiles - only ID
numbers. Name-to-inode mapping requires lots of decisions and
trade-offs for memory vs. performance. Such features can be added
on top of it via another layer or two of indirection.

- It does not support the notion of directories/subdirectories.  Such
features can theoretically be added on top of it, however.

- An EFS can add data blocks on demand, but cannot currently be
shrunk. It needs a vaccuum-like feature.


<b>EPFS vs. whefs</b>

whio_epfs is a spin-off/refactoring of the whefs project:

    http://code.google.com/p/whefs/

The primary differences are:

- whio_epfs does not name inodes. They have only numeric IDs. It leaves
the various complications and memory-vs-performance tradeoffs
involving storage of inodes and searching of inodes by name to
higher-level implementations (like whefs).

- A whio_epfs container file has a hard-coded limit on the number of
inodes (defined by the user when the EFS is created) but the data
block count can grow as needed, as opposed to being hard-coded. The
block count can optionally be capped by the client.

- whio_epfs allows any given inode to be opened an arbitrary number of times
by an arbitrary number of readers and/or writers (whefs allows any
number of read-only opens, but only one writer).

- It is structured to allow stack allocation of most of its data, to
help client code reduce calls to malloc().


<b>Concepts Overview</b>

Here is an overview of the core concepts encapsulated by this
embedded (pseudo-)filesystem (EFS) API:

- The whio_epfs class manages a single EFS container file.

- A EFS container file (accessed via the whio_dev API) acts as
storage. It need not be a file - any random-access storage supported
by the whio_dev interface will do.

- Each EFS has a hard-coded limit on the number of pseudo-file entries
it may contain. The pseudofiles are typically called "inodes" in EFS
jargon, though that term is not 100% accurate compared to its use in
system-level filesystem drivers and whatnot.

- Each EFS entry (inode) has a numerical ID, starting at 1. Any given
inode is either "in-use" or "not in use". An in-use inode is the
equivalent of an existing file. Unused inodes represent empty slots
waiting to be used. The inode ID 0 is reserved as the not-an-inode
sentry value.

- Each inode is associated with 0 or more data blocks. All blocks are
the same size, as determined when the EFS is created (via
whio_epfs_mkfs()). Each inode records the ID of its initial data block
also records its virtual size (which may span a partial block).

- Each data block contains a few bytes of bookkeeping and up to N
bytes of user data (as defined via whio_epfs_mkfs()).

- Clients open inodes as whio_dev objects, and then access them via
the whio_dev API. Thus they can be used in any generic algorithms
written for that API, e.g. whio_dev_writef(). They can be used with
the whio_stream interface by using whio_stream_for_dev().


<b>TODOs:</b>

- Finish the whio_epfs_namer API.

- Consider re-modelling the inode table. Now that we have whio_ht, we
can make a dynamically expanding inode table, instead of a fixed-size
one, with the same average O(1) performance for reading/writing the
inode.  It would require a bit more i/o overhead, but the general
performance properties would be the same. The current approach
guarantees O(1) access whereas a hashtable would guaranty us O(1) as
long as the number if inodes is less than the hashtable size (assuming
the inodes' IDs is their hash value, which would give us an ideal
hashcode distribution), and after that it would be amortized O(1) but
sometimes a little bit slower. There would be some chicken/egg details
to work out regarding where to store such an inode table.

**/

/** @page page_whio_epfs_layout whio_epfs filesystem layout

    A whio_epfs filesystem (EFS) is contained in a so-called container
    file. The container file has the following internal layout:

    [MAGIC BYTES]
    [FS OPTIONS]
    [FS HINTS]
    [INODES TABLE]
    [BLOCKS TABLE...]

    Those sections contain:

    MAGIC BYTES: some basic sanity-checking data which allows us to
    ensure that a given file is a EFS container file.

    FS OPTIONS: see the whio_epfs_fsopt type.

    FS HINTS: some internal hints for the EFS to help optimize certain
    operations (see whio_epfs::hints).

    INODES TABLE: each inode (EFS entry) contains the following data (not necessarily
    in this order):

    - The numeric ID of the inode, staring with 1. (ID 0="not an inode")

    - Timestamp, in Unix-epoch format, of the last change to the inode.

    - The virtual size of the pseudofile, in bytes.

    - ID of the first data block, or 0 if (size==0).

    - Internal flags.

    - IDs of the next and previous free inodes (or 0 if this inode is
    used).  The next/previous free inode IDs are used for managing a
    linked list so that we can allocate new inodes to the client from
    the free-list O(1) time.

    The inodes table is whio_epfs::fsopt.inodeCount entries long, and
    each entry takes up whio_epfs_sizeof_inode bytes in the storage.

    The BLOCKS TABLE contains a list of metadata and client data. Each
    block contains:

    - The numeric ID of the block, staring with 1.
    - ID of next block in the chain
    - Internal flags.
    - Client data
    - ID of next free block (or 0 if this block is used). See the notes
    above regarding inode free-list links.

    The client-data part of each block is whio_epfs::fsopt::blockSize
    bytes long. If whio_epfs::fsopt::maxBlocks is not 0 then a EFS
    will not be allowed to expand beyond that many blocks, otherwise
    it may grow to an arbitrary number of blocks (within the numeric
    limits of whio_epfs_id_t).

    The block and inode ID 0 is reserved for "not a block" resp. "not
    an inode."

    The blocks and inodes are structured as a linked list (blocks,
    singly, and inodes, doubly). These links do not imply any sort of
    relationship between the object, except that we use it to arrange
    all "unused" objects in a list so that we can dole then out later
    on.

    Initially (just after EFS creation), all blocks/inodes are
    "unused", ready to be doled out to the client. As blocks/inodes
    are allocated to the client, the free-list link(s) is (are)
    modified to "remove" the object from the free-list. The managing
    whio_epfs object must simply know the ID of the first object in
    the free-list in order to allocate, in O(1) time, the
    object. Managing the links adds a small i/o factor to that O(1),
    but not much: at most, read/modify/write of 1 other blocks or up
    to 2 other inodes.

    Most management is done directly at the head of the list (the
    exception being inodes opened via an explicit ID, which require
    manipulation later in the chain), and the free-lists operate is
    LIFO order. The most recently "freed" object will be the next one
    allocated. This is part of what makes the list processing quite
    cheap and the lookup O(1). When the EFS is constructed, the
    initialization process goes out of its way to ensure that the
    initial list is ordered from lowest to highest record ID.
*/

/** @page page_whio_epfs_memcosts whio_epfs memory costs

     Here are some notes about the memory costs of whio_epfs, mainly
     for use in finding good values for use with
     whio_epfs_mempool_setup()...

     For typical use, where only a couple handles are opened at once
     and data block chains for the opened handles do not grow really
     long, a whio_epfs object can get by with less than half a
     kilobyte(!) of memory in use at any given time.

     An opened EFS which has not opened any handles takes up
     sizeof(whio_epfs) bytes (which is, as of this writing, smaller
     than sizeof(FILE)). They do not dynamically allocate any memory
     until they have to open a handle.

     Each opened handle costs approximately:

     - sizeof(whio_epfs_handle)

     - plus (sizeof(whio_epfs_block)*N), where N is approximately
     equal to the number of blocks owned by that handle. N may be
     larger than the current block count due to
     pre-allocation/reservation. The blocks list is not allocated
     until the blocks are actually read from or written to. Simply
     opening an inode will not allocate its block chain. There is no
     client-side mechanism to determine the number of blocks
     associated with an inode, but it can be calculated by dividing
     the inode's size by the fs' block size.

     When multiple handles are opened for the same inode:

     - One list of blocks is shared amongst them.

     - Closing the handle may not free its memory immediately - it
     cannot be destroyed until the last opened handle pointing to it
     is closed. This is a side-effect of how handle sharing is
     implemented (but i'd like to replace this model eventually).

     Using whio_epfs_dev_open() opens a handle (with the above costs)
     and allocates about sizeof(whio_dev)+(about)20 bytes for its
     implementation data.
*/

/** @page page_whio_epfs_conventions whio_epfs Conventions


<b>Naming conventions:</b>

- Types and free functions are named in lower_case_with_underscore.

- Struct member function pointers typically use lower_with_underscore,
but this is not a rule.

- Struct member non-function-pointer variables typically use
initialLowerCamelCase, but this is not a rule.

- All public API members have the name prefix "whio_epfs".

- Functions which pertain to an instance of a specific type of object
are typically named class_name_verb(), as opposed to
verb_class_name(). e.g. property_get() instead of get_property(). The
reason is because it makes searching through the API easier (and doc
tools can sort the names, thereby grouping them properly).

- Public API header files live in <wh/whio/...> and should follow the
same naming conventions as for Types. Private header files may be
named or located wherever the implementor prefers.


<b>Pointer-to-pointer parameters for functions with flexible allocation
rules:</b>

Many functions in the API which deal with object initialization allow
the caller to either provide his own memory or to allow the library to
allocate it for him. Such functions have a signature which looks
something like:

@code
int init_func( some_type **obj, ... );
@endcode

Most functions using this convention allow both of these calling options:

Client-allocated object (stack or otherwise):

@code
some_type st = { ... sane values ... };
some_type * ptr = &st;
int rc = init_func( &ptr, ... );
@endcode

In that case, such functions will assume that the st object was
empty-initialized, and will proceed to use it for futher opertations.

Eventual clean-up of the st object depends on its exact type, but it
must not be free()'d if it was created on the stack. Most of the
whio_epfs types which support such initialization provide separate API
functions for cleaning up the object's internals and for freeing the
actual object memory (freeing should not be done on stack-allocated
objects, but clean-up should).

Alternately, let the library allocate it:

@code
some_type * ptr = NULL;
int rc = init_func( &ptr, ... );
@endcode

In this case, the library will (somehow try to) allocate a some_type
object and assign *ptr to that (on success - it does not do so on
error).  The caller takes over ownership and must destroy the object
as described in the documentation for init_func().

The reasons such routines are set up this way, as opposed to simply
returning a pointer to the created resource, are:

- A core project goal is keeping memory costs low and reducing the
calls to malloc(). To this end, we structure the code to support stack
allocation whenever feasible.

- It allows us to return richer error information via the conventional
return value mechanism, as opposed to simply returning a NULL pointer
and not reporting _why_ it is NULL.

**/
#ifdef __cplusplus
extern "C" {
#endif

    /**
       An array of numbers, ending with 0, which contains version information
       about the compile-time configuration of whio_epfs. These bytes are stored
       in EFS files, and versions of whio_epfs built with one set of configuration
       options are not readable by builds configured differently.

       The list contains the following values:

       - Year part of the whio_epfs FS format version number.
       - Month part of the whio_epfs FS format version number.
       - Day part of the whio_epfs FS format version number.
       - WHIO_SIZE_T_BITS
       - WHIO_EPFS_ID_T_BITS
       - WHIO_EPFS_CONFIG_LABEL_LENGTH
       - whio_epfs_sizeof_namer_label
       - A 0 to mark the end of the list.
    */
    extern const uint16_t whio_epfs_magic_bytes[];

    /**
       whio_dev ioctls supported by whio_dev objects returned
       from whio_epfs_dev_open().
    */
    enum whio_epfs_ioctl {
    /**
       Third argument to whio_dev_ioctl() MUST be a pointer
       to a whio_epfs_id_t. The inode ID of the device is
       assigned to that pointer.
    */
    whio_epfs_ioctl_INODE_ID = whio_dev_ioctl_mask_WHIO_EPFS | 0x01,
    /**
       Third argument to whio_dev_ioctl() MUST be a pointer
       to a (whio_epfs_inode*). A pointer to the device's associated
       inode is stored in that parameter.
    */
    whio_epfs_ioctl_INODE_PTR = whio_dev_ioctl_mask_WHIO_EPFS | 0x02,
    /**
       Third argument to whio_dev_ioctl() MUST be a pointer
       to a (whio_epfs_handle*). A pointer to the device's associated
       handle is stored in that parameter.
    */
    whio_epfs_ioctl_HANDLE_PTR = whio_dev_ioctl_mask_WHIO_EPFS | 0x04
    };
    
    /**
       Various flags used by the whio_epfs API.  The flags pertaining
       to whio_epfs, whio_epfs_inode, whio_epfs_handle, and
       whio_epfs_block objects are limited to 8 bits.
    */
    enum whio_epfs_flags {
    /**
       Flags the EFS as being under the influence of mmap().
     */
    WHIO_EPFS_FLAG_FS_IS_MMAPPED = 0x01,

    /** Signifies that the flagged inode or block is in use. */
    WHIO_EPFS_FLAG_IS_USED = 0x02,

    /** Signifies that the flagged whio_epfs object
        owns its dev member. */
    WHIO_EPFS_FLAG_FS_OWNS_DEV = WHIO_EPFS_FLAG_IS_USED,

    /** Used by whio_epfs objects. We can do away with this, using the
        whio_iomodes enum instead.
     */
    WHIO_EPFS_FLAG_RW = 0x04,

    /**
       An inode flag to mark "internal" inodes.

       See whio_epfs_inode_set_internal() and
       whio_epfs_inode_is_internal().

       TODO: reconsider this. It was only added for
       namer inodes but those have the INODE_IS_NAMER
       flag.
    */
    WHIO_EPFS_FLAG_INODE_IS_INTERNAL = WHIO_EPFS_FLAG_RW,

    /**
       A special-case marker to flag an inode as having been
       allocated by a whio_epfs_namer object. It is up to the
       namer implementations to set this in their format()
       routine.
    */
    WHIO_EPFS_FLAG_INODE_IS_NAMER = 0x08,
    
    /**
       Not yet used.

       Signifies that the flagged object has changed state and needs
       to be flushed.
    */
    WHIO_EPFS_FLAG_DIRTY = 0x10,

    /**
       Not yet used.

       Signifies that the flagged object has obtained a write lock on
       the storage.

       Used by: handles
    */
    WHIO_EPFS_FLAG_HAS_LOCKW = 0x20,

    /**
       Not yet used.

       Signifies that the flagged object has obtained a read lock on
       the storage.

       Used by: handles
    */
    WHIO_EPFS_FLAG_HAS_LOCKR = 0x40,

    /**
       Convenience form of (WHIO_EPFS_FLAG_HAS_LOCKR |
       WHIO_EPFS_FLAG_HAS_LOCKW).
    */
    WHIO_EPFS_FLAG_HAS_LOCK = WHIO_EPFS_FLAG_HAS_LOCKR | WHIO_EPFS_FLAG_HAS_LOCKW,

    /**
       whio_epfs_handle objects created with
       whio_epfs_handle_alloc() get this flag
       added to whio_epfs_handle::flags so that
       whio_epfs_handle_free() knows whether or not
       it should deallocate the handle.

       TODO: get rid of this. Handles are _only_ allocated
       dynamically, so this stack-allocation hack is not needed and i
       think i'll need space for 1 more flag.
     */
    WHIO_EPFS_HANDLE_ALLOC_STAMP = 0x80

    
    };


    /**
       Metadata for an on-storage data block in a whio_epfs EFS.
    */
    struct whio_epfs_block
    {
        /**
           Block ID. These start at 1. 0 is reserved for "not a
           block".
        */
        whio_epfs_id_t id;
        /** ID of next block in this chain, or 0 for no block. */
        whio_epfs_id_t nextBlock;
        /** Used only by free blocks. Points to the next free block. */
        whio_epfs_id_t nextFree;
        /** Internal flags. */
        uint8_t flags;
    };
    /** Convenience typedef. */
    typedef struct whio_epfs_block whio_epfs_block;
    /** An empty whio_epfs_block initialization object. */
#define whio_epfs_block_empty_m {0/*id*/,0/*nextBlock*/,0/*nextFree*/,0/*flags*/}
    /** An empty whio_epfs_block initialization object. */
    extern const whio_epfs_block whio_epfs_block_empty;


    /**
       Container for managing an on-storage chain of whio_epfs_block
       objects.
    */
    struct whio_epfs_block_list
    {
        /** Array of blocks. */
        whio_epfs_block * list;
        /** The number of items allocated. */
        whio_epfs_id_t alloced;
        /** The number of items currently in use. */
        whio_epfs_id_t count;
    };
    /** Convenience typedef. */
    typedef struct whio_epfs_block_list whio_epfs_block_list;
    /** An empty whio_epfs_block_list initialization object. */
#define whio_epfs_block_list_empty_m {NULL,0,0}
    /** An empty whio_epfs_block_list initialization object. */
    extern const whio_epfs_block_list whio_epfs_block_list_empty;
    
    /**
       Metadata for an on-storage "inode" (a whio_epfs pseudofile
       entry).

       This data is all internal, not for client use. It is not
       opaque so that we can stack-allocate them.
    */
    struct whio_epfs_inode
    {
        /**
           The inode's id. These start at 1. 0 is reserved for
           "not an inode".
        */
        whio_epfs_id_t id;

        /**
           ID of the first data block associated with this inode.
           0 means no blocks.
        */
        whio_epfs_id_t firstBlock;
        /**
           The virtual size of the inode. The equivalent of
           a file size.
        */
        whio_size_t size;

        /**
           The timestamp of the last modification on the
           inode, in Unix Epoch format.

           The time zone is currently undefined (assume local), but
           consideration is being given to standardizing on gmtime.

           i could justify increasing this to uint64_t if i'd remove
           the cflags member.
        */
        uint32_t mtime;

        /**
           The number of current active open()s on this handle.  It
           must not be destroyed until this value drops to 0 (which
           happens when the last handle which references it is
           closed).
        */
        uint8_t openCount;

        /**
           Internal flags. Client code must not modify these.
        */
        uint8_t flags;

        /**
           Client-defined flags. The whio_epfs API does
           nothing with these flags - they are reserved for
           client use.
        */
        uint32_t cflags;

        /**
           Used only by free inodes, to link to the next free inode.
        */
        whio_epfs_id_t nextFree;
        /**
           Used only by free inodes, to link to the previous free inode.

           inodes must be dual-linked, unlike blocks, because the ability
           to open them directly by id confuses a single-link list and
           can cause it to have cycles.
        */
        whio_epfs_id_t prevFree;

        /**
           A cache of the block chain for this inode.
        */
        whio_epfs_block_list blocks;
    };
    /** Convenience typedef. */
    typedef struct whio_epfs_inode whio_epfs_inode;

    /** An empty whio_epfs_inode initialization object. */
#define whio_epfs_inode_empty_m {                \
        0/*id*/,                                \
            0/*firstBlock*/,      \
            0/*size*/,                          \
            0/*mtime*/,                    \
            0/*openCount*/,                         \
            0/*flags*/,                         \
            0/*cflags*/,                         \
            0/*nextFree*/,                       \
            0/*prevFree*/,                       \
            whio_epfs_block_list_empty_m         \
            }

    /** An empty whio_epfs_inode initialization object. */
    extern const whio_epfs_inode whio_epfs_inode_empty;

    struct whio_epfs;

    /**
       whio_epfs_handle represents a handle to an opened whio_epfs
       pseudofile. "Opened" essentially means "prepared for i/o
       operations."

       All members of this type should be considered private. They are
       only non-opaque so that we can allocate them on the stack.
       This type is internal to the whio_epfs API and the public API
       provides no functions which use these objects.

       Notes about how we internally use these (just in case i
       forget)...

       Each whio_epfs_handle (hereafter "handle") refers to
       a single "opened" inode. An opened inode is one on which
       we can peform i/o, accessing its internal data blocks
       via the whio_dev API.

       Write operations on a handle may cause the inode itself or its
       associated data blocks to be updated on storage.

       When a given inode is opened multiple times, each handle uses
       the same inode but have their own iomode and position cursor
       into the data bytes.

       Potential TODO:

       Remove the inode member and instead encapsulate the operations
       handles/blocks perform on inodes into a small interface. All
       required operations:

       - changing the mtime, size, and associated first block ID
       - fetching the size and first block ID
       - flushing the inode to storage
       - freeing the memory associated with the inode

       (i think that's all of them)

       Those ops would be encapsulated behind a more generic
       interface. The purpose of this would be to allow us to use
       handles/block chains independently of inodes (or the concrete
       type of the inode). The reason for THAT would be so that we can
       store the inode table inside a block chain. The goal is to
       eventually move the inode table into a whio_udb or whio_ht
       instance inside the block chain in the EPFS. Why? Because then
       we have an essentially unbounded inode count instead of a
       fixed-sized inode table, but still have amortized O(1) access
       to the inodes given their ID number (which we would use as the
       hash key in the whio_ht/whio_udb container, and would only get
       hash collisions once the number of inodes exceeds the hashtable
       size).
    */
    struct whio_epfs_handle
    {
        /**
            The inode this handle refers to. All opened handles
            which refer to the same inode point to the same
            inode handle. It is freed when the last handle
            using that inode is closed.
        */
        whio_epfs_inode * inode;

        /**

            Current pseudofile position cursor, equivalent to a file
            position cursor.

            Each handle has its own cursor.
        */
        whio_size_t cursor;

        /**
           Not yet used.

           This is the number of handles opened with write locks.
           When this reaches 0 we need to unlock our write lock
           or replace it with a read lock if (openCount>0).
        */
        uint8_t writerCount;

        /** Internal flags. */
        uint8_t flags;
        /**
           The i/o mode (RW/RO) of this object.
        */
        whio_iomode_mask iomode;

        /** The whio_epfs this object came from. */
        struct whio_epfs * fs;
    };

    /**
       Convenience typedef.
     */
    typedef struct whio_epfs_handle whio_epfs_handle;

    /** An empty whio_epfs_handle initialization object. */
#define whio_epfs_handle_empty_m {               \
        NULL/*inode*/,                           \
        0U/*cursor*/,               \
        0U/*writerCount*/,\
        0U/*flags*/, \
        WHIO_MODE_INVALID/*iomode*/,  \
        NULL/*fs*/                    \
    }

    /** An empty whio_epfs_handle initialization object. */
    extern const whio_epfs_handle whio_epfs_handle_empty;

    /**
       This structure defines the basic properties of a whio_epfs
       container. They are set with an EPFS container is created, and
       are not modified after that.
    */
    struct whio_epfs_fsopt
    {
        /**
           Maximum number of inodes a EFS can hold. It may not
           be zero.


           Reminders to self:

           The whio lib now has all the components we need to be able
           to store the inode table inside a whio_ht inside the
           EFS. That would allow us to have an essentially unbounded
           inode count. This is, with the current archecture, a
           chicken-egg scenario, however.  We need to add one internal
           layer of abstraction between whio_epfs_handle and
           whio_epfs_inode in oder to be able to do that. The
           abstraction would allow us to open handles without an
           associated inode record. All updates which block-level
           operations now make to inodes would instead operate through
           the abstraction layer. With that, we could internally open
           a handle/block chain and store the inode table there. We
           would need to store the block ID of the start of the inode
           table in the EFS-level metadata, so that we would know
           where to find the table. Or we reserve block #1 for that
           purpose. The inode table would then become a whio_ht
           containing (id-to-encoded-inode) entries. The
           for-each-inode op would become relatively expensive
           (because iterating over a whio_ht is relatively
           inefficient). Opening inodes by ID would become a search
           operation (amortized O(1)) instead of a
           jump-directly-to-the-inode-ID. Or... we don't use a whio_ht
           at all, but use whio_blockdev. That'd be much more
           efficient and probably easier to implement. Hmmm...

           Anyway...
        */
        whio_epfs_id_t inodeCount;
        /** Maximum number of blocks an EFS can hold. 0 means a limit
            bounded only by storage limits or the numeric range of
            whio_epfs_id_t.

            Reminders to self:

            In theory we can get away with changing this, in a very
            controlled manner, at runtime. We must ensure that it is
            always 0 or is greater than
            whio_epfs::hints::maxEverUsedBlock. We could use this to
            add blocks to a block-capped EFS, by bumping up the number
            (or re-setting this value to 0 ought to due the
            trick!). The next-free-block routine will create blocks as
            needed in the new/expanded/uninitialized space, so we
            needn't pad out the EFS to fill in the new blocks (but
            might want to, e.g. the (whio-epfs-mkfs --fill) option).
        */
        whio_epfs_id_t maxBlocks;
        /**
           The size of each data block in a EFS container. It should
           be a "reasonable" value, and the library may reject values
           which it deems to be "too small."  For storing small files,
           the optimal block size is probably somewhere just over the
           average size of the files being stored. For storing files
           with arbitrary sizes, having a larger block size will
           reduce runtime memory costs (since we need to manager fewer
           blocks for large files) but will waste storage space for
           small files. e.g. if the block size is 32kb and we store
           4kb in it, we're wasting (or "not yet using") 28kb of it.
           If, however, we store a file of 1MB, a 32kb block size will
           cause the library to have to allocate space for managing 32
           (=1M/32k) block records. Those records are small
           (sizeof(whio_epfs_block)) bytes), but for clients wanting
           to reduce memory allocations, a larger data block size can
           shave a few bytes off.

           Another thing to consider when picking a block size is
           whether or not a whio_epfs_namer will be used. If so, and
           if it stores its names in a pseudofile in the EFS, then
           having a too-small block size is likely to hurt the namer's
           performance notably. (Ideally, a namer's data will fit into
           a single block.)
        */
        whio_size_t blockSize;
    };
    /** Convenience typedef. */
    typedef struct whio_epfs_fsopt whio_epfs_fsopt;

    /** An empty whio_epfs_fsopt initialization object. */
#define whio_epfs_fsopt_empty_m {0,0,0}

    /** An empty whio_epfs_fsopt initialization object. */
    extern const whio_epfs_fsopt whio_epfs_fsopt_empty;

    /**
       List of array indexes used by whio_epfs::offsets and
       whio_epfs::sizes. The values are array indexes and therefore
       must start at 0 and increment by one.

       These values may change from commit to commit, but they
       are not part of the EFS container format.
    */
    enum whio_epfs_offsz {
    /** The magic bytes entry.

    fs->offsets[whio_epfs_index_magic] == offset into EFS of magic bytes.

    fs->sizes[whio_epfs_index_magic] == encoded size of magic bytes.
    */
    whio_epfs_index_magic = 0,
    /** whio_epfs_fsopt entry.

    fs->offsets[whio_epfs_index_fsopt] == offset into EFS of whio_epfs_fsopt.

    fs->sizes[whio_epfs_index_fsopt] == encoded size of whio_epfs_fsopt.
    */
    whio_epfs_index_fsopt,
    /** whio_epfs_hints entry.


    fs->offsets[whio_epfs_index_hints] == offset into EFS of internal fs hints.

    fs->sizes[whio_epfs_index_hints] == encoded size of internal fs hints.
    */
    whio_epfs_index_hints,
    /** EFS label entry.

    fs->offsets[whio_epfs_index_label] == offset into EFS of label string.

    fs->sizes[whio_epfs_index_label] == maximum encoded size of label string.
    */
    whio_epfs_index_label,
    /**
       "Namer label" space.

       fs->offsets[whio_epfs_index_namer_label] == offset into EFS of namer data.

       fs->sizes[whio_epfs_index_namer_label] == maximum encoded size of namer data.
    */
    whio_epfs_index_namer_label,
    /** Inode table entry.

    fs->offsets[whio_epfs_index_inode] == offset into EFS of inode table.

    fs->sizes[whio_epfs_index_inode] == encoded size of whio_epfs_inode.
    */
    whio_epfs_index_inode,
    /** Block table entry.

    fs->offsets[whio_epfs_index_blockMeta] == offset into EFS of blocks table.

    fs->sizes[whio_epfs_index_blockMeta] == encoded size of whio_epfs_block.
    */
    whio_epfs_index_blockMeta,
    /** MUST be the last entry in this enum and MUST be the number of items
        in this enum (minus THIS item). */
    whio_epfs_index_count
    };
    /**
       The whio_epfs_sizeof enum defines the on-storage sizes of
       various whio_epfs data structures. The only data structure
       who's size is not a compile-time constant is the size of the
       data blocks (which is defined in whio_epfs_fsopt::blockSize).
    */
    enum whio_epfs_sizeof {
        /**
            Encoded size of a whio_epfs_id_t.
        */
        whio_epfs_sizeof_id = 
#if WHIO_EPFS_ID_T_BITS == 8
    whio_sizeof_encoded_uint8
#elif WHIO_EPFS_ID_T_BITS == 16
    whio_sizeof_encoded_uint16
#elif WHIO_EPFS_ID_T_BITS == 32
    whio_sizeof_encoded_uint32
#elif WHIO_EPFS_ID_T_BITS == 64
    whio_sizeof_encoded_uint64
#else
#  error "WHIO_EPFS_ID_T_BITS must be one of: 8, 16, 32, 64"
#endif
        ,
    /**
       Encoded size of whio_epfs_magic_bytes.
    */
    whio_epfs_sizeof_magic = 1/*tag byte*/
        + (whio_sizeof_encoded_uint16 * 7/*whio_epfs_magic_bytes[0..N]*/)
        ,
    /**
       Encoded size of whio_epfs_fsopt.
    */
    whio_epfs_sizeof_fsopt = 1/*tag byte*/
        + whio_epfs_sizeof_id /* inodeCount*/
        + whio_epfs_sizeof_id /* maxBlocks*/
        + whio_sizeof_encoded_size_t /* blockSize */
        ,
    /**
       Encoded size of whio_epfs_hints.
    */
    whio_epfs_sizeof_hints = 1/*tag byte*/
        + (5 * whio_epfs_sizeof_id) /* whio_epfs::whio_epfs_hints::(
                                       maxEverUsedBlock,
                                       maxEverUsedInode,
                                       freeInodeList,
                                       freeBlockList,
                                       blockCount) */
        ,
    /**
       Encoded size of whio_epfs_inode.
    */
    whio_epfs_sizeof_inode = 1/*tag byte*/
        + whio_epfs_sizeof_id/*id*/
        + whio_sizeof_encoded_uint8/*flags*/
        + whio_epfs_sizeof_id/*nextFree*/
        + whio_epfs_sizeof_id/*prevFree*/
        + whio_epfs_sizeof_id/*firstBlock*/
        + whio_sizeof_encoded_uint32/*cflags*/
        + whio_sizeof_encoded_size_t/*size*/
        + whio_sizeof_encoded_uint32/*mtime*/
        ,
    /**
       Encoded size of whio_epfs_block. This is independent of
       whio_epfs_fsopt::blockSize.
    */
    whio_epfs_sizeof_blockMeta = 1/*tag byte*/
        + whio_epfs_sizeof_id/*id*/
        + whio_epfs_sizeof_id/*nextBlock*/
        + whio_epfs_sizeof_id/*nextFree*/
        + whio_sizeof_encoded_uint8/*flags*/
        ,

    /**
       whio_epfs_sizeof_label_payload is an alias for
       WHIO_EPFS_CONFIG_LABEL_LENGTH, provided so debugging output
       can show us a name instead of an expanded macro value.
    */
    whio_epfs_sizeof_label_payload = WHIO_EPFS_CONFIG_LABEL_LENGTH,
    /**
       This on-storage size of an EFS label. The label can be
       set by the client to arbitrary bytes.
    */
    whio_epfs_sizeof_label = 1/*tag byte*/
        + whio_epfs_sizeof_label_payload /* label bytes */
    ,
    /**
       On storage amount of space for storing a namer's
       name and its metadata.
    */
    whio_epfs_sizeof_namer_label_payload = 128/*pretty arbitrary*/,
    /**
       Defines the length of the "namer label", which is an area
       of the EFS reserved for storing:

       a) the name/id associated with a concrete whio_epfs
       implementation.

       b) Optionally a small amount of metadata for use by that
       implementation, stored directly after the namer's id.
       
     */
    whio_epfs_sizeof_namer_label = 1/*tag byte*/
        +whio_epfs_sizeof_namer_label_payload
    };

    /**
       A list of whio_epfs_handle objects.
    */
    struct whio_epfs_handle_list
    {
        /**
           The list of objects.

           Maintenance note: this list is a (**) instead of a (*),
           unlike the other list types this library uses, because of
           how handle linking works. TODO: revisit that, since handles
           are linked differently as of 20110802.
        */
        whio_epfs_handle ** list;
        /** Number of items allocated in the list. */
        whio_epfs_id_t alloced;
        /** Number of items used in the list. */
        whio_epfs_id_t count;
    };
    /** Convenience typedef. */
    typedef struct whio_epfs_handle_list whio_epfs_handle_list;
    /** An empty whio_epfs_handle_list initialization object. */
#define whio_epfs_handle_list_empty_m {        \
        NULL/*list*/,                             \
            0/*alloced*/,                       \
            0/*used*/                           \
            }
    /** An empty whio_epfs_handle_list initialization object. */
    extern const whio_epfs_handle_list whio_epfs_handle_list_empty;

    struct whio_epfs_namer;

    /**
       The non-const string type used by the whio_epfs_namer API. It
       is not simply (char *) so that whio_epfs_namer implementations
       can store, e.g., UTF16 or even binary names.

       @see whio_epfs_namer_const_string
    */
    typedef
    /*unsigned char * */
    void * whio_epfs_namer_string;
    /**
       The _const_ string type used by the whio_epfs_namer API. It is unsigned
       so that whio_epfs_namer implementations can store, e.g., UTF16
       or even binary names.

       Note that this typedef exists because (const
       whio_epfs_namer_string) is not the same as the value of this
       typedef.

       @see whio_epfs_namer_string
    */
    typedef
    /*unsigned char const * */
    void const * whio_epfs_namer_const_string;
      
      

    /**
       This is a callback function type used by
       whio_epfs_api::foreach().  Each time it is called it is passed
       the "self" namer object, the ID of an in-use/named inode, the
       binary form of the inode's name, the length of that name, and
       any client-specific data passed to whio_epfs_api::foreach().

       Returns 0 on success. If it returns non-0 then for-each looping
       stops and that code is returned to the foreach() caller.

       The name bytes are owned by the namer object and their lifetime
       is not guaranteed to surpass this function call. Thus this
       function must ignore or consume the bytes, but must not hold
       the pointer for later dereferencing.

       Remember that namers are not required to null-terminate the
       names they pass on to this callback, and clients must take care
       to null-terminate them if needed. This allowance is so that
       namers can store binary or UTF16 data directly, and handle any
       encoding/decoding themselves.

       TODO:

       Consider changing this to take a (whio_epfs_inode const *)
       instead of an inode ID. The problem with that is that namers
       don't have that information to pass on, and getting at it would
       require that they tinker with internal APIs.
    */
    typedef int (*whio_epfs_namer_foreach_callback)( struct whio_epfs_namer *,
                                                     whio_epfs_id_t inodeID,
                                                     whio_epfs_namer_const_string, whio_size_t length,
                                                     void * callbackData );

    
    /** @struct whio_epfs_namer_api
       
       An abstract interface for mapping names to inodes
       in whio_epfs objects.

       This class is not used directly by clients, but via the
       whio_epfs_namer API. This class acts as a "vtbl" of member
       functions for that class.

       As a rule, it is not legal for any members in an instance of
       this object to be NULL. If an implementation is not possible
       for a given case (e.g. foreach() isn't feasible for a given
       back-end) then the function should return
       whio_rc.UnsupportedError.

       TODOS:

       - Re-think the whole binary name allowance. It complicates
       implementations and client code. Consider allowing only
       null-terminated strings. It actually might be useful to store,
       e.g., integer names for some special cases (e.g. mapping enum
       values to pseudofiles), but the added confusion in the API
       doesn't currently seem worth it.
    */
    struct whio_epfs_namer_api
    {
        /**
           "Formats" the namer for use with a given
           EFS. This is called by the core API when
           whio_epfs_namer_format() is called.

           The arguments are:

           self: the namer object. It will have been allocated by the core API,
           but whether or not its internal/private data has been set up by this
           point is implementation-specified.

           fs: the EFS on whose behalf the namer will function.

           metadata: a relatively small amount of memory where the
           namer may optionally store information for its own use. The
           canonical example is storing an inode ID, and the
           referenced inode is used to store further namer
           information. The metadata bytes are filled with NULLs when this
           is called by the core library.

           metalen: the length, in bytes, of the metadata memory. Its
           size is derived from:

           (whio_epfs_sizeof_namer_label_payload - length_of_namer_label - 1)

           Thus it is long enough to store a few small pieces of
           information, but not everything the namer will need for
           mapping inodes to names.  The main intention is that this
           function stores an inode ID in that memory (or more than
           one, if needed), and that that inode be used for storing
           the naming information. The namer interface does not
           explicitly have an inode ID in the interface because in the
           abstract namers do not _need_ one. That is, whether or not
           a namer needs a supplemental inode is an implementation
           detail of the namer.

           If this function returns non-0 then the formatting process
           fails and the EFS does not write the metadata to the
           EFS. If it succeeds (returns 0) then the EFS writes the
           namer's label and the metadata to storage.

           The core API will never call this function for a read-only
           fs, since any writing on such an object will fail.
        */
        int (*format)( struct whio_epfs_namer * self, struct whio_epfs * fs, void * metadata, whio_size_t metalen );

        /**
           Called by the EFS core when an EFS is opened. This function
           is similar to format(), but must try to initialize the
           namer from data set up by format().

           The arguments are identical to those of format() except
           that the metadata is populated by the EFS core (from info
           stores in the EFS container) before calling this. It will
           contain any metadata stored by a previous call to format().

           If this function fails (returns non-0) then opening of the
           EFS will ignore the error and proceeds without using the
           namer. The function whio_epfs_has_namer() can be used to
           determine if the EFS has an active (loaded/opened) namer
           instance.

           Implementations "really should" support read-only EFS
           instances, and if they cannot then this function should
           return whio_rc.AccessError.
        */
        int (*open)( struct whio_epfs_namer * self, struct whio_epfs * fs, void const * metadata, whio_size_t metalen );

        /**
           Must assign len bytes from the given name as the name of
           the inode with the given id.

           If name is NULL or len is 0 then the entry's name should be
           cleared (this is used to signify that the inode is no
           longer in use). In this case, the implementation should
           not trigger an error if no such entry already exists
           (because these arguments were telling us to remove the
           entry, anyway).

           Note that the interface allows clients to use binary names,
           which means that the given name need not be
           null-terminated. If the parameter is a string, the len
           parameter should be its conventional strlen() (without
           counting the trailing NUL).

           Returns non-0 on error, but should only error if for some
           reason it cannot store the mapping. Error conditions
           include:

           - whio_rc.ArgError: Arguments are invalid, including !self
           or !id.

           - whio_rc.RangeError: i is not in range for self's
           EFS. That said, the whio_epfs API will never pass an
           invalid i value to this function (it will verify the number
           before calling it).

           - whio_rc.AccessError: a different inode already has the
           same name. The API does not allow for multiple inodes to
           have the same name. AccessError can also indicate that
           this object is read-only.
        */
        int (*set)( struct whio_epfs_namer * self, whio_epfs_id_t id, whio_epfs_namer_const_string name, whio_size_t len );

        /**
           Gets the name for the given inode ID and copies it to name,
           which must be at least *len bytes long. When using string
           keys, it is up to the client to be sure that the following
           byte is a NUL. (This is to allow us to suppoort binary
           names or encodings like UTF16.)

           None of the parameters may be null.

           Returns non-0 on error. On success it must write _up_ _to_
           *len bytes of the name to the target memory and modify *len
           to contain the actual number of bytes written to the
           target.

           If no entry is found then whio_rc.NotFoundError should be
           returned, *len should be set to 0, and *name should be set
           to a NUL byte. (These last two bits simplify certain
           client-side use cases.)

           Because a namer is not required to use null-terminated
           strings as names, the returned *len parameter must not
           count any null terminator added by the
           namer. Implementations may, if space allows, NUL-terminate
           the target bytes, but it is up to the client to ensure that
           the resulting bytes are NUL-terminated if the clients
           needs them to be.

           Error conditions include:

           - whio_rc.ArgError: Arguments are invalid, including !self,
           !id, !name, or !len

           - whio_rc.RangeError: *len is too short to store the whole
           name, or id is out of range. (The EPFS internals will never
           pass an out-of range id to this function.)

           - whio_rc.NotFoundError: no entry was found for the given
           ID. In this case, implementations must set *name=0
           and *len = 0.
        */
        int (*get)( struct whio_epfs_namer * self, whio_epfs_id_t id,
                    whio_epfs_namer_string name, whio_size_t * len );

        /**
           Searches for the given name. If found, id is assigned its
           inode value.

           If no entry can be found, implementations should:

           - Set *id to 0 (which is not a valid inode ID).
           - Return whio_rc.NotFoundError.

           Remember that implementations may use binary names, which
           means that the nameLen parameter must _not_ include a byte
           for a terminating NUL when using c-style string keys.

           Returns 0 on success.

           Error codes/conditions include:

           - whio_rc.ArgError: Arguments are invalid, including !self,
           !name, !id, or !nameLen.

           As an exception to the rule, this member may legally be
           NULL, which will cause whio_epfs_name_search() to return
           whio_rc.UnsupportedError.
        */
        int (*search)( struct whio_epfs_namer * self, whio_epfs_id_t * id,
                       whio_epfs_namer_const_string name, whio_size_t nameLen );

        /**
           For each "used" entry in the names table (that is, all
           named entries), it must call callback( self, entryID,
           entryName, nameLengthInBytes, callbackData ). If the
           callback returns non-0 then looping must stop and return
           that error code. The order of the calls is
           implementation-dependent, and need not be in sequential
           inode order, but the callback must only be called once per
           entry and only for in-use entries.

           The implementation is not required to guaranty that names
           passed to the callback have a specific lifetime. e.g.  it
           is free to re-use the same string buffer on each loop
           iteration, overwriting its contents on each run.

           If an implementation of this function is not feasible for a
           given back-end, the implementation should return
           whio_rc.UnsupportedError. That said, implementors "should"
           try really hard to provide an implementation.

           As an exception to the rule, this member may legally be
           NULL, which will cause whio_epfs_name_foreach() to return
           whio_rc.UnsupportedError.
        */
        int (*foreach)( struct whio_epfs_namer * self,
                        whio_epfs_namer_foreach_callback callback,
                        void * callbackData );
        
        /**
           Must free up all internal resources allocated for self, but
           does not free up the self object. This is the proper way to
           clean up whio_epfs_namer objects. The deallocation of the
           self object depends on how it was created.

           After calling this, the self object must not be used except
           to free it or re-initialize it for further use.

           This is not to be called by the client - whio_epfs_close()
           will call this. Calling this function while a whio_epfs is
           using it will lead to undefined results, very possibly a
           crash or memory corruption.

           Returns 0 on success.

           Error codes/conditions include:

           - whio_rc.ArgError: !self.
        */
        int (*cleanup)( struct whio_epfs_namer * self );
    };
    /** Convenience typedef. */
    typedef struct whio_epfs_namer_api whio_epfs_namer_api;

    /** @struct whio_epfs_namer

       whio_epfs_namer defines backend-generic interface
       for mapping names to inodes for whio_epfs objects.
       A whio_epfs object may have a single whio_epfs_namer
       associated with it, and that namer object is then
       responsible for mapping EPFS inode IDs to client-usable
       names.

       A whio_epfs object references inodes only by their unique ID
       (of type whio_epfs_id_t), starting with 1 and going up to the
       number baked in to the whio_epfs object when it is initially
       created or subsequently opened. The inode ID of 0 is reserved
       for "not an inode." This interface is responsible for mapping
       those IDs to names, and it provides the basic
       getting/setting/searching features required for generically
       adding them to a whio_epfs instance.

       Why not just build in names support to the core engine? Been
       there, done that, reimplemented it three times and still wasn't
       happy with the memory-vs-performance trade-offs. Thus this
       interface was split out of the core to allow us to try out
       different inode naming options without muddling up the EPFS
       internals with details like caching and hashing.

       This class is not used as-is. Instead, some external API must
       configure one of these objects, initializing its "api" member
       to a set of functions which can provide the features required
       by this API. The instance may use private/internal data, which
       is stored in the "impl" member and must eventually be cleaned
       up by calling namer->api->cleanup(namer) (which must be
       implemented to clean up the private/internal data). The core
       EFS API uses the whio_epfs_namer_reg class to register and load
       namer implementations, and those objects store the core
       information needed for a given namer implementation (e.g. its
       member function implementations).

       The namer may store its data within the parent EPFS object and
       may reserve an inode (or multiple inodes) for its own use and
       keeping the data in there. For this to be useful, the client
       must have a way of storing and reading the namer's data via via
       EFS pseudofiles (i.e., the whio_dev interface). e.g. whio_ht or
       whio_udb can be used to store the names, and can be hosted
       within a whio_epfs pseudofile. (This use case is, not
       coincidentally, the reason whio_udb and whio_ht were initially
       implemented.)

       @see whio_epfs_namer_format()
    */
    struct whio_epfs_namer
    {
        /**
           The member functions for this object.
        */
        whio_epfs_namer_api const * api;

        /**
           Implementation-specific private data, for use only by the
           concrete implementations of this instance. Any
           dynamically-allocated resources stored here should be
           cleaned up when the api->cleanup() member is called.
        */
        whio_impl_data impl;
    };
    /** Convenience typedef. */
    typedef struct whio_epfs_namer whio_epfs_namer;
    /** @def whio_epfs_namer_empty_m

        Empty initialization whio_epfs_namer object.
    */        
#define whio_epfs_namer_empty_m {NULL,whio_impl_data_empty_m}
    /** Empty initialization whio_epfs_namer object. */
    extern const whio_epfs_namer whio_epfs_namer_empty;

    /**
       A type for whio_epfs_namer allocators. Implementations must:

       - allocate a new whio_epfs_namer object, and optionally
       allocate internal memory it needs (or that can be deferred to
       the namer's initialization routine).

       - assign *n to that object

       - Returns 0 on success or non-zero on error (ideally a whio_rc
       code like whio_rc.AllocError).
    */
    typedef int (*whio_epfs_namer_factory_f)( whio_epfs_namer ** n );

    /**
       The counterpart of whio_epfs_namer_factory_f, this interface
       specifies a destructor for whio_epfs_namer instances. Implementations
       must:

       - Free n using a means complementary to the allocation from the
       matching whio_epfs_namer_factory_f implementation.

       By the time this is called, n->api->cleanup(n) will have
       already been called to free up resources used by n.
    */
    typedef void (*whio_epfs_namer_free_f)( whio_epfs_namer * n );

    /** @struct whio_epfs_namer_reg

       A type used for holding whio_epfs_namer registration
       information.  This type allows a whio_epfs to load registered
       whio_epfs_namer implementations when opening an EFS.
     */
    struct whio_epfs_namer_reg
    {
        whio_epfs_namer_api const * api;
        /**
           Allocator for new instances.
        */
        whio_epfs_namer_factory_f alloc;

        /**
           Deallocator for namer instances allocated via this object.
        */
        whio_epfs_namer_free_f free;

        /**
           Stores a unique name for a given whio_epfs_namer
           implementation.  If the label is smaller than
           whio_epfs_sizeof_namer_label_payload then it must be
           NUL-terminated, and it may optionally be followed by
           namer-specific internal data. This allows namers to store a
           few bytes of metadata within the EFS, e.g. a block number
           telling them where they keep their name mappings.
        */
        unsigned char label[whio_epfs_sizeof_namer_label_payload];
    };

    /** Convenience typedef. */
    typedef struct whio_epfs_namer_reg whio_epfs_namer_reg;
    /** Empty-initialized whio_epfs_namer_reg instance. Not all bytes of its
        label are guaranteed to be 0, but the first byte is. */
#define whio_epfs_namer_reg_empty_m { NULL/*api*/, NULL/*alloc*/, NULL/*free*/, {/*label*/0} }
    /** Empty-initialized whio_epfs_namer_reg instnace. Not all bytes of its
        label are guaranteed to be 0, but the first byte is.
    */
    extern const whio_epfs_namer_reg whio_epfs_namer_reg_empty;

    
    /** @struct whio_epfs

       whio_epfs contains the internal state data used by the
       whio_epfs API for managing an embedded pseudo-filesystem (EFS).

       The internals of this class must be considered to be
       private. The class is only non-opaque so that we can
       stack-allocate the objects or embed them in higher-level
       objects without requiring an extra allocation.

       All whio_epfs objects must be either allocated via
       whio_epfs_alloc() or must be initialized using either the
       whio_epfs_empty_m macro (for inlined static initialization) or
       whio_epfs_empty (for copy initialization). For example:

       @code
       // Stack-allocated:
       whio_epfs fs = whio_epfs_empty;

       // Dynamically allocated:
       whio_epfs * fsp = whio_epfs_alloc();

       // Inlined static initialization:
       static struct Foo_
       {
           whio_epfs fs;
       } Foo = {
           whio_epfs_empty_m
       };
       @endcode

       whio_epfs objects must be initialized using one of these
       approaches before they are used. Relying on default-initialized
       values (or memset()ing all values to 0) will lead to undefined results.

       Objects created using whio_epfs_alloc() MUST be freed using
       whio_epfs_free(), and not free(), as whio_epfs_alloc() may
       allocate using an arbitrary mechanism and may allocate
       private data for the EFS instance.
    */
    struct whio_epfs
    {
        /**
           Storage device for the EFS.
        */
        whio_dev * dev;
        /**
           Core EFS options.
         */
        whio_epfs_fsopt fsopt;
        /**
           Internal state flags.
        */
        uint8_t flags;
        /**
           File descriptor, used only for mmap() purposes (which is
           still experimental).  If dev does not report its file
           descriptor we assume mmap() is not possible and disable
           it. mmap() support is a built-time option and it is not
           known to be 100% reliable.
         */
        int fileno;
        /**
           Internal error state.

           This flag is not consistently used internally, so don't
           rely on it - use the error codes returned from functions
           instead.
           
           This flag is only used for marking error state during
           initialization and cleanup of an fs. It signals
           whio_epfs_close() to skip certain operations. It is set by
           various open/mkfs routines which detect an error early in
           the process but are far enough along that they must call
           whio_epfs_close() to clean up. Cleanup should not, however,
           do any writing in that case. If it does, e.g., a mkfs which
           fails because it couldn't get a lock might still overwrite
           part of the target file. (Been there, debugged that.)
        */
        int err;
        /** Table of on-storage sizes of internal record types. */
        whio_size_t offsets[whio_epfs_index_count];
        /** Table of on-storage offsets of internal records/tables. */
        whio_size_t sizes[whio_epfs_index_count];
        /**
           Stores the list of currently-opened handles.
        */
        whio_epfs_handle_list handles;
        /**
           Used in exactly the same way as whio_dev::client. The
           whio_epfs API does not use this data except to clean it up
           (if client.dtor is not null) when the EFS is closed.  It is
           legal for client.data to be NULL and client.dtor to be
           non-NULL. In that case, client.dtor(NULL) will be called
           when the EPFS is closed, which the client can used to
           trigger something other than a cleanup operation.
        */
        whio_client_data client;
        /**
           Internal hints for a whio_epfs object, not for use
           by client code. Some of these are persistant (stored
           in an EFS container), some are transient.
        */
        struct whio_epfs_hints
        {

            /**
               This stores the highest used inode ID.  This is simply
               a slight performance optimization so that we can abort
               certain read-the-next-inode loops earlier than we
               normally would.

               TODO: get rid of this. freeInodeList makes this
               obsolete. Removing it changes the file format, though.
             */
            whio_epfs_id_t maxEverUsedInode;
            /**
               ID of the first free block, or 0 if there are none.
             */
            whio_epfs_id_t freeInodeList;

            /**
               ID of the first free block, or 0 if there are none.

               Each block contains a member
               (whio_epfs_block::nextFree) which points to the next
               free item in the chain, or 0 if the block has no
               right-hand neighbors.
             */
            whio_epfs_id_t freeBlockList;

            /**
               The highest block ID which has been added to the EFS.
             */
            whio_epfs_id_t blockCount;

            /**
               Block counterpart of maxEverUsedInode.

               TODO: i think we can get rid of this. freeBlockList
               made this obsolete. Removing it changes
               the file format, though.
            */
            whio_epfs_id_t maxEverUsedBlock;

            /**
               An internal stamp with which we mark all
               dynamically-allocated whio_epfs objects. Not
               persistent. This is used so that some of the API
               (e.g. whio_epfs_close()) can work consistently on both
               stack- and heap-allocated whio_epfs objects.
            */
            void const * allocStamp;

            /**
               This is a best guess as to whether or not
               the fs can use locking via the whio_dev_ioctl()
               interface. It will attempt to check a lock, and if
               locking does not return whio_rc.UnsupportedError
               then we will assume locking is, in general, possible,
               else further locking attempts will be disabled.

               The library does not yet lock everything it needs to -
               only the skeleton for that support is in place.
               
               Values:

               <0 = don't know or haven't checked.

               0 = seems to not be supported.

               >0 = seems to be supported.
            */
            int8_t storageLockingMode;

            /**
               When a whio_epfs instance is initialized, it records
               its current time offset from GMT. This difference is
               then applied to inode timestamps as we "touch" them.
               This member exists because as a malloc() reduction
               optimization. On my system (Linux) gmtime() and
               gmtime_r() both allocate memory, seemingly on every
               call. With this optimization, we call gmtime() only
               once per fs instance instead of every time we touch an
               inode's timestamp (which happens on every write
               operation on that inode).

               Obviously, if the system's timezone changes after fs
               initialization, the resulting timestamps will be
               off. But that corner case is worth the reduction in
               malloc() calls this gives me :-D.
               
               Added 20110422.
            */
            int32_t gmtOffset;
        } hints;

        /**
           Details for the optional internal memory allocator.
        */
        struct whio_epfs_mempool
        {
            /** Memory reserved for use as an allocation source. */
            unsigned char * mem;
            /** Length of mem, in bytes. */
            whio_size_t size;
        } pool;
        /**
           Allocator used for de/re/allocating EFS-internal
           memory.
        */
        whio_allocator alloc;
        /** Holds the EFS' namer (if any). */
        struct whio_epfs_namer_
        {
            whio_epfs_namer * n;
            /** The underlying namer registration object. This API
                calls n->api->cleanup(n) before calling this
                reg->free(n).
            */
            whio_epfs_namer_reg reg;
        } namer;
    };
    /** Convenience typedef. */
    typedef struct whio_epfs whio_epfs;
    /** Empty whio_epfs initialization object. */
    extern const whio_epfs whio_epfs_empty;

    /** Empty whio_epfs initialization object. */
#define whio_epfs_empty_m {                      \
        0/*dev*/,                               \
            whio_epfs_fsopt_empty_m,             \
            0/*flags*/,                         \
            -1/*fileno*/,                         \
            0/*err*/,                           \
            {/*offsets*/0},                     \
            {/*sizes*/0},                       \
            whio_epfs_handle_list_empty_m, \
            whio_client_data_empty_m,\
            {/*hints*/\
                0U/*maxEverUsedInode*/,         \
                    0U/*freeInodeList*/,        \
                    0U/*freeBlockList*/,        \
                    0U/*blockCount*/,               \
                    0U/*maxEverUsedBlock*/,         \
                    NULL/*allocStamp*/,\
                    -1/*storageLockingMode*/,\
                    0/*gmtOffset*/ \
            },                 \
            {/*pool*/ \
                NULL/*mem*/,\
                0U/*size*/\
            },                                         \
            whio_allocator_empty_m, \
            {/*namer*/\
                NULL/*n*/, \
                whio_epfs_namer_reg_empty_m/*reg*/ \
            } \
         }

    /**
        Allocates a new whio_epfs object, which the caller owns. It
        may be allocated by an arbitrary mechanism and must be
        deallocated using whio_epfs_free() as opposed to free().
    */
    whio_epfs * whio_epfs_alloc();

    /**
       Deallocates an object created with whio_epfs_alloc(), but does
       not destruct internal state objects (that is done by
       whio_epfs_close()).

       If fs was not created by whio_epfs_alloc() then this function
       will empty out that fs' state, but:

       a) It won't deallocate any memory used by internal state - use
       whio_epfs_close() for that, as this function will in fact leak
       them. It will overwrite all internal state of fs to an empty
       state EXCEPT for the stamp which tells us whether whio_epfs_alloc()
       allocated the object.

       b) It will not actually free fs in that case, as it is assumed
       to have been allocated somewhere else (presumably on the stack
       or as part of another object).

       Returns 0 on success. The only error conditions are:

       - !fs (whio_rc.ArgError)
    */
    int whio_epfs_free( whio_epfs * fs );

    /**
       Associates an arbitrary piece of client data with fs.

       Either of data or dtor may be null.
       
       If dtor is not null then when fs is closed it will call the
       dtor and pass the data pointer to it. A non-null dtor and a
       null data argument doesn't normally make much sense, but it's
       not stricly illegal as long as the dtor function gracefully
       handles being passed NULL. Client code could use this to
       trigger a non-cleanup operation when the EPFS is closed.

       If client data had previously been applied to fs, it is
       replaced and it is NOT destroyed, even if it had a destructor
       set.  It is up to the caller to decide if the data being
       replaced needs to be destroyed, and to do so if necessary.

       Returns 0 on success. The only error condition is (!fs), which
       causes whio_rc.ArgError to be returned.

       This API places no value on data and dtor, and never uses the
       client data except when closing an EFS.  When closing, if the
       dtor is set then it is called (early in the closing process)
       and passed the data pointer. Because client data is destroyed
       quite early, the object is allowed, during its destruction,
       to interact with fs. For example, if the client data points
       back to an internally-used inode handle for storing app-specific
       information, it is legal to close that handle via the client-data
       dtor. However, because the client data is destroyed early in the
       process (which is done _so_ that it may legally interact with fs),
       it cannot point to any data which fs needs in order to shut down.
       e.g. the client data is not allowed to be associated with any
       internal FS state objects, as that could cause the fs to crash
       later in the closing step (i.e. using the data after the client
       dtor destroyed it).

       Remember that the dtor function is semantically equivalent to
       free(), but that the client is free to do basically whatever
       he wants there.
    */
    int whio_epfs_client_data_set( whio_epfs * fs, void * data, void (*dtor)(void *) );

    /**
       Returns the client data previously set via
       whio_epfs_client_data_set(), or NULL if !fs or no data has been
       set.
    */
    void * whio_epfs_client_data_get( whio_epfs * fs );

    /**
       An type containing data for initializing certain options of a
       whio_epfs object. This contains only options which need to be
       set up while the EPFS is being initialized, as opposed to
       options which can be tweaked arbitrarily at runtime or are
       baked-in to the EFS container.

       The sense of this type is to use it as a parameter to fs
       initialization routines, rather than a more conventional list
       of arguments. This allows us to add parameters to it without
       breaking existing usage, as long as those parameters have
       sensible default values (client code should copy the
       whio_epfs_setup_opt_store_empty object to get the defaults!).

       Another use of this type is communicating information about
       whio_epfs initialization back to the caller. Certain members
       may be changed by the various initialization routines to notify
       interested callers of certain details.
    */
    struct whio_epfs_setup_opt
    {
        /**
           Storage-related options.
        */
        struct whio_epfs_setup_opt_store
        {
            /**
               The device an fs should use for storage. The setup
               routines will set this to NULL if the associated fs
               takes over ownership of the device. Performing any i/o
               on dev from outside of the whio_epfs API will
               eventually lead to undefined behaviour, possibly
               corruption.
            */
            whio_dev * dev;
            /**
               If true, the fs should take over ownership of its
               storage device (cleaning it up when the filesystem is
               closed).

               On an unsuccessful initialization the fs never takes
               over ownership of a client-provided device.

               In practice this almost always needs to be set to true,
               as it is rare that the clients needs a direct handle to
               the storage device after initializing a whio_epfs which
               manages it.
            */
            bool takeDevOnSuccess;

            /**
               If true, the fs will attempt to enable locking support.
               If support was requested but dev does not appear to
               report locking then the setup routines will set this
               value to false.
            */
            bool enableLocking;

            /**
               If true, whio_epfs_openfs() and friends will
               fail early on if they cannot get an immediate
               lock on the storage, as opposed to waiting on
               a lock. The locking is not available then this
               option is ignored.
            */
            /*bool failIfNoInitialLock; */
        } storage;
        /**
           HIGHLY EXPERIMENTAL! Do not yet use in client code!

           Options related to the fs memory allocator.
        */
        struct whio_epfs_setup_opt_memory
        {
            /**
               Start of the memory to be used as an allocation pool.
               The setup routines will set this to NULL if the
               associated fs is able to use it as a memory
               pool. Ownership of the memory is not changed, however.

               If a client _requires_ that memory pool support be
               enabled: he must first set it up via this object, and
               after opening the fs he should check if the mem member
               has been set to NULL. If it is NULL, memory pool
               initialization worked, else the pool was not set up and
               the library will automatically fall back to
               malloc()/free() (regardless of the value of
               fallbackOnOOM).
            */
            void * mem;
            /**
               Length of mem, in bytes.
            */
            whio_size_t size;
            /**
               If true, the fs should fall back to the standard
               de/re/allocators if the internal memory pool fills up,
               otherwise it should fail allocations with an
               out-of-memory error when the pool fills up.

               If pool initialization fails, the library will
               automatically fall back to malloc()/free() regardless
               of the value of fallbackOnOOM.
            */
            bool fallbackOnOOM;
        } memory;
    };
    /** Convenience typedef. */
    typedef struct whio_epfs_setup_opt whio_epfs_setup_opt;
    /**
       Empty-initializated whio_epfs_setup_opt object. It sets up
       several default values, and should be uses as a basis for
       initializing whio_epfs_setup_opt objects.
    */
#define whio_epfs_setup_opt_empty_m {\
        {/*storage*/ \
            NULL/*dev*/,                    \
                false/*takeDevOnSuccess*/,       \
                (WHIO_EPFS_CONFIG_ENABLE_STORAGE_LOCKING ? true : false)/*enableLocking*/, \
        },                              \
        {/*memory*/ \
            NULL/*mem*/,\
            0/*size*/,\
            false/*fallbackOnOOM*/\
         }\
    }
    /**
       Empty-initializated whio_epfs_setup_opt object. This object
       should be used to initialize client-defined whio_epfs_setup_opt
       objects, as it sets certain default values.
    */
    extern const whio_epfs_setup_opt whio_epfs_setup_opt_empty;
    
    /**
       Returns fs' primary options. They are never changed during
       the life of fs.

       Only returns NULL if fs is NULL.
    */
    whio_epfs_fsopt const * whio_epfs_options(whio_epfs const * fs);
    
    /**
       Creates a new whio_epfs filesystem in the given whio_dev object.
       The previous contents, if any, will be destroyed.

       None of the arguments may be null, but *fs may be null. If *fs
       is NULL, a new whio_epfs is allocated and (on success) assigned
       to *fs, else *fs is assumed to point to a clean,
       client-allocated whio_epfs object.

       How sopt is interpreted, and possibly changed, is described in
       whio_epfs_openfs(), so please see that function for how to
       intialize and populate it, and regarding ownership of objects
       stored in the sopt parameter.

       The fsopt parameter describes the basic parameters of the
       filesystem.  If certain ranges or combinations are violated
       then whio_rc.RangeError may be returned.

       On success, whio_rc.OK is returned and fs points to a populated
       whio_epfs object. If the user passed fs as a pointer to NULL, he
       must eventually free the returned object using
       whio_epfs_finalize(). If he passed in his own object then it
       must be cleaned up as appropriate (whio_epfs_finalize() for
       heap-allocated and whio_epfs_close() for stack-allocated).

       Example:

       @code
       // Set up general fs options:
       whio_epfs_fsopt fo = whio_epfs_fsopt_empty;
       fo.maxBlocks = 1000; // 0=grow on demand
       fo.blockSize = 1024 * 16;
       fo.inodeCount = 250;

       // Open/mkfs-specific options, including the storage device:
       whio_epfs_setup_opt so = whio_epfs_setup_opt_empty;
       so.storage.dev = whio_dev_for_filename("my.epfs","w+");
       assert( NULL != so.storage.dev );
       so.storage.takeDevOnSuccess = true;

       // Create the fs:
       whio_epfs * fs = NULL; // DO NOT(!!!) use an uninitialized pointer!!!
       rc = whio_epfs_mkfs( &fs, &so, &fo );
       if( rc ) { //error
           // We need to clean up the storage device:
           so.storage.dev->api->finalize( so.storage.dev );
           return ...;
       }
       ... use fs ...
       whio_epfs_finalize( fs );
       @endcode

       See also the convenience function whio_epfs_mkfs_file(), which
       takes a slightly higher-level set of parameters.
       
       @see whio_epfs_mkfs2()
       @see whio_epfs_openfs()
       @see whio_epfs_mkfs_file()
    */
    int whio_epfs_mkfs( whio_epfs ** fs, whio_epfs_setup_opt * sopt, whio_epfs_fsopt const * fsopt );

    /**
       This is a short-hand form of whio_epfs_mkfs() which uses
       compile-time defaults for the locking- and memory-related
       options.
    
       If takeStore is true then on success ownership of store is
       passed on to fs, and it will be destroyed when fs is closed. If
       takeStore is false then ownership of store is not changed and
       store must outlive fs. Ownership is not transfered if this
       function fails.

       Returns 0 on success. On error, the caller needs to deallocate
       fs only if he heap-allocated it (e.g. via whio_epfs_alloc())
       before calling this function. On error, ownership of
       store is never changed.

       @see whio_epfs_mkfs()
    */
    int whio_epfs_mkfs2( whio_epfs ** fs, whio_dev * store, whio_epfs_fsopt const * opt, bool takeStore );

    /**
       Assumes that store is a whio_epfs filesystem and initializes a
       whio_epfs object to access it.

       None of the arguments may be null.
       
       fs may not be null. If *fs is null, a new whio_epfs is
       allocated, else fs is assumed to point to a clean,
       stack-allocated whio_epfs object (or re-use of a heap-allocated
       object after it has been properly cleaned up).  See
       whio_epfs_mkfs() for more details - the ownership rules for fs
       are the same.

       The opened fs is configured according to the values of the opt
       object, as described below...

       
       opt->store.dev:
       
       opt->store.dev must be set to an opened device. If
       opt->store.takeDevOnSuccess is true then ownership of opt->store.dev
       is (on success) passed on to fs, otherwise ownership of
       opt->store.dev does not change. On error, ownership of
       opt->store.dev is never changed. If ownership of opt->store.dev
       is passed on to fs then opt->store.dev will be set to NULL when
       this function returns, to signify to the caller that fs has
       taken over ownership of the device.

       If opt->store.dev->api->iomode(opt->store.dev) returns a value
       greater than 0 then fs is opened in read/write mode, else it is
       opened read-only. It is important that the storage not be
       modified by any means other than via the whio_epfs API, as
       modifying it will almost certainly corrupt it.
       

       opt->store.enableLocking:
       
       If opt->store.enableLocking is true then the EFS will _attempt_
       to initialize file locking support. If locking support cannot
       be enabled, opt->store.enableLocking will be set to false when
       this function returns, but that is not considered an error by
       the engine (the client can check its value and abort if
       needed).  File locking is on by default (if the storage device
       appears to support it), but it can cause horrendous slow-downs
       if the storage is on a network-mounted drive (e.g. NFS, where i
       once saw an 8000% increase in app run-time due to file locking
       over NFS). If the caller requires locking, he can check the
       value of opt->store.enableLocking after this function returns,
       and abort if locking is not available.  Be aware, however, that
       not all whio_dev devices need locking. e.g. the memory-based
       device classes do not support record locking. Note that the fs
       is not guaranteed to support or use locking, but it tries to
       (or will try to).

       
       opt->memory (optional):

       If the of opt->memory.mem is non-null then
       whio_epfs_mempool_setup() is called, using the parameters set
       in opt->memory. If memory pool initialization succeeds then
       opt->memory.mem will be set to NULL to signify that fs has
       taken over write-ownership of the memory. Actual ownership of
       the memory is as defined for whio_epfs_mempool_setup().  It is
       not considered an error for memory pool setup to fail. In that
       case, this routine may succeed but will not set opt->memory.mem
       to NULL (to signify that it didn't take over logical ownership
       of the memory). Note that even if the memory pool is set up, fs
       itself will never be allocated within that pool (it's a
       chicken/egg scenario).


       Lifetime of the opt object:

       After this function returns, fs does not directly point to any
       memory which is still set in the opt object (remember that
       pointers in the opt object may be modified by this function -
       see above), and the opt object need not outlive fs.


       Return codes:

       Returns 0 on success. On error, the fs will be internally
       cleaned up, but the caller needs to deallocate fs if he
       heap-allocated it (e.g. via whio_epfs_alloc()) before calling
       this function. On error, ownership of storage device never
       changes.

       Error codes include (but are not necessarily limited to):

       - whio_rc.ArgError means one of the arguments was invalid.

       - whio_rc.ConsistencyError means that store does not appear to
       contain a whio_epfs filesystem.

       - whio_rc.IOError means there was a read error while
       determining wether store is an EFS.

       - whio_rc.AllocError means that fs (or one of its parts) could
       not be allocated. Out of memory.


       Usage example:

       @code
       whio_epfs_setup_opt opt = whio_epfs_setup_opt_empty;
       opt.storage.dev = whio_dev_for_filename( "my.epfs", "r+" );
       if( !dev ) { // error: could not open file
           return ...;
       }
       opt.storage.takeDevOnSuccess = true;
       opt.storage.enableLocking = true;
       whio_epfs * fs = NULL; // NEVER(!!!) use an uninitialize pointer!
       int rc = whio_epfs_openfs( &fs, &opt );
       if( rc ) { // error: we must clean up opt.storage.dev: ...
           opt.storage.dev->finalize(opt.storage.dev);
           return ...;
       }
       if( ! opt.storage.enableLocking )
       {
           // We requested locking support but it could not
           // be enabled. Whether or not this is an error is
           // app-dependent.
       }
       @endcode

       In this example, on success ownership of dev is passed on to
       fs, and ownership of fs is passed to the caller, who must
       eventually use whio_epfs_finalize() to destroy it.

       To add an internal memory pool to the above fs object, we could
       do:

       @code
       // In a scope which will out-live the EPFS object, e.g. global:
       unsigned char mempool[4000];
       ...
       // Then modify the opt object like so _before_ calling openfs2():
       opt.memory.mem = mempool;
       opt.memory.size = sizeof(mempool);
       opt.memory.fallbackOnOOM = true;
       // ^^ true = fall back to std allocators if we run out of memory
       @endcode

       PS: DO NOT use the memory pool. It's known to cause memory
       corruption in some test code.
    */
    int whio_epfs_openfs( whio_epfs ** fs, whio_epfs_setup_opt * opt );

    /**
       This is a short-hand form of whio_epfs_openfs() which uses
       compile-time defaults for the locking- and memory-related
       options.

       whio_epfs_openfs() is more flexible, and should be prefered over
       this function, but all of the notes below apply to both.

       Semantics and ownership of fs parameter are described in
       whio_efps_openfs().
       
       The store device is the underlying storage to use for the
       fs. If takeStore is true then on success fs will take over
       exclusive ownership of store, and will close it when the EFS is
       closed. On error ownership of store is never changed.
       
       @see whio_epfs_openfs()
    */
    int whio_epfs_openfs2( whio_epfs ** fs, whio_dev * store, bool takeStore );

    /**
       Tries to open an existing file an an EPFS container.

       None of the arguments may be null, but *fs may point to null.
       If !*fs then this function will allocate a new object and (on
       success) assign *fs to that object. The caller takes ownership
       of *fs and must eventually call whio_epfs_finalize() to destroy
       it. On error, *fs is not re-assigned.
       
       filename is the name of the file to open. It must already exist.

       If writeMode is true then the device is opened in read/write mode,
       otherwise it is opened in read-only mode.

       Returns 0 on success. On error non-zero is returned and *fs is
       never modified.

       @see whio_epfs_mkfs_file()
       @see whio_epfs_mkfs()
       @see whio_epfs_open()
    */
    int whio_epfs_openfs_file( whio_epfs ** fs, char const * filename, bool writeMode );

    /**
       Tries to initialize a file as an EPFS container.

       None of the parameters may be 0.
       
       The semantics and ownership of the fs parameter are as
       described for whio_epfs_openfs_file().

       The fsopt parameter is as described for whio_epfs_mkfs().

       The filename parameter must be a non-empty string refering to a
       local file (local=accessible via a filesystem path). If the
       file exists and allowOverwrite is false then
       whio_rc.AccessError is returned, otherwise the file is created
       or overwritten to make a new EPFS filesystem. As a special
       case, if the filename is ":memory:" then an in-memory device is
       created which will expand as the EPFS expands. When using such
       a device, routines which otherwise do not alloc might return
       whio_rc.AllocError if memory cannot be allocated for the
       device.

       If creation of the fs fails then the file may be left in an
       inconsistent state and should be removed (or analysed, or
       whatever) by the client.
       
       @see whio_epfs_mkfs()
       @see whio_epfs_open()
       @see whio_epfs_openfs_file()
    */
    int whio_epfs_mkfs_file( whio_epfs ** fs,
                             char const * filename,
                             bool allowOverwrite,
                             whio_epfs_fsopt const * fsopt );

    
    /**
       Please read all of these docs before using this function...

       First: HIGHLY EXPERIMENTAL! It normally seems to work, but once
       in a while i'm getting memory corruption in objects allocated
       through the custom allocator, seemingly via the block array
       reallocations (which hints at a bug in the realloc impl).

       Until the above warning is gone, please do not use this
       function or the related functionality built on top of it
       (e.g. whio_epfs_setup_opt::memory).

       This function tries to set up a memory pool for fs' own use, so
       that fs does not have to use malloc()/realloc() as much. This
       reduces calls into the OS and helps provide good locality of
       reference for various fs-internal objects (which tend to
       reference one-another).

       This functionality might or might not be compiled in. If it is
       not, this function will return whio_rc.UnsupportedError. In
       that case, fs will fall back to using the C-standard allocation
       routines.

       If used at all, this function must be called _immediately_ after
       initialization of fs (via whio_epfs_mkfs2(), whio_epfs_openfs2(),
       or similar). If it is called after fs allocates any resources
       for its own use then results are undefined.
       
       mem must be a pointer to @a size bytes of memory. The memory
       must outlive fs and must not be modified during fs' lifetime by
       any means other than fs' internal API. size must be larger than
       some vague compile-time constant (tip: try values larger than
       300) or this function will fail with error code
       whio_rc.RangeError.

       A portion of mem (about 120-200 bytes, depending on various
       compile-time options) will be reserved for the memory
       management data. Another (1-1.5% of size) may (depending on the
       size of mem) be reserved if the allocator needs more space for
       its management data. The rest can be used for allocating the
       various bits fs may need during its lifetime. See \ref
       page_whio_epfs_memcosts for more information about the memory
       costs.

       Because fs-associated client data is destructed early in the
       fs-closing process, while some internals are still live, it is
       not legal for @a mem to be used as "client data" via
       whio_epfs_client_data_set() if a destructor is set for that
       data (if there is no destructor then mem may be the client data
       object).

       If the internal pool runs out of memory, its behaviour depends
       on the fallback argument. If fallback is false then allocation
       will fail (returning NULL) for over-allocation.  If fallback is
       true, the API will fall back to using
       malloc()/realloc()/free().

       For many use cases, mem can be a stack-allocated buffer
       (e.g. allocated globally or in main()), as long as it outlives
       fs. It is also legal for mem to come from malloc(), but in that
       case the caller must be sure to free it after fs is
       closed. Closing fs will disassociate mem from fs, and it will
       need to be set up again if you want to re-use fs and the memory
       pool.

       Returns 0 on success. Error case return codes:

       - whio_rc.ArgError means mem or fs are null.

       - whio_rc.RangeError = size is too small to be useful.

       - whio_rc.AccessError = fs' memory pool was already set up.

       In theory (and if i've done my part right), setting up a pool
       large enough (1-2kb should do, 5kb would be a lot) can keep the
       whio_epfs API from ever having to dynamically allocate memory
       in the context of fs. At least for the average use case, where
       only a few handles are opened at a time, and block chains do
       not get extraordinarily long. The one malloc() call we normally
       cannot escape from is when using file-based storage, since
       calling fopen() allocates a FILE handle.
       
       ACHTUNG, ACHTUNG, ACHTUNG:
       
       The following list contains the ONLY functions which may
       legally be called _before_ whio_epfs_mempool_setup(). All
       others may indirectly induce undefined behaviour if
       whio_epfs_mempool_setup() is called after they are called:

       - whio_epfs_mkfs() (not whio_epfs_mkfs2())
       - whio_epfs_openfs() (not whio_epfs_openfs2())

       To set up a memory pool at the time the fs is initialized, as
       opposed to afterwards, use whio_epfs_mkfs() or
       whio_epfs_openfs(). Doing so removes any concerns about legal
       call ordering.
       
       If you actually read this far, you have my blessing to use this
       function. If you skipped to the end, please go back and read
       these docs before using it. And then if you see weird behaviour
       please try not using this, to be sure that the allocator is not
       the problem.
    */
    int whio_epfs_mempool_setup( whio_epfs * fs, void * mem, whio_size_t size, bool fallback );

    /** @deprecated Made obsolete via evolution.

        A type for collecting certain metrics from a whio_epfs memory
        pool. It is mainly intended for debuggering.
    */
    struct whio_epfs_mempool_stats_t
    {
        /** Number of allocated objects in the pool. */
        whio_size_t allocedObjects;
        /** Number of allocated blocks in the pool. */
        whio_size_t allocedBlocks;
        /** Total number of memory blocks in the pool. */
        whio_size_t blockCount;
        /** Size of each memory block in the pool. */
        whio_size_t blockSize;
        /**
           The total number of bytes in the underlying pool which are
           reserved for allocation purposes. This number will be
           smaller than the value passed to whio_epfs_mempool_setup(),
           since the allocator's innards are stored directly in the
           client-supplied buffer.
        */
        whio_size_t memorySize;
    };
    /** Convenience typedef. */
    typedef struct whio_epfs_mempool_stats_t whio_epfs_mempool_stats_t;

    /** @deprecated

       This function will go away once the allocator abstraction
       layer is consistently used internally.
       
       Populates dest, which may not be null, with some current
       metrics from fs' memory pool.

       On success 0 is returned and dest is modified. On error non-0
       is returned and dest is not modified.

       If the memory pool is not active or the feature is not compiled
       in then whio_rc.UnsupportedError is returned. If either fs or
       dest are null then whio_rc.ArgError is returned.
    */
    int whio_epfs_mempool_stats( whio_epfs const * fs, whio_epfs_mempool_stats_t * dest );
    
    /**
       Closes fs, making it available for re-use with whio_epfs_mkfs2()
       and friends.  This should be used to clean up stack-allocated
       whio_epfs objects, or dynamically-allocated whio_epfs objects
       before re-using them.

       Any opened handles which have not been closed by the time this
       is called will be closed automatically (but see below regarding
       whio_epfs_dev_open()). That means that all still-open handles
       are invalidated by this, and they should neither be used nor
       freed by the client (this routine frees them).

       If fs->client.dtor is not null then it is called and passed
       fs->client.data as the first step in the cleanup process.
       
       Returns 0 on success. The only error condition is when !fs.

       After calling this, fs may again be used as the target for
       whio_epfs_mkfs2() or whio_epfs_openfs2().


       MISFEATURES:

       - Devices opened via whio_epfs_dev_open() must have been closed
       by the time this is called or a leak will occur (and
       potentially a crash later on). whio_epfs does not yet have the
       infrastructure to track such opened devices other than by their
       inode handle (which doesn't link back to the device). This is
       on the to-fix list. To consider: if we allocate the whio_dev
       objects via a WHALLOC_API(book) object, we could inherently
       free up the devices at close-time without risking a leak. The
       same goes for whio_epfs_handles (those are a bitch to clean up
       properly in this routine!).
    */
    int whio_epfs_close( whio_epfs *fs );

    /**
       Calls whio_epfs_close(fs) and then frees fs' memory. fs is
       invalidated by this call.

       DO NOT pass this a stack-allocated object - use whio_epfs_close()
       to clean those up instead!
       
       If fs was not created with whio_epfs_alloc() then results
       are technically undefined. That said, the implementation
       tries to detect if fs was allocated via whio_epfs_alloc(),
       and does not actually free it if it was not (which may lead
       to a leak, but won't immediately crash on you).
       
       Returns 0 on success. The only reported error condition is when
       !fs. However, if fs was not allocated by whio_epfs_alloc(), this
       routine will effectively close it, but will _not_ deallocate it,
       and will report success.
    */
    int whio_epfs_finalize( whio_epfs *fs );

    /** Returns true only if fs is not null and is opened in
        read/write mode.
    */
    bool whio_epfs_is_rw( whio_epfs const * const fs );

    /**
       Returns the size of the EPFS container, or 0 if !fs or on an
       i/o error. Note that this has different error semantics than
       whio_dev_size() because 0 is not a valid EPFS size and is
       easier to work with than whio_dev_size()'s error code.

       Note that this is non-const because determining the size _may_
       (depending on the storage back-end) require seek()ing
       (i.e. non-const access).
    */
    whio_size_t whio_epfs_size(whio_epfs * fs);

    
    /**
       If fs is opened for read/write then this flushes the storage
       and returns a storage-dependent non-zero value on error. If fs
       is read-only then whio_rc.AccessError is returned. If !fs then
       whio_rc.ArgError is returned.

       The difference between calling this and, say, the flush()
       member of a device returned from whio_epfs_dev_open(), is that
       this flushes the underlying storage of the EFS container,
       whereas the latter only ensures that the current inode state is
       written to that storage (but not necessarily flushed).
       
       Do not call it too often, as it can be relatively slow.

       It is not normally necessary for client code to call this,
       but internals which muck with persistent data should use
       this to ensure that the metadata is written.

       Returns 0 on success.
    */
    int whio_epfs_flush( whio_epfs * fs );
    
    /**
       Returns the number of data blocks fs currently holds, or 0 if
       not fs. Note that blocks are added to fs as needed, so this
       number changes over time. If fs->fsopt.maxBlocks is not 0 then
       the block count will not be allowed to exceed that value.  Note
       that this refers to the "real" number of blocks and may differ
       from the number of USED blocks, which might be smaller than
       than the value returned by this function.

       This is an O(1) operation.
    */
    whio_epfs_id_t whio_epfs_block_count( whio_epfs const * fs );
    
    /**
       Opens the given inode for random access with the given
       read/write mode. If inodeID is 0 then mode must include
       WHIO_MODE_FLAG_CREATE and the next available (free/unused)
       inode will be opened for read/write access.

       dev must be non-null and *dev must either point to null or an
       empty-initialized object. On success, the created whio_dev
       object will be stored there. It must be closed or finalized as
       described in detail below.

       The open modes are as follows:

       - WHIO_MODE_READ opens the device in read-only mode. An inode
       with the given ID must have already been marked as used or this
       routine will fail.
       
       - WHIO_MODE_RW opens the device in read/write mode. The
       inode in question must currently be "in use", meaning that it
       must have been "created" via a prior open operation which used
       WHIO_MODE_FLAG_CREATE.
       
       - WHIO_MODE_FLAG_CREATE can be ORed together with
       WHIO_MODE_RW, and will "create" the inode entry if
       needed. It doesn't truly "create" anything, but it allows
       opening of an inode which is currently unused. It is called
       "create" because of its logical similarity to the O_CREAT flag
       for the open(2) system call. In this mode, if id==0 and no
       unused inodes are found then this function will fail
       with whio_rc.DeviceFullError.

       - The WHIO_MODE_RWC flag is equivalent to
       (WHIO_MODE_RW | WHIO_MODE_FLAG_CREATE).

       - WHIO_MODE_FLAG_TRUNCATE can be OR'd together with
       WHIO_MODE_WRITE to signify that the device should be
       truncated to 0 bytes after it is opened. Under very tight
       memory conditions truncation can actually fail (because it must
       load the inode block chain, which requires allocation). If a
       new inode is created via WHIO_MODE_FLAG_CREATE and
       truncation failed, the error recovery will unlink the new
       inode.

       Opening will fail with code whio_rc.AccessError if mode
       contains WHIO_MODE_FLAG_CREATE but fs is in read-only
       mode. It will also fail for non-create RO and RW modes if the
       inode has never been marked as being in-use (via opening with
       WHIO_MODE_FLAG_CREATE).

       On error, non-0 is returned and dev is _probably_ not
       modified. It may be modified if, e.g., truncation fails (in
       which case the state of the device's data is undefined).  If
       the user passes in a dev pointer to NULL then it will always be
       NULL on error (and the internally-allocated object is of course
       freed up). If the user passes in his own custom-allocated dev
       pointer than that device is close()d on error and the caller
       must deallocate it in a manner appropriate to its allocation
       method.

       More notes on truncation failure: if this function allocated
       *dev and truncation fails then the device is deallocated and
       *dev will be set to null when this function returns. If the
       client passed in a value for *dev then *dev is close()d before
       this function returns but its memory must still be freed using
       whatever method is appropriate for it.

       The returned object is a full-fledged whio_dev implementation,
       and can be used in all contexts which a "normal" whio_dev is.

       On success dev is non-null and ownership of h is transfered to
       dev. Ownership of dev is as follows:

       If !*dev, this function allocated the device and it must be
       destroyed using the whio-standard whio_dev::finalize()
       approach, e.g. dev->api->finalize(dev). If *dev (the caller
       allocated it), it must be either finalized as above (if it was
       allocated dynamically) or be closed using dev->api->close(dev)
       (if it was allocated on the stack or via an alternate
       allocation method).

       Closing/finalizing dev after fs is closed will lead to
       undefined behaviour, very possibly a crash.

       Example:

       @code
       whio_dev * d = NULL; // NEVER(!!!) use an uninitialized pointer!
       int rc = whio_epfs_dev_open( myfs, &d, 0, WHIO_MODE_RWC );
       if( rc ) { ... error ... }
       else {
           whio_epfs_id_t id = whio_epfs_dev_inode_id(d);
           // ... use device, then destroy it ...
           d->api->finalize(d);
       }
       @endcode
       
       whio_dev interface notes:

       Peculiarities of the returned whio_dev device vis-a-vis the
       whio_dev standard interface:

       - seek() will always succeed unless it is told to go to a point
       before the start of the file or the seek would cause a numeric
       underflow/overflow. Other than those cases, the validity of the
       position is not checked until the next read/write.

       - flush() will (in write mode) update the inode table with the
       object's current inode metadata (e.g. size, timestamp, and
       first block ID). Closing the device will flush it if it is
       opened in write mode. In read-only mode flush() will return
       whio_rc.AccessError.

       - truncate() and write(): because writing may cause the block
       count to increase, this function might have to allocate memory
       to store the expanded block chain. If that allocation fails,
       write() or truncate() will fail. In practice, it only fails
       this way when using a custom memory allocator which has a very
       low storage capacity.

       - Calling whio_dev_ioctl(dev,...) with a second argument of
       whio_epfs_ioctl_INODE_ID and a third argument of type
       (whio_epfs_id_t*) will set the 3rd argument to the inode ID
       associated with the device. (Or use whio_epfs_dev_inode_id() to
       fetch it.)

       - Calling whio_dev_ioctl(dev,...) with a second argument of
       whio_epfs_ioctl_INODE_PTR and a third argument of type
       (whio_epfs_inode**) will set the 3rd argument to the pointer
       to the inode associated with the device. (Or use whio_epfs_dev_inode()
       to fetch it.)

       - Calling whio_dev_ioctl(dev,...) with a second argument of
       whio_epfs_ioctl_HANDLE_PTR and a third argument of type
       (whio_epfs_HANDLE**) will set the 3rd argument to the pointer
       to the handle associated with the device.

       - Calling whio_dev_ioctl(dev,...) with a second argument of
       whio_dev_ioctl_GENERAL_size requires a 3rd (whio_size_t*)
       argument to which the current (unflushed) size of the inode is
       written. This is _much_ more efficient than calculating the
       length by seek()ing. See whio_epfs_dev_size() for a simpler way
       to get this information.
       
       - The dev->client member is not used by this API, and can be
       used by the client as described in the documentation for
       whio_dev::client.

       Having said all of that about getting a pointer to the device's
       internal inode and handle data... don't do it unless you are
       writing a tool for use with this library and you are aware that
       any incorrect fiddling of the inode/handle objects can corrupt
       the EFS, leak memory, or otherwise cause Undefined Behaviour.

       
       Opening an inode multiple times:

       If a given inode is opened multiple times, all opened
       references to it share the same underlying inode object and
       block chain but each has their own logical file position cursor
       and access mode. Thus when updating a given inode, read-only
       opened handles will see any changes in size, timestamp, and
       block list associated with the inode. Such changes are not
       written to disk until the inode is flushed, either by closing
       it or by calling dev->api->flush(dev) on its i/o device proxy
       (but flushing only works for devices opened in write mode).

       In the face of multiple opens, any handles which are linked to
       by others are closed as normal, but handle for the "master
       copy" will not actually be freed until all handles linked to it
       are also closed. This is required so that the inode instance
       which is shared amongst linked handles does not change memory
       locations at runtime (which would invalidate pointers to it).

       By the way, no inode can be opened more than
       (2^sizeof(whio_epfs_handle::openCount)) times
       concurrently. Trying to open it more times than that will fail
       with error code whio_rc.RangeError. (This is an artificial
       limitation, by the way.)

       Misfeatures:

       - If *dev is closed after fs is closed, there is a potential
       crash condition. Fixing this is on the TODO list but requires
       more infrastructure in the whio_epfs class to maintain the
       object links. In any case, closing the device after fs is
       closed is in Direct Violation of the API documentation, so i'm
       in no hurry to add that infrastructure :). (That said, in
       script-engine binding cases lifetimes can prove more
       problematic, so this will likely eventually be fixed because
       i like to bind C/C++ code to JavaScript engines.)
    */
    int whio_epfs_dev_open( whio_epfs * fs, whio_dev ** dev, whio_epfs_id_t inodeID, whio_iomode_mask mode );

    /**
       This works like whio_epfs_dev_open(), but takes an inode name instead
       of an inode ID.

       The semantics of the fs, dev, and mode parameters, as well as
       the return value, are the same as for whio_epfs_dev_open().

       If mode contains the flag WHIO_MODE_FLAG_CREATE and no inode is
       found with the given name, a new entry is created with the
       given name. If subsequent naming of that inode fails then the
       new inode is removed and the error code is propagated back to
       the caller.

       If mode contains the flag WHIO_MODE_FLAG_EXCL and an inode is
       found with the given name, whio_rc.AccessError is returned.

       
    */
    int whio_epfs_dev_open_by_name( whio_epfs * fs, whio_dev ** dev,
                                    whio_epfs_namer_const_string name,
                                    whio_size_t nameLength,
                                    whio_iomode_mask mode );

    
    /**
       If d was initialized via whio_epfs_dev_open() then its associated
       inode ID is returned.

       In any other case, 0 is returned (which is not a legal inode ID).

       This is equivalent to the whio_epfs_ioctl_INODE_ID ioctl, but
       is faster.
    */
    whio_epfs_id_t whio_epfs_dev_inode_id( whio_dev const * d );

    /**
       If dev was initialized via whio_epfs_dev_open() then its
       current (unflushed) size is returned, else whio_rc.SizeTError
       is returned.

       As of 20110730, whio_dev_size() tries to determine the size via
       ioctl before falling back to seek()ing, so this function is now
       equivalent to whio_dev_size(), but is still a tick faster
       because it avoids one levels function-call indirection.

       This function is basically equivalent to:

       @code
       whio_size_t sz = 0;
       whio_dev_ioctl( dev, whio_dev_ioctl_GENERAL_size, &sz );
       @endcode

       except for the different error-reporting mechanism.
    */
    whio_size_t whio_epfs_dev_size( whio_dev const * dev );
    
    /**
       If dev was initialized for read/write access via
       whio_epfs_dev_open() then its associated inode is returned. In
       any other case, NULL is returned.

       It is up to the caller to behave responsibly with the inode's
       data. Changing certain fields (especially whio_epfs_inode::size
       or whio_epfs_inode::firstBlock) could lead to data loss or EFS
       corruption.

       The returned inode is owned by the containing EPFS engine, and
       must not be deallocated nor dereferenced after dev has been
       closed.

       Returns non-NULL on success. Error conditions include:

       - !dev (whio_rc.ArgError).

       - dev is not-a EPFS inode i/o device (whio_rc.ArgError).

       - dev is read-only (whio_rc.AccessError). Use
       whio_epfs_dev_inode_c() to fetch a read-only inode.

       This routine is equivalent to the whio_epfs_ioctl_INODE_PTR
       ioctl, but is a bit faster.
       
       @see whio_epfs_dev_inode_c()
    */
    whio_epfs_inode * whio_epfs_dev_inode( whio_dev * dev );

    /**
       Const-correct form of whio_epfs_dev_inode(). It differs only in that
       it will return an inode pointer for a read-only device.

       @see whio_epfs_dev_inode()
    */
    whio_epfs_inode const * whio_epfs_dev_inode_c( whio_dev const * dev );

    /**
       If dev was initialized via whio_epfs_dev_open() then its mtime
       (last modification time) field is updated to the given time, or
       to the current system time if (time==-1).

       The given time, if not -1, is assumed to be GMT time. (Why? Because
       i can't seem to get the local-to-GMT conversion working properly,
       or at lest not without indirectly malloc()ing for each timestamp
       update.)

       Note that writing to a device automatically updates its mtime
       to the current time.

       ACHTUNG: The mtime of an inode is not written to storage until
       the device is flushed, either via its flush() member or by
       closing it.
       
       Returns 0 on success. Error conditions include:

       - !dev (whio_rc.ArgError).
       - dev is not-a EPFS inode i/o device (whio_rc.ArgError).
       - dev is read-only (whio_rc.AccessError).

       @see whio_epfs_dev_mtime()
    */
    int whio_epfs_dev_touch( whio_dev * dev, uint32_t time );

    /**
       If dev was initialized via whio_epfs_dev_open() then the time
       parameter (if not NULL) is set to that device's last
       modification time.

       Returns 0 on success. Error conditions include:

       - !dev (whio_rc.ArgError).
       - dev is not-a EPFS inode i/o device (whio_rc.ArgError).

       @see whio_epfs_dev_touch()
    */
    int whio_epfs_dev_mtime( whio_dev const * dev, uint32_t * time );

    
    /**
       If dev was opened in read/write mode via whio_epfs_dev_open()
       then the "client flags" for its its associated inode are set to
       the given value. dev must have been opened in read/write.

       The client flags are not used by this library, and are reserved
       for use by clients to add a small amount of metadata to
       inodes. They are stored in the EFS container along with the
       other inode metadata.

       ACHTUNG #1: this function does not flush the device, and any
       changes to the flags will not be written to storage until dev
       is flushed (remember that closing it flushes it).

       ACHTUNG #2: the mtime of the inode is not modified by this
       function. Whether or not it should be is a philosophical
       question.
       
       On success 0 is returned. Error conditions include:

       - !dev (whio_rc.ArgError).
       - dev is-not-a EPFS whio_dev instance (whio_rc.ArgError).
       - dev is opened read-only (whio_rc.AccessError).

       @see whio_epfs_dev_client_flags_get()
    */
    int whio_epfs_dev_client_flags_set( whio_dev * dev, uint32_t flags );

    /**
       If dev was opened via whio_epfs_dev_open()
       then the "client flags" for its its associated inode are copied
       to *flags (if flags is not NULL).

       On success 0 is returned and flags (if not null) is updated to the
       current flags value. Error conditions include:

       - !dev (whio_rc.ArgError).
       - dev is-not-a EPFS whio_dev instance (whio_rc.ArgError).

       Passing a NULL for flags is essentially a no-op, but could be
       used to test whether dev is-a EPFS whio_dev instance (this
       function would succeed in that case).
       
       @see whio_epfs_dev_client_flags_set()
    */
    int whio_epfs_dev_client_flags_get( whio_dev const * dev, uint32_t * flags );

    /**
       Tries to "remove" the given inode from the filesystem, marking
       its record as unused.

       Unlinking wipes all data associated with the given inode,
       overwriting them with zeroes (making this an O(N) operation,
       where N is the size of the associated data).

       On success 0 is returned. Error cases include:

       - inodeID is out of bounds (whio_rc.RangeError).

       - inodeID is not currently used (whio_rc.RangeError). It is
       arguable, however, as to whether this should qualify as an
       error condition or be silently ignored. whio_rc.RangeError is
       ambiguous for this case.
       
       - fs is opened read-only (whio_rc.AccessError).
       
       - The given inode is currently opened (whio_rc.AccessError).

       - An i/o error while reading or flushing the inode data: a
       propagated error code.

       Unlinking is an O(N) operation, where N is a function of the
       number of blocks belonging to the inode (because all must be
       traversed and cleared) and the block size (because each block
       is zeroed out).

       If whio_epfs_has_namer(fs) then the namer is asked to
       remove the name mapping. If it fails, unlinking is _not_
       performed and that error code is returned to the caller.
    */
    int whio_epfs_unlink( whio_epfs * fs, whio_epfs_id_t inodeID );

    /**
       Works like whio_epfs_unlink(), but searches for the inode
       to unlink by name. This can only work if fs has a namer
       installed.

       Returns 0 on success (found and unlinked), non-zero on error.
       There are any number of underlying error cases, including (but
       not limited to) whio_rc.NotFoundError to whio_rc.AllocError to
       whio_rc.IOError. (An allocation error can _potentially_ occur
       within the underlying namer instance.)

       See whio_epfs_unlink() for more information, in particular about
       error conditions.
    */
    int whio_epfs_unlink_by_name( whio_epfs * fs,
                                  whio_epfs_namer_const_string name,
                                  whio_size_t nameLen );
        
    
    /**
       whio_epfs_inode_foreach_f describes a callback for use with
       whio_epfs_foreach_inode().  It is called from whio_epfs_foreach_inode(),
       passing:

       - fs is the whio_epfs object to which the entry belongs.

       - ent is the current entry being iterated over.

       - clientData is the client-specified argument passed to
       whio_epfs_foreach_inode().
    */
    typedef int (*whio_epfs_inode_foreach_f)( whio_epfs * fs, whio_epfs_inode const * ent, void * clientData );

    /**
       whio_epfs_inode_predicate_f() describes a predicate functor for use with
       whio_epfs_inode_foreach(). n is the current inode being iterated
       over. clientData is the client-determined argument passed to
       whio_epfs_inode_foreach().
    */
    typedef bool (*whio_epfs_inode_predicate_f)( whio_epfs * fs, whio_epfs_inode const * n, void * clientData );

    /**
       A whio_epfs_inode_predicate_f() implementation which always
       returns true if fs and n are not null. This is intended for use
       with whio_epfs_foreach_inode() and friends, and can be used to
       match all (even unused) inodes.
    */
    bool whio_epfs_inode_predicate_true( whio_epfs * fs, whio_epfs_inode const * n, void * clientData );


    /**
       Walks each inode entry in fs, starting at the begin position
       and going until one before the end position. (That is,
       begin/end measures an exclusive range in the form
       [begin,end)). For each entry forEach(fs,entry,forEachData) may
       or may not be called, depending on the 'where' parameter
       (described below). If forEach() returns any value other than 0
       then looping stops and that return code is returned.

       Note that inode indexes start with 1, not 0. As a special case,
       if end is 0 then it is treated as "until the end of the inode
       list."

       The forEach function may not be null. The forEachData pointer
       may be anything - it is passed on as-is to the forEach
       function.

       If where() is not NULL then it is called for each inode, and
       only those inodes for which where() returns true are passed on
       to forEach(). The where() callback is passed whereData as its
       second argument, so the caller may use that to pass on extra
       information to the query function. If (!where) then all
       used/in-use inodes are passed to forEach(). If you also want to
       traverse unused inodes then create a where() function which
       always returns true (or pass whio_epfs_inode_predicate_true as
       the where function).

       On success, whio_rc.OK is returned. The other failure cases are:

       - fs or forEach are null: whio_rc.ArgError

       - begin or end fall outside of fs' inode range: whio_rc.RangeError

       - end is not 0 and (begin>end): whio_rc.RangeError
       
       - reading an inode fails: some propagated error code.

       - If forEach() returns non-0, procecssing stops and that
       result is returned.

       ACHTUNG: this bypasses the opened-inodes cache (because search
       time would grow exponentially as the number of opened inodes
       grew). Thus the inodes passed to forEach() may not reflect
       unflushed state of inodes which are currently opened for write
       access.
    */
    int whio_epfs_foreach_inode_in_range( whio_epfs * fs,
                                          whio_epfs_id_t begin,
                                          whio_epfs_id_t end,
                                          whio_epfs_inode_predicate_f where, void * whereData,
                                          whio_epfs_inode_foreach_f func, void * foreachData );

    /**
       Equivalent to
       whio_epfs_foreach_inode_in_range(fs,1,0,where,whereData,func,foreachData).
    */
    int whio_epfs_foreach_inode( whio_epfs * fs, whio_epfs_inode_predicate_f where, void * whereData,
                                 whio_epfs_inode_foreach_f func, void * foreachData );


    /**
        Returns true if ino is not null and the inode's in-use flag is
        set. This generally needn't be used by client code, but can be
        useful in conjunction with whio_epfs_foreach_inode().
    */
    bool whio_epfs_inode_is_used( whio_epfs_inode const * ino );


    /**
       Returns true if fs is not NULL and ino is (not 0 and is less
       than or equal whio_epfs_options(fs)->inodeCount). It returns false in all
       other cases.
    */
    bool whio_epfs_inode_id_in_bounds( whio_epfs const * fs, whio_epfs_id_t ino );

    /**
       Tries to parse inp as a whio_epfs_id_t in either decimal format
       or hexidecimal if the second byte of inp is either 'x' or 'X'.

       On success 0 is returned and *tgt is set to the id value.

       If !inp or !tgt then whio_rc.ArgError is returned.

       If allowExtraChars is true then parsing will succeed even if
       the parsed number has trailing characters after the numeric
       part. Thus it would parse "0x16hi" as 20 (=0x16) and ignore the
       "hi" parts. If allowExtraChars is false then the last character
       must be NULL or the parse will fail.

       TODO:

       - Refactor this to work like strtol(), such that it reports the
       address off the last character it looks at. The client then has
       to make the determination of whether the trailing character is
       valid or not. This approach is more generic, allowing the
       client to incrementally parse IDs from longer strings, e.g.  "1
       7 9, 13". But more generic == more handling on the client side.
    */
    int whio_epfs_parse_id( char const * inp, bool allowExtraChars, whio_epfs_id_t * tgt );
    /*int whio_epfs_parse_id( char const * inp, whio_epfs_id_t * tgt, char const ** end );*/

    /**
       Tries to parse a string as either a single whio_epfs_id_t or as
       a pair of whio_epfs_id_t's representing a range of values.

       inp in expected to be a null-terminated string in one of these
       formats:

       1) ###

       2) ###-###

       Where ### is an inode ID in a format supported by
       whio_epfs_parse_id().
  
       On success:

       Case 1) begin=###, end=begin

       Case 2) begin=#1, end=#2

       All other cases cause non-zero (error) to be returned, and
       begin/end are not modified.

       Either of begin or end may be null, in which case any parsed
       value is not set for that entry.
       
       This function does not certify that end comes after begin,
       nor does it certify that the values fall within a given
       range (other than that of the whio_epfs_id_t type).

       Note that the parsed begin/end range is INCLUSIVE, whereas
       whio_epfs_foreach_inode_in_range() uses an end-exclusive
       (STL-style) range. When using the values with that function,
       add 1 to the end value.


       TODO:

       Refactor this to report the address of the last character
       parsed, to allow the client to determine if trailing characters
       are legal or not.
    */
    int whio_epfs_parse_range( char const * inp, whio_epfs_id_t * begin, whio_epfs_id_t * end );

    /**
       Writes a client-defined label to the fs.

       The legal argument combinations for (lbl,n) are:

       - lbl must be at least n bytes long, and n must be no greater
       than whio_epfs_sizeof_label_payload. If n is less than
       whio_epfs_sizeof_label_payload then the written label will be
       padded with NULLs to fill that length.

       - If lbl is NULL then a blank (all-null) label is written and n
       is ignored.

       - If n is 0 the effect is the same as if lbl is NULL.

       Returns whio_rc.OK on success.

       Errors include:

       - fs is null: whio_rc.ArgError
       
       - lbl is non-null and n is greater than
       whio_epfs_sizeof_label_payload: whio_rc.RangeError

       - Write fails: whio_rc.IOError

       - fs is opened for read-only access: whio_rc.AccessError
    */
    int whio_epfs_label_set( whio_epfs * fs, char const * lbl, whio_size_t n );

    /**
       Reads the client-defined label from fs and copies it to lbl.
       lbl must be valid memory at least
       whio_epfs_sizeof_label_payload bytes long, and on success
       exactly whio_epfs_sizeof_label_payload bytes will be copied to
       it. If the client needs to guaranty that lbl gets
       null-terminated, he should allocate it as 1 byte larger than
       whio_epfs_sizeof_label_payload and add a null byte to it.

       On failure lbl will not be modified.
       
       Returns 0 on success.

       Errors include:

       - either arg is null: whio_rc.ArgError
       
       - Read error: whio_rc.IOError
   
       - Read succeeded but data is not what we expected:
       whio_rc.ConsistencyError
    */
    int whio_epfs_label_get( whio_epfs * fs, char * lbl );

    /**
       Searches for a registered whio_epfs_namer_reg object.  If
       found, *reg (if reg is not NULL) is populated with its data and
       0 is returned.

       Error conditions/codes:

       - If no entry found: whio_rc.NotFoundError

       - If name is longer than or the same length as (as measured by
       strlen()) whio_epfs_sizeof_namer_label_payload:
       whio_rc.RangeError

       @see whio_epfs_namer_reg_add()
    */
    int whio_epfs_namer_reg_search( char const * name, whio_epfs_namer_reg * reg );

    /**
       Adds a COPY OF the given whio_epfs_namer_reg object to the
       internal registry. If an entry already exists with the same
       name then whio_rc.AccessError is returned. If !reg or reg is
       not populated then whio_rc.ArgError is returned. If the
       internal list fills up then whio_rc.AllocError is returned.

       The internal list has a limited/static size. The library
       guarantees that at least 10 slots are available for client
       use. (It is not expected that clients will ever use more than
       1.)

       On success 0 is returned.

       @see whio_epfs_namer_reg_search()
    */
    int whio_epfs_namer_reg_add( whio_epfs_namer_reg const * reg );

    /**
       Prepares a whio_epfs_namer object for use with a given EFS
       instance.

       The namer is allocated using reg->alloc().  When fs is closed
       it will call namer->api->cleanup(namer) to free n's internal
       resources. If reg->free non-NULL then when fs is closed it will
       call reg->free(namer) to free the namer object after calling
       namer->api->cleanup(namer).

       Note that the reg pointer's contents are copied, so reg need
       not live longer than the call to this function.

       In the abstract, preparing the namer looks like this:

       - Register or load a whio_epfs_namer_reg instance, using
       whio_epfs_namer_reg_add() or whio_epfs_namer_reg_search().

       - Format the EFS (or re-use an existing EFS).

       - Call this function.

       
       Returns 0 on success or some other whio_rc value on error.

       Caveats, gotchas, and warnings:

       - Each whio_epfs can have, at most, one associated namer, and
       this routine fails with whio_rc.AccessError if fs already has a
       namer object.

       - There is currently no API for disassociating a namer from
       an EFS. A consequence of this is that it's not currently possible
       to replace a namer once one is set up for an EFS instance. (Adding
       this is on the TODO list.)

       - A namer is allowed to store entries within the fs
       object. Whether or not it assigns a name to such internal
       inodes is up to the implementation. On one hand, if we don't
       have a name them the namer's for-each operation will not reveal
       the inode (which is generally desireable), but the EFS's
       for-each-inode operation will reveal it, but it won't have a
       name. Which condition is less evil is a matter of debate. i
       tend to think that it should have a name, because the
       for-each-inode operation is much more likely to be used than
       the for-each-name operation.

       Here is an example of setting up a namer:

       @code
       // First, try to load a registered namer class:
       
       whio_epfs_namer_reg reg = whio_epfs_namer_reg_empty;
       int rc = whio_epfs_namer_reg_search( "whio_epfs_namer_ht", &reg );
       if( 0 != rc ) { ... error ... }

       // Second, apply it to a freshly-formatted EFS:
       // Assume that 'fs' is such an EFS.

       rc = whio_epfs_namer_format( fs, &reg );
       if( 0 != rc ) { ... error ... }
       @endcode
    */
    int whio_epfs_namer_format( whio_epfs * fs, whio_epfs_namer_reg const * reg );
    
    /**
       Returns true if fs is non-NULL and has a whio_epfs_namer
       associated with it.
    */
    bool whio_epfs_has_namer( whio_epfs const * fs );
    
    /**
       IFF fs has a namer then this function uses that namer to set
       the name of the given inodeID.  n must be NULL or be valid
       memory at least len bytes long. An n value of NULL and/or a len
       value of 0 means to clear any name associated with the
       inode. inodeID must be a valid inode ID for the given fs, but
       the inode need not be in-use for this function to work. i.e.
       it is possible to name "free" inodes which are not currently in
       use by the EFS.

       Whether or not the len parameter has an artificial upper limit
       is up to the underlying namer.

       Returns 0 on success. See whio_epfs_namer_api::set() for more
       details.

       If fs has no namer then whio_rc.ArgError is returned, but that
       return code is also returned if any other arguments are
       invalid.
    */
    int whio_epfs_name_set( whio_epfs * fs, whio_epfs_id_t inodeID, whio_epfs_namer_const_string n, whio_size_t len );

    /**
       IFF fs has a namer then this function uses that namer to fetch
       the name of the given inodeID. n must be valid memory at least
       *len bytes long. inodeID must be a valid inode ID for the given
       fs, but the inode need not be in-use for this function to work.

       Whether or not the len parameter has an artificial upper limit
       is up to the underlying namer. It may return a whio_rc.RangeError
       len is too small.

       On success it returns 0, modifies _up_to_ len bytes of n, and
       sets *len to the actual number of bytes modified.

       See whio_epfs_namer_api::get() for more details.

       FIXME: if *len is too short, set *len to the size we would
       need in order to fullfil the request.
    */
    int whio_epfs_name_get( whio_epfs * fs, whio_epfs_id_t inodeID, whio_epfs_namer_string n, whio_size_t * len );

    /**
       IFF fs has a namer then this function uses that namer to search
       the inode ID associated with the given name. name must be valid
       memory at least *len bytes long.

       Whether or not the len parameter has an artificial upper limit
       is up to the underlying namer. It may return a whio_rc.RangeError
       len is too small.

       On success it returns 0, modifies and assigns the found inode ID
       to *inodeID.

       If no entry is found then whio_rc.NotFoundError is returned
       and *inode is set to 0.

       See whio_epfs_namer_api::search() for more details.

       Note that searching by name is an optional feature of the namer
       API. If the namer does not support it, whio_rc.UnsupportedError
       is returned.
    */
    int whio_epfs_name_search( whio_epfs * fs, whio_epfs_id_t * inodeID, whio_epfs_namer_const_string name, whio_size_t nameLength );

    /**
       IFF fs has a namer then this function uses that namer to iterate
       over the names of all named inodes (those without names are
       not visited).

       For each visited inode, the callback is called and passed the
       name information. Note that the inodes are not guaranteed to be
       called in numerically sequential order - that is an
       implementation detail of the underlying namer implementation.
       The callback function is passed the callbackParameter, which
       the client may use to transport arbitrary information into the
       callback (e.g. a buffer for copying the names to).

       Note that the callback does not get any EFS information other than the
       inode ID and name. If you want information such as the inode's size
       and timestamp then use whio_epfs_foreach_inode() and fetch the
       name from that function's callback.

       On success it returns 0.

       See whio_epfs_namer_api::foreach() for more details.

       Note that the for-each operation an optional feature of the namer
       API. If the namer does not support it, whio_rc.UnsupportedError
       is returned.
    */
    int whio_epfs_name_foreach( whio_epfs * fs, whio_epfs_namer_foreach_callback callback, void * callbackData );

    /**
       Returns true if ino is not NULL and has the "is internal"
       flag set.
    */
    bool whio_epfs_inode_is_internal( whio_epfs_inode const * ino );

    /**
       Given a virtual position within block-chunked storage with
       blocks of size blockSize, this function returns the number of
       those blocks which are needed to hold a byte written at the
       given virtual position. Thus it always returns a positive
       number, even if pos is 0 (because writing to pos 0 would
       require 1 block).

       Results are undefined if blockSize is 0.

       Constrast with whio_epfs_block_count_for_size().
    */
    whio_size_t whio_epfs_block_count_for_pos( whio_size_t blockSize,
                                               whio_size_t pos );
    /**
       Given a virtual size within block-chunked storage with
       blocks of size blockSize, this function returns the number of
       those blocks which are needed to hold an object with the
       given size. Thus it returns 0 when sz is 0 (since we need
       not blocks to hold 0 bytes).

       Results are undefined if blockSize is 0.

       Constrast with whio_epfs_block_count_for_pos().
    */
    whio_epfs_id_t whio_epfs_block_count_for_size( whio_size_t blockSize,
                                                   whio_size_t sz );

    
    
#ifdef __cplusplus
        } /* extern "C" */
#endif

#endif /* WANDERINGHORSE_NET_WHIO_EPFS_H_INCLUDED */
/* end file include/wh/whio/whio_epfs.h */
