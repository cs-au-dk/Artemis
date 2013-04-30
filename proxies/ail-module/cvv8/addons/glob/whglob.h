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
