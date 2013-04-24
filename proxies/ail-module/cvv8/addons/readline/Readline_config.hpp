#ifndef S11N_NET_LIBREADLINECPP_CONFIG_H_INCLUDED
#define S11N_NET_LIBREADLINECPP_CONFIG_H_INCLUDED 1
/**
   Main configuration for Readline.{cpp,hpp}. Changing these options
   also means one must also change the linker args and possibly the
   includes path.
*/

#define LIBREADLINECPP_USE_LIBEDITLINE 0
// ^^^ set to 1 to use -leditline, else 0. The libeditline code is way
// outdated and needs to be removed.
#if (1 == LIBREADLINECPP_USE_LIBEDITLINE)
#  define LIBREADLINE_CPP_IMPLEMENTATION_NAME "libeditline"
#  define LIBREADLINECPP_LICENSE "Public domain"
#  define LIBREADLINECPP_USE_GENUINE_LIBEDIT 0
#else
#  define LIBREADLINECPP_USE_GENUINE_LIBEDIT 0
// ^^^ set to 1 to use -ledit
#endif


#if (1 == LIBREADLINECPP_USE_GENUINE_LIBEDIT)
#  define LIBREADLINE_CPP_IMPLEMENTATION_NAME "libedit"
#  define LIBREADLINECPP_LICENSE "Public domain"
#  define LIBREADLINECPP_USE_LIBREADLINE 0
#else
#  define LIBREADLINECPP_USE_LIBREADLINE 1
// ^^^ set to 1 to use -lreadline, but be aware that it's GPL
#endif


#if (1 == LIBREADLINECPP_USE_LIBREADLINE)
#  define LIBREADLINE_CPP_IMPLEMENTATION_NAME "libreadline"
#  define LIBREADLINECPP_LICENSE "GNU General Public License version 2 or higher. Copyright (c) 2002-2009 stephan beal (http://wanderinghorse.net/home/stephan)"
#endif


#ifndef LIBREADLINE_CPP_IMPLEMENTATION_NAME
#  define LIBREADLINE_CPP_IMPLEMENTATION_NAME "stdin"
#  define LIBREADLINECPP_LICENSE "Public domain"
#endif

#define LIBREADLINECPP_VERSION "2005.12.22"


#endif // S11N_NET_LIBREADLINECPP_CONFIG_H_INCLUDED
