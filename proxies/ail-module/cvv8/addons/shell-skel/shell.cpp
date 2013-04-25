/**
   Test/demo code for the v8-convert API.
   
   This file implements a very basic shell application which
   reads in a single JS file and executes it.
   
   The shell's JS environment can be extended without changing
   this code by doing the following:
   
   Define INCLUDE_SHELL_BINDINGS to a string - the name of a
   header file which declares a function for setting up your bindings.
   
   Define SETUP_SHELL_BINDINGS to the name of the function to call 
   to initialize the client-side bindings. The function must accept 
   a single argument of type v8::Handle<v8::Object> and must add any 
   desired bindings to that object (which is the shell's "global 
   object").
   
   Example:
   
   @code
   g++ -c \
        '-DINCLUDE_SHELL_BINDINGS="my.hpp"' \
        -DSETUP_SHELL_BINDINGS=my::SetupBindings \
        -I/path/to/v8 \
        -I/path/to/v8/convert \
        -o my_shell.o \
        shell.cpp
   @endcode
   
   Note the extra quotes around the INCLUDE_SHELL_BINDINGS bits, to
   make sure that the shell does not strip the double-quotes required
   by this code.

   If built without those macros then the shell will still work but will not
   contain any client-custom bindings. See
   cvv8::V8Shell::SetupDefaultBindings() for the list of features
   added to the JS engine. In addition to those, this shell provides a
   JS-side gc() function which is a proxy for v8::V8::IdleNotification().
*/

#include <cassert>
#include <iostream>

#ifndef CERR
#define CERR std::cerr << __FILE__ << ":" << std::dec << __LINE__ << " : " 
#endif

#ifndef COUT
#define COUT std::cout << __FILE__ << ":" << std::dec << __LINE__ << " : "
#endif


#include "cvv8/v8-convert.hpp"
#include "cvv8/V8Shell.hpp"
namespace cv = cvv8;

#if defined(INCLUDE_SHELL_BINDINGS)
#  include INCLUDE_SHELL_BINDINGS
#endif

static int v8_main(int argc, char const * const * argv)
{
    assert( argc >= 2 );
    cv::Shell shell(NULL, argc, argv);
    shell.SetupDefaultBindings()
#if 0 /* the v8 team keeps changing the signature of IdleNotification() */
        ("gc", cv::FunctionToInCa<bool (),v8::V8::IdleNotification>::Call )
#endif
    ;
    try
    {
        
#if defined(SETUP_SHELL_BINDINGS)
        {
            v8::Handle<v8::Object> global( shell.Global() )
                /* We do this, instead of passing shell.Global() directly,
                   in case the function takes a non-const reference.
                */;
            SETUP_SHELL_BINDINGS(global);
        }
#endif
        char const * fname = argv[1];
        v8::Handle<v8::Value> rc = shell.ExecuteFile( fname );
    }
    catch(std::exception const & ex)
    {
        CERR << "Caught a std::exception: " << ex.what() << '\n';
        return 3;
    }
    catch(...)
    {
        CERR << "A non-std::exception native exception was thrown! Srsly.\n";
        return 4;
    }
    return 0;
}

int main(int argc, char const * const * argv)
{

    if( (argc<2) || ('-'==*(argv[1]) ))
    {
        CERR << "Usage:\n\t" << argv[0] << " script.js [-- [script arguments]]"
             << "\nAll arguments after '--' are available in the script via "
             << "the global 'arguments' Array object.\n";
        
        return 1;
    }
    int const rc = v8_main(argc, argv);
    //CERR << "Done! rc="<<rc<<'\n';
    return rc;
}

