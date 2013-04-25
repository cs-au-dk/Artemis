/**
   Test/demo code for the v8-convert API.
*/
#if defined(NDEBUG)
#  undef NDEBUG  // force assert() to work
#endif

#include <cassert>
#include <iostream>
#include <fstream>
#include <iterator>
#include <algorithm>

#ifndef CERR
#define CERR std::cerr << __FILE__ << ":" << std::dec << __LINE__ << ":" <<__FUNCTION__ << "(): "
#endif

#ifndef COUT
#define COUT std::cout << __FILE__ << ":" << std::dec << __LINE__ << " : "
#endif

#include <iostream>

#include "cvv8/v8-convert.hpp"
#include "cvv8/V8Shell.hpp"
namespace cv = cvv8;
//typedef v8::Handle<v8::Value> ValueHandle;
#define ValueHandle v8::Handle<v8::Value>

#include "ConvertDemo.hpp"
#define JSTR(X) v8::String::New(X)

#include <cstdio> /* puts() */

#if !defined(_WIN32)
#  include <unistd.h> /* only for sleep() */
#  define do_sleep ::sleep
#else
#  include <windows.h> /* only for Sleep() */
#  define do_sleep(N) ::Sleep((N)*1000)
#endif


ValueHandle test1_callback( v8::Arguments const & argv )
{
    using namespace v8;
    Local<Value> myref /* to keep v8 from prematurly cleaning my object. */;
    Local<Function> jf;
    BoundNative * fooPtr;
    Local<Object> myobj;
    {
        BoundNative::SetupBindings( v8::Context::GetCurrent()->Global() );
        //v8::HandleScope scope;
        Handle<Function> const & ctor( cv::ClassCreator<BoundSubNative>::Instance().CtorFunction() );
        CERR << "Calling NewInstance()\n";
        myref = ctor->NewInstance(0, NULL);
        CERR << "Called NewInstance()\n";
        fooPtr = cv::CastFromJS<BoundNative>(myref);
        CERR << "NewInstance() == @"<<(void const *)fooPtr<<'\n';
        assert( 0 != fooPtr );
        myobj = Object::Cast(*myref);
        ValueHandle varg[] = {
          JSTR("Example of binding functions taking (char const *) arguments.")
        };
        int const argc = 1;
        jf = Function::Cast( *(myobj->Get(JSTR("puts"))) );
        jf->Call( myobj, argc, varg );
        jf = Function::Cast( *(myobj->Get(JSTR("bogo"))) );
        jf->Call( myobj, argc, varg );
        jf = Function::Cast( *(myobj->Get(JSTR("bogo2"))) );
        jf->Call( myobj, argc, varg );
        jf = Function::Cast( *(myobj->Get(JSTR("nativeParam"))) );
        varg[0] = myobj;
        jf->Call( myobj, argc, varg );
#if 1
        jf = Function::Cast( *(myobj->Get(JSTR("runGC"))) );
        CERR << "runGC handle isEmpty?=="<<jf.IsEmpty()<<'\n';
        jf->Call( myobj, 0, varg );
#endif
    }

    typedef cv::FunctionPtr< int (char const *), ::puts > PUTS;
    PUTS::FunctionType putstr = PUTS::Function;
    putstr("roundabout use of puts()");
    
    typedef cv::FunctionPtr< void (), doNothing > DoNothingFP;
    DoNothingFP::Function();
    typedef cv::FunctionPtr< void (), doNothing > DoNothingFP2;
    DoNothingFP2::Function();
    typedef cv::FunctionPtr< int (int), doSomething > DoSomething;
    DoSomething::Function(13);

    
    typedef cv::MethodPtr< BoundNative, void (void), &BoundNative::doFoo > DoFoo;
    typedef cv::MethodPtr< BoundNative, double (int,double), &BoundNative::doFoo2 > DoFoo2;

    typedef cv::ConstMethodPtr< BoundNative, double (int,double), &BoundNative::operator() > DoFooOp2;

    v8::InvocationCallback cb;
    CERR << "Calling doNothing():\n";
    cb = cv::FunctionToInCa< void (), doNothing >::Call;
    cb(argv);

  
    CERR << "Calling doSomething():\n";
    cb = cv::FunctionToInCa< int (int), doSomething >::Call;
    cb(argv);
    BoundNative & foo = *fooPtr;
    CERR << "Calling foo.doFoo2():\n";
    cv::MethodToInCa< BoundNative, double (int, double), &BoundNative::doFoo2 >::Call(foo, argv);

    
    CERR << "Calling foo.operator():\n";
    cv::ConstMethodToInCa< BoundNative, double (int, double), &BoundNative::operator() >::Call(foo, argv);

    CERR << "Calling foo.invo() (non-const):\n";
    cv::MethodToInCa< BoundNative, ValueHandle(v8::Arguments const &), &BoundNative::invo >::Call(foo, argv);


    CERR << "Calling foo.invo() (const):\n";
    cv::ConstMethodToInCa< BoundNative, ValueHandle(v8::Arguments const &), &BoundNative::invo >::Call(foo, argv);


    CERR << "Calling sampleCallback():\n";
    cb = cv::FunctionToInCa< ValueHandle(v8::Arguments const &), sampleCallback >::Call;
    cb(argv);


    CERR << "Calling foo.invo() (static):\n";
    cb = cv::FunctionToInCa< ValueHandle(v8::Arguments const &), BoundNative::invoStatic >::Call;
    cb(argv);

    CERR << "argv-forwarder (void):\n";
    cv::FunctionForwarder< void () >::Call( doNothing, argv );
    CERR << "argv-forwarder (int):\n";
    cv::FunctionForwarder< int (int) >::Call( doSomething, argv );

    CERR << "argv-forwarder (int) via forwardFunction():\n";
    cv::forwardFunction( doSomething, argv );
    CERR << "argv-forwarder (void) via forwardFunction():\n";
    cv::forwardFunction( doNothing, argv );

    CERR << "argv-method-forwarder (void):\n";
    cv::MethodForwarder< BoundNative, void () >::Call( foo, &BoundNative::doFoo, argv );

     CERR << "argv-method-forwarder (int,double):\n";
     cv::MethodForwarder< BoundNative, double (int,double) >::Call( foo, &BoundNative::doFoo2, argv );
     CERR << "same thing using forwardMethod(T, MemFunc, Arguments):\n";
     cv::forwardMethod( foo, &BoundNative::doFoo2, argv );
     cv::forwardMethod( foo, &BoundNative::doFoo, argv );
     try
     {
         cv::forwardMethod<BoundNative>( &BoundNative::doFoo, argv )
             /* won't actually work b/c argv.This() is-not-a BoundNative */
             ;
     }
     catch(cv::MissingThisException const & ex )
     {
         CERR << "Got expected exception: " << ex.Buffer() << '\n';
     }
     catch(...) { throw; }

     CERR << "argv-const-method-forwarder (void):\n";
     cv::ConstMethodForwarder< BoundNative, void () >::Call( foo, &BoundNative::doFooConst, argv );

     CERR << "Calling forwardConstMethod(T, MemFunc, Arguments):\n";
     cv::forwardConstMethod( foo, &BoundNative::doFooConst, argv );
     cv::forwardConstMethod( foo, &BoundNative::doFooConstInt, argv );
     try
     {
         cv::forwardConstMethod<BoundNative>( &BoundNative::doFooConstInt, argv )
             /* won't actually work b/c argv.This() is-not-a BoundNative */
             ;
     }
     catch(cv::MissingThisException const & ex )
     {
         CERR << "Got expected exception: " << ex.Buffer() << '\n';
     }
     catch(...) { throw; }
#if 0
     jf = Function::Cast( *(myobj->Get(JSTR("destroy"))) );
     CERR << "Calling myObject.destroy()...\n";
     jf->Call( Local<Object>(Object::Cast(*myref)), 0, NULL );
#endif

     
     CERR << "Done\n";
     CERR << "NOTE: you may see an exception message directly before or after this "
          << "function returns regarding a missing native 'this' pointer. Don't "
          << "panic - it is _expected_ here.\n"
         ;
     return v8::Undefined();
}

struct MyType
{
    MyType()
    {
        CERR << "MyType::MyType() @ "<<this<<'\n';
    }
    MyType( int i, double d ) {
        CERR << "MyType::MyType("<<i<<", "<<d<<") @ "<<this<<'\n';
    }
    MyType( char const * str ) {
        CERR << "MyType::MyType("<<str<<") @ "<<this<<'\n';
    }
    MyType( v8::Arguments const & argv ) {
        CERR << "MyType::MyType("<<argv.Length()<<" arg(s)) @ "<<this<<'\n';
    }
    ~MyType() {
        CERR << "MyType::~MyType() @ "<<this<<'\n';
    }
    
    
};
//-----------------------------------
// Policies used by cv::ClassCreator
namespace cvv8 {
    // Optional: used mostly for error reporting purposes but can
    // also be used to hold the class' JS-side name (which often differs
    // from its native name).
    // If used, it should be declared (and optionally defined) before other
    // ClassCreator policies.
#if 1
    CVV8_TypeName_DECL((MyType));
    CVV8_TypeName_IMPL((MyType),"MyType");
#elif 1
    CVV8_TypeName_IMPL2((MyType),"MyType");
#else
    template <>
    char const * TypeName< MyType >::Value = "MyType";
#endif

    // MyType constructors we want to bind to v8 (there are several other ways
    // to do this): This does NOT need to be a member of this class: it can be
    // defined anywhere which is convenient for the client. It must come
    // after TypeName, if TypeName will be specialized.
    typedef cv::Signature<MyType (
        cv::CtorForwarder<MyType *()>,
        cv::CtorForwarder<MyType *(char const *)>,
        cv::CtorForwarder<MyType *( int, double )>,
        cv::CtorForwarder<MyType *( v8::Arguments const &)>
    )> MyTypeCtors;

    // The policy which tells ClassCreator how to instantiate and
    // destroy native objects.
    template <>
    class ClassCreator_Factory<MyType>
     : public ClassCreator_Factory_CtorArityDispatcher< MyType, MyTypeCtors >
    {};

    // A JSToNative specialization which makes use of the plumbing
    // installed by ClassCreator. This is required so that
    // CastFromJS<MyType>() will work, as the JS/native binding process
    // requires that we be able to convert (via CastFromJS()) a JS-side
    // MyType object to a C++-side MyType object.
    template <>
    struct JSToNative< MyType > : JSToNative_ClassCreator< MyType >
    {};
    

}

//-----------------------------------
// Ultra-brief ClassCreator demo. See ConvertDemo.?pp for MUCH more.
void bind_MyType( v8::Handle<v8::Object> dest )
{
    typedef cv::ClassCreator<MyType> CC;
    CC & cc(CC::Instance());
    if( cc.IsSealed() ) { // the binding was already initialized.
        cc.AddClassTo( cv::TypeName<MyType>::Value, dest );
        return;
    }
    // Else initialize the bindings...
    cc
        ("destroy", CC::DestroyObjectCallback)
        .AddClassTo( cv::TypeName<MyType>::Value, dest );
}

void test1(cv::Shell & shell)
{
    using namespace v8;
    HandleScope scope;
    bind_MyType( shell.Global() );

    if(1)
    {
        Handle<Function> hf = FunctionTemplate::New(test1_callback)->GetFunction();
        Handle<Value> args[] = {
            Integer::New(3),
            Number::New(5.1),
            Undefined()
        };
        CERR << "Calling binding function...\n";
        TryCatch catcher;
        hf->Call( shell.Context()->Global(), 3, args );
        catcher.Reset();
        CERR << "Returned from binding function.\n";
    }
    else
    {
        BoundNative::SetupBindings( shell.Global() );
    }

    char const * extScr = "./test.js";
    CERR << "Calling external script ["<<extScr<<"]...\n";
    if(1)
    {
        Local<Object> global( shell.Context()->Global() );
        assert( ! global.IsEmpty() );
        Local<Function> jf( Function::Cast( *(global->Get(JSTR("load"))) ) );
        assert( ! jf.IsEmpty() );
        cv::CallForwarder<1>::Call( global, jf, extScr );
    }
    else if(1)
    {
        shell.ExecuteFile( extScr );
    }
    CERR << "Returned from external script\n";
}

#if 1 || defined(_MSVC_VER)
#define TRY_FORK 0
#else
#include <unistd.h>
#define TRY_FORK 1
void js_fork( v8::Handle<v8::Function> f )
{
    pid_t p = ::fork();
    if( p ) return;
    else
    {
        f->Call( f, 0, NULL );
        exit(0);
    }
}
typedef cvv8::PredicatedInCaDispatcher< CVV8_TYPELIST((
    cv::PredicatedInCa< cv::ArgAt_IsFunction<0>, cv::FunctionToInCa<void (v8::Handle<v8::Function>), js_fork> >
))> ForkCallback;
#endif

static int v8_main(int argc, char const * const * argv)
{
    cv::Shell shell(NULL,argc,argv);
    //v8::Handle<v8::Object> global = shell.Global();
    shell.SetupDefaultBindings()
#if 0
        /* the v8 devs occassionally change IdleNotification's signature, which
           breaks type-safe templates... */
        ("gc", cv::FunctionToInCa<bool (),v8::V8::IdleNotification>::Call )
#endif
#if TRY_FORK
        ("fork", ForkCallback::Call)
#endif
    ;
    try
    {
        test1(shell);
    }
    catch(std::exception const & ex)
    {
        CERR << "EXCEPTION: " << ex.what() << '\n';
        return 1;
    }
    catch(...)
    {
        CERR << "UNKNOWN EXCEPTION!\n";
        return 1;
    }
    if(0)
    {
        CERR << "Trying to force GC... This will likely take 5-10 seconds... "
             << "wait for it to see the weak pointer callbacks in action...\n"
#if 0 // this appears to have been fixed...
             << "ON SOME MACHINES THIS IS CRASHING ON ME IN V8 at some point "
             << "on 64-bit builds, but not on 32-bit...\n"
#endif
            ;
        while( !v8::V8::IdleNotification() )
        {
            CERR << "sleeping briefly before trying again...\n";
            do_sleep(1);
        }
        CERR << "v8 says GC is done.\n";
    }
    return 0;
}

int main(int argc, char const * const * argv)
{

    int const rc = v8_main(argc, argv);
    CERR << "Done! rc="<<rc<<'\n';
    return rc;
}

