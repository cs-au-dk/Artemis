/**
   Test/demo code for the cvv8 API.
   
*/
#if defined(NDEBUG)
#  undef NDEBUG  // force assert() to work
#endif

#include <cassert>
#include <v8.h>

/*
  The following macros and typedefs are only for the convenience
  of the test code author, and do not necessarily reflect
  best practices.
*/
#include "cvv8/v8-convert.hpp"
#include "cvv8/NativeToJSMap.hpp"
#ifndef CERR
#include <iostream> /* only for debuggering */
#define CERR std::cerr << __FILE__ << ":" << std::dec << __LINE__ << ":" << __FUNCTION__<< "(): "
#endif
#define JSTR(X) v8::String::New(X)
namespace cv = cvv8;
//typedef v8::Handle<v8::Value> ValueHandle;
#define ValueHandle v8::Handle<v8::Value>

void doFoo();
void doNothing();
int doSomething(int x);
ValueHandle sampleCallback( v8::Arguments const & argv );

/**
   Class to bind to JS space.
*/
struct BoundNative
{
public:
    int publicInt;
    static int publicStaticInt;
    BoundNative(int val = 42)
        : publicInt(val)
    {
        CERR << "@"<<(void const *)this<<" is constructing.\n";
    }
    /*
      dtor MUST be virtual if we want to subclass this type, or the
      bindings mechanism will only call the base-most dtor at cleanup
      time. (Been there, debuggered that.)
     */
    virtual ~BoundNative()
    {
        CERR << "@"<<(void const *)this<<" is destructing.\n";
    }

    void puts(char const *str) const
    {
        CERR << "@"<<(void const *)this<<"->puts(\""<<str<<"\")\n";
    }
    
    void doFoo()
    {
        assert( 0 != this )/*YES, i have seen that happen during initial development. */;
        CERR << "@"<<(void const *)this<<"->doFoo()!\n";
    }
    void doFoo1(int i)
    {
        assert( 0 != this );
        CERR << "@"<<(void const *)this<<"->doFoo1("<<i<<")!\n";
    }
    void doFooConst() const
    {
        CERR << "@"<<(void const *)this<<"->doFooConst()!\n";
    }
    int doFooConstInt() const
    {
        CERR << "@"<<(void const *)this<<"->doFooConstInt()!\n";
        return 7;
    }

    void nativeParam( BoundNative const * other )
    {
        CERR << '@'<<(void const *)this<<"->nativeParam(@"<<(void const *)other<<")\n";
    }
    
    void nativeParamRef( BoundNative & other )
    {
        CERR << '@'<<(void const *)this<<"->nativeParam(@"<<(void const *)&other<<")\n";
    }

    void nativeParamConstRef( BoundNative const & other ) const
    {
        CERR << '@'<<(void const *)this<<"->nativeParam(@"<<(void const *)&other<<")\n";
    }

#if 1
    /**
       Binding his to JS requires that CastToJS<T>() work so that we
       can cast the return type. No generic impl of CastToJS() is
       possible, and getting it to work requires extra tooling,
       normally in the class binding code, to map native objects
       to their JS counterparts.
    */
    BoundNative * nativeReturn()
    {
        CERR << '@'<<(void const *)this<<"->nativeReturn()\n";
        return this;
    }
    BoundNative const * nativeReturnConst() const
    {
        CERR << '@'<<(void const *)this<<"->nativeReturnConst()\n";
        return this;
    }
    
    BoundNative & nativeReturnRef()
    {
        CERR << '@'<<(void const *)this<<"->nativeReturnRef()\n";
        return *this;
    }
    BoundNative const & nativeReturnConstRef() const
    {
        CERR << '@'<<(void const *)this<<"->nativeReturnConstRef()\n";
        return *this;
    }
#endif
    double doFoo2(int i, double x)
    {
        assert( 0 != this );
        CERR << "@"<<(void const *)this<<"->doFoo2("<<i<<", "<<x<<")!\n";
        return x * i;
    }

    double operator()( int i, double x ) const
    {
        assert( 0 != this );
        CERR << "@"<<(void const *)this<<"->operator()("<<i<<", "<<x<<")!\n";
        return x * i;
    }
    ValueHandle invo( v8::Arguments const & )
    {
        assert( 0 != this );
        CERR << "@"<<(void const *)this<<"->invo()  (non-static, non-const)\n";
        return ValueHandle();
    }
    int invoInt( v8::Arguments const & )
    {
        assert( 0 != this );
        CERR << "@"<<(void const *)this<<"->invoInt()  (non-static, non-const)\n";
        return 3;
    }
    int invoIntConst( v8::Arguments const & ) const
    {
        assert( 0 != this );
        CERR << "@"<<(void const *)this<<"->invoIntConst()  (non-static, const)\n";
        return 7;
    }
    ValueHandle invo( v8::Arguments const & ) const
    {
        assert( 0 != this );
        CERR << "@"<<(void const *)this<<"->invo()  (const)\n";
        return ValueHandle();
    }

    static ValueHandle invoStatic( v8::Arguments const & )
    {
        CERR << "invo() (static)\n";
        return ValueHandle();
    }

    /**
       Adds a JS binding of this class, called "BoundNative", to the given
       object. It also installs the BoundSubNative class.
       Throws a native exception on error.

    */
    static void SetupBindings( v8::Handle<v8::Object> const & dest );

    int getInt() const
    {
        return this->publicInt;
    }
    int getIntNonConst()
    {
        return this->publicInt;
    }

    void setInt(int v)
    {
        this->publicInt = v;
    }


    void overload()
    {
        CERR << "@"<<(void const *)this<<"->overload0()\n";
    }
    void overload(int a)
    {
        CERR << "@"<<(void const *)this<<"->overload1("<<a<<")\n";
    }
    void overload(int a,int b)
    {
        CERR << "@"<<(void const *)this<<"->overload2("<<a<<", "<<b<<")\n";
    }
    void overload( v8::Arguments const & argv )
    {
        CERR << "@"<<(void const *)this<<"->overloadN("<<argv.Length()<<" arg(s))\n";
    }

    BoundNative * self() { return this; }
    BoundNative & selfRef() { return *this; }
    BoundNative const * self() const { return this; }
    BoundNative const & selfRefConst() const { return *this; }
    
    
    int throwingGetter() const { throw std::runtime_error("You called throwingGetter()! What did you expect?"); }
    void throwingSetter(int) { throw std::runtime_error("You called throwingSetter()! What did you expect?"); }

    v8::Handle<v8::Value> operator<<( v8::Handle<v8::Value> const & t ) const
    {
        return t;
    }

};

// BoundNative Ctors we want to bind to v8 (there are several other ways to do this):
typedef cv::Signature<BoundNative (
    cv::CtorForwarder<BoundNative *()>,
    cv::CtorForwarder<BoundNative *(int)>
)> BoundNativeCtors;
/**
   A class for testing/demonstrating subclassing of bound types.
 */
struct BoundSubNative : public BoundNative
{
    BoundSubNative()
    {
        CERR << "@"<<(void const *)this<<" is constructing\n";
    }
    virtual ~BoundSubNative()
    {
        CERR << "@"<<(void const *)this<<" is destructing\n";
    }

    void subFunc() const
    {
        CERR << "@"<<(void const *)this<<"->subFunc()\n";
    }

    /**
       See the demo impl code for how we override BoundNative'
       toString with this one.
     */
    v8::Handle<v8::Value> toString() const
    {
        return cv::StringBuffer() << "[object BoundSubNative@"<<(void const *)this<<"]";
    }
    
    struct NonBoundType
    {};
    
    /**
        This function shows how we can use ToInCaVoid<> (and friends)
        to bind a function which returns a type we cannot cast
        back to JS. Those bindings do not instantiate (in the C++
        templates sense of the word) the conversion of the return
        type, whereas ToInCa<> (and friends) would fail to bind
        this (probably with a link-time error).
    */
    NonBoundType & nonBoundNative()
    {
        static NonBoundType bob = NonBoundType();
        return bob;
    }
    NonBoundType const & nonBoundNative() const
    {
        static const NonBoundType bob = NonBoundType();
        return bob;
    }

};


/**
   The following code is mostly here for use with ClassCreator<>, a
   class-binding mechanism which is demonstrated in
   ConvertDemo.cpp. It mostly shows how to use ClassCreator<> policies
   to customize the ClassCreator bindings for a particular class.
*/
namespace cvv8 {

    /**
        Optional: used mainly by error reporting code but can also be used
        as a convenient place to store the type's JS name (which often differs
        from its C++ name).
    */
    CVV8_TypeName_DECL((BoundNative));
    CVV8_TypeName_DECL((BoundSubNative));

#if 0 // replaced by CVV8_TypeName_DECL()
    //! Optional: used by some error reporting code.
    template <>
    struct TypeName< BoundNative >
    {
        static char const * Value;
    };
    //! Optional: used by some error reporting code.
    template <>
    struct TypeName< BoundSubNative >
    {
        static char const * Value;
    };
#endif
    /**
        This is required by subclasses for certain constellations of internal
        fields/type-safety options. It is always optional for base classes,
        since the default implementation is reasonable for non-subclassing
        cases.
    */
    template <>
    struct ClassCreator_TypeID<BoundSubNative> : ClassCreator_TypeID<BoundNative>
    {};

    /**
       Optional: customize internal field layout for the JS class.

       When subclassing bound types from other bound types, all must
       have the same layout (and possibly the same base internal type ID)
       or native object lookups won't work properly. To do this, wrapped
       subclasses should subclass their ClassCreator_InternalFields from the
       parent class' ClassCreator_InternalFields.
    */
    template <>
    struct ClassCreator_InternalFields<BoundNative>
        // Use default settings for additional type-safety at runtime:
        //: ClassCreator_InternalFields_Base<BoundNative>
        // Add a number of interal fields for your own use, optionally
        // moving the TypeID and native object fields:
        : ClassCreator_InternalFields_Base<BoundNative,8/*# of fields*/,4/*TypeID field*/,7/*native object field*/>
        // Use a negative 2nd value to disable the extra type-safety checking:
        //: ClassCreator_InternalFields_Base<BoundNative,1,-1,0>
    {
    };
    /**
       Required only when subclassing BoundNative and customizing
       ClassCreator_InternalFields<BoundNative>.
       
       The BoundSubNative bound type requires the same internal field layout
       as its parent class, and we do that by subclassing the parent class'
       InternalFields policy. If we never customize the field layout for our
       type then even subclasses can use the default implementation of this
       policy (i.e. they need not explicitly specialize it).
    */
    template <>
    struct ClassCreator_InternalFields<BoundSubNative>
        : ClassCreator_InternalFields<BoundNative>
    {
    };

    /**
      This policy class is required unless you just want to bind to 
      the default constructor. It creates native objects for the 
      underlying binding code.
    */
    template <>
    class ClassCreator_Factory<BoundNative>
    {
    public:
        typedef BoundNative * ReturnType;
        static ReturnType Create( v8::Persistent<v8::Object> & jsSelf, v8::Arguments const & argv );
        static void Delete( ReturnType obj );
    };

    template <>
    class ClassCreator_Factory<BoundSubNative>
    {
    public:
        typedef BoundSubNative * ReturnType;
        static ReturnType Create( v8::Persistent<v8::Object> & jsSelf, v8::Arguments const & argv );
        static void Delete( ReturnType obj );
    };

    /**
        Normally optional, but must be set to true if JS code should be
        allowed to subclass the bound type. If subclassing will never
        be used, you can potentially optimize out a few operations by
        subclassing Opt_Bool<false> here.

        Note that the default setting of this policy is true (search
        prototypes).        
    */
    template <>
    struct ClassCreator_SearchPrototypeForThis<BoundNative> : Opt_Bool<true>
    {};
    template <>
    struct ClassCreator_SearchPrototypeForThis<BoundSubNative> : ClassCreator_SearchPrototypeForThis<BoundNative>
    {};

    /**
       Optional: enable function calls to BoundNative() to work like a
       constructor call. Without this, calling BoundNative() without
       'new' will cause a JS-side exception.
    */
    template <>
    struct ClassCreator_AllowCtorWithoutNew<BoundNative> : Opt_Bool<true>
    {};

    /**
        Unlike some other policies, the AllowCtorWithoutNew policy for
        subclasses _may_ differ from their parent class.
    */
    template <>
    struct ClassCreator_AllowCtorWithoutNew<BoundSubNative>
        : ClassCreator_AllowCtorWithoutNew<BoundNative>
    {};

    /**
       Required specialization so that the conversion API can derive
       the native 'this' object from v8::Arguments::This() and from
       function arguments of our bound type.

       This implementation works by using the plumbing installed
       by ClassCreator.
    */
    template <>
    struct JSToNative<BoundNative>
        : JSToNative_ClassCreator<BoundNative>
    {};

    /**
        Native-to-JS conversion. This conversion is only possible when
        we explicitly add support to the class-binding code to add
        the necessary binding metadata. Alternately, if the bound class
        contains v8-defined data types, e.g. a Handle<Object> referring
        to itself then implementing NativeToJS is easy to do - just
        return the handle held by the native.
        
        In this example we're using the NativeToJSMap helper code to 
        plug in/unplug our bindings during native object 
        construction/destruction via the the ClassCreator's factory 
        policy (ClassCreator_Factory<BoundNative>).        
    */
    template <>
    struct NativeToJS<BoundNative>
        :  NativeToJSMap<BoundNative>::NativeToJSImpl
    {};

    /**
       Required: Install js-to-native conversion for BoundSubNative.
    */
    template <>
    struct JSToNative<BoundSubNative>
        : JSToNative_ClassCreator<BoundSubNative>
    {};

    /**
       Optional: Install native-to-js conversion for BoundSubNative. See
       NativeToJSMap<BoundNative> for more details. If client C++ code will
       not directly reference the subtype by name, but instead only uses the
       base type(s), this specialization is not needed.
    */
    template <>
    struct NativeToJS<BoundSubNative>
        :  NativeToJSMap<BoundSubNative>::NativeToJSImpl
    {};

}
