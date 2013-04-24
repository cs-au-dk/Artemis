#!/bin/bash
########################################################################
# Generates code for the the # v8::convert API (and friends).
count=${1-0}

test "$count" -gt 0 || {
    echo "Usage: $0 NUMBER (>=1) COMMAND(s)"
cat <<EOF
Commands:
  CtorForwarder
  MethodSignature
  ConstMethodSignature
  MethodForwarder
  FunctionForwarder
  CallForwarder
EOF
    echo "Generates specializations for operations taking exactly NUMBER arguments."
    exit 1
}
shift

ValHnd="v8::Handle<v8::Value>"
aTDecl="" # typename A0, typename A1,...
aTParam="" # A0, A1 ...
aFDecl="" # A0 a0, A1 a1, ...
aNToJSCalls="" # CastToJS(a0), CastToJS(a1)...
castCalls="" # CastFromJS<A0>(argv[0]), ...
castTypedefs="" # typedef ArgCaster<A#> AC#, ...
castInits="" # AC# ac#; ...
callArgs="" # a0, ... aN
sigTypeDecls="" # SignatureType::ArgType# A#...
unlocker="V8Unlocker<UnlockV8> const & unlocker( V8Unlocker<UnlockV8>() );"
at=0

########################################################
# must be called first to populate the shared vars
function makeLists()
{
    for (( at = 0; at < count; at = at + 1)); do
    #echo "at=$at"
	local AT="A${at}"
    local arg="a${at}"
	aTDecl="${aTDecl} typename ${AT}"
	aTParam="${aTParam} ${AT}"
    aFDecl="${aFDecl} ${AT} ${arg}" # A0 a0, A1 a1, ...
    aNToJSCalls="${aNToJSCalls} CastToJS(${arg})" # CastToJS(a0), CastToJS(a1)...

	callArgs="${callArgs}${arg}"
        #sigTypeDecls="${sigTypeDecls}typedef typename SignatureType::ArgType${at} ${AT};"
        sigTypeDecls="${sigTypeDecls}typedef typename sl::At< ${at}, Signature<Sig> >::Type ${AT};\n"
	#castCalls="${castCalls} CastFromJS< ${AT} >(argv[${at}])"
        castTypedefs="${castTypedefs} typedef ArgCaster<${AT}> AC${at};\n"
        #castInits="${castInits} AC${at} ac${at};"
        #castCalls="${castCalls} ac${at}.ToNative(argv[${at}])"
        castInits="${castInits} AC${at} ac${at}; A${at} arg${at}(ac${at}.ToNative(argv[${at}]));\n"
        castCalls="${castCalls} arg${at}"
	test $at -ne $((count-1)) && {
	    aTDecl="${aTDecl},"
	    aTParam="${aTParam},"
	    castCalls="${castCalls},"
        callArgs="${callArgs},"
        aFDecl="${aFDecl},"
        aNToJSCalls="${aNToJSCalls},"
	}
    done
    #tmplsig="${tmplsig} RV (WrappedType::*Func)(${aTParam})";
    castOps="${castTypedefs} ${castInits}"
}

function mycat()
{
    perl -pe 's|\\n|\n\t\t|g'
}

#######################################################
# Creates CtorForwarder specializations.
function makeCtorForwarder()
{

    local err_too_few_args="CtorForwarder<T,${count}>::Ctor() expects at least ${count} JS arguments!"
    local err_exception="CtorForwarder<T,${count}>::Ctor() Native ctor threw an unknown native exception type!"

    mycat <<EOF
namespace Detail {
template <typename Sig>
struct CtorForwarderProxy<Sig,${count}>
{
    enum { Arity = ${count} };
    typedef typename Signature<Sig>::ReturnType ReturnType;
    static ReturnType Call( v8::Arguments const & argv )
    {
        if( argv.Length() < Arity )
        {
            throw std::range_error("${err_too_few_args}");
        }
        else
        {
            ${sigTypeDecls}
            ${castTypedefs}
            ${castInits}
            typedef typename TypeInfo<ReturnType>::Type Type;
            return new Type( ${castCalls} );
        }
    }
};
}
EOF

} # makeCtorForwarder


########################################################################
# Create MethodSignature<> and friends...
function makeMethodSignature()
{
    mycat <<EOF
template <typename T, typename RV, ${aTDecl} >
struct MethodSignature< T, RV (${aTParam}) > : Signature< RV (T::*)(${aTParam}) >
{
};
template <typename T, typename RV, ${aTDecl} >
struct MethodSignature< T, RV (*)(${aTParam}) > : MethodSignature< T, RV (${aTParam}) >
{
};

template <typename T, typename RV, ${aTDecl} >
struct MethodSignature< T, RV (T::*)(${aTParam}) > :
    MethodSignature< T, RV (${aTParam}) >
{};

template <typename T, typename RV, ${aTDecl} >
struct MethodSignature< T const, RV (${aTParam}) > :
    ConstMethodSignature< T, RV (${aTParam}) >
{};

template <typename T, typename RV, ${aTDecl} >
struct MethodSignature< T const, RV (T::*)(${aTParam}) > :
    MethodSignature< T const, RV (${aTParam}) >
{};

#if 1 // msvc? Apparently this works.
template <typename T, typename RV, ${aTDecl} >
struct MethodSignature< T const, RV (T::*)(${aTParam}) const > :
    MethodSignature< T const, RV (${aTParam}) >
{};
#endif


EOF
}

########################################################################
# Create ConstMethodSignature<> and friends...
# TODO: move this into makeMethodSignature.
function makeConstMethodSignature()
{
    mycat <<EOF
template <typename T, typename RV, ${aTDecl} >
struct ConstMethodSignature< T, RV (${aTParam}) > : Signature< RV (T::*)(${aTParam}) const >
{
};
template <typename T, typename RV, ${aTDecl} >
struct ConstMethodSignature< T, RV (T::*)(${aTParam}) const > :
    ConstMethodSignature< T, RV (${aTParam}) >
{};
EOF

}


########################################################################
# Generates FunctionForwarder<>
function makeFunctionForwarder()
{

mycat <<EOF
namespace Detail {
    template <typename Sig, bool UnlockV8>
    struct FunctionForwarder<${count},Sig,UnlockV8> : FunctionSignature<Sig>
    {
        typedef FunctionSignature<Sig> SignatureType;
        typedef char AssertArity[ (${count} == sl::Arity<SignatureType>::Value) ? 1 : -1];
        typedef typename SignatureType::FunctionType FunctionType;
        typedef typename SignatureType::ReturnType ReturnType;
        static ReturnType CallNative( FunctionType func, v8::Arguments const & argv )
        {
            ${sigTypeDecls}
            ${castTypedefs}
            ${castInits}
            ${unlocker}
            return (ReturnType)(*func)( ${castCalls} );
        }
        static ${ValHnd} Call( FunctionType func, v8::Arguments const & argv )
        {
            return CastToJS( CallNative( func, argv ) );
        }
    };

    template <typename Sig, bool UnlockV8>
    struct FunctionForwarderVoid<${count},Sig,UnlockV8> : FunctionSignature<Sig>
    {
        typedef FunctionSignature<Sig> SignatureType;
        typedef char AssertArity[ (${count} == sl::Arity<SignatureType>::Value) ? 1 : -1];
        typedef typename SignatureType::FunctionType FunctionType;
        typedef typename SignatureType::ReturnType ReturnType;
        static ReturnType CallNative( FunctionType func, v8::Arguments const & argv )
        {
            ${sigTypeDecls}
            ${castTypedefs}
            ${castInits}
            ${unlocker}
            return (ReturnType)(*func)( ${castCalls} );
        }
        static ${ValHnd} Call( FunctionType func, v8::Arguments const & argv )
        {
            CallNative( func, argv );
            return v8::Undefined();
        }
    };
}
EOF

}

########################################################################
# Generates MethodForwarder<>
function makeMethodForwarder_impl()
{
    local class=MethodForwarder
    local parent=MethodSignature
    local constness=""
    if [[ "x$1" = "xconst" ]]; then
        parent=ConstMethodSignature
        class=ConstMethodForwarder
        constness="const"
    fi
mycat <<EOF
namespace Detail {
    template <typename T, typename Sig, bool UnlockV8>
    struct ${class}<T, ${count},Sig, UnlockV8> : ${parent}<T,Sig>
    {
        typedef ${parent}<T,Sig> SignatureType;
        typedef char AssertArity[ (${count} == sl::Arity<SignatureType>::Value) ? 1 : -1];
        typedef typename SignatureType::FunctionType FunctionType;
        typedef typename SignatureType::ReturnType ReturnType;
        static ReturnType CallNative( T ${constness} & self, FunctionType func, v8::Arguments const & argv )
        {
            ${sigTypeDecls}
            ${castTypedefs}
            ${castInits}
            ${unlocker}
            return (ReturnType)(self.*func)( ${castCalls} );
        }
        static ${ValHnd} Call( T ${constness} & self, FunctionType func, v8::Arguments const & argv )
        {
            try { return CastToJS( CallNative( self, func, argv ) ); }
            HANDLE_PROPAGATE_EXCEPTION;
        }
        static ReturnType CallNative( FunctionType func, v8::Arguments const & argv )
        {
            T ${constness} * self = CastFromJS<T>(argv.This());
            if( ! self ) throw MissingThisExceptionT<T>();
            return (ReturnType)CallNative(*self, func, argv);
        }
        static ${ValHnd} Call( FunctionType func, v8::Arguments const & argv )
        {
            try { return CastToJS( CallNative(func, argv) ); }
            HANDLE_PROPAGATE_EXCEPTION;
        }
    };

    template <typename T, typename Sig, bool UnlockV8>
    struct ${class}Void<T, ${count},Sig, UnlockV8> : ${parent}<T,Sig>
    {
        typedef ${parent}<T,Sig> SignatureType;
        typedef char AssertArity[ (${count} == sl::Arity<SignatureType>::Value) ? 1 : -1];
        typedef typename SignatureType::FunctionType FunctionType;
        typedef typename SignatureType::ReturnType ReturnType;
        static ReturnType CallNative( T ${constness} & self, FunctionType func, v8::Arguments const & argv )
        {
            ${sigTypeDecls}
            ${castTypedefs}
            ${castInits}
            ${unlocker}
            return (ReturnType)(self.*func)( ${castCalls} );
        }
        static ${ValHnd} Call( T ${constness} & self, FunctionType func, v8::Arguments const & argv )
        {
            try
            {
                CallNative( self, func, argv );
                return v8::Undefined();
            }
            HANDLE_PROPAGATE_EXCEPTION;
        }
        static ReturnType CallNative( FunctionType func, v8::Arguments const & argv )
        {
            T ${constness} * self = CastFromJS<T>(argv.This());
            if( ! self ) throw MissingThisExceptionT<T>();
            return (ReturnType)CallNative(*self, func, argv);
        }
        static ${ValHnd} Call( FunctionType func, v8::Arguments const & argv )
        {
            try
            {
                CallNative(func, argv);
                return v8::Undefined();
            }
            HANDLE_PROPAGATE_EXCEPTION;
        }
    };
}
EOF
}

function makeMethodForwarder()
{
    makeMethodForwarder_impl
    makeMethodForwarder_impl const
}

function makeCallForwarder()
{
mycat <<EOF
//! Specialization for ${count}-arity calls.
template <>
struct CallForwarder<${count}>
{
    template <${aTDecl}>
    static v8::Handle<v8::Value> Call( v8::Handle<v8::Object> const & self,
                                       v8::Handle<v8::Function> const & func,
                                       ${aFDecl}
                                     )
    {
        v8::Handle<v8::Value> args[] = {
            ${aNToJSCalls}
        };
        return (self.IsEmpty() || func.IsEmpty())
            ? Toss("Illegal argument: empty v8::Handle<>.")
            : func->Call(self, sizeof(args)/sizeof(args[0]), args);
    }
    template <${aTDecl}>
    static v8::Handle<v8::Value> Call( v8::Handle<v8::Function> const & func,
                                       ${aFDecl}
                                     )
    {
        return Call( func, func, ${callArgs} );
    }

};
EOF
}

##########################################################
# here we go...
makeLists

for command in $@; do
case $command in
    *Signature|*Forwarder|CtorForwarder)
	make${command} || {
        rc=$?
        echo "make${command} failed with rc $rc" 1>&2
        exit $rc
    }
	;;
    *)
	echo "Unhandled command: ${command}"
	exit 2
    ;;
esac
done
