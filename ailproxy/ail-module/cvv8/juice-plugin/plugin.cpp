#include <v8/juice/juice.h>
#include <v8/juice/plugin.h>
#include "../ConvertDemo.cpp"


static v8::Handle<v8::Value> plugin_init( v8::Handle<v8::Object> dest )
{
    CERR << "PLUGGING IN BoundNative TO V8-JUICE...\n";
    return BoundNative::bindJSClass( dest );
}


V8_JUICE_PLUGIN_STATIC_INIT(plugin_init);
