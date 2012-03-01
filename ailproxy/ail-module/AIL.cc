#define BUILDING_NODE_EXTENSION
#include <node.h>
#include "reader.h"

using namespace v8;

void InitAll(Handle<Object> target) {
  Reader::Init(target);
}

NODE_MODULE(AIL, InitAll)
