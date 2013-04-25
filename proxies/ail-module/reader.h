#ifndef READER_H
#define READER_H

#include <node.h>

extern "C" {
#include "./ailreader/src/ail.h"
}

class Reader : public node::ObjectWrap {
 public:
  static void Init(v8::Handle<v8::Object> target);

 private:
  Reader();
  ~Reader();

  static v8::Handle<v8::Value> New(const v8::Arguments& args);
  static v8::Handle<v8::Value> GenerateResponse(const v8::Arguments& args);

  ail_t m_ail;

};
#endif 
