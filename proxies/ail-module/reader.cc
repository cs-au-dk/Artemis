/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#define BUILDING_NODE_EXTENSION
#include <node.h>
#include <string>
#include <fstream>
#include "cvv8/include/cvv8/v8-convert.hpp"

#include "reader.h"

using namespace v8;

Reader::Reader() {};
Reader::~Reader() {};

void Reader::Init(Handle<Object> target) {
  Local<FunctionTemplate> templ = FunctionTemplate::New(New);
  templ->SetClassName(String::NewSymbol("Reader"));
  templ->InstanceTemplate()->SetInternalFieldCount(1);
  
  templ->PrototypeTemplate()->Set(String::NewSymbol("generateResponse"), FunctionTemplate::New(GenerateResponse)->GetFunction());

  Persistent<Function> constructor = Persistent<Function>::New(templ->GetFunction());
  target->Set(String::NewSymbol("Reader"), constructor);
}

Handle<Value> Reader::New(const Arguments& args) {
  HandleScope scope;
  
  // Test and Coerce arguments
  if (args.Length() != 1) {
    return ThrowException(Exception::TypeError(String::New("AIL Constructor: Illegal Argument")));
  }
  
  if (!args[0]->IsString()) {
    return ThrowException(Exception::TypeError(String::New("Illegal argument: ailschema")));
  }

  std::string ailSchemaPath = cvv8::CastFromJS<std::string>(args[0]);
    
  std::ifstream ifs(ailSchemaPath.data());
  std::string rawAILSchema((std::istreambuf_iterator<char>(ifs)), std::istreambuf_iterator<char>());

  // Construct AIL
  ail_t ail;

  char* schema_folder;
  get_schema_folder(ailSchemaPath.c_str(), &schema_folder);

  if(construct_ail(&ail, rawAILSchema.data(), schema_folder)) {
    return ThrowException(Exception::TypeError(String::New("Error reading AIL specification")));
  }

  Reader* reader = new Reader();
  reader->m_ail = ail;
  reader->Wrap(args.This());

  return args.This();
}


Handle<Value> Reader::GenerateResponse(const Arguments& args) {
  HandleScope scope;
  Reader* reader = ObjectWrap::Unwrap<Reader>(args.This());
  
  // Test and Coerce arguments
  if (args.Length() != 3) {
    return ThrowException(Exception::TypeError(String::New("Proper use: generate_response_permutation()")));
  }
    
  if (!args[0]->IsArray()) {
    return ThrowException(Exception::TypeError(String::New("Illegal argument: path")));
  }

  if (!args[1]->IsArray()) {
    return ThrowException(Exception::TypeError(String::New("Illegal argument: kwargs")));
  }

  if (!args[2]->IsArray()) {
    return ThrowException(Exception::TypeError(String::New("Illegal argument: vwargs")));
  }

  std::vector<std::string> kwargs = cvv8::CastFromJS<std::vector<std::string> >(args[1]);
  std::vector<std::string> vwargs = cvv8::CastFromJS<std::vector<std::string> >(args[2]);
    
  if (kwargs.size() != vwargs.size()) {
    Exception::TypeError(String::New("Proper use: generate_response_permutation(string requestURL, string pathToJSONSchema, ...)"));  
    }
    
  std::vector<std::string> opArgs = cvv8::CastFromJS<std::vector<std::string> >(args[0]);
    
  // Test for relevant operation
  ail_operation_t operation;
    
  char* operationArgs[opArgs.size()];
  for(int i = 0; i < opArgs.size(); ++i) {
    operationArgs[i] = const_cast<char*>(opArgs.at(i).data());
  }
    
  char* keywordArgs[kwargs.size()];
  for(int i = 0; i < kwargs.size(); ++i) {
    keywordArgs[i] = const_cast<char*>(kwargs.at(i).data());
  }
    
  char* valueArgs[vwargs.size()];
  for(int i = 0; i < vwargs.size(); ++i) {
      valueArgs[i] = const_cast<char*>(vwargs.at(i).data());
  }
    
  if(get_operation_for_request(reader->m_ail, &operation, operationArgs, opArgs.size(), keywordArgs, valueArgs, kwargs.size()) != 0){
    return v8::Undefined();
  }

  // Generate and return response

  ail_response_t response;

  if(generate_response_permutation(operation, &response) != 0) {
    return ThrowException(Exception::TypeError(String::New("Something went wrong generating response")));
  }
    
  std::string buffer;
    
  //buffer.append("HTTP/1.1 200 OK\n\n");
    
  struct response_chunk * current = response;
  while (current != NULL) {
    buffer.append((current->chunk));
    current = current->next;
  }
  
  return scope.Close(String::New(buffer.c_str()));
}
