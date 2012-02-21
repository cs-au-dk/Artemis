#include <node.h>
#include <string.h>
#include <string>
#include <fstream>

extern "C" {
#include "ailreader/src/ail.h"
}

#include "cvv8/include/cvv8/v8-convert.hpp"


using namespace v8;

Handle<Value> generate_response_permutation(const Arguments& args) {
    HandleScope scope;

    // Test and Coerce arguments
    if (args.Length() != 4) {
        return ThrowException(
            Exception::TypeError(String::New("Proper use: generate_response_permutation(string requestURL, string pathToJSONSchema, ...)"))
        );
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

    if (!args[3]->IsString()) {
       return ThrowException(Exception::TypeError(String::New("Illegal argument: ailschema")));
    }

    std::vector<std::string> kwargs = cvv8::CastFromJS<std::vector<std::string> >(args[1]);
    std::vector<std::string> vwargs = cvv8::CastFromJS<std::vector<std::string> >(args[2]);

    if (kwargs.size() != vwargs.size()) {
      Exception::TypeError(String::New("Proper use: generate_response_permutation(string requestURL, string pathToJSONSchema, ...)"));  
    }
    
    std::vector<std::string> opArgs = cvv8::CastFromJS<std::vector<std::string> >(args[0]);
    std::string ailSchemaPath = cvv8::CastFromJS<std::string>(args[3]);
    
    std::ifstream ifs(ailSchemaPath.data());
    std::string rawAILSchema((std::istreambuf_iterator<char>(ifs)), std::istreambuf_iterator<char>());

    // Construct AIL
    ail_t AIL;

    char * schema_folder;
    get_schema_folder(ailSchemaPath.c_str(), &schema_folder);

    if(construct_ail(&AIL, rawAILSchema.data(), schema_folder)) {
      return ThrowException(Exception::TypeError(String::New("Error reading AIL specification")));
    }

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
    
    if(get_operation_for_request(AIL, &operation, operationArgs, \
        opArgs.size(), keywordArgs, valueArgs, kwargs.size()) != 0){
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

void RegisterModule(Handle<Object> target) {
    target->Set(String::NewSymbol("generate_response_permutation"),
        FunctionTemplate::New(generate_response_permutation)->GetFunction());
}

NODE_MODULE(ailreader, RegisterModule);
