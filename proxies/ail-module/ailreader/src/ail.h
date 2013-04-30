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

#include <yajl/yajl_tree.h>

#ifndef AIL_READER_H
#define AIL_READER_H

struct ail_schema {
    struct ail_schema * next;
    char * file_name;
    yajl_val payload;
};

typedef struct ail_schema * ail_schema_t;

struct ail_url_fragment {
    
    struct ail_url_fragment * next;
    char * text;

};

typedef struct ail_url_fragment * ail_url_fragment_t;

struct ail_url_kwarg {
    
    struct ail_url_kwarg * next;

    char * keyword;
    char * value;

};

typedef struct ail_url_kwarg * ail_url_kwarg_t;

struct ail_operation {
    struct ail_operation * next;

    ail_url_fragment_t fragments;
    ail_url_kwarg_t kwargs;
    ail_schema_t schemas;
};

typedef struct ail_operation * ail_operation_t;

struct ail {
    char * domain;

    ail_operation_t operations;
    unsigned int num_operations;
};

typedef struct ail * ail_t;

struct response_chunk {
    struct response_chunk * next;
    char * chunk;
};

typedef struct response_chunk * ail_response_t;

int construct_ail(ail_t* ail, const char* raw_ail, char * schema_folder);
int allocate_operation(ail_operation_t * operation);
int allocate_schema(ail_schema_t * schema);
int allocate_url_fragment(ail_url_fragment_t * fragment);
int allocate_url_kwarg(ail_url_kwarg_t * kwarg);

int load_schema(ail_schema_t schema);

int get_operation_for_request(const ail_t ail, ail_operation_t * operation, \
                              char ** args, int argc, char** kwargs, char** vwargs, int kwargc);

int generate_response_permutation(const ail_operation_t operation, ail_response_t* response);

int operationcmp(const ail_operation_t operation, char** args, int argc, char** kwargs, char** vwargs, int kwargc);
void print_response(const ail_response_t);

void get_schema_folder(const char * source, char ** schema_folder);

#endif // AIL_READER_H
