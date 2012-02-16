/*
    Copyright 2011 Casper Svenning Jensen. All rights reserved.

    Redistribution and use in source and binary forms, with or without modification, are
    permitted provided that the following conditions are met:

    1. Redistributions of source code must retain the above copyright notice, this list of
        conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright notice, this list
        of conditions and the following disclaimer in the documentation and/or other materials
        provided with the distribution.

    THIS SOFTWARE IS PROVIDED BY CASPER SVENNING JENSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
    WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
    FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL CASPER SVENNING JENSEN
    OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
    CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
    SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
    ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
    NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
    ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

    The views and conclusions contained in the software and documentation are those of the
    authors and should not be interpreted as representing official policies, either expressed
    or implied, of Casper Svenning Jensen
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

int construct_ail(ail_t* ail, const char* raw_ail);
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

#endif // AIL_READER_H
