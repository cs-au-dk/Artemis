//
// Copyright 2012 Aarhus University
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

// lemon parser specification

%include {

	#include <stdio.h>
	#include <stdlib.h>
	#include <assert.h>
	#include <string.h>

	#include "scanner.h"
	#include "parser.h"
	#include "ail.h"

	ail_t parsed_ail;
}

// DIRECTIVES

%token_type {scanner_token*}

%default_type {void*}
%type operation {ail_operation_t}
%type schemas {ail_schema_t}
%type schemalist {ail_schema_t}
%type url {ail_url_fragment_t}
%type arguments {ail_url_kwarg_t}
%type argumentlist {ail_url_kwarg_t}

%syntax_error {printf("\n\n!!! SYNTAX ERROR !!!\n\n");}

// GRAMMAR

ail ::= TOKEN_AIL_START TOKEN_DOMAIN(DOMAIN) operations. { parsed_ail->domain = DOMAIN->data.string; }
ail ::= TOKEN_AIL_START TOKEN_DOMAIN(DOMAIN). { parsed_ail->domain = DOMAIN->data.string; }
ail ::= TOKEN_AIL_START. {  }

operations ::= operation(OPERATION) operations. { 
	OPERATION->next = parsed_ail->operations; 
	parsed_ail->operations = OPERATION; 
	parsed_ail->num_operations++; 
} // COPY DOWN

operations ::= operation(OPERATION). { 
	OPERATION->next = parsed_ail->operations; 
	parsed_ail->operations = OPERATION; 
	parsed_ail->num_operations++; 
} // COPY OF ABOVE

operation(OPERATION) ::= TOKEN_METHOD url(FRAGMENT) TOKEN_ROUND_BRACKET_OPEN arguments(KWARGS) TOKEN_ROUND_BRACKET_CLOSE TOKEN_COLON schemas(SCHEMAS). {
	allocate_operation(&OPERATION);
	OPERATION->fragments = FRAGMENT;
	OPERATION->kwargs = KWARGS;
	OPERATION->schemas = SCHEMAS;
}

url(PFRAGMENT) ::= TOKEN_STRING(TOKEN) TOKEN_SLASH url(FRAGMENT). {
	allocate_url_fragment(&PFRAGMENT);
	PFRAGMENT->text = TOKEN->data.string;
	PFRAGMENT->next = FRAGMENT;
}
url(FRAGMENT) ::= TOKEN_STRING(TOKEN). {
	allocate_url_fragment(&FRAGMENT);
	FRAGMENT->text = TOKEN->data.string;
}

arguments(PKWARGS) ::= argumentlist(KWARGS). {
	PKWARGS = KWARGS;
}
arguments(KWARGS) ::= . {
	KWARGS = NULL;
}

argumentlist(PKWARGS) ::= TOKEN_STRING(KEYWORD) TOKEN_COLON TOKEN_STRING(VALUE) TOKEN_COMMA argumentlist(KWARGS). {
	allocate_url_kwarg(&PKWARGS);
	PKWARGS->keyword = KEYWORD->data.string;
	PKWARGS->value = VALUE->data.string;
	PKWARGS->next = KWARGS;
}
argumentlist(KWARGS) ::= TOKEN_STRING(KEYWORD) TOKEN_COLON TOKEN_STRING(VALUE). {
	allocate_url_kwarg(&KWARGS);
	KWARGS->keyword = KEYWORD->data.string;
	KWARGS->value = VALUE->data.string;
}

schemas(SCHEMAS) ::= TOKEN_VOID. { SCHEMAS = NULL; }
schemas(SCHEMAS) ::= schemalist(SCHEMALIST). { SCHEMAS = SCHEMALIST; }

schemalist(SCHEMALIST1) ::= TOKEN_AT TOKEN_STRING(TOKEN) TOKEN_PIPE schemalist(SCHEMALIST2). {
	allocate_schema(&SCHEMALIST1);
	SCHEMALIST1->file_name = TOKEN->data.string;
	load_schema(SCHEMALIST1);
	SCHEMALIST1->next = SCHEMALIST2;
}
schemalist(SCHEMALIST) ::= TOKEN_AT TOKEN_STRING(TOKEN). {
	allocate_schema(&SCHEMALIST);
	SCHEMALIST->file_name = TOKEN->data.string;
	load_schema(SCHEMALIST);
}

