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

// -- re2c scanner specification

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define _IN_SCANNER
#include "scanner.h"
#include "parser.h"

#define YYCTYPE char
#define YYCURSOR (buffer->current)
#define YYLIMIT (buffer->end)
#define YYMARKER (marker)

int scan(scanner_buffer *buffer, scanner_token *token) {

	buffer->start = buffer->current;
	const char * marker;

	while(1) {

	/*!re2c
	re2c:indent:top = 2;
	re2c:yyfill:enable = 0;

	"http"("s"?)"://"[a-zA-Z0-9\.]+(":"[0-9]+)? {
		char *string;

		string = strndup(buffer->start, YYCURSOR - buffer->start);

		token->data.string = string;
		token->id = TOKEN_DOMAIN;

		return SCANNER_RESULT_TOKEN;
	}

	"URL" {
		token->id = TOKEN_AIL_START;
		return SCANNER_RESULT_TOKEN;
	}

	"POST"|"GET" {
		token->id = TOKEN_METHOD;
		return SCANNER_RESULT_TOKEN;
	}

	"void" {
		token->id = TOKEN_VOID;
		return SCANNER_RESULT_TOKEN;
	}

	"(" {
		token->id = TOKEN_ROUND_BRACKET_OPEN;
		return SCANNER_RESULT_TOKEN;
	}

	")" {
		token->id = TOKEN_ROUND_BRACKET_CLOSE;
		return SCANNER_RESULT_TOKEN;
	}

	"/" {
		token->id = TOKEN_SLASH;
		return SCANNER_RESULT_TOKEN;
	}

	":" {
		token->id = TOKEN_COLON;
		return SCANNER_RESULT_TOKEN;
	}

	"@" {
		token->id = TOKEN_AT;
		return SCANNER_RESULT_TOKEN;
	}

	"," {
		token->id = TOKEN_COMMA;
		return SCANNER_RESULT_TOKEN;
	}

	"|" {
		token->id = TOKEN_PIPE;
		return SCANNER_RESULT_TOKEN;
	}

	" "|"\t"|"\n" {
		buffer->start = buffer->current;
		continue;
	}

	[a-zA-Z0-9_\-*\.\[\]]+|"\"".*"\""|"''" {
		char *string;

		int correct_quote = 0;

		if (*(buffer->start) == '"' || *(buffer->start) == '\'') {
			correct_quote = 1;
		}

		if (YYCURSOR - buffer->start - correct_quote * 2 != 0) {
			string = strndup(buffer->start + correct_quote, \
				YYCURSOR - buffer->start - correct_quote * 2);
		} else {
			string = "";
		}

		token->data.string = string;
		token->id = TOKEN_STRING;

		return SCANNER_RESULT_TOKEN;
	}

	"\000" { return SCANNER_RESULT_EOF; }

	[^] { return SCANNER_RESULT_ERR; }
	*/

	}
}
