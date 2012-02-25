
#ifndef SCANNER_H
#define SCANNER_H

// RETURNCODES
#define SCANNER_RESULT_TOKEN 0
#define SCANNER_RESULT_EOF -1
#define SCANNER_RESULT_ERR -2

typedef struct _scanner_buffer {
	const char* start;
	const char* current;
	const char* end;
} scanner_buffer;

typedef struct _scanner_token {

	int id;

	union {
		int integer;
		char* string;
	} data;

} scanner_token;

int scan(scanner_buffer *buffer, scanner_token *token);

#endif