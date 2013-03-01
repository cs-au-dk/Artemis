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

int parse_ail(ail_t ail, const char * raw_ail) {

    // setup scanner

    scanner_buffer *buffer;
    buffer = malloc(sizeof(scanner_buffer));

    buffer->start = raw_ail;
    buffer->current = buffer->start;
    buffer->end = raw_ail + strlen(raw_ail);

    // setup parser

    void* parser = ParseAlloc(malloc);
    parsed_ail = ail;

    // run

    int result;

    while (1) {
        scanner_token * token;
        token = malloc(sizeof(scanner_token));

        result = scan(buffer, token);

        if (SCANNER_RESULT_TOKEN != result) {
            break;
        }

        Parse(parser, token->id, token);
    }

    Parse(parser, 0, 0);

    if (result == SCANNER_RESULT_ERR) {
        printf("UNEXPECTED TOKEN\n");
        printf("Token found at byte offset %i\n", buffer->current - raw_ail);
        return 1;
    }

    // cleanup

    ParseFree(parser, free);

    return 0;

}
