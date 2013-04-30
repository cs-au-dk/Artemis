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
        return -1;
    }

    // cleanup

    ParseFree(parser, free);

    return 0;

}