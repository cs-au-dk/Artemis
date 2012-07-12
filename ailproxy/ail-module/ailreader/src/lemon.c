
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