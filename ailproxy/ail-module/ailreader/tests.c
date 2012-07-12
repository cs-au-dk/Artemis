/*
    Copyright 2011 Casper Svenning Jensen. All rights reserved.

    Redistribution and use in source and binary! forms, with or without modification, are
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
    ANY THEORY OF LIABILITY, WHETHER IN operation, STRICT LIABILITY, OR TORT (INCLUDING
    NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
    ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

    The views and conclusions contained in the software and documentation are those of the
    authors and should not be interpreted as representing official policies, either expressed
    or implied, of Casper Svenning Jensen
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <malloc.h>
#include <time.h>
#include <CUnit/Basic.h>

#include "ail.h"
#include "scanner.h"
#include "parser.h"

char * FIXTURE_AIL_SIMPLE = "\
    URL http://localhost:8000\
    \
    GET ajax/search(query:*) : @simpleajax.0.json\
    GET ajax/get_page(query:*, page:*) : @simpleajax.1.json\
    GET ajax/*(id:*) : @simpleajax.2.json|@simpleajax.3.json\
    ";

char * FIXTURE_AIL_SIMLE2 = "\
URL http://localhost:8000\
\
GET impresspages/ImpressPages-1.0.12/ip_backend_worker.php(pageId:'',\
    security_token:*,\
    languageId:'',\
    externalLinking:0,\
    websiteId:'',\
    action:getChildren,\
    module_id:347,\
    type:'',\
    id:'',\
    zoneName:'') : @simpleajax.2.json\
";

char * FIXTURE_AIL_MINIMAL = "\
    URL\
    ";

char * fixture_folder = "./fixtures/";

void ailParseMinimalTest(void) {
    ail_t ail;

    int error = construct_ail(&ail, FIXTURE_AIL_MINIMAL, fixture_folder);

    CU_ASSERT_FATAL(error == 0);

    CU_ASSERT(strcmp(ail->domain, "") == 0);
    CU_ASSERT(ail->num_operations == 0);

}

void ailParseSimpleTest(void) {
    ail_t ail;

    int error = construct_ail(&ail, FIXTURE_AIL_SIMPLE, fixture_folder);

    CU_ASSERT_FATAL(error == 0);

    CU_ASSERT(strcmp(ail->domain, "http://localhost:8000") == 0);

    CU_ASSERT_FATAL(ail->num_operations == 3);
    CU_ASSERT_FATAL(ail->operations != NULL);
    CU_ASSERT_FATAL(ail->operations->schemas != NULL);
    CU_ASSERT_FATAL(ail->operations->next != NULL);
    CU_ASSERT_FATAL(ail->operations->next->schemas != NULL);
}

void scannerTestMinimal(void) {

    scanner_token *token;
    scanner_buffer *buffer;

    token = malloc(sizeof(scanner_token));
    buffer = malloc(sizeof(scanner_buffer));

    buffer->start = FIXTURE_AIL_MINIMAL;
    buffer->current = buffer->start;
    buffer->end = FIXTURE_AIL_MINIMAL + strlen(FIXTURE_AIL_MINIMAL);

    CU_ASSERT_FATAL(scan(buffer, token) == SCANNER_RESULT_TOKEN);
    CU_ASSERT_FATAL(token->id == TOKEN_AIL_START);

    CU_ASSERT_FATAL(scan(buffer, token) == SCANNER_RESULT_EOF);

}

void scannerTestSimple(void) {

    scanner_token *token;
    scanner_buffer *buffer;

    token = malloc(sizeof(scanner_token));
    buffer = malloc(sizeof(scanner_buffer));

    buffer->start = FIXTURE_AIL_SIMPLE;
    buffer->current = buffer->start;
    buffer->end = FIXTURE_AIL_SIMPLE + strlen(FIXTURE_AIL_SIMPLE);

    CU_ASSERT_FATAL(scan(buffer, token) == SCANNER_RESULT_TOKEN);
    CU_ASSERT_FATAL(token->id == TOKEN_AIL_START);

    CU_ASSERT_FATAL(scan(buffer, token) == SCANNER_RESULT_TOKEN);
    CU_ASSERT_FATAL(token->id == TOKEN_DOMAIN);
    CU_ASSERT_FATAL(strcmp(token->data.string, "http://localhost:8000") == 0);

}

void ailOperationLookupFailTest(void) {
    ail_t ail;
    ail_operation_t operation = NULL;

    CU_ASSERT_FATAL(0 == \
        construct_ail(&ail, FIXTURE_AIL_SIMPLE, fixture_folder));

    char * args[] = {"something", "something"};
    int argc = 2;
    char * kwargs[] = {"keyword1"};
    char * vwargs[] = {"value"};
    int kwargc = 1;

    CU_ASSERT(1 == \
        get_operation_for_request(ail, &operation, args, argc, kwargs, vwargs, kwargc));

    CU_ASSERT(operation == NULL);
}

void ailOperationLookupTest(void) {
    ail_t ail;
    ail_operation_t operation = NULL;

    CU_ASSERT_FATAL(0 == \
        construct_ail(&ail, FIXTURE_AIL_SIMPLE, fixture_folder));

    char * args[] = {"ajax", "search"};
    int argc = 2;
    char * kwargs[] = {"query"};
    char * vwargs[] = {"value"};
    int kwargc = 1;

    CU_ASSERT_FATAL(0 == \
        get_operation_for_request(ail, &operation, args, argc, kwargs, vwargs, kwargc));

    CU_ASSERT_FATAL(operation != NULL);
}

void ailOperationLookupTest2(void) {
    ail_t ail;
    ail_operation_t operation = NULL;

    CU_ASSERT_FATAL(0 == \
        construct_ail(&ail, FIXTURE_AIL_SIMPLE, fixture_folder));

    char * args[] = {"ajax", "delete"};
    int argc = 2;
    char * kwargs[] = {"id"};
    char * vwargs[] = {"2079868250"};
    int kwargc = 1;

    CU_ASSERT_FATAL(0 == \
        get_operation_for_request(ail, &operation, args, argc, kwargs, vwargs, kwargc));

    CU_ASSERT_FATAL(operation != NULL);

    CU_ASSERT_FATAL(operation->schemas != NULL);
    CU_ASSERT_FATAL(operation->schemas->next != NULL);
    CU_ASSERT_FATAL(operation->schemas->next->next == NULL);
    CU_ASSERT_FATAL(operation->schemas->file_name != NULL);
    CU_ASSERT_FATAL(operation->schemas->payload != NULL);
}

void ailOperationLookupTest3(void) {
    ail_t ail;
    ail_operation_t operation = NULL;

    CU_ASSERT_FATAL(0 == \
        construct_ail(&ail, FIXTURE_AIL_SIMLE2, fixture_folder));

    char * args[] = {"impresspages", "ImpressPages-1.0.12", "ip_backend_worker.php"};
    int argc = 3;
    char * kwargs[] = {"pageId", "security_token", "languageId", "externalLinking", "websiteId", "action", "module_id", "type", "id", "zoneName"};
    char * vwargs[] = {"", "d4afb865fcc94217d6c72531caaab74e", "", "0", "", "getChildren", "347", "", "", ""};
    int kwargc = 10;

    CU_ASSERT_FATAL(0 == \
        get_operation_for_request(ail, &operation, args, argc, kwargs, vwargs, kwargc));

    CU_ASSERT_FATAL(operation != NULL);
}

void ailOperationCmpTest(void) {

    ail_url_fragment_t f2;
    allocate_url_fragment(&f2);
    f2->text = "f2";

    ail_url_fragment_t f1;
    allocate_url_fragment(&f1);
    f1->text = "f1";
    f1->next = f2;

    ail_url_kwarg_t kwarg2;
    allocate_url_kwarg(&kwarg2);
    kwarg2->keyword = "keyword2";
    kwarg2->value = "value2";

    ail_url_kwarg_t kwarg1;
    allocate_url_kwarg(&kwarg1);
    kwarg1->keyword = "keyword1";
    kwarg1->value = "*";
    kwarg1->next = kwarg2;
       
    ail_operation_t operation;
    allocate_operation(&operation);
    operation->kwargs = kwarg1;
    operation->fragments = f1;

    CU_ASSERT(0 == operationcmp(operation, \
                               (char*[]){"f1", "f2"}, 2, \
                               (char*[]){"keyword1", "keyword2"}, \
                               (char*[]){"value1", "value2"}, 2));

    CU_ASSERT(0 != operationcmp(operation, \
                               (char*[]){"xyz"}, 1, \
                               (char*[]){"123", "321", "4"}, \
                               (char*[]){"ddd", "111", "fda"}, 3));
}

void ailGenerateResponsePermutationGeneric(char * schema_path) {
    
    ail_schema_t schema1;
    allocate_schema(&schema1);
    schema1->file_name = schema_path;

    CU_ASSERT_FATAL(load_schema(schema1) == 0);

    ail_schema_t schema2;
    allocate_schema(&schema2);
    schema2->file_name = schema_path;
    load_schema(schema2);
    schema2->next = schema1;

    ail_operation_t operation;
    allocate_operation(&operation);
    operation->schemas = schema2;
    
    ail_response_t response = NULL;

    CU_ASSERT_FATAL(0 == \
        generate_response_permutation(operation, &response));

    CU_ASSERT_FATAL(NULL != response);

    //print_response(response);
}

void ailGenerateResponsePermutation(void) {
    ailGenerateResponsePermutationGeneric("fixtures/300.json");
    ailGenerateResponsePermutationGeneric("fixtures/simpleajax.0.json");
    ailGenerateResponsePermutationGeneric("fixtures/simpleajax.1.json");
    ailGenerateResponsePermutationGeneric("fixtures/simpleajax.2.json");
    ailGenerateResponsePermutationGeneric("fixtures/simpleajax.3.json");
}

int main (int argc, char** argv) {
    srandom (time (0));

    CU_pSuite pSuite = NULL;

    /* initialize the CUnit test registry */
    if (CUE_SUCCESS != CU_initialize_registry())
        return CU_get_error();

    /* add a suite to the registry */
    pSuite = CU_add_suite("Suite_1", NULL, NULL);
    if (NULL == pSuite) {
        CU_cleanup_registry();
        return CU_get_error();
    }

    /* add the tests to the suite */
    if (NULL == CU_add_test(pSuite, "Generate response permutation", ailGenerateResponsePermutation) ||
        NULL == CU_add_test(pSuite, "Scanner test minimal", scannerTestMinimal) ||
        NULL == CU_add_test(pSuite, "Scanner test simple", scannerTestSimple) ||
        NULL == CU_add_test(pSuite, "Parser test minimal", ailParseMinimalTest) ||
        NULL == CU_add_test(pSuite, "Parser test simple", ailParseSimpleTest) ||
        NULL == CU_add_test(pSuite, "Operation lookup fail test", ailOperationLookupFailTest) ||
        NULL == CU_add_test(pSuite, "Operation lookup test", ailOperationLookupTest) ||
        NULL == CU_add_test(pSuite, "Operation lookup test 2", ailOperationLookupTest2) ||
        NULL == CU_add_test(pSuite, "Operation lookup test 3", ailOperationLookupTest3) ||
        NULL == CU_add_test(pSuite, "Operation-cmp test", ailOperationCmpTest)) {
        CU_cleanup_registry();
        return CU_get_error();
    }

    /* Run all tests using the CUnit Basic interface */
    CU_basic_set_mode(CU_BRM_VERBOSE);
    CU_basic_run_tests();
    CU_cleanup_registry();

    return CU_get_error();
}