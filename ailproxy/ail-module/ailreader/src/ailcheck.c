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

#include <stdio.h>
#include <malloc.h>

#include "ail.h"

int main(int argc, char** argv) {

  if (argc < 2) {
    printf("Usage: ailcheck /path/to/file.ail");
    return 1;
  }

  FILE* fp = fopen(argv[1], "rb");

  /* Get number of bytes */
  fseek(fp, 0L, SEEK_END);
  long size = ftell(fp);
  fseek(fp, 0L, SEEK_SET);

  /* Remember to add room for the null terminator */
  char * raw_ail = malloc(sizeof(char) * (size + 1));

  fread(raw_ail, sizeof(char), size, fp);
  fclose(fp);

  char * schema_folder;
  get_schema_folder(argv[1], &schema_folder);

  ail_t ail;
  if (construct_ail(&ail, raw_ail, schema_folder) != 0) {
    printf("FAILED READING AIL FILE\n");
    return 1;
  }

  printf("SYNTAX OK\n");
  return 0;
}
