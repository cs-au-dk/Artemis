
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