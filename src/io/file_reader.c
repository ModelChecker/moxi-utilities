#include "file_reader.h"

#include <stdio.h>


int init_file_reader(file_reader_t *reader, const char *filename)
{
    FILE *f = fopen(filename, "r");
    flockfile(f); // blocking file lock, let's us use getc_unlocked safely

    reader->file = f;
    reader->pos = 0;
    reader->lineno = 0;
    reader->col = 0;

    if (f == NULL) {
        reader->cur = EOF;
        return -1;
    }

    reader->cur = '\n';
    return 0;
}


int close_file_reader(file_reader_t *reader)
{
    funlockfile(reader->file);
    return fclose(reader->file);
}


int file_reader_next_char(file_reader_t *reader)
{
    if (reader->cur == EOF) {
        return EOF;
    }

    if (reader->cur == '\n') {
        reader->lineno++;
        reader->col = 0;
    }

    reader->cur = getc_unlocked(reader->file);

    reader->pos++;
    reader->col++;

    return reader->cur;
}

