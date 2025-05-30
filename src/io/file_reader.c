#include "file_reader.h"

#include <stdio.h>


int init_file_reader(file_reader_t *reader, const char *filename)
{
    FILE *f = fopen(filename, "r");

    reader->file = f;
    reader->pos = 0;
    reader->loc = (loc_t) {0, 0};

    if (f == NULL) {
        reader->cur = EOF;
        return -1;
    }

#ifdef _POSIX_C_SOURCE
    flockfile(f); // blocking file lock, let's us use getc_unlocked safely
#endif

    reader->cur = '\n';
    return 0;
}


int close_file_reader(file_reader_t *reader)
{
#ifdef _POSIX_C_SOURCE
    funlockfile(reader->file);
#endif
    return fclose(reader->file);
}


int file_reader_next_char(file_reader_t *reader)
{
    if (reader->cur == EOF) {
        return EOF;
    }

    if (reader->cur == '\n') {
        reader->loc.lineno++;
        reader->loc.col = 0;
    }

#ifdef _POSIX_C_SOURCE
    reader->cur = getc_unlocked(reader->file);
#else
    reader->cur = getc(reader->file);
#endif

    reader->pos++;
    reader->loc.col++;

    return reader->cur;
}

