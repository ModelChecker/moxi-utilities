/**
 * 
 * 
*/
#ifndef __FILE_READER_H__
#define __FILE_READER_H__


#include <stdio.h>
#include <stdint.h>


typedef struct file_reader {
    FILE *file;
    int cur;
    uint64_t pos;
    uint64_t lineno;
    uint64_t col;
} file_reader_t;


/**
 * Initializes `reader` by locking and opening `filename`. 
 * Returns -1 if file cannot be opened, 0 otherwise.
*/
int init_file_reader(file_reader_t *reader, const char *filename);

/**
 * Unlocks and closes `reader->file`.
 * Returns the value of `fclose` on `reader->file`.
*/
int close_file_reader(file_reader_t *reader);


int file_reader_next_char(file_reader_t *reader);


#endif