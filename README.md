# MoXI Sort Checker

A reference sort checker for MoXI. The following programs are required:

- gcc
- gperf
- python 3.10 or newer

To build `moxisc`, run

    make

The generated program `moxisc` takes a single file as input

    moxisc <filename>

To run the test suite, run

    python3 test/test.py