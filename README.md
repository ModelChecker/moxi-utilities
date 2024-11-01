# MoXI Sort Checker

A reference sort checker for MoXI. The following programs are required:

- C compiler
- make
- gperf
- Python 3.9 or newer

To build, run

    make

The generated program `moxisc` takes a single file as input

    moxisc <filename>

To run the test suite, run

    python3 test/test.py

Much of the internals are adapted from Yices, including the parsing and type checking technique. See [their source code](https://github.com/SRI-CSL/yices2) (especially the SMTLIB2 sections) for reference. 