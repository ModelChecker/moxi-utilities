import pathlib
import subprocess
import sys

# FILE_DIR = /path/to/moxisc/test
FILE_DIR = pathlib.Path(__file__).parent

# EXECUTABLE = /path/to/moxisc/moxisc
EXECUTABLE = FILE_DIR.parent / "moxisc"

if not EXECUTABLE.is_file():
    print(f"error: executable not a file ({EXECUTABLE})")

status = 0

for file in FILE_DIR.rglob("*.moxi"):
    # A file is expected to fail if the last char is 'X'
    # Example: "test_fileX.moxi"
    should_fail = (file.stem[-1] == "X")

    command = [str(EXECUTABLE), str(file)]
    proc = subprocess.run(command, text=True, capture_output=True)

    actually_fails = (proc.returncode != 0)

    if actually_fails and not should_fail:
        print(f"[FAIL] {file}")
        print("\t" + proc.stderr[:-1])
        status = 1
    elif not actually_fails and should_fail:
        print(f"[FAIL] {file}")
        print("\t" + "moxisc returned 0")
        status = 1
    else:
        print(f"[PASS] {file}")

sys.exit(status)