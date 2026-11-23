#!/usr/bin/env python3
"""Compile a CPN object, then link and run it with C and C++ host programs.

Example:
  python3 clang/utils/cpn-smoke-test.py --clang build/bin/clang

The selected compiler needs the experimental CPN26 entry mode and a working
native linker/CRT. This exercises the bootstrap's foreign C boundary; it is
not a CPN26 Core conformance test or a cross-target execution test. Optional
--cc and --cxx drivers can test the same object with a different host compiler.
By default the C++ host uses Clang's g++ driver mode, including for linking.
"""

import argparse
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile


CPN_SOURCE = """\
extern "C" void host_callback();
extern "C" void cpn_entry() { host_callback(); }
"""

HOST_SOURCE = """\
static int calls;

#ifdef __cplusplus
extern "C" {
#endif

void cpn_entry(void);
void host_callback(void) { ++calls; }

#ifdef __cplusplus
}
#endif

int main(void) {
  cpn_entry();
  return calls != 1;
}
"""


def find_driver(value):
    driver = shutil.which(value)
    if driver is None:
        raise ValueError("compiler driver not found: " + value)
    # Preserve names such as clang++: resolving that symlink changes the driver
    # mode used for the final host link.
    return str(Path(driver).absolute())


def run(command, timeout):
    print("+ " + shlex.join(str(part) for part in command), flush=True)
    subprocess.run(command, check=True, timeout=timeout)


def check_linking(directory, clang, cc, cxx, timeout):
    cpn_source = directory / "entry.cpn"
    host_source = directory / "host.c"
    object_suffix = ".obj" if os.name == "nt" else ".o"
    executable_suffix = ".exe" if os.name == "nt" else ""
    cpn_object = directory / ("entry" + object_suffix)
    cpn_source.write_text(CPN_SOURCE, encoding="utf-8")
    host_source.write_text(HOST_SOURCE, encoding="utf-8")

    run(
        [clang, "-x", "cpn", "-std=cpn26", "-c", cpn_source, "-o", cpn_object],
        timeout,
    )
    for name, driver, language, standard in (
        ("c", cc, "c", "c17"),
        ("cxx", cxx, "c++", "c++17"),
    ):
        host_object = directory / (name + object_suffix)
        executable = directory / ("cpn-host-" + name + executable_suffix)
        run(
            [*driver, "-x", language, "-std=" + standard, "-c", host_source,
             "-o", host_object],
            timeout,
        )
        # Link object files without a source-language override. Each host driver
        # selects its ordinary native runtime and linker contract.
        run([*driver, host_object, cpn_object, "-o", executable], timeout)
        run([executable], timeout)
        print("PASS: CPN object linked and ran with " + language, flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clang", required=True, help="path to the built CPN Clang")
    parser.add_argument("--cc", help="GCC-compatible C driver (default: --clang)")
    parser.add_argument(
        "--cxx", help="GCC-compatible C++ driver (default: --clang in g++ mode)"
    )
    parser.add_argument(
        "--work-dir", type=Path,
        help="parent directory in which to retain a fresh smoke-test directory",
    )
    parser.add_argument(
        "--timeout", type=float, default=60,
        help="timeout in seconds for each compiler, linker, or execution step",
    )
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be greater than zero")

    try:
        clang = find_driver(args.clang)
        cc = [find_driver(args.cc)] if args.cc else [clang]
        cxx = [find_driver(args.cxx)] if args.cxx else [clang, "--driver-mode=g++"]
        if args.work_dir:
            args.work_dir.mkdir(parents=True, exist_ok=True)
            directory = Path(
                tempfile.mkdtemp(prefix="cpn-smoke-", dir=args.work_dir)
            ).resolve()
            print("Retaining test files in " + str(directory), flush=True)
            check_linking(directory, clang, cc, cxx, args.timeout)
        else:
            with tempfile.TemporaryDirectory(prefix="cpn-smoke-") as temporary:
                check_linking(Path(temporary), clang, cc, cxx, args.timeout)
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
