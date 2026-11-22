"""Command line driver for one CPN26 root unit."""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

sys.dont_write_bytecode = True

from compiler import Module
from syntax import Error


def main():
    parser = argparse.ArgumentParser(prog="cpnc", description=__doc__)
    parser.add_argument(
        "--std", required=True, choices=["CPN26"], help="source edition"
    )
    parser.add_argument(
        "--preset",
        choices=["Debug", "Release", "MinimalDebug", "MinimalRelease"],
        default="Debug",
    )
    parser.add_argument(
        "--identifiers", choices=["ascii", "unicode"], default="unicode"
    )
    parser.add_argument(
        "--config", type=Path, metavar="cpn.config", help="project configuration file"
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("-S", "--emit-llvm", action="store_true", help="write LLVM IR")
    mode.add_argument("--check", action="store_true", help="type check a root unit")
    mode.add_argument(
        "-c", action="store_true", help="emit an x86-64 Linux ELF object (default)"
    )
    parser.add_argument("-o", type=Path, metavar="OUTPUT")
    parser.add_argument("--llc", metavar="PATH", help="path to LLVM's llc")
    parser.add_argument("source", type=Path)
    parser.add_argument("--root-id", help="stable logical identity of the CPN26 root")
    args = parser.parse_args()
    output = args.o or args.source.with_suffix(".ll" if args.emit_llvm else ".o")
    diagnostic_path = args.source
    try:
        if not args.check and output.resolve() == args.source.resolve():
            parser.error("output would overwrite the source")

        def warning(token, message, category="WARNING"):
            print(
                f"{diagnostic_path}:{token.line}:{token.column}: {category}: {message}",
                file=sys.stderr,
            )

        module = Module(args.preset, args.identifiers, warning)
        if args.config:
            if args.config.name != "cpn.config":
                parser.error("project configuration must be named cpn.config")
            diagnostic_path = args.config
            module.project_config(args.config.read_text(encoding="utf-8-sig"))
        diagnostic_path = args.source
        try:
            logical_path = args.source.resolve().relative_to(Path.cwd()).as_posix()
        except ValueError:
            logical_path = args.source.name
        ir = module.compile(
            args.source.read_text(encoding="utf-8-sig"), logical_path, args.root_id
        )
        if args.check:
            return 0
        # Publish only a complete artifact, including when the backend fails.
        with TemporaryDirectory(dir=output.parent) as temp:
            artifact = Path(temp) / "output"
            if args.emit_llvm:
                artifact.write_text(ir, encoding="utf-8")
            else:
                sibling = Path(sys.argv[0]).resolve().with_name("llc")
                backend = args.llc or (
                    str(sibling) if sibling.is_file() else shutil.which("llc")
                )
                if not backend:
                    parser.exit(
                        1,
                        "cpnc: ERROR: llc not found; build llc or specify --llc PATH\n",
                    )
                subprocess.run(
                    [
                        backend,
                        "-filetype=obj",
                        "-relocation-model=pic",
                        "-o",
                        str(artifact),
                        "-",
                    ],
                    input=ir.encode(),
                    check=True,
                )
            os.replace(artifact, output)
    except (Error, OSError, UnicodeError, subprocess.CalledProcessError) as exc:
        print(f"{diagnostic_path}:{exc}", file=sys.stderr)
        return 1
    except RecursionError:
        parser.exit(1, "cpnc: ERROR: source nesting or instantiation limit exceeded\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
