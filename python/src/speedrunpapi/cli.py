"""Run the bundled Colony analyzer with no network install step."""
from __future__ import annotations

import shutil
import subprocess
import sys
from importlib import resources


def main() -> int:
    node = shutil.which("node") or shutil.which("nodejs")
    if not node:
        print("ᑕ. requires Node.js 20 or later on PATH.", file=sys.stderr)
        return 127
    bundled = resources.files("speedrunpapi").joinpath("speedrunpapi.mjs")
    with resources.as_file(bundled) as file_path:
        return subprocess.run([node, str(file_path), *sys.argv[1:]], check=False).returncode


if __name__ == "__main__":
    raise SystemExit(main())
