"""Allow `python -m smack` as an alias for the `smack` CLI script.

Picks up the same entry point pyproject.toml's [project.scripts] wires.
Useful when the bin/smack wrapper isn't on PATH (e.g. running from a
pip-install --user / venv that hasn't been activated).
"""

from __future__ import annotations

from smack import main

if __name__ == "__main__":
    main()
