"""SV-COMP integration: portfolio driver + result XML emission.

Intentionally empty re-export surface: ``smack.svcomp.utils`` already
does ``import smack.top`` at module scope and ``smack.top`` imports
back into ``smack.svcomp.utils``. Adding a `verify_bpl_svcomp`
re-export here (eager or lazy) doesn't help because the cycle is in
the importer chain, not at this package boundary.

Callers should keep using ``from smack.svcomp.utils import verify_bpl_svcomp``
until the top.py / svcomp.utils mutual import is untangled. The
modernization-status doc tracks this as a follow-up.
"""
