"""CDCL(T) core orchestrator.

Bridges ``syntax`` expressions with the standalone ``sat`` solver and coordinates
``theories``, ``tactics``, ``quantifiers``, and ``model`` construction.
Will promote to a ``smt/`` subpackage as implementation grows.

Depends on: ``syntax``, ``sat``, ``theories``, ``tactics``, ``quantifiers``, ``model``.
"""
