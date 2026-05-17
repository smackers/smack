"""Verification result and property enums for the SMACK CLI.

Extracted from share/smack/top.py during Phase B5 of the modernization plan.
`smack.top` re-exports these names so existing callers (svcomp/, errtrace,
frontend, etc.) continue to work without modification.
"""

import argparse
import functools
from enum import Flag, auto


class VResult(Flag):
    """
    This class represents verification results.
    `MEMSAFETY_ERROR` and `ERROR` do not correspond to any results. They are
    used to group certain results.
    """

    VERIFIED = auto()
    ASSERTION_FAILURE = auto()
    INVALID_DEREF = auto()
    INVALID_FREE = auto()
    INVALID_MEMTRACK = auto()
    OVERFLOW = auto()
    RUST_PANIC = auto()
    TIMEOUT = auto()
    UNKNOWN = auto()
    MEMSAFETY_ERROR = INVALID_DEREF | INVALID_FREE | INVALID_MEMTRACK
    ERROR = (
        ASSERTION_FAILURE | INVALID_DEREF | INVALID_FREE | INVALID_MEMTRACK | OVERFLOW | RUST_PANIC
    )

    def __str__(self):
        return (self.name or "").lower().replace("_", "-")

    def description(self):
        """Return the description for certain result."""

        descriptions = {
            VResult.ASSERTION_FAILURE: "",
            VResult.INVALID_DEREF: "invalid pointer dereference",
            VResult.INVALID_FREE: "invalid memory deallocation",
            VResult.INVALID_MEMTRACK: "memory leak",
            VResult.OVERFLOW: "integer overflow",
            VResult.RUST_PANIC: "Rust panic",
        }

        if self in descriptions:
            return descriptions[self]
        else:
            raise RuntimeError(f"No description associated with result: {self}")

    def return_code(self):
        """Return the exit code for each result."""

        return_codes = {
            VResult.VERIFIED: 0,
            VResult.ASSERTION_FAILURE: 1,
            VResult.INVALID_DEREF: 2,
            VResult.INVALID_FREE: 3,
            VResult.INVALID_MEMTRACK: 4,
            VResult.OVERFLOW: 5,
            VResult.RUST_PANIC: 6,
            VResult.TIMEOUT: 126,
            VResult.UNKNOWN: 127,
        }

        if self in return_codes:
            return return_codes[self]
        else:
            raise RuntimeError(f"No return code associated with result: {self}")

    def message(self, args):
        """Return SMACK's output for each result."""

        if self is VResult.VERIFIED:
            return (
                "SMACK found no errors"
                + ("" if args.modular else f" with unroll bound {args.unroll}")
                + "."
            )
        elif self in VResult.ERROR:
            description = self.description()
            return "SMACK found an error" + (f": {description}" if description else "") + "."
        elif self is VResult.TIMEOUT:
            return "SMACK timed out."
        elif self is VResult.UNKNOWN:
            return "SMACK result is unknown."
        else:
            raise RuntimeError(f"No message associated with result: {self}")


class PropertyAction(argparse.Action):
    """
    This class defines the argparse action when the arguments of the `--check`
    option are consumed.
    """

    def __init__(self, option_strings, dest, **kwargs):
        super().__init__(option_strings, dest, **kwargs)

    def __call__(self, parser, namespace, values, option_string=None):
        """
        Fold the provided arguments with bitwise or. This is equivalent to
        extending the property list with the arguments.
        """

        setattr(
            namespace,
            self.dest,
            functools.reduce(lambda x, y: x | y, values, getattr(namespace, self.dest)),
        )


# Shaobo: shamelessly borrowed it from https://stackoverflow.com/a/55500795
class VProperty(Flag):
    """
    This class defines the properties that SMACK verifies. `NONE` is a special
    value that does not correspond to any property. It's used simply to get
    around the default value issue when the action similar to `extend`.
    """

    NONE = 0
    ASSERTIONS = auto()
    VALID_DEREF = auto()
    VALID_FREE = auto()
    MEMLEAK = auto()
    MEMORY_SAFETY = VALID_DEREF | VALID_FREE | MEMLEAK
    INTEGER_OVERFLOW = auto()
    RUST_PANICS = auto()

    def __str__(self):
        return (self.name or "").lower().replace("_", "-")

    def __repr__(self):
        return str(self)

    @staticmethod
    def argparse(s):
        try:
            return VProperty[s.upper().replace("-", "_")]
        except KeyError:
            return s

    @staticmethod
    def mem_safe_subprops():
        return [VProperty.VALID_DEREF, VProperty.VALID_FREE, VProperty.MEMLEAK]

    def contains_mem_safe_props(self):
        """
        Test if a property is either memory-safety or any of its subproperties.
        """

        return bool(self & VProperty.MEMORY_SAFETY)

    def boogie_attr(self):
        """
        Return the attribute of Boogie assert command for certain property.
        """

        def get_attr_from_result(x):
            if x in VResult.MEMSAFETY_ERROR:
                return x.name.lower()[2:]
            else:
                return x.name.lower()

        attrs = {
            VProperty.VALID_DEREF: get_attr_from_result(VResult.INVALID_DEREF),
            VProperty.VALID_FREE: get_attr_from_result(VResult.INVALID_FREE),
            VProperty.MEMLEAK: get_attr_from_result(VResult.INVALID_MEMTRACK),
            VProperty.INTEGER_OVERFLOW: get_attr_from_result(VResult.OVERFLOW),
            VProperty.RUST_PANICS: get_attr_from_result(VResult.RUST_PANIC),
        }

        if self in attrs:
            return attrs[self]
        else:
            raise RuntimeError(f"No assertion Boogie attribute associated withproperty: {self}")

    def result(self):
        """Link SMACK properties with results"""

        res = {
            VProperty.VALID_DEREF: VResult.INVALID_DEREF,
            VProperty.VALID_FREE: VResult.INVALID_FREE,
            VProperty.MEMLEAK: VResult.INVALID_MEMTRACK,
            VProperty.INTEGER_OVERFLOW: VResult.OVERFLOW,
            VProperty.RUST_PANICS: VResult.RUST_PANIC,
        }

        if self in res:
            return res[self]
        else:
            raise RuntimeError(f"No SMACK result associated with property: {self}")
