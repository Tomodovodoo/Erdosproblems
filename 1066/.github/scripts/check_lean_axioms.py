#!/usr/bin/env python3
"""Fail if Lean #print axioms output contains non-allowlisted axioms."""

from __future__ import annotations

import os
import re
import sys


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_LINE = re.compile(r"^(.+?) depends on axioms:\s*\[(.*)\]\s*$", re.S)
NO_AXIOM_LINE = re.compile(r"^(.+?) does not depend on any axioms\s*$")


def parse_axioms(raw: str) -> set[str]:
    raw = raw.strip()
    if not raw:
        return set()
    return {item.strip() for item in raw.split(",") if item.strip()}


def main() -> int:
    lines = list(sys.stdin)
    for line in lines:
        print(line, end="")

    checked = 0
    failures: list[str] = []

    i = 0
    while i < len(lines):
        stripped = lines[i].strip()

        if " depends on axioms:" in stripped:
            parts = [stripped]
            while "]" not in parts[-1] and i + 1 < len(lines):
                i += 1
                parts.append(lines[i].strip())
            combined = " ".join(parts)
            match = AXIOM_LINE.match(combined)
            if not match:
                failures.append(f"could not parse axiom output: {combined}")
                i += 1
                continue
            checked += 1
            theorem, raw_axioms = match.groups()
            unexpected = sorted(parse_axioms(raw_axioms) - ALLOWED_AXIOMS)
            if unexpected:
                failures.append(
                    f"{theorem} uses non-allowlisted axioms: {', '.join(unexpected)}"
                )
            i += 1
            continue

        match = NO_AXIOM_LINE.match(stripped)
        if match:
            checked += 1
        i += 1

    if failures:
        print("\nLean axiom audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        print(
            "Allowed axioms: " + ", ".join(sorted(ALLOWED_AXIOMS)),
            file=sys.stderr,
        )
        return 1

    if checked == 0:
        print("Lean axiom audit failed: no #print axioms output was checked.", file=sys.stderr)
        return 1

    expected_raw = os.environ.get("EXPECTED_AXIOM_CHECKS")
    if expected_raw:
        try:
            expected = int(expected_raw)
        except ValueError:
            print(
                f"Lean axiom audit failed: EXPECTED_AXIOM_CHECKS is not an integer: {expected_raw!r}",
                file=sys.stderr,
            )
            return 1
        if checked < expected:
            print(
                f"Lean axiom audit failed: checked {checked} declarations, expected at least {expected}.",
                file=sys.stderr,
            )
            return 1

    print(f"\nLean axiom audit passed for {checked} declarations.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
