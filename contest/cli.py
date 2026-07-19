"""CLI entry point: solidity-divergence adjudicate|reject-gate|register|known-gaps|run-samples.

Each subcommand delegates to the corresponding module's existing entrypoint;
no adjudication logic is reimplemented here.
"""

import argparse
import json
import sys


def cmd_adjudicate(rest: list[str]) -> int:
    from . import adjudicate
    return adjudicate._main(rest)


def cmd_adjudicate_file(rest: list[str]) -> int:
    from . import manifest
    return manifest._main(rest)


def cmd_reject_gate(rest: list[str]) -> int:
    from . import reject_gate
    return reject_gate._main(rest)


def cmd_register(rest: list[str]) -> int:
    from . import exclusion_register
    print(json.dumps(exclusion_register.register_summary(), indent=2))
    return 0


def cmd_known_gaps(rest: list[str]) -> int:
    from . import known_gaps
    print(json.dumps(known_gaps.registry_summary(), indent=2))
    return 0


def cmd_run_samples(rest: list[str]) -> int:
    from . import run_samples
    return run_samples.main()


def main() -> None:
    parser = argparse.ArgumentParser(
        prog="solidity-divergence",
        description="Adjudicate solidity-lean divergence submissions and inspect the harness registries",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    subparsers.add_parser(
        "adjudicate",
        help="Adjudicate a submission directory (delegates to adjudicate._main)",
        add_help=False,
    )
    subparsers.add_parser(
        "adjudicate-file",
        help="Adjudicate a single-file .sol+manifest submission (manifest._main)",
        add_help=False,
    )
    subparsers.add_parser(
        "reject-gate",
        help="Run the reject gate over .sol sources (delegates to reject_gate._main)",
        add_help=False,
    )
    subparsers.add_parser(
        "register",
        help="Print the exclusion register summary",
    )
    subparsers.add_parser(
        "known-gaps",
        help="Print the known-gaps registry summary",
    )
    subparsers.add_parser(
        "run-samples",
        help="Run the sample self-test suite",
    )

    # Split off the subcommand, pass the remainder straight through so the
    # delegated module parses its own flags (--solc, --json, etc.).
    args, rest = parser.parse_known_args()

    dispatch = {
        "adjudicate": cmd_adjudicate,
        "adjudicate-file": cmd_adjudicate_file,
        "reject-gate": cmd_reject_gate,
        "register": cmd_register,
        "known-gaps": cmd_known_gaps,
        "run-samples": cmd_run_samples,
    }
    raise SystemExit(dispatch[args.command](rest))


if __name__ == "__main__":
    main()
