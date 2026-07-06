#!/usr/bin/env python3
"""Audit solc-AST frontend shape coverage for the Forge/interpreter manifest."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Sequence

import solc_ast_to_lean_source as frontend


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def load_manifest(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        manifest = json.load(handle)
    if not isinstance(manifest, dict) or not isinstance(manifest.get("cases"), list):
        raise ValueError("manifest must contain a JSON object with a cases array")
    return manifest


def add_counts(target: dict[str, int], source: dict[str, int]) -> None:
    for key, value in source.items():
        target[key] = target.get(key, 0) + value


def add_child_field_counts(
    target: dict[str, dict[str, int]], source: dict[str, dict[str, int]]
) -> None:
    for field, children in source.items():
        target_children = target.setdefault(field, {})
        for child_type, count in children.items():
            target_children[child_type] = target_children.get(child_type, 0) + count


def case_source_path(repo: Path, case: dict[str, Any]) -> Path | None:
    solc_import = case.get("solc_import")
    if not isinstance(solc_import, dict):
        return None
    source = solc_import.get("source")
    if not isinstance(source, str):
        return None
    path = Path(source)
    if not path.is_absolute():
        path = repo / path
    return path


def case_contract(case: dict[str, Any]) -> str | None:
    solc_import = case.get("solc_import")
    if not isinstance(solc_import, dict):
        return None
    contract = solc_import.get("contract")
    return contract if isinstance(contract, str) else None


def case_namespace(case: dict[str, Any]) -> str:
    solc_import = case.get("solc_import")
    if not isinstance(solc_import, dict):
        return "SolidCore.Solidity.SolcAstImport.Generated"
    namespace = solc_import.get("namespace")
    if isinstance(namespace, str):
        return namespace
    return "SolidCore.Solidity.SolcAstImport.Generated"


def audit_manifest(manifest_path: Path, solc: str) -> tuple[dict[str, Any], int]:
    repo = repo_root()
    manifest = load_manifest(manifest_path)
    all_counts = {}
    all_child_fields = {}
    source_child_fields = {}
    metadata_child_fields = {}
    unclassified_child_fields = {}
    all_scalar_fields = {}
    source_scalar_fields = {}
    analysis_scalar_fields = {}
    metadata_scalar_fields = {}
    unclassified_scalar_fields = {}
    source_scalar_values = {}
    unknown_source_scalar_values = {}
    cases = []
    render_failures = []
    source_count = 0
    rendered_count = 0

    for case in manifest["cases"]:
        if not isinstance(case, dict):
            continue
        source = case_source_path(repo, case)
        if source is None:
            continue
        source_count += 1
        source_name, ast = frontend.run_solc_ast(solc, source)
        coverage = frontend.frontend_coverage(ast)
        add_counts(all_counts, coverage["nodeTypes"])
        add_child_field_counts(all_child_fields, coverage["childFields"])
        add_child_field_counts(source_child_fields, coverage["sourceChildFields"])
        add_child_field_counts(metadata_child_fields, coverage["metadataChildFields"])
        add_child_field_counts(
            unclassified_child_fields,
            coverage["unclassifiedChildFields"],
        )
        add_counts(all_scalar_fields, coverage["scalarFields"])
        add_counts(source_scalar_fields, coverage["sourceScalarFields"])
        add_counts(analysis_scalar_fields, coverage["analysisScalarFields"])
        add_counts(metadata_scalar_fields, coverage["metadataScalarFields"])
        add_counts(unclassified_scalar_fields, coverage["unclassifiedScalarFields"])
        add_child_field_counts(source_scalar_values, coverage["sourceScalarValues"])
        add_child_field_counts(
            unknown_source_scalar_values,
            coverage["unknownSourceScalarValues"],
        )

        rendered = False
        render_error = ""
        contract = case_contract(case)
        if contract is None:
            render_error = "missing solc_import.contract"
        else:
            try:
                frontend.render_module(
                    ast,
                    source_name,
                    contract,
                    case_namespace(case),
                    body_only=True,
                )
                rendered = True
                rendered_count += 1
            except frontend.ImportError as exc:
                render_error = str(exc)

        if render_error:
            render_failures.append(
                {
                    "name": str(case.get("name")),
                    "source": str(source.relative_to(repo)),
                    "error": render_error,
                }
            )

        cases.append(
            {
                "name": case.get("name"),
                "source": str(source.relative_to(repo)),
                "rendered": rendered,
                "renderError": render_error,
                "metadata": coverage["metadata"],
                "excluded": coverage["excluded"],
                "unimplemented": coverage["unimplemented"],
                "unclassifiedChildFields": coverage["unclassifiedChildFields"],
                "unclassifiedScalarFields": coverage["unclassifiedScalarFields"],
                "unknownSourceScalarValues": coverage["unknownSourceScalarValues"],
            }
        )

    aggregate = {
        "supported": {},
        "metadata": {},
        "excluded": {},
        "unimplemented": {},
    }

    for node_type, count in sorted(all_counts.items()):
        aggregate[frontend.node_type_status(node_type)][node_type] = count

    classified_supported_node_types = sorted(frontend.SUPPORTED_NODE_TYPES)
    classified_metadata_node_types = sorted(frontend.METADATA_NODE_TYPES)
    unseen_supported_node_types = sorted(
        set(classified_supported_node_types) - set(aggregate["supported"])
    )
    unseen_metadata_node_types = sorted(
        set(classified_metadata_node_types) - set(aggregate["metadata"])
    )

    source_scalar_value_domains = {
        frontend.child_field_key(parent, field): sorted(
            frontend.scalar_value_repr(value) for value in values
        )
        for (parent, field), values in sorted(
            frontend.SOURCE_SCALAR_VALUE_DOMAINS.items()
        )
    }

    classified_source_child_fields = sorted(
        frontend.child_field_key(parent, field)
        for parent, field in frontend.SOURCE_CHILD_FIELDS
    )
    classified_metadata_child_fields = sorted(
        frontend.child_field_key(parent, field)
        for parent, field in frontend.METADATA_CHILD_FIELDS
    )
    classified_source_scalar_fields = sorted(
        frontend.child_field_key(parent, field)
        for parent, field in frontend.SOURCE_SCALAR_FIELDS
    )

    unseen_source_child_fields = sorted(
        set(classified_source_child_fields) - set(source_child_fields)
    )
    unseen_metadata_child_fields = sorted(
        set(classified_metadata_child_fields) - set(metadata_child_fields)
    )
    unseen_source_scalar_fields = sorted(
        set(classified_source_scalar_fields) - set(source_scalar_fields)
    )

    unseen_source_scalar_values = {
        field: sorted(set(values) - set(source_scalar_values.get(field, {})))
        for field, values in source_scalar_value_domains.items()
        if set(values) - set(source_scalar_values.get(field, {}))
    }

    report = {
        "sources": source_count,
        "nodeTypes": dict(sorted(all_counts.items())),
        "classifiedSupportedNodeTypes": classified_supported_node_types,
        "classifiedMetadataNodeTypes": classified_metadata_node_types,
        "supported": aggregate["supported"],
        "metadata": aggregate["metadata"],
        "excluded": aggregate["excluded"],
        "unimplemented": aggregate["unimplemented"],
        "unseenSupportedNodeTypes": unseen_supported_node_types,
        "unseenMetadataNodeTypes": unseen_metadata_node_types,
        "classifiedSourceChildFields": classified_source_child_fields,
        "classifiedMetadataChildFields": classified_metadata_child_fields,
        "childFields": dict(sorted(all_child_fields.items())),
        "sourceChildFields": dict(sorted(source_child_fields.items())),
        "metadataChildFields": dict(sorted(metadata_child_fields.items())),
        "unclassifiedChildFields": dict(sorted(unclassified_child_fields.items())),
        "unseenSourceChildFields": unseen_source_child_fields,
        "unseenMetadataChildFields": unseen_metadata_child_fields,
        "classifiedSourceScalarFields": classified_source_scalar_fields,
        "scalarFields": dict(sorted(all_scalar_fields.items())),
        "sourceScalarFields": dict(sorted(source_scalar_fields.items())),
        "analysisScalarFields": dict(sorted(analysis_scalar_fields.items())),
        "metadataScalarFields": dict(sorted(metadata_scalar_fields.items())),
        "unclassifiedScalarFields": dict(sorted(unclassified_scalar_fields.items())),
        "unseenSourceScalarFields": unseen_source_scalar_fields,
        "sourceScalarValueDomains": source_scalar_value_domains,
        "sourceScalarValues": dict(sorted(source_scalar_values.items())),
        "unseenSourceScalarValues": dict(sorted(unseen_source_scalar_values.items())),
        "unknownSourceScalarValues": dict(sorted(unknown_source_scalar_values.items())),
        "renderedSources": rendered_count,
        "renderFailures": render_failures,
        "cases": cases,
    }

    status = 0
    if (
        aggregate["excluded"]
        or aggregate["unimplemented"]
        or unseen_supported_node_types
        or unseen_metadata_node_types
        or unclassified_child_fields
        or unseen_source_child_fields
        or unseen_metadata_child_fields
        or unclassified_scalar_fields
        or unseen_source_scalar_fields
        or unknown_source_scalar_values
        or unseen_source_scalar_values
        or render_failures
    ):
        status = 1
    return report, status


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=repo_root() / "tests" / "forge-harness" / "manifest.json",
    )
    parser.add_argument("--solc", default="solc")
    parser.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        solc = frontend.resolve_executable(args.solc)
        report, status = audit_manifest(args.manifest, solc)
    except (frontend.ImportError, OSError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
        return status
    print("solc_ast_frontend_audit=" + ("pass" if status == 0 else "fail"))
    print(f"sources={report['sources']}")
    print(f"node_types={len(report['nodeTypes'])}")
    print(f"supported_node_types={len(report['supported'])}")
    print(
        "classified_supported_node_types="
        + str(len(report["classifiedSupportedNodeTypes"]))
    )
    print("unseen_supported_node_types=" + str(len(report["unseenSupportedNodeTypes"])))
    print(f"metadata_node_types={len(report['metadata'])}")
    print(
        "classified_metadata_node_types="
        + str(len(report["classifiedMetadataNodeTypes"]))
    )
    print("unseen_metadata_node_types=" + str(len(report["unseenMetadataNodeTypes"])))
    print(f"excluded_node_types={len(report['excluded'])}")
    print(f"unimplemented_node_types={len(report['unimplemented'])}")
    print(f"child_fields={len(report['childFields'])}")
    print(f"source_child_fields={len(report['sourceChildFields'])}")
    print(
        "classified_source_child_fields="
        + str(len(report["classifiedSourceChildFields"]))
    )
    print("unseen_source_child_fields=" + str(len(report["unseenSourceChildFields"])))
    print(f"metadata_child_fields={len(report['metadataChildFields'])}")
    print(
        "classified_metadata_child_fields="
        + str(len(report["classifiedMetadataChildFields"]))
    )
    print(
        "unseen_metadata_child_fields="
        + str(len(report["unseenMetadataChildFields"]))
    )
    print(f"unclassified_child_fields={len(report['unclassifiedChildFields'])}")
    print(f"scalar_fields={len(report['scalarFields'])}")
    print(f"source_scalar_fields={len(report['sourceScalarFields'])}")
    print(
        "classified_source_scalar_fields="
        + str(len(report["classifiedSourceScalarFields"]))
    )
    print("unseen_source_scalar_fields=" + str(len(report["unseenSourceScalarFields"])))
    print(f"analysis_scalar_fields={len(report['analysisScalarFields'])}")
    print(f"metadata_scalar_fields={len(report['metadataScalarFields'])}")
    print(f"unclassified_scalar_fields={len(report['unclassifiedScalarFields'])}")
    print(f"source_scalar_value_fields={len(report['sourceScalarValues'])}")
    print(
        "unknown_source_scalar_value_fields="
        + str(len(report["unknownSourceScalarValues"]))
    )
    print(
        "source_scalar_value_domain_fields="
        + str(len(report["sourceScalarValueDomains"]))
    )
    print(
        "unseen_source_scalar_value_fields="
        + str(len(report["unseenSourceScalarValues"]))
    )
    print(f"rendered_sources={report['renderedSources']}")
    print(f"render_failures={len(report['renderFailures'])}")
    if report["metadata"]:
        print("metadata=" + ",".join(sorted(report["metadata"])))
    if report["excluded"]:
        print("excluded=" + ",".join(sorted(report["excluded"])))
    if report["unimplemented"]:
        print("unimplemented=" + ",".join(sorted(report["unimplemented"])))
    if report["unseenSupportedNodeTypes"]:
        print(
            "unseen_supported_node_types="
            + ",".join(report["unseenSupportedNodeTypes"])
        )
    if report["unseenMetadataNodeTypes"]:
        print(
            "unseen_metadata_node_types="
            + ",".join(report["unseenMetadataNodeTypes"])
        )
    if report["unclassifiedChildFields"]:
        print("unclassified_child_fields=" + ",".join(sorted(report["unclassifiedChildFields"])))
    if report["unclassifiedScalarFields"]:
        print("unclassified_scalar_fields=" + ",".join(sorted(report["unclassifiedScalarFields"])))
    if report["unknownSourceScalarValues"]:
        print("unknown_source_scalar_values=" + ",".join(sorted(report["unknownSourceScalarValues"])))
    if report["unseenSourceScalarValues"]:
        print(
            "unseen_source_scalar_value_fields="
            + ",".join(sorted(report["unseenSourceScalarValues"]))
        )
        for field, values in sorted(report["unseenSourceScalarValues"].items()):
            print("unseen_source_scalar_values." + field + "=" + ",".join(values))
    if report["unseenSourceScalarFields"]:
        print(
            "unseen_source_scalar_fields="
            + ",".join(report["unseenSourceScalarFields"])
        )
    if report["unseenSourceChildFields"]:
        print(
            "unseen_source_child_fields="
            + ",".join(report["unseenSourceChildFields"])
        )
    if report["unseenMetadataChildFields"]:
        print(
            "unseen_metadata_child_fields="
            + ",".join(report["unseenMetadataChildFields"])
        )
    if report["renderFailures"]:
        print(
            "render_failures="
            + ",".join(item["name"] for item in report["renderFailures"])
        )
    return status


if __name__ == "__main__":
    raise SystemExit(main())
