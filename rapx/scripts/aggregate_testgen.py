#!/usr/bin/env python3
"""Aggregate RAPx testgen artifacts into CSV files.

The script is intentionally dependency-free so it can run in experiment
environments without installing Python packages.  It accepts either testgen
directories directly or parent directories that contain one or more testgen
subdirectories.
"""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any, Iterable


def load_json(path: Path) -> dict[str, Any] | None:
    try:
        with path.open("r", encoding="utf-8") as file:
            return json.load(file)
    except (OSError, json.JSONDecodeError):
        return None


def discover_testgen_dirs(paths: Iterable[Path]) -> list[Path]:
    discovered: set[Path] = set()
    for path in paths:
        path = path.resolve()
        if (path / "contract_coverage.json").is_file():
            discovered.add(path)
            continue
        if path.name == "testgen" and path.is_dir():
            discovered.add(path)
            continue
        for candidate in path.rglob("testgen"):
            if (candidate / "contract_coverage.json").is_file():
                discovered.add(candidate.resolve())
    return sorted(discovered)


def coverage_totals(testgen_dir: Path) -> dict[str, Any]:
    coverage = load_json(testgen_dir / "contract_coverage.json") or {}
    totals = coverage.get("totals", {})
    return {
        "testgen_dir": str(testgen_dir),
        "schema_version": coverage.get("schema_version", ""),
        "reached": totals.get("reached", 0),
        "lifted": totals.get("lifted", 0),
        "bound": totals.get("bound", 0),
        "violation_edge": totals.get("violation_edge", 0),
        "generated": totals.get("generated", 0),
        "compiled": totals.get("compiled", 0),
        "sink_executed": totals.get("sink_executed", 0),
        "ub": totals.get("ub", 0),
    }


def family_rows(testgen_dir: Path) -> list[dict[str, Any]]:
    coverage = load_json(testgen_dir / "contract_coverage.json") or {}
    rows = []
    for bucket in coverage.get("per_family", []):
        rows.append(
            {
                "testgen_dir": str(testgen_dir),
                "family": bucket.get("name", ""),
                "reached": bucket.get("reached", 0),
                "lifted": bucket.get("lifted", 0),
                "bound": bucket.get("bound", 0),
                "violation_edge": bucket.get("violation_edge", 0),
                "generated": bucket.get("generated", 0),
                "compiled": bucket.get("compiled", 0),
                "sink_executed": bucket.get("sink_executed", 0),
                "ub": bucket.get("ub", 0),
            }
        )
    return rows


def case_rows(testgen_dir: Path) -> list[dict[str, Any]]:
    rows = []
    for metadata_path in sorted(testgen_dir.glob("tests/case*/case_metadata.json")):
        metadata = load_json(metadata_path) or {}
        rows.append(
            {
                "testgen_dir": str(testgen_dir),
                "case": metadata.get("case_name", metadata_path.parent.name),
                "schema_version": metadata.get("schema_version", ""),
                "calls": len(metadata.get("calls", [])),
                "targets": len(metadata.get("targets", [])),
                "hints": len(metadata.get("hints", [])),
                "sink_markers": len(metadata.get("sink_markers", [])),
                "executed_contracts": len(metadata.get("executed_contracts", [])),
                "compile_success": metadata.get("compile_success", False),
                "miri_ub": metadata.get("miri_ub", False),
                "eval_result": metadata.get("eval_result", ""),
            }
        )
    return rows


def write_csv(path: Path, rows: list[dict[str, Any]], fields: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "paths",
        nargs="+",
        type=Path,
        help="testgen directories or parent directories containing testgen outputs",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("testgen_aggregate"),
        help="directory for summary.csv, family_coverage.csv, and case_summary.csv",
    )
    args = parser.parse_args()

    testgen_dirs = discover_testgen_dirs(args.paths)
    summary = [coverage_totals(path) for path in testgen_dirs]
    families = [row for path in testgen_dirs for row in family_rows(path)]
    cases = [row for path in testgen_dirs for row in case_rows(path)]

    write_csv(
        args.out / "summary.csv",
        summary,
        [
            "testgen_dir",
            "schema_version",
            "reached",
            "lifted",
            "bound",
            "violation_edge",
            "generated",
            "compiled",
            "sink_executed",
            "ub",
        ],
    )
    write_csv(
        args.out / "family_coverage.csv",
        families,
        [
            "testgen_dir",
            "family",
            "reached",
            "lifted",
            "bound",
            "violation_edge",
            "generated",
            "compiled",
            "sink_executed",
            "ub",
        ],
    )
    write_csv(
        args.out / "case_summary.csv",
        cases,
        [
            "testgen_dir",
            "case",
            "schema_version",
            "calls",
            "targets",
            "hints",
            "sink_markers",
            "executed_contracts",
            "compile_success",
            "miri_ub",
            "eval_result",
        ],
    )
    print(f"aggregated {len(testgen_dirs)} testgen directories into {args.out}")


if __name__ == "__main__":
    main()
