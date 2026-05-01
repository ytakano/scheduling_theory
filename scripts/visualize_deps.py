#!/usr/bin/env python3
"""Generate RocqSched dependency graphs and reports.

The output is intentionally machine-generated.  Re-run:

    make deps-graph

to refresh docs/deps.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


DECL_RE = re.compile(
    r"^\s*(Definition|Fixpoint|Function|Lemma|Theorem|Inductive|Record|Axiom|Parameter)\s+([A-Za-z_][A-Za-z0-9_']*)\b",
    re.MULTILINE,
)


@dataclass(frozen=True)
class RootSpec:
    symbol: str
    area: str
    kind: str
    required: bool = True


ROOTS: list[RootSpec] = [
    RootSpec("check_periodic_edf_checked_sidecar", "edf", "checker"),
    RootSpec("check_periodic_edf_checked_sidecar_extracted", "edf", "extraction-entry"),
    RootSpec("check_periodic_edf_checked_sidecar_extracted_with_offsets", "edf", "extraction-entry"),
    RootSpec("check_periodic_edf_checked_sidecar_extracted_sound", "edf", "soundness"),
    RootSpec("check_periodic_edf_csv_certificate_sound", "edf", "soundness"),
    RootSpec("periodic_dbf", "edf", "definition"),
    RootSpec("window_dbf_test_upto_true_implies_bounded_window_dbf", "edf", "soundness"),
    RootSpec("AwkernelTaskTraceEntry", "awkernel", "record"),
    RootSpec("AwkernelSchedTraceEntry", "awkernel", "record"),
    RootSpec("AwkernelTaskTraceKind", "awkernel", "inductive"),
    RootSpec("DispatchModel", "awkernel", "inductive"),
    RootSpec("awk_workload_accepts_sched_trace_spurious", "awkernel", "checker"),
    RootSpec("awk_workload_accepts_global_fifo_scheduler_relation_sched_trace_spurious", "awkernel", "checker"),
    RootSpec("awk_workload_accepts_edf_fifo_scheduler_relation_sched_trace_spurious", "awkernel", "checker"),
    RootSpec("awk_workload_checker_acceptance_spurious_global_fifo_scheduler_rel", "awkernel", "soundness"),
    RootSpec("project_schedule", "awkernel", "projection"),
]

MISSING_CANDIDATES = [
    "check_periodic_edf_checked",
    "periodic_edf_witness_check",
    "dbf",
    "busy_window",
    "backlog_free",
    "completed_by",
    "hyperperiod",
    "normalize_trace",
    "check_awkernel_trace",
    "check_worker_core_trace",
    "strict_dispatch_policy",
    "spurious_dispatch_policy",
]

SLICE_ROOTS = {
    "edf_checker_slice": [
        "check_periodic_edf_checked_sidecar_extracted",
        "check_periodic_edf_checked_sidecar_extracted_with_offsets",
    ],
    "edf_checker_proof_slice": [
        "check_periodic_edf_checked_sidecar_extracted_sound",
        "check_periodic_edf_csv_certificate_sound",
        "window_dbf_test_upto_true_implies_bounded_window_dbf",
    ],
    "awkernel_trace_checker_slice": [
        "awk_workload_accepts_sched_trace_spurious",
        "awk_workload_accepts_global_fifo_scheduler_relation_sched_trace_spurious",
        "awk_workload_accepts_edf_fifo_scheduler_relation_sched_trace_spurious",
    ],
    "awkernel_trace_to_schedule_slice": [
        "project_schedule",
        "awk_workload_checker_acceptance_spurious_global_fifo_scheduler_rel",
    ],
    "extraction_boundary_slice": [
        "check_periodic_edf_checked_sidecar_extracted",
        "check_periodic_edf_checked_sidecar_extracted_sound",
        "awk_workload_accepts_global_fifo_scheduler_relation_sched_trace_spurious",
        "awk_workload_checker_acceptance_spurious_global_fifo_scheduler_rel",
    ],
}

HASKELL_BOUNDARIES = [
    ("periodic_edf_witness_check", "scripts/periodic_edf_witness_check.hs"),
    ("AwkernelWorkloadAcceptance", "extracted/haskell/AwkernelWorkloadAcceptance.hs"),
    ("PeriodicEDFSchedulability", "extracted/haskell/PeriodicEDFSchedulability.hs"),
]


def run(cmd: list[str], cwd: Path, commands: list[str], capture: bool = False) -> subprocess.CompletedProcess[str]:
    commands.append(" ".join(cmd))
    return subprocess.run(
        cmd,
        cwd=cwd,
        check=True,
        text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.PIPE if capture else None,
    )


def safe_name(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", name)


def logical_module(path: Path) -> str:
    rel = path.with_suffix("")
    parts = rel.parts
    if parts[0] == "theories":
        return "RocqSched." + ".".join(parts[1:])
    if parts[0] == "Tutorials":
        return "Tutorials." + ".".join(parts[1:])
    return ".".join(parts)


def scan_declarations(repo: Path) -> dict[str, dict[str, str]]:
    declarations: dict[str, dict[str, str]] = {}
    for path in sorted((repo / "theories").rglob("*.v")):
        text = path.read_text(encoding="utf-8")
        rel = path.relative_to(repo)
        module = logical_module(rel)
        for match in DECL_RE.finditer(text):
            kind, symbol = match.groups()
            line = text[: match.start()].count("\n") + 1
            declarations[symbol] = {
                "kind": kind,
                "path": str(rel),
                "module": module,
                "line": str(line),
            }
    return declarations


def node_color_for_path(path: str) -> str:
    if "/TaskModels/Periodic/" in path:
        return "#d9ead3"
    if "/Operational/Awkernel/" in path:
        return "#d9eaf7"
    if "/Operational/Common/" in path:
        return "#e7d9f7"
    if "/Analysis/" in path:
        return "#fff2cc"
    if "/Extraction/" in path:
        return "#fce5cd"
    return "#eeeeee"


def vo_to_module(path: str) -> str | None:
    if not path.startswith("theories/") or not path.endswith(".vo"):
        return None
    return "RocqSched." + path.removeprefix("theories/").removesuffix(".vo").replace("/", ".")


def generate_module_graph(repo: Path, out: Path, commands: list[str]) -> tuple[int, int]:
    dep = run(["rocq", "dep", "-f", "_CoqProject"], repo, commands, capture=True).stdout
    edges: set[tuple[str, str]] = set()
    nodes: set[str] = set()
    for line in dep.splitlines():
        if ":" not in line:
            continue
        lhs, rhs = line.split(":", 1)
        lhs_modules = [vo_to_module(tok) for tok in lhs.split()]
        lhs_modules = [mod for mod in lhs_modules if mod is not None]
        if not lhs_modules:
            continue
        target = lhs_modules[0]
        nodes.add(target)
        for tok in rhs.split():
            dep_mod = vo_to_module(tok)
            if dep_mod is None or dep_mod == target:
                continue
            nodes.add(dep_mod)
            edges.add((target, dep_mod))

    dot_path = out / "module_graph.dot"
    with dot_path.open("w", encoding="utf-8") as f:
        f.write("digraph module_graph {\n")
        f.write("  rankdir=LR;\n")
        f.write("  graph [fontsize=10, labelloc=t, label=\"RocqSched module dependencies\"];\n")
        f.write("  node [shape=box, style=\"rounded,filled\", fontsize=9];\n")
        f.write("  edge [color=\"#777777\"];\n")
        for node in sorted(nodes):
            pseudo_path = "theories/" + node.removeprefix("RocqSched.").replace(".", "/") + ".v"
            f.write(f'  "{node}" [fillcolor="{node_color_for_path(pseudo_path)}"];\n')
        for src, dst in sorted(edges):
            f.write(f'  "{src}" -> "{dst}";\n')
        f.write("}\n")
    render_dot(repo, dot_path, commands)
    return len(nodes), len(edges)


def render_dot(repo: Path, dot_path: Path, commands: list[str], engine: str = "dot") -> None:
    svg_path = dot_path.with_suffix(".svg")
    pdf_path = dot_path.with_suffix(".pdf")
    ps_path = dot_path.with_suffix(".ps")
    run([engine, "-Tsvg", str(dot_path), "-o", str(svg_path)], repo, commands)
    run([engine, "-Tpdf", str(dot_path), "-o", str(pdf_path)], repo, commands)
    if (not pdf_path.exists()) or pdf_path.stat().st_size < 1024:
        run([engine, "-Tps", str(dot_path), "-o", str(ps_path)], repo, commands)
        run(["ps2pdf", str(ps_path), str(pdf_path)], repo, commands)
        ps_path.unlink(missing_ok=True)


def generate_object_graph(
    repo: Path,
    out: Path,
    symbol: str,
    module: str,
    commands: list[str],
    depth: int,
) -> tuple[Path | None, str | None]:
    stem = safe_name(symbol)
    dpd = out / "objects" / f"{stem}.dpd"
    dot = out / "objects" / f"{stem}.dot"
    raw_dot = out / "objects" / f"{stem}.full.dot"
    with tempfile.TemporaryDirectory(prefix="rocqsched-dpd-") as tmp_s:
        tmp = Path(tmp_s)
        probe = tmp / f"{stem}.v"
        probe.write_text(
            "\n".join(
                [
                    f"From RocqSched Require Import {module.removeprefix('RocqSched.')}.",
                    "Require dpdgraph.dpdgraph.",
                    f'Set DependGraph File "{dpd}".',
                    f"Print DependGraph {symbol}.",
                    "",
                ]
            ),
            encoding="utf-8",
        )
        try:
            run(["rocq", "c", "-Q", "theories", "RocqSched", str(probe)], repo, commands, capture=True)
        except subprocess.CalledProcessError as exc:
            return None, (exc.stderr or exc.stdout or str(exc)).strip()
    if not dpd.exists() or dpd.stat().st_size == 0:
        return None, "dpdgraph did not produce a non-empty .dpd file"
    objects_dir = out / "objects"
    run(
        ["dpd2dot", "-with-defs", "-rm-trans", "-o", f"{stem}.full.dot", f"{stem}.dpd"],
        objects_dir,
        commands,
    )
    prune_dot_to_root_hops(raw_dot, dot, symbol, depth)
    raw_dot.unlink(missing_ok=True)
    render_dot(repo, dot, commands, engine="sfdp")
    proof_dot = out / "objects" / f"{stem}.proofs.dot"
    proof_raw_dot = out / "objects" / f"{stem}.proofs.full.dot"
    run(
        ["dpd2dot", "-without-defs", "-rm-trans", "-o", f"{stem}.proofs.full.dot", f"{stem}.dpd"],
        objects_dir,
        commands,
    )
    prune_dot_to_root_hops(proof_raw_dot, proof_dot, symbol, depth)
    proof_raw_dot.unlink(missing_ok=True)
    render_dot(repo, proof_dot, commands, engine="sfdp")
    return dot, None


IDENT_RE = r'(?:"([^"]+)"|([A-Za-z_][A-Za-z0-9_]*))'
EDGE_RE = re.compile(IDENT_RE + r"\s*->\s*" + IDENT_RE)
NODE_LABEL_RE = re.compile(IDENT_RE + r"\s*\[(.*label\s*=\s*\"([^\"]+)\".*)\]")


def match_id(match: re.Match[str], offset: int = 0) -> str:
    return match.group(offset + 1) or match.group(offset + 2)


def parse_dot(paths: Iterable[Path]) -> tuple[set[str], set[tuple[str, str]], dict[str, str]]:
    nodes: set[str] = set()
    edges: set[tuple[str, str]] = set()
    labels: dict[str, str] = {}
    for path in paths:
        if path is None or not path.exists():
            continue
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            edge = EDGE_RE.search(line)
            if edge:
                src = match_id(edge, 0)
                dst = match_id(edge, 2)
                nodes.update([src, dst])
                edges.add((src, dst))
                continue
            node = NODE_LABEL_RE.search(line)
            if node:
                node_id = match_id(node, 0)
                label = node.group(4)
                nodes.add(node_id)
                labels[node_id] = label
    return nodes, edges, labels


def node_matches_root(node: str, label: str, root: str) -> bool:
    candidates = {node, label, node.split(".")[-1], label.split(".")[-1]}
    return root in candidates or node.endswith("." + root) or label.endswith("." + root)


def collect_slice(
    roots: list[str],
    nodes: set[str],
    edges: set[tuple[str, str]],
    labels: dict[str, str],
    depth: int,
) -> tuple[set[str], set[tuple[str, str]]]:
    out_edges: dict[str, set[str]] = defaultdict(set)
    in_edges: dict[str, set[str]] = defaultdict(set)
    for src, dst in edges:
        out_edges[src].add(dst)
        in_edges[dst].add(src)

    root_nodes = {
        node
        for node in nodes
        for root in roots
        if node_matches_root(node, labels.get(node, node), root)
    }
    selected = set(root_nodes)
    queue = deque((node, 0) for node in root_nodes)
    while queue:
        node, dist = queue.popleft()
        if dist >= depth:
            continue
        for nxt in sorted(out_edges[node] | in_edges[node]):
            if nxt not in selected:
                selected.add(nxt)
                queue.append((nxt, dist + 1))
    selected_edges = {(src, dst) for src, dst in edges if src in selected and dst in selected}
    return selected, selected_edges


def read_dot_graph(path: Path) -> tuple[dict[str, str], dict[str, str], set[tuple[str, str]]]:
    node_lines: dict[str, str] = {}
    labels: dict[str, str] = {}
    edges: set[tuple[str, str]] = set()
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        edge = EDGE_RE.search(line)
        if edge:
            edges.add((match_id(edge, 0), match_id(edge, 2)))
            continue
        node = NODE_LABEL_RE.search(line)
        if node:
            node_id = match_id(node, 0)
            node_lines[node_id] = line
            labels[node_id] = node.group(4)
            continue
    return node_lines, labels, edges


def prune_dot_to_root_hops(raw_dot: Path, pruned_dot: Path, root: str, depth: int) -> tuple[int, int]:
    node_lines, labels, edges = read_dot_graph(raw_dot)
    out_edges: dict[str, set[str]] = defaultdict(set)
    for src, dst in edges:
        out_edges[src].add(dst)
    root_nodes = {
        node
        for node in set(node_lines) | {src for src, _ in edges} | {dst for _, dst in edges}
        if node_matches_root(node, labels.get(node, node), root)
    }
    selected = set(root_nodes)
    queue = deque((node, 0) for node in root_nodes)
    while queue:
        node, dist = queue.popleft()
        if dist >= depth:
            continue
        for nxt in sorted(out_edges[node]):
            if nxt not in selected:
                selected.add(nxt)
                queue.append((nxt, dist + 1))
    selected_edges = {(src, dst) for src, dst in edges if src in selected and dst in selected}
    with pruned_dot.open("w", encoding="utf-8") as f:
        f.write(f"digraph {safe_name(root)} {{\n")
        f.write("  graph [ratio=0.5]\n")
        f.write("  node [style=filled]\n")
        for node in sorted(selected):
            line = node_lines.get(node)
            if line is not None:
                f.write(line + "\n")
            else:
                f.write(f"  {node} [label=\"{node}\"] ;\n")
        for src, dst in sorted(selected_edges):
            f.write(f"  {src} -> {dst} [] ;\n")
        f.write("}\n")
    return len(selected), len(selected_edges)


def render_slice(
    repo: Path,
    out: Path,
    name: str,
    roots: list[str],
    selected: set[str],
    selected_edges: set[tuple[str, str]],
    labels: dict[str, str],
    commands: list[str],
) -> None:
    dot = out / "slices" / f"{name}.dot"
    with dot.open("w", encoding="utf-8") as f:
        f.write(f"digraph {safe_name(name)} {{\n")
        f.write("  rankdir=LR;\n")
        f.write(f'  graph [fontsize=10, labelloc=t, label="{name}"];\n')
        f.write('  node [shape=box, style="rounded,filled", fontsize=9, fillcolor="#eeeeee"];\n')
        root_set = set(roots)
        for node in sorted(selected):
            label = labels.get(node, node)
            fill = "#fce5cd" if any(node_matches_root(node, label, root) for root in root_set) else "#eeeeee"
            f.write(f'  "{node}" [label="{label}", fillcolor="{fill}"];\n')
        for src, dst in sorted(selected_edges):
            f.write(f'  "{src}" -> "{dst}";\n')
        f.write("}\n")
    render_dot(repo, dot, commands)


def generate_pipeline(repo: Path, out: Path, commands: list[str]) -> None:
    dot = out / "pipeline.dot"
    dot.write_text(
        """digraph pipeline {
  rankdir=LR;
  graph [fontsize=10, labelloc=t, label="Checker trust and refinement pipelines"];
  node [shape=box, style="rounded,filled", fontsize=10, fillcolor="#eeeeee"];
  edge [color="#555555"];

  subgraph cluster_edf {
    label="EDF";
    color="#9fc5e8";
    edf_csv [label="CSV periodic task set", fillcolor="#d9eaf7"];
    edf_gen [label="untrusted Rust witness generator", fillcolor="#f4cccc"];
    edf_cbor [label="CBOR witness", fillcolor="#fff2cc"];
    edf_hs [label="extracted Haskell checker", fillcolor="#d9ead3"];
    edf_thm [label="Rocq soundness theorem", fillcolor="#d9ead3"];
    edf_csv -> edf_gen -> edf_cbor -> edf_hs -> edf_thm;
  }

  subgraph cluster_awk {
    label="Awkernel";
    color="#b6d7a8";
    awk_raw [label="raw Awkernel trace", fillcolor="#fff2cc"];
    awk_norm [label="scheduler-facing event trace", fillcolor="#d9eaf7"];
    awk_check [label="spurious trace checker", fillcolor="#d9ead3"];
    awk_sched [label="projected schedule", fillcolor="#d9eaf7"];
    awk_service [label="service / completion", fillcolor="#d9eaf7"];
    awk_refine [label="policy / refinement theorem", fillcolor="#d9ead3"];
    awk_raw -> awk_norm -> awk_check -> awk_sched -> awk_service -> awk_refine;
  }
}
""",
        encoding="utf-8",
    )
    render_dot(repo, dot, commands)


def write_missing(out: Path, missing: list[str], dpd_failures: dict[str, str]) -> None:
    lines = ["# Missing Symbols", ""]
    if missing:
        lines += ["## Not Found In Rocq Sources", ""]
        lines += [f"- `{symbol}`" for symbol in sorted(missing)]
        lines.append("")
    if dpd_failures:
        lines += ["## Dpdgraph Failures", ""]
        for symbol, error in sorted(dpd_failures.items()):
            one_line = " ".join(error.split())
            lines.append(f"- `{symbol}`: {one_line[:240]}")
        lines.append("")
    if not missing and not dpd_failures:
        lines.append("No missing symbols or dpdgraph failures were detected.")
    (out / "missing_symbols.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_report(
    out: Path,
    commands: list[str],
    rocq_version: str,
    declarations: dict[str, dict[str, str]],
    missing: list[str],
    dpd_failures: dict[str, str],
    module_counts: tuple[int, int],
    object_dots: dict[str, Path],
    depth: int,
) -> None:
    command_summary = [
        "make deps-graph",
        "rocq --version",
        "make all",
        "rocq dep -f _CoqProject",
        "rocq c -Q theories RocqSched <temporary dpdgraph probe>.v",
        "dpd2dot -with-defs -rm-trans <root>.dpd",
        "dpd2dot -without-defs -rm-trans <root>.dpd",
        "dot/sfdp and ps2pdf for SVG/PDF rendering",
    ]
    lines = [
        "# RocqSched Dependency Graphs",
        "",
        "This directory is machine-generated by `make deps-graph`.",
        "",
        "## Environment",
        "",
        f"- Rocq version: `{rocq_version}`",
        f"- Module graph: `{module_counts[0]}` modules, `{module_counts[1]}` edges",
        "",
        "## Commands",
        "",
    ]
    lines += [f"- `{cmd}`" for cmd in command_summary]
    lines += [
        "",
        "## Confirmed Rocq Roots",
        "",
        "| Symbol | Kind | Module | Source |",
        "| --- | --- | --- | --- |",
    ]
    for root in ROOTS:
        info = declarations.get(root.symbol)
        if info is None:
            continue
        lines.append(
            f"| `{root.symbol}` | {info['kind']} / {root.kind} | `{info['module']}` | `{info['path']}:{info['line']}` |"
        )

    lines += [
        "",
        "## Generated Graphs",
        "",
        "- Module dependency graph: `module_graph.svg`, `module_graph.pdf`",
        "- Pipeline diagram: `pipeline.svg`, `pipeline.pdf`",
        f"- Object graphs: `objects/*.svg`, `objects/*.pdf`; each rendered graph is pruned to dependencies reachable from its root in at most `{depth}` hops.",
        f"- Focused slices: `slices/*.svg`; slices use the same `{depth}`-hop default and include reverse dependencies inside the generated object graph set.",
        "",
        "## Important Dependency Chains",
        "",
        "- EDF checker: `periodic_edf_witness_check.hs` calls extracted `check_periodic_edf_checked_sidecar_extracted` or the offset-aware variant; Rocq soundness is rooted at `check_periodic_edf_checked_sidecar_extracted_sound` and `check_periodic_edf_csv_certificate_sound`.",
        "- Awkernel checker: extracted `awk_workload_accepts_*_spurious` accepts scheduler traces; `awk_workload_checker_acceptance_spurious_global_fifo_scheduler_rel` connects accepted traces to a scheduler-facing relation over the projected schedule.",
        "",
        "## Trust Boundary",
        "",
        "- Untrusted inputs: CSV task sets, generated CBOR witnesses, raw Awkernel traces.",
        "- Untrusted producer: Rust witness generator. Its output is checked by extracted Haskell.",
        "- Trusted base: Rocq kernel, extraction mapping for arithmetic, extracted checker code, and Haskell runtime/parser code.",
        "",
        "## Computational vs Proof Roots",
        "",
        "- Computational/extracted roots include EDF sidecar checkers and Awkernel `awk_workload_accepts_*` functions.",
        "- Proof roots include EDF soundness theorems and Awkernel scheduler-facing refinement lemmas.",
        "",
        "## Missing Or Failed Roots",
        "",
        "See `missing_symbols.md`.",
        "",
    ]
    if object_dots:
        lines += ["## Object Graph Roots", ""]
        lines += [f"- `{symbol}` -> `{path.relative_to(out)}`" for symbol, path in sorted(object_dots.items())]
        lines.append("")
    if missing or dpd_failures:
        lines += [
            "Some plan candidates were not present under their example names. They are recorded rather than inferred.",
            "",
        ]
    (out / "README.md").write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default="docs/deps")
    parser.add_argument("--depth", type=int, default=3)
    args = parser.parse_args()

    repo = Path.cwd()
    out = repo / args.out
    commands: list[str] = []

    if out.exists():
        shutil.rmtree(out)
    (out / "objects").mkdir(parents=True)
    (out / "slices").mkdir(parents=True)

    rocq_version = run(["rocq", "--version"], repo, commands, capture=True).stdout.strip().replace("\n", " ")
    run(["make", "all"], repo, commands)
    declarations = scan_declarations(repo)
    missing = [symbol for symbol in MISSING_CANDIDATES if symbol not in declarations]
    missing += [root.symbol for root in ROOTS if root.required and root.symbol not in declarations]

    module_counts = generate_module_graph(repo, out, commands)
    generate_pipeline(repo, out, commands)

    object_dots: dict[str, Path] = {}
    dpd_failures: dict[str, str] = {}
    for root in ROOTS:
        info = declarations.get(root.symbol)
        if info is None:
            continue
        dot, failure = generate_object_graph(repo, out, root.symbol, info["module"], commands, args.depth)
        if dot is not None:
            object_dots[root.symbol] = dot
        else:
            dpd_failures[root.symbol] = failure or "unknown error"

    nodes, edges, labels = parse_dot(object_dots.values())
    for name, roots in SLICE_ROOTS.items():
        existing_roots = [root for root in roots if root in declarations and root in object_dots]
        selected, selected_edges = collect_slice(existing_roots, nodes, edges, labels, args.depth)
        render_slice(repo, out, name, existing_roots, selected, selected_edges, labels, commands)

    write_missing(out, missing, dpd_failures)
    write_report(out, commands, rocq_version, declarations, missing, dpd_failures, module_counts, object_dots, args.depth)
    return 0


if __name__ == "__main__":
    sys.exit(main())
