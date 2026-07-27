"""Generate a checked LK proof of R(3,3) <= 6.

The proof branches on the color of each edge.  Once either color contains a
triangle, that branch is closed immediately.  Branches are joined with the
law of excluded middle and cut.
"""

from __future__ import annotations

from functools import cache
from itertools import combinations
from pathlib import Path
import re
import sys


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from main import (  # noqa: E402
    DEFAULT_SEQUENT,
    Proof,
    Prop,
    Sequent,
    _make_proof,
    emit_n3,
    generate_n3,
    parse_sequent,
)


EDGES = tuple(
    f"P{left}{right}"
    for left, right in combinations(range(1, 7), 2)
)
TRIANGLES = tuple(
    (
        f"P{first}{second}",
        f"P{first}{third}",
        f"P{second}{third}",
    )
    for first, second, third in combinations(range(1, 7), 3)
)

LOWER_BOUND_SEQUENT = """Q12,Q23,Q34,Q45,Q15,
~Q13,~Q14,~Q24,~Q25,~Q35
|-
~(
    (Q12*Q13*Q23) + (~Q12*~Q13*~Q23)
    + (Q12*Q14*Q24) + (~Q12*~Q14*~Q24)
    + (Q12*Q15*Q25) + (~Q12*~Q15*~Q25)
    + (Q13*Q14*Q34) + (~Q13*~Q14*~Q34)
    + (Q13*Q15*Q35) + (~Q13*~Q15*~Q35)
    + (Q14*Q15*Q45) + (~Q14*~Q15*~Q45)
    + (Q23*Q24*Q34) + (~Q23*~Q24*~Q34)
    + (Q23*Q25*Q35) + (~Q23*~Q25*~Q35)
    + (Q24*Q25*Q45) + (~Q24*~Q25*~Q45)
    + (Q34*Q35*Q45) + (~Q34*~Q35*~Q45)
)"""


def variable(name: str) -> Prop:
    return Prop.variable(name)


def conjunction(parts: tuple[Prop, ...]) -> Prop:
    result = parts[0]
    for part in parts[1:]:
        result = Prop.binary("and", result, part)
    return result


def contains_prop(root: Prop, target: Prop) -> bool:
    if root == target:
        return True
    return root.kind == "or" and any(
        contains_prop(child, target) for child in root.args
    )


def weaken_left(proof: Proof, additions: frozenset[Prop]) -> Proof:
    result = proof
    for prop in sorted(additions, key=str):
        if prop not in result.conclusion.ant:
            result = _make_proof("KL", (prop,), (result,))
    return result


def lift_disjunct(proof: Proof, root: Prop, target: Prop) -> Proof:
    if root == target:
        return proof
    if root.kind != "or":
        raise RuntimeError(f"{target} is not a disjunct of {root}")

    left, right = root.args
    if contains_prop(left, target):
        premise = lift_disjunct(proof, left, target)
        premise = _make_proof("KR", (right,), (premise,))
    elif contains_prop(right, target):
        premise = lift_disjunct(proof, right, target)
        premise = _make_proof("KR", (left,), (premise,))
    else:
        raise RuntimeError(f"{target} is not a disjunct of {root}")
    return _make_proof("orR", (left, right), (premise,))


@cache
def excluded_middle(prop: Prop) -> Proof:
    identity = _make_proof("Id", (prop,), ())
    negated = _make_proof("notR", (prop,), (identity,))
    return _make_proof(
        "orR",
        (prop, Prop.unary("not", prop)),
        (negated,),
    )


def monochromatic_triangle(
    true_edges: frozenset[str],
    false_edges: frozenset[str],
) -> tuple[tuple[str, str, str], bool] | None:
    for triangle in TRIANGLES:
        edge_set = frozenset(triangle)
        if edge_set <= true_edges:
            return triangle, True
        if edge_set <= false_edges:
            return triangle, False
    return None


def generate_upper_bound() -> str:
    goal = parse_sequent(DEFAULT_SEQUENT)
    if len(goal.suc) != 1:
        raise RuntimeError("Ramsey goal must have exactly one succedent.")
    goal_prop = next(iter(goal.suc))

    @cache
    def triangle_proof(
        triangle: tuple[str, str, str],
        positive: bool,
    ) -> Proof:
        literals = tuple(
            variable(edge)
            if positive
            else Prop.unary("not", variable(edge))
            for edge in triangle
        )
        context = frozenset(literals)
        identities = tuple(
            weaken_left(
                _make_proof("Id", (literal,), ()),
                context - {literal},
            )
            for literal in literals
        )
        first_pair = _make_proof(
            "andR",
            (literals[0], literals[1]),
            (identities[0], identities[1]),
        )
        term = conjunction(literals)
        term_proof = _make_proof(
            "andR",
            (conjunction(literals[:2]), literals[2]),
            (first_pair, identities[2]),
        )
        return lift_disjunct(term_proof, goal_prop, term)

    @cache
    def build(
        edge_index: int,
        true_edges: frozenset[str],
        false_edges: frozenset[str],
    ) -> Proof:
        found = monochromatic_triangle(true_edges, false_edges)
        context = frozenset(
            [variable(edge) for edge in true_edges]
            + [
                Prop.unary("not", variable(edge))
                for edge in false_edges
            ]
        )
        if found is not None:
            triangle, positive = found
            base = triangle_proof(triangle, positive)
            return weaken_left(base, context - base.conclusion.ant)

        if edge_index >= len(EDGES):
            raise RuntimeError(
                "A complete coloring without a monochromatic triangle "
                "was encountered."
            )

        edge_name = EDGES[edge_index]
        edge = variable(edge_name)
        negated_edge = Prop.unary("not", edge)
        positive_branch = build(
            edge_index + 1,
            true_edges | {edge_name},
            false_edges,
        )
        negative_branch = build(
            edge_index + 1,
            true_edges,
            false_edges | {edge_name},
        )
        cases = _make_proof(
            "orL",
            (edge, negated_edge),
            (positive_branch, negative_branch),
        )

        excluded = excluded_middle(edge)
        excluded = _make_proof("KR", (goal_prop,), (excluded,))
        excluded = weaken_left(excluded, context)
        case_formula = Prop.binary("or", edge, negated_edge)
        return _make_proof("cut", (case_formula,), (excluded, cases))

    root = build(0, frozenset(), frozenset())
    if root.conclusion != goal:
        raise RuntimeError(
            f"Generated conclusion {root.conclusion} differs from {goal}."
        )
    header = [
        "// Proof of R(3,3) <= 6.",
        "// Generated by demos/generate_ramsey_proof.py.",
        "// The 15 variables color the edges of K6; each disjunct is a",
        "// monochromatic triangle in one of the two colors.",
        "",
    ]
    return "\n".join(header) + emit_n3(goal, root)


def renumber_proofs(program: str, offset: int) -> str:
    return re.sub(
        r"\bproof([0-9]+)\b",
        lambda match: f"proof{int(match.group(1)) + offset}",
        program,
    )


def generate() -> str:
    upper_bound = generate_upper_bound()
    proof_numbers = [
        int(value) for value in re.findall(r"\bproof([0-9]+)\b", upper_bound)
    ]
    lower_bound = generate_n3(LOWER_BOUND_SEQUENT)
    lower_bound = renumber_proofs(
        lower_bound,
        max(proof_numbers, default=-1) + 1,
    )
    lower_numbers = [
        int(value) for value in re.findall(r"\bproof([0-9]+)\b", lower_bound)
    ]
    if not lower_numbers:
        raise RuntimeError("The lower-bound generator produced no proof.")
    lower_bound = re.sub(
        rf"\bproof{max(lower_numbers)}\b",
        "ramsey_lower_bound",
        lower_bound,
    )
    lower_header = [
        "",
        "// Proof of R(3,3) > 5.",
        "// The Q variables describe a two-coloring of K5.",
        "// True edges form the cycle 1-2-3-4-5-1; false edges form",
        "// its complementary 5-cycle. Neither color has a triangle.",
        "",
    ]
    return upper_bound.rstrip() + "\n" + "\n".join(lower_header) + lower_bound


def main() -> None:
    output = PROJECT_ROOT / "proofs" / "Ramsey's_theorem.n3"
    output.write_text(generate(), encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
