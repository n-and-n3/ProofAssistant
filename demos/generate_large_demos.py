"""Generate the large demonstration proofs with the project's proof synthesizer."""

from __future__ import annotations

import sys
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from main import generate_n3  # noqa: E402


def balanced_conjunction(formulas: list[str]) -> str:
    if not formulas:
        raise ValueError("At least one formula is required.")

    current = formulas
    while len(current) > 1:
        current = [
            f"({current[index]}*{current[index + 1]})"
            if index + 1 < len(current)
            else current[index]
            for index in range(0, len(current), 2)
        ]
    return current[0]


def generate_excluded_middle_demo(proposition_count: int) -> Path:
    formulas = [
        f"(P{index}+~P{index})"
        for index in range(proposition_count)
    ]
    goal = "|- " + balanced_conjunction(formulas)
    output = Path(__file__).parent / (
        f"large_excluded_middle_{proposition_count}.n3"
    )
    output.write_text(generate_n3(goal), encoding="utf-8")
    return output


def main() -> None:
    for proposition_count in (512, 2048):
        output = generate_excluded_middle_demo(proposition_count)
        print(output)


if __name__ == "__main__":
    main()
