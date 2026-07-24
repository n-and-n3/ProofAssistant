# Demonstration programs

All valid examples can be checked with `main2.cpp`:

```sh
g++ -std=c++20 -O2 -Wall -Wextra -Werror main2.cpp -o main2
./main2 demos/01_identity.n3
```

## Small examples

- `01_identity.n3` proves `|- A -> A` in four lines.
- `02_modus_ponens.n3` proves `A, A -> B |- B`.

## Intentional syntax errors

The files under `errors/` must fail:

- `01_missing_semicolon.n3`: the `Type` statement has no semicolon.
- `02_missing_template_bracket.n3`: `Id<A>()` is missing `>`.
- `03_missing_identifier.n3`: `print` has no sequent identifier.

Each error should report a different English diagnostic with a line and column
range.

## Medium example

`03_chain_and_contraposition.n3` has 58 lines. Its claim is:

```text
(A->B)*(B->C)*(C->D)*(D->E)
|-
(A->E)*(~E->~A)*(A->D)*(~D->~A)
```

It combines transitivity of implication with two contraposition results.

## Generated stress examples

- `large_excluded_middle_512.n3`: 2,561 lines.
- `large_excluded_middle_2048.n3`: 10,241 lines.

They prove a balanced conjunction of 512 or 2,048 instances of excluded
middle, `(Pi + ~Pi)`. Both files were produced by the Python automatic prover,
not handwritten.

Regenerate them with:

```sh
python3 demos/generate_large_demos.py
```
