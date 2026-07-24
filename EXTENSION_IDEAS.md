# ProofAssistant extension ideas

Difficulty uses five levels: 1 is a small local change and 5 is a substantial
language or architecture project. Interest is subjective and also uses five
levels.

| Idea | Difficulty | Interest | What makes it valuable |
|---|---:|---:|---|
| Better diagnostics and recovery | 2 | 4 | Report several errors in one run, show source excerpts and carets, and suggest likely fixes. |
| Formatter | 2 | 3 | Gives `.n3` a canonical layout and is useful before editor integration. |
| Proof-tree printer | 2 | 5 | Export derivations as text, Graphviz, SVG, or LaTeX so users can inspect what a proof means. |
| `cut` rule | 2 | 4 | Small kernel addition with a large effect on how reusable and human-readable proofs can be. |
| Named lemmas and parameters | 3 | 5 | Turns repeated proof fragments into reusable abstractions instead of copied rule applications. |
| Module/import system | 3 | 4 | Allows a standard library of lemmas, but requires namespaces, cycle handling, and source-aware diagnostics. |
| LSP server | 4 | 5 | Enables live diagnostics, hover types, go-to-definition, references, completion, and semantic highlighting. |
| Incremental evaluator | 4 | 4 | Rechecks only statements affected by an edit; especially useful for the LSP and very large proofs. |
| Interactive proof mode | 4 | 5 | Shows the current goals and lets users apply rules one step at a time, like a small theorem-prover REPL. |
| Tactic language | 4 | 5 | Adds commands such as `intro`, `cases`, `assumption`, and `auto`, compiling them into kernel-checked rules. |
| Proof-term serialization | 3 | 4 | A stable JSON or binary format makes testing, caching, visualization, and external tooling easier. |
| `true` and `false` constants | 2 | 3 | A manageable first extension to the proposition language and sequent rules. |
| First-order predicates and quantifiers | 5 | 5 | Adds terms, variables, substitution, scopes, freshness conditions, and quantifier rules. |
| Natural numbers | 5 | 5 | Requires term syntax, equality, induction, computation or rewriting, and a much richer type discipline. |
| Equality and rewriting | 4 | 5 | Makes algebraic and arithmetic proofs practical, but requires careful substitution and congruence handling. |
| Multiple proof backends | 4 | 4 | Export to Lean, Coq, Isabelle, or SMT-LIB for cross-checking and interoperability. |
| Kernel hardening and fuzzing | 3 | 4 | Property tests and parser fuzzing improve confidence that malformed proofs cannot bypass validation. |

## Suggested order

1. Improve diagnostics, add a formatter, and add proof-tree output.
2. Add `cut`, named lemmas, and a small standard library.
3. Separate parsing, semantic analysis, and kernel checking behind stable APIs.
4. Build an LSP on those APIs, then add incremental re-evaluation.
5. Add an interactive mode and tactics that elaborate into the small trusted
   kernel.
6. Only then expand the logic toward equality, first-order quantifiers, and
   natural numbers.

This order keeps the trusted kernel small while making the language pleasant
to use. Natural numbers are especially interesting, but starting there would
mix parser design, binding, types, computation, equality, induction, and proof
automation into one large change.

## Particularly promising projects

### LSP

The current token and AST source spans are already the first prerequisite.
The next architectural step is to make parsing and evaluation return structured
diagnostics instead of printing or throwing as their only interface. A minimal
LSP can begin with live diagnostics and hover information; completion and
go-to-definition can follow once symbols have stable definitions.

### `cut`

For sequents `Γ |- Δ, A` and `A, Γ |- Δ`, `cut<A>` derives `Γ |- Δ`.
Implementation is relatively small, but it should verify that both remaining
contexts match exactly. It also creates interesting follow-up work: proof
normalization and cut elimination.

### Natural numbers

A serious natural-number extension should not encode numbers as proposition
names. It needs a term layer distinct from propositions, such as `Nat`, `0`,
`succ(n)`, functions, equality, and induction. This is a new logic rather than
one extra inference rule, so it is best treated as a later milestone after
binding, substitution, and reusable lemmas are solid.
