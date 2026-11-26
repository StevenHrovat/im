# The card check

A GitHub Action (and the script behind it) that gives any Lean project the arsenal's gate. For the modules it is pointed at:

1. **Well-formed.** The modules build: every statement elaborates against the project's own Mathlib, or the check fails.
2. **No escape hatch** in their source (`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`,
   `ofReduceBool`, `skipKernelTC`; code only, never comments or strings). A statement left open is named instead:
   `R136a1 "name" P` (`Arsenal.R136a1`), a hypothesis, never an axiom.
3. **The kernel's axiom report.** Every declaration rests on `propext`, `Quot.sound`, `Classical.choice` at most.
4. **The route and the derivation** of every declaration: the outside inputs its statement names (every `R136a1 "name" _`,
   seen through the definitions of the checked modules and of the arsenal) and the declarations its proof uses directly. A
   declaration of type `Arsenal.Problems.Card` is listed as a card. The report goes to the job summary and to
   `card-check-report/report.txt`.

## Credit

A correct DMP route is a DAG, and the route is the credit: who formulated each step the result is built on. In Lean the derivation
is a DAG by construction (a declaration is admitted only after everything it uses), so the check prints it as a path:

```
credit: DMP.GRH.R136a1.RHLibrary.Problems.riemann_of_library (GRH: derived)
credit: DMP.GRH.Problems.poincare (GRH: reading)
```

`DMP.`, then `GRH.`, then the modules of the declaration's derivation in import order (each after everything it imports; the
arsenal's modules by their own name), then the declaration.

* **`DMP.GRH.` starts every route.** The first author's reading (2026-11-26): binary is the shape of a problem, and GRH is a
  universal decoder for binary, so every route of the problem card API starts at GRH. The first half rests on a proof: a yes/no
  question has exactly two answers (`ArsenalCore.Possibility.answers_of_idem`). The second half, GRH as the universal decoder, is
  the reading.
* **Derived or reading.** `GRH: derived` when the declaration's derivation passes through `Arsenal.GRH` (RH's does: the arsenal's
  ladder from GRH down to RH, `Arsenal.GRH.riemannHypothesis_of_dirichlet`). `GRH: reading` otherwise (Poincaré, P ≠ NP and BSD use
  nothing of `Arsenal.GRH`): there the root is the reading above, not a step the kernel checked. The two are kept apart, so the
  check never reports a derivation that the kernel does not show.

**What it cannot do.** It does not decide whether a statement is true and does not find proofs: no program can, for every
statement (Turing 1936; in Mathlib, `ComputablePred.halting_problem`). A module the check passes is well-formed and honest about
what it rests on. A card in it is solved only where a proof is there, in the module or named as an outside input.

## Use

In a Lean project (any Lean and Mathlib version it pins), in a workflow:

```yaml
- uses: actions/checkout@v4
- uses: StevenHrovat/im/arsenal/card-check@<commit>
  with:
    project: .              # the Lake project's folder
    modules: MyProject.Cards MyProject.Routes
```

The card shape and the layer are optional: to use them, require the arsenal (`../README.md`, "Using it") and
`import Arsenal.Problems`. Without the arsenal, steps 1 to 3 and the derivation work the same, and no outside inputs are listed.

Locally: `arsenal/card-check/card-check.sh <project-dir> <Module> ...` (Lean on the PATH; Mathlib's prebuilt files fetched with
`lake exe cache get`).

## Its own check

`arsenal/card-check/selftest.sh` plants three modules in the arsenal for one run and removes them: a `sorry` (refused by the
source scan), an axiom declared in an unchecked module and used in a checked one (refused by the axiom report), and a card with
a named outside input (passes; the card and the input listed). It needs the arsenal built against Mathlib, as
`../tools/check.sh` does, so it is not part of `tools/verify`.

Run on the arsenal itself (`card-check.sh . Arsenal.Problems Arsenal.RHLibrary`): 92 declarations, 4 cards, none resting on more
than the three standard axioms; outside inputs: the RH library and Perelman's proof (`Arsenal.Problems.millennium_left`).

The paper it serves: [Draft 6 of GUID v8](https://github.com/StevenHrovat/gravity/blob/main/docs/paper/D6/latex/guid-v8-D6.pdf).
