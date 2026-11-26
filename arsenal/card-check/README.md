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
