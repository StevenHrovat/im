# The SS1 verifier (design draft, nothing built yet)

Status: draft for the owner's words. No code in this pull request. Date: 2026-10-26.

## What it is for

`AGENTS.md` (the same file in DMP, Gravity, IM and CM) tells every coding agent to read DMP.SS1 first and, once it exists, to run every
script it writes through an SS1 verifier before anything runs. DMP.SS1 is the setup-script subset of DMP: a subset of its actions, a
superset of its rules (the owner, 2026-10-26). The owner's reasoning: if DMP holds fully, SS1 is easy to prove, because everything SS1
allows is something DMP already allows. So the verifier is a small program that answers one question per scripted action: is this inside
SS1? It is installed as an MCP server, so an agent calls it as a tool and a person can run it on the command line.

An agent that cannot install it must confirm it has an SS1 verifier for every action it scripts, in every script language where one
exists. The first language is C#.

## Why it lives in IM

- IM already holds the language of acts (`docs/language.md`, `src/Im/Language`): a verb on a noun with adjectives, signed. A scripted action
  is such an act; the verifier is the reference verifier of that language, narrowed to the SS1 table.
- IM holds DMP and Gravity (`vendor/`). A verifier here can pin the exact DMP it checks against and cite the Lean proof of the subset claim
  from Gravity. DMP and Gravity cannot hold code or look down the chain; CM sits above IM, so it receives the verifier by re-pinning IM.
- `docs/language.md` already lists the reference verifier and the MCP facade of the cm.ii interfaces as the next work in IM. The SS1
  verifier is the first consumer of both and should not run ahead of them in CM.
- It needs no CM constellation, so it can be cloned and used from a clean checkout of DMP, Gravity and IM alone (the open-source goal).

CM stays the place where the verifier is run in the gate (`tools/verify`) and where the scripts of administrators live.

## Shape

One executable, `Im.Ss1.Mcp` (C#, .NET 10, MCP over stdio, the official C# SDK, Apache 2.0, as `docs/acknowledgements.md` already records
for MCP), plus a library `Im.Ss1` that holds the rules and no I/O so that the tests and the Lean-checked table can run on it.

MCP tools (read-only, each annotated `readOnlyHint`):

| Tool | Input | Answer |
|---|---|---|
| `ss1_status` | none | the pinned DMP and SS1 version, the languages with a verifier (today `csharp`), the verifier's own hash |
| `ss1_verify` | language, source text or path | verdict (`inside`, `outside`, `unknown`), and per finding: the rule, the line, the action kind |
| `ss1_confirm` | language, hash of the verified source | a short statement an agent pastes into its reply: verifier version, language, source hash, verdict |

The verifier never runs the script and never writes. `unknown` counts as `outside`: what is not fully trusted is not let through (C-infinity).

Install: a single `.exe` per platform, fetched from a release of IM with its sha256 recorded in `SETUP.md` (a new toolchain row, which also
makes `check-setup.sh` track it). `AGENTS.md` says "install it when available": the agent reads the row, downloads, checks the hash, runs
`ss1_status`. If any step fails the agent falls back to the confirmation duty in `AGENTS.md`.

## What it checks for C#

Two tables, both from SS1 once it is written down, not from this draft:

1. **Actions (the subset).** Each call in the script that reaches outside the process is classified as an IM act kind (`docs/language.md`,
   twelve kinds): read, write or execute on a noun of a layer. Only the kinds SS1 lists pass. Unclassifiable calls (reflection, dynamic
   loading, `Process.Start` with a computed command line) are `unknown`.
2. **Rules (the superset).** The rules of the safe-script standard (guard first, host and context asserted, read-only or changes declared,
   dry run before apply, read before write, absolute paths, no secret literal, no ambient authority), plus whatever SS1 adds.

How the source is read is the open design question below.

## The proof claim

If SS1 is a subset of DMP's actions and a superset of its rules, then `ss1_verify = inside` implies the DMP verifier accepts each act.
That is a theorem for Gravity (`evidence/Dmp`), stated over the same two tables the C# reads, and checked by the same differential method as
the IM language (`proof/`): the table is generated into C# or compared against it, so the two cannot drift. Both chains of the root
chain apply (C22): the intent chain DMP to IM to CM, and the evidence chain from the verifier's tests up. Nothing here is claimed until
DMP.SS1 has a text to state the theorem about.

## Open questions for the owner

1. **The text of DMP.SS1.** It is not written anywhere yet. Where does it live: a chapter in DMP, or an extension (the parked idea of
   extensions per layer, with `import DMP`)? The verifier waits for it. Needs the owner's own words.
2. **Reading C# source.** Options: (a) Roslyn (MIT, Microsoft) for a real syntax and semantic model, one dependency beyond the base class
   library, which IM avoids today; (b) a restricted C# subset the verifier parses itself, no dependency but a smaller language; (c) the
   script is not analysed at all but must be written as IM sentences (a data file), which is the cleanest proof and the biggest change for
   agents. Recommendation: (a), declared as a dependency in `SETUP.md` and pinned, because agents will write ordinary C#.
3. **Other languages.** PowerShell is what administrators run today. The verifier for it would be a second implementation behind the same three tools. Not before C#.
4. **Release channel.** A GitHub release of IM is the simplest source for the `.exe`; the repositories are not public yet, so the first
   consumers install from a local build until they are.

## Pull request order after the owner's OK

1. DMP.SS1 text (the owner's words), then the Lean statement of the subset claim in Gravity.
2. The reference verifier and the MCP facade in IM (already planned).
3. `Im.Ss1` and `Im.Ss1.Mcp`, the `SETUP.md` row, and the `AGENTS.md` sentence changes from "when available" to the install step.
