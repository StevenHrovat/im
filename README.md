# IM, the Interstellar Medium

The machine- and audit-readable medium every CMOS part speaks: the byte format of IM, the client side of a session, and the trust core
it rests on (the dual chain of trust, chain verdicts with roles as EKUs, enrolment, the IM signer). The specification is chapter 04 of
[DMP, the Dark Matter Protocol](https://github.com/StevenHrovat/dmp/blob/main/04-im.md); the verify rules live in Milky Way, part of
[CM, Canis Major](https://github.com/StevenHrovat/cm). Status: draft, IM version 0.

Used by Milky Way (which also verifies), Doppler (which issues tokens) and any device agent or client (which knocks, answers the
challenge and sends messages). It is its own library so that no CM constellation references another (constitution C1).

**A second reading of the letters: Identity Multiplication.** The name stays the Interstellar Medium. The letters also read true as
Identity Multiplication: the arsenal's rotation API (`arsenal/Arsenal/Rotation.lean`) is multiplication by a number on the unit
circle, which keeps the norm and moves only the phase, so what is carried keeps its identity across every step.


| Type | What it is | Used by |
|---|---|---|
| `ImWriter`, `ImReader`, `ImFormatException` | canonical big-endian encoding, strict reading with limits, error codes without content | everything here |
| `ImTags`, `ImKeys`, `ImChains` | domain tags, the one signature algorithm (ECDSA P-256, SHA-256, 64-byte P1363) over SubjectPublicKeyInfo keys, chains in wire order | token, envelope, frames |
| `ImTokenClaims`, `ImTokenCodec`, `ImToken` | the token: Doppler calls `Issue(claims, signer, issuedAt)` with its `ImTokenSigner` key; readers call `Parse` | Doppler, the verifier |
| `ImRoles`, `ImKinds` | the wire spelling of the enrolled roles; the table of kinds and the permission each needs | Doppler (role to permissions), the verifier |
| `ImEnvelopeCodec`, `ImEnvelope`, `ImHeartbeat` | the signed envelope; the heartbeat payload | senders, the verifier |
| `ImFrames`, `ImClientSession` | the handshake frames; the client side of a session (checks the gate in the role `MilkyWayGate`) | device agents, the simulator |
| `ImStreamFraming`, `ImTls`, `ImTlsIdentity`, `ImTlsClientConnection` | frames on a stream (4-byte length first); TLS 1.3 with mutual certificates checked by `ITrustAnchors` in their roles; the device side of a session over TLS, bound to the gate certificate TLS showed (DMP 05, "Transport encryption"); `ImTlsIdentity.Of` exports a signer's key for TLS, `ImTlsIdentity.Bound` takes a certificate already joined to a key that cannot be exported (a TPM key) as it is | device agents, the gate's transport, the simulator |

What Doppler does with it: issue a token per enrolled device with `ImTokenCodec.Issue`, giving every enrolled role `im.session.open` and
`im.heartbeat.send` in version 0; keep `IEnrolmentRegistry` true (subject, role, KeyId of the device key, revoked). Changing a field, a tag
or the algorithm is a contract change (C4) and a new IM version.

## The language

IM is the language of acts: a sentence is a verb (read, write or execute) on a noun (an item of an information layer) with its adjectives
(dry or apply; what a write expects to find), spoken with both witnesses' grants and signed so it proves itself. The grammar, its wire form
and its laws: [docs/language.md](docs/language.md). The proof that every sentence of the closed grammar keeps every law, decided by Lean's
kernel: [proof/](proof/) (`proof/tools/check.sh`). The C# of the sentence: `src/Im/Language`. What IM stands on, with thanks:
[docs/acknowledgements.md](docs/acknowledgements.md); what the proof found: [docs/findings.md](docs/findings.md).

IM holds DMP and Gravity in the versions it is intended for, byte for byte with a PIN ([vendor/](vendor/README.md), DMP 00 "The root
chain"), and with them `vendor/dmp/SETUP.md`, the one setup file of the four root repositories: what to install, from where, with which
hash. `tools/lean-install.sh` follows it.

## The arsenal

[arsenal/](arsenal/README.md) holds IM's transferable Lean results that need Mathlib (Lean v4.34.0, Mathlib v4.34.0, nothing else),
imported from here only. Its gate is a lint: a change contains nothing that cannot run, so nothing that cannot be soundly constructed; a
statement left open is answered R136a1 (a named hypothesis), never `sorry`. First piece: the Mathlib-only core of Birch and
Swinnerton-Dyer.

## Two kernels, the Externals and the supply

IM contains two kernels in the sense of G0: not their content, a pinned link to each, whose supply every valid minting needs (the first
author, 2026-11-25; DMP 01, mint prep: preparing a minting stores every dependency and verifies each against its pin, and the White Key
Holders carry it). The root repository stays lean (DMP 00: toolchains join only at mint prep).

- **The Externals** ([externals/EXTERNALS](externals/EXTERNALS)): the Lean toolchain (the language and the first kernel, Lean's own,
  with `leanchecker`), lean4export, nanoda (the second kernel, written separately, in Rust) and lean4lean (an optional third), each by
  its commit or its sha256; Mathlib and every package it needs are pinned by commit in `arsenal/lake-manifest.json`.
- **Proven before used**: `tools/trust-roundtrip.sh` fetches every pinned commit by its id and recomputes the id from its content, and
  rebuilds each held copy (`vendor/`) byte for byte, before every commit and push (`.githooks`; once per clone:
  `git config core.hooksPath .githooks`) and in `tools/verify`. Gravity pins IM by construction, so what Gravity uses of IM is a
  proven IM.
- **The supply** (mint prep): `tools/rebuild supply <dir>` fetches every External by its pin, recomputes each hash and writes the
  offline supply; `tools/rebuild supply-verify <dir>` refuses a supply in which anything is missing or differs.
- **The check**: `tools/rebuild check <core|arsenal|path> [quick|full] [--supply <dir>]`. Lean's kernel replays the declarations
  (`leanchecker`, `--fresh` from nothing in full mode) and nanoda checks the exported terms; a declaration counts only when both accept
  it, on the standard axioms only. Quick mode checks the target's own modules with the first kernel and, with the second, the target
  together with everything it uses, Mathlib and Lean core included. Full mode checks the whole closure with both (hours, about 16 GB of
  RAM for Mathlib) and writes a stamp. With `--supply` everything comes from the supply, offline, and Mathlib is built from its source;
  without it Mathlib's prebuilt files are fetched, and only the kernels' re-check makes them trusted. `<path>` is any Lake project
  that pins IM, for example a Gravity build folder of the paper's Lean. `tools/verify` runs `tools/rebuild check core` on every
  change.
- **The API, a k by k table**: `tools/rebuild matrix <repo> ...` takes IM and the repositories named; the cell in a row and a column
  says whether the row proves the column (the diagonal: the part's own round trip; off it: the row holds the column, its copy proven
  back and forth, or pins it, the pinned commit proven), and the command passes only when every cell is `+`. A repository that uses
  IM asserts exactly that (the first author, 2026-11-25: "gravity can use it as an API, because it just has to assert an array of k by
  k with + at each cell"). A cell where no proof relates two parts shows `·` and does not count as `+`; whether it may is the first
  author's decision. Today IM and Gravity give a 2 by 2 of `+`.

## Build and test

```
tools/verify             # the one gate: pins, trusted hashes, the setup file, the scrub scan, build, tests, the proof, two kernels; exit 0 or 1
tools/rebuild check core # IM's finite layer through both kernels (seconds once the checkers are built)
dotnet build Im.slnx
dotnet test Im.slnx
proof/tools/check.sh     # the proof alone (lean and lake on the PATH: tools/lean-install.sh)
arsenal/tools/check.sh   # the arsenal: lint, build against Mathlib, axiom report (arsenal/README.md)
```

C# on .NET 10, no dependency beyond the base class library. Package versions live in `Directory.Packages.props` only.
`tools/scrub-scan.sh` keeps identifiers of real organisations, hosts, people and credentials out of the repository.

Licensed under the Apache License 2.0 ([LICENSE](LICENSE)).
