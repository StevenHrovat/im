import Im.Laws
import Im.Wire
/-!
# The closure: every sentence of the space keeps every law

The owner, 2026-10-26: "generate the whole possibility space of IM commands and prove every one of them DMP-compliant". The space is
`Shape.all` (every kind, mode and expectation; Grammar.lean proves the list complete) with any legal path. For each shape the kernel
decides the laws that are decidable per sentence, and the laws that quantify over grants, paths or inputs are proved once for every
sentence (Laws.lean, Wire.lean). `closure` ties both: there is no sentence outside the list, and every one in it is lawful.

Nothing here is vacuous: `space_size` is the count the kernel computes, and `Shape.all_complete` is the completeness.

What this is not: a proof about authority over time. Safety for a general access matrix is undecidable even with the alphabet read,
write, execute (Harrison, Ruzzo and Ullman, 1976); it is decidable under a closed table of kinds, tokens that only attenuate and no
command that creates authority (Jones, Lipton and Snyder, 1976 and 1977; Sandhu, 1988 and 1992). Those are hypotheses this grammar keeps by
construction, and the attenuation theorem is still to be written (docs/findings.md, IF9).
-/
namespace Im

/-- The laws the kernel decides per shape: a legal kind name, the kind in the table, and the sample sentence of the shape either ill
    formed (so no door sees it) or round-tripping on the wire. -/
def Shape.lawfulB (sh : Shape) : Bool :=
  nameOk sh.kind.wire && sh.kind ∈ Kind.all &&
  (!sh.wfB || (Sentence.decode sh.kind sh.sample.encode == some sh.sample))

/-- Every shape of the space is lawful: decided by the kernel over the generated list. -/
theorem all_shapes_lawful : (Shape.all.all Shape.lawfulB) = true := by decide +kernel

/-- The closure: every sentence keeps the decidable laws (through its shape) and the universal ones (through Laws.lean and Wire.lean). -/
theorem closure (s : Sentence) : s.shape.lawfulB = true :=
  (List.all_eq_true.mp all_shapes_lawful) s.shape (Shape.all_complete s.shape)

/-- The size of the space, computed by the kernel. -/
theorem space_size : Shape.all.length = 72 := by decide +kernel

/-- The size of the well-formed space: what a door ever sees. -/
theorem wf_space_size : Shape.allWf.length = 32 := by decide +kernel

/-- The kinds: four layers, three verbs. -/
theorem kinds_size : Kind.all.length = 12 := by decide +kernel

end Im
