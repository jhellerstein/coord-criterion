import CoordCriterion.Instances.Examples

/-!
# Paper §5, "Composition and Proper Coordination" (`sections/composition.tex`)

Statement layer for Section `sec:composition`.  Read it side by side with
`sections/composition.tex`: the `/-! ## … -/` headers follow the section's
subsections, entries appear in paper order, and each entry quotes the claim
it formalizes.  Numbered results and displayed equations are named by their
LaTeX label; unlabeled claims are `«sec:composition/<slug>»`.  The proofs
are in Appendix `app:composition`; its curried evaluation and the converse
counterexample are in `Paper/AppD_Composition.lean`.

The section has no subsection heading for sequential composition; its label
`sec:sequential-composition` sits after the section opening.  Composition with
independent inputs (`sec:parameterized-composition`) is in Appendix
`app:composition` and `Paper/AppD_Composition.lean`; the Proper Coordination
entries below state both the sequential and the parameterized forms.

Library: `Appendix/Composition.lean` (namespace `CC.Comp`) and the examples
at the end of `Instances/Examples.lean` (namespace `CC.Inst`).

Conventions: a table is `Table I O := I → O → Prop`; `Spec I O` is a table
total on all of `I` with orders on `I` and `O`; products carry the
componentwise order; the composed input `I × J × A` is `I × (J × A)`;
`Comp.graph f` is the table of `f`, and `Comp.Monotone f` is
`∀ x y, x ≼ y → f x ≼ f y`.  A commitment strategy is recorded by its
declared committed table `K ⊆ S₁` (`Comp.CommitTable`), whose field `total`
is totality preservation; `κ.spec` is `K` read as a specification.
-/

namespace CC
namespace Paper

open CC.Comp (Monotone graph)

/-! ## Sequential composition (`sec:sequential-composition`) -/

/-- Eq. `eq:spec-composition`:
`S₂ ∘ S₁ = π_{I,O}(S₁ ⋈_M S₂) = {(i,o) : ∃ m. (i,m) ∈ S₁ ∧ (m,o) ∈ S₂}`. -/
theorem «eq:spec-composition» {I M O : Type} (S1 : Table I M) (S2 : Table M O) (i : I) (o : O) :
    Comp.tcomp S1 S2 i o ↔ ∃ m, S1 i m ∧ S2 m o :=
  Iff.rfl

/-- "Since `S₁` is total on `I` and `S₂` is total on `M` (it has a row at
every `m ∈ M`), every `i ∈ I` has a nonempty fiber in `S₂ ∘ S₁`."  Lean: the
composition is the specification `Comp.seq sp1 sp2`, whose table is
`tcomp`; totality is its `total` field. -/
theorem «sec:composition/seq-total» {I M O : Type} [PO I] [PO M] [PO O]
    (sp1 : Spec I M) (sp2 : Spec M O) :
    (Comp.seq sp1 sp2).S = Comp.tcomp sp1.S sp2.S ∧ ∀ i, ∃ o, Comp.tcomp sp1.S sp2.S i o :=
  ⟨rfl, (Comp.seq sp1 sp2).total⟩

/-- Totality of `S₂` on *all* of `M` is needed (not stated in the paper; it
explains the hypothesis above).  If `S₂` is total only on a proper subset of
`M`, Lemma `lem:composition` fails even when the composed table is total. -/
theorem «sec:composition/middle-totality-needed» :
    Comp.s1.LiftedMono ∧ (Comp.restrict Comp.t2).LiftedMono ∧
      (∀ i, ∃ o, Comp.tcomp Comp.s1.S Comp.t2 i o) ∧
      ¬ (Comp.restrict (Comp.tcomp Comp.s1.S Comp.t2)).LiftedMono :=
  Comp.restricted_middle_counterexample

/-- **Lemma `lem:composition`** (Composition): "If `Spec₁` and `Spec₂`
satisfy Lifted Monotonicity, then the ordered specification with table
`S₂ ∘ S₁` satisfies Lifted Monotonicity." -/
theorem «lem:composition» {I M O : Type} [PO I] [PO M] [PO O] {sp1 : Spec I M} {sp2 : Spec M O}
    (h1 : sp1.LiftedMono) (h2 : sp2.LiftedMono) : (Comp.seq sp1 sp2).LiftedMono :=
  Comp.seq_liftedMono h1 h2

/-- "By associativity the lemma extends to finite pipelines." -/
theorem «sec:composition/associativity» {I M O P : Type} (S1 : Table I M) (S2 : Table M O)
    (S3 : Table O P) :
    Comp.tcomp (Comp.tcomp S1 S2) S3 = Comp.tcomp S1 (Comp.tcomp S2 S3) :=
  Comp.tcomp_assoc S1 S2 S3

/-- "For a function `f`, its table `{(i,f(i))}` satisfies
Lifted Monotonicity exactly when `f` is monotone.  Tables of functions are closed
under `∘`."  Lean: the composition of the tables of `f` and `g` is the
table of `g ∘ f`, and the table of `f` satisfies Lifted
Monotonicity iff `f` is monotone. -/
theorem «sec:composition/function-tables» {I M O : Type} [PO I] [PO M] [PO O] (f : I → M) (g : M → O) :
    Comp.seq (graph f) (graph g) = graph (g ∘ f) ∧ ((graph f).LiftedMono ↔ Monotone f) :=
  ⟨Comp.seq_graph f g, Comp.graph_liftedMono_iff f⟩

/-- "The CRDT observations of Section `sec:crdt-instance` have this shape: a
client query `q` over the replica state `s` is the composition `q ∘ s`, and
compositions of monotone functions are monotone (Corollary
`cor:functional-composition`), so monotonicity of `q` on all of the state domain
suffices."  Lean: the
corollary applied to `s = Inst.st s₀` (monotone by
`«sec:crdt-instance/state-monotone»`) and a monotone `q`. -/
theorem «sec:composition/crdt-query» {D Y : Type} [PO D] [Inst.JSL D] [PO Y] (s0 : D)
    {q : D → Y} (hq : Monotone q) : Monotone (q ∘ (Inst.st s0 : Inst.FSet D → D)) :=
  Comp.functional_composition (Inst.st_mono s0) hq

/-! ## Proper Coordination (`sec:proper-coordination`) -/

/-- "A commitment strategy for `S₁` … fixes at each input `i` the upstream
outputs committed to at `i`.  Its committed table is the set `K ⊆ S₁` of those
rows.  It is totality-preserving when `K` has a row at every input, so that
the commitments never leave an input without a permitted output."  Lean:
`Comp.CommitTable sp1` (fields `K`, `sub : K ⊆ S₁`, `total`); "We take `K` as
declared rather than derived from runs." -/
abbrev «sec:composition/commitment-strategy» {I M : Type} [PO I] [PO M] (sp1 : Spec I M) : Type :=
  Comp.CommitTable sp1

/-- **Definition `def:proper-coordination`** (Proper Coordination): "A
totality-preserving commitment strategy with committed table `K` is proper
for the composition when the resolved specification `S₂ ∘ K` is consistent
and every output at every state of it reachable without commitment is
exposable."  Lean: `Comp.Proper` on the resolved specification, instantiated
as `Comp.ProperSeq κ sp2` (`S₂ ∘ K`) and, for the parameterized form of
Appendix `app:composition` ("`G ⋆ K` as the resolved table"),
`Comp.ProperPar κ G`. -/
theorem «def:proper-coordination» :
    (∀ {I M O : Type} [PO I] [PO M] [PO O] {sp1 : Spec I M} (κ : Comp.CommitTable sp1)
        (sp2 : Spec M O),
        Comp.ProperSeq κ sp2 ↔
          ((Comp.seq κ.spec sp2).Consistent ∧
            ∀ τ : State (Comp.seq κ.spec sp2), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o)) ∧
      ∀ {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C] {F : Spec (I × A) B}
        (κ : Comp.CommitTable F) (G : Spec (J × B) C),
        Comp.ProperPar κ G ↔
          ((Comp.par κ.spec G).Consistent ∧
            ∀ τ : State (Comp.par κ.spec G), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- "The second clause follows from the first by Complete CALM and the
exposure boundary (Theorem `thm:complete-calm`,
Proposition `prop:exposure-boundary`): once the upstream commitments are
made, the composition needs no further commitment." -/
theorem «sec:composition/second-clause» {I O : Type} [PO I] [PO O] (sp : Spec I O)
    (h : sp.Consistent) :
    ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  Comp.proper_second_clause sp h

/-- "Neither `S₁`, `S₂`, nor the unresolved composition need be monotone."
Lean: two witnesses.  (1) `S₁ = anyS` (one input, fiber `{x, y}` of
incomparable outputs) and `S₂ ∘ S₁` with `S₂ = id` violate Lifted
Monotonicity, yet committing to `x` is proper.  (2) The converse example
of Appendix `app:composition` (`«app:composition/converse-example»`): `S₂`
also violates it. -/
theorem «sec:composition/neither-monotone» :
    (¬ Comp.anyS.LiftedMono ∧ ¬ (Comp.seq Comp.anyS Comp.idS).LiftedMono ∧
        Comp.ProperSeq Comp.kappaX Comp.idS) ∧
      (¬ Comp.anyS.LiftedMono ∧ ¬ Comp.s2NM.LiftedMono ∧
        ¬ (Comp.seq Comp.anyS Comp.s2NM).LiftedMono ∧ Comp.ProperSeq Comp.kappaX Comp.s2NM) :=
  ⟨Comp.monotone_commitment_neither_monotone,
    Inst.converse_example.2.2.2.2.2.1, Inst.converse_example.2.2.2.2.2.2.1,
    Inst.converse_example.2.2.2.2.2.2.2.1, Inst.converse_example.2.2.2.2.2.2.2.2⟩

/-- **Corollary `thm:proper-coordination`** (Proper Coordination): "A
totality-preserving commitment strategy is proper for a composition if and
only if the resolved specification satisfies Lifted Monotonicity."  Lean: the
sequential form and the independently parameterized form (Appendix
`app:composition`). -/
theorem «thm:proper-coordination» :
    (∀ {I M O : Type} [PO I] [PO M] [PO O] {sp1 : Spec I M} (κ : Comp.CommitTable sp1)
        (sp2 : Spec M O),
        Comp.ProperSeq κ sp2 ↔ (Comp.seq κ.spec sp2).LiftedMono) ∧
      ∀ {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C] {F : Spec (I × A) B}
        (κ : Comp.CommitTable F) (G : Spec (J × B) C),
        Comp.ProperPar κ G ↔ (Comp.par κ.spec G).LiftedMono :=
  ⟨fun κ sp2 => Comp.proper_coordination_seq κ sp2, fun κ G => Comp.proper_coordination_par κ G⟩

/-- **Corollary `cor:monotone-commitment`** (Committing upstream to a monotone
function): "If the committed table `K` of a totality-preserving commitment
strategy is the table of a monotone function and the downstream
specification `S₂` satisfies Lifted Monotonicity, the strategy is proper."
Lean: the sequential form and the independently parameterized form with `G`
in place of `S₂` (Appendix `app:composition`). -/
theorem «cor:monotone-commitment» :
    (∀ {I M O : Type} [PO I] [PO M] [PO O] {sp1 : Spec I M} (κ : Comp.CommitTable sp1)
        (sp2 : Spec M O) (f : I → M),
        κ.K = (graph f).S → Monotone f → sp2.LiftedMono → Comp.ProperSeq κ sp2) ∧
      ∀ {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C] {F : Spec (I × A) B}
        (κ : Comp.CommitTable F) (G : Spec (J × B) C) (f : I × A → B),
        κ.K = (graph f).S → Monotone f → G.LiftedMono → Comp.ProperPar κ G :=
  ⟨fun κ sp2 f hK hf h2 => Comp.monotone_commitment_seq κ sp2 f hK hf h2,
    fun κ G f hK hf hG => Comp.monotone_commitment_par κ G f hK hf hG⟩

/-- "The converse fails: a strategy can be proper even when the downstream
specification is not monotone (Appendix `app:composition`)."  Lean: the
counterexample `«app:composition/converse-example»`: `S₂` fails Lifted
Monotonicity, and the strategy is proper. -/
theorem «sec:composition/converse-fails» :
    ¬ Comp.s2NM.LiftedMono ∧ Comp.ProperSeq Comp.kappaX Comp.s2NM :=
  ⟨Inst.converse_example.2.2.2.2.2.2.1, Inst.converse_example.2.2.2.2.2.2.2.2⟩

/-- **Example `ex:committed-log-composition`** (Committed log composed with a
key-value store), for any deterministic state machine `δ` and two distinct
commands: "Then `S₁` is non-monotone, since distinct next entries are
incompatible outputs in one fiber.  So is the key-value store specification
`S₂ ∘ S₁`, since concurrent commands ordered oppositely give incompatible
responses. … `K` is the table of a monotone function.  Deterministic
execution makes `S₂` monotone.  By Corollary `cor:monotone-commitment` the log
commitments are proper, and `S₂ ∘ K` is consistent with no commitment in the
store."  Lean: `I = M = Inst.Pfx Cmd` (prefix order); `smrS1`, `smrK` (commit
to the arrival order, `K(i) = i`), `smrS2 δ σ₀` (the table of execution
`execF δ σ₀`). -/
theorem «ex:committed-log-composition» {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R) (σ0 : Stt)
    {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) :
    ¬ (Inst.smrS1 (Cmd := Cmd)).LiftedMono ∧
      ¬ (Comp.seq Inst.smrS1 (Inst.smrS2 δ σ0)).LiftedMono ∧
      (Inst.smrK (Cmd := Cmd)).K = (graph fun i : Inst.Pfx Cmd => i).S ∧
      Monotone (fun i : Inst.Pfx Cmd => i) ∧ (Inst.smrS2 δ σ0).LiftedMono ∧
      Comp.ProperSeq Inst.smrK (Inst.smrS2 δ σ0) ∧
      (Comp.seq Inst.smrK.spec (Inst.smrS2 δ σ0)).Consistent :=
  Inst.smr_example δ σ0 hne

/-- "There, bare reads are consistent when each response records the log
position it read from, but not when the specification demands the latest
value (Example `ex:bare-reads`)."  Lean: with position-tagged responses
(`Inst.bareG`) the resolved table `G ⋆ K` is consistent; with latest-value
responses (`Inst.latestG`) it violates Lifted Monotonicity, hence is not
consistent, once some command `c` changes what some read `r` returns.  See
`«ex:bare-reads»` in `Paper/AppD_Composition.lean`. -/
theorem «sec:composition/bare-reads» {Cmd Stt R Rd V : Type} (δ : Stt → Cmd → Stt × R)
    (rd : Stt → Rd → V) (σ0 : Stt) :
    (Comp.par Inst.logK.spec (Inst.bareG δ rd σ0)).Consistent ∧
      ∀ {c : Cmd} {r : Rd}, rd (δ σ0 c).1 r ≠ rd σ0 r →
        ¬ (Comp.par Inst.logK.spec (Inst.latestG δ rd σ0)).Consistent :=
  ⟨(Comp.monotone_commitment_par Inst.logK _ (fun p => p.1) rfl Inst.logK_monotone
      (Inst.bareG_liftedMono δ rd σ0)).1,
    fun hc h => (Inst.latest_not_proper δ rd σ0 hc).1 ((complete_calm _).1 h)⟩

end Paper
end CC
