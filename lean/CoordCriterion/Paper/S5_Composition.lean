import CoordCriterion.Appendix.Guarded

/-!
# Paper §5, "Composition and Irredundant Coordination" (`sections/composition.tex`)

Statement layer for Section `sec:composition`.  Read it side by side with
`sections/composition.tex`: the `/-! ## … -/` headers follow the section's
subsections, entries appear in paper order, and each entry quotes the claim
it formalizes.  Numbered results and displayed equations are named by their
LaTeX label; unlabeled claims are `«sec:composition/<slug>»`.  The proofs
are in Appendix `app:composition`; its curried evaluation, the counterexamples, and the
covering argument are in `Paper/AppD_Composition.lean`.

The section has no subsection heading for sequential composition; its label
`sec:sequential-composition` sits after the section opening.  Composition with
independent inputs (`sec:parameterized-composition`) is in Appendix
`app:composition` and `Paper/AppD_Composition.lean`.

Library: `Appendix/Composition.lean` (namespace `CC.Comp`), the examples at
the end of `Instances/Examples.lean` (namespace `CC.Inst`), and guarded
composition in `Appendix/Guarded.lean` (namespace `CC.Guard`).

Conventions: a table is `Table I O := I → O → Prop`; `Spec I O` is a table
total on all of `I` with orders on `I` and `O`; products carry the
componentwise order; the composed input `I × J × A` is `I × (J × A)`;
`Comp.graph f` is the table of `f`, and `Comp.Monotone f` is
`∀ x y, x ≼ y → f x ≼ f y`.  For an upstream `𝒫 : Spec I M` and a store
`f : M → O`, `Guard.comp 𝒫 f` is `𝒦 ∘ 𝒫`, `Guard.img f σ` is the image
state `f(σ)`, and `Guard.obs f` replaces each output `m` by `f(m)` (and
erases commitments).
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

/-! ## Composite CALM (`sec:composite-calm`) -/

/-- "The composite is itself an ordered specification, so Complete CALM
applies to it directly.  Specification `S₂ ∘ S₁` is consistent exactly when it
satisfies Lifted Monotonicity, and then no output needs a commitment (Theorem
`thm:complete-calm`, Proposition `prop:exposure-boundary`)." -/
theorem «sec:composite-calm/complete-calm» {I M O : Type} [PO I] [PO M] [PO O]
    (sp1 : Spec I M) (sp2 : Spec M O) :
    ((Comp.seq sp1 sp2).Consistent ↔ (Comp.seq sp1 sp2).LiftedMono) ∧
      ((Comp.seq sp1 sp2).LiftedMono →
        ∀ τ : State (Comp.seq sp1 sp2), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o) :=
  ⟨complete_calm _, fun h =>
    (exposure_boundary _).1 ((liftedMono_iff_commonExpansion _).1 h)⟩

/-- "A monotone composite does not mean that each component can run without
commitments.  Consider an upstream specification with one input and two
incomparable outputs, and a downstream function that maps both to the same
value.  The composite has one row, so it is monotone.  The upstream component
still cannot emit either output without choosing, so a pipeline in which
neither component commits never emits anything."  Lean: `𝒫 = Dist.spU`, the
constant store; every run of `𝒫` under the empty basis emits nothing. -/
theorem «sec:composite-calm/components-commit» :
    (Guard.comp Dist.spU (fun _ : Dist.B2 => ())).LiftedMono ∧
      ∀ es ρ, SysExec Dist.noBasis (canon Dist.spU ()) es ρ → Guard.emitted es = [] :=
  Guard.composite_monotone_not_enough

/-! ## Irredundant Coordination (`sec:irredundant-coordination`) -/

/-- "The store `𝒦` is the specification with table `{(m,f(m))}`, and the
composite `𝒦 ∘ 𝒫` has table `{(i,f(m)) : (i,m) ∈ P}`.  For a state `σ = (i,R)`
of `𝒫`, its image `f(σ)` is the state `(i, {(k,f(m)) : (k,m) ∈ R})` of the
composite." -/
theorem «sec:irredundant-coordination/image» {I M O : Type} [PO I] [PO M] [PO O]
    (sp : Spec I M) (f : M → O) :
    (∀ i o, (Guard.comp sp f).S i o ↔ ∃ m, sp.S i m ∧ o = f m) ∧
      ∀ σ : State sp, (Guard.img f σ).cur = σ.cur ∧
        ∀ k o, (Guard.img f σ).R k o ↔ ∃ m, σ.R k m ∧ o = f m :=
  ⟨fun _ _ => Iff.rfl, fun _ => ⟨rfl, fun _ _ => Iff.rfl⟩⟩

/-- "A commitment of `𝒫` may keep `m'` and remove `m`, with `m` and `m'`
incomparable but `f(m) ≼ f(m')`.  Its image removes a row refined by a row it
keeps, which Equation `eq:commitment-excludes` forbids.  In the composite,
emitting `f(m')` needs no commitment at all, since it retires `f(m)`."
Lean: `𝒫 = Comp.anyS` (fiber `{x, y}`), `f = Guard.fLvl` (`x ↦ lo`,
`y ↦ hi`); the choice `c_y`. -/
theorem «sec:irredundant-coordination/no-pushforward» :
    (∃ τ, (choiceC Comp.Two.y).app (canon Comp.anyS Comp.Pt.pt) = some τ ∧
      ∀ c : Commitment (Guard.comp Comp.anyS Guard.fLvl),
        c.app (Guard.img Guard.fLvl (canon Comp.anyS Comp.Pt.pt)) ≠ some (Guard.img Guard.fLvl τ)) ∧
    ¬ Exposable (canon Comp.anyS Comp.Pt.pt) Comp.Two.y ∧
      Exposable (canon (Guard.comp Comp.anyS Guard.fLvl) Comp.Pt.pt) Guard.Lvl.hi :=
  ⟨Guard.push_not_commitment, Guard.choice_becomes_retirement⟩

/-- **Definition `def:irredundant-coordination`** (Irredundant Coordination):
"The guarded composite coordinates at most once when every run of `𝒫` under
`ℬ`, with each output `m` replaced by `f(m)`, is a run of `𝒦 ∘ 𝒫`, and the
store's part of it is a run of `𝒦` under the empty basis.  It coordinates at
least once when every output event `Out_γ(m)` of `𝒫` at a state `σ` such that
`f(m)` is not exposable at `f(σ)` has `γ ≠ ε`.  It is irredundant when it
coordinates at most once and at least once."  Lean: `Guard.AtMostOnce` also
records that the composite run's table contains the image of `𝒫`'s (the
sense in which the composite run follows `𝒫`'s), and the store's run is that
of Theorem `thm:guarded-runs`(2). -/
theorem «def:irredundant-coordination» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    (B : Basis sp) (f : M → O) :
    (Guard.Irredundant B f ↔ Guard.AtMostOnce B f ∧ Guard.AtLeastOnce B f) ∧
      (Guard.AtLeastOnce B f ↔ ∀ (σ τ : State sp) γ m, SysStep B σ (.output γ m) τ →
        ¬ Exposable (Guard.img f σ) (f m) → γ ≠ []) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- **Theorem `thm:guarded-runs`** (Guarded runs): "Let `f` be monotone and
`ℬ` any basis of `𝒫`.  (1) Every run of `𝒫` under `ℬ`, with each output `m`
replaced by `f(m)`, is a run of `𝒦 ∘ 𝒫` from the same canonical state.  After
each event, the composite run's table contains the image of `𝒫`'s.  (2) The
outputs of such a run form a chain, and the store's run on them is a run of
`𝒦` under the empty basis.  (3) If finitely many runs of `𝒫` can be brought to
a common state with current input `j`, under any bases, the corresponding
composite runs are confluent at `j`."  Lean: (1) `Guard.guarded_run` (the
lockstep form, after each event, is `Guard.guarded_lockstep`); (2)
`Guard.emitted_chain`, `Guard.store_run`; (3) `Guard.guarded_confluent`, for
any composite runs whose tables contain the images. -/
theorem «thm:guarded-runs» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M} {f : M → O}
    (hf : Monotone f) (B : Basis sp) :
    (∀ i es ρ, SysExec B (canon sp i) es ρ →
      ∃ ρ', Exec (canon (Guard.comp sp f) i) (es.map (Guard.obs f)) ρ' ∧ ρ'.cur = ρ.cur ∧
        ∀ k o, Guard.imgT f ρ.R k o → ρ'.R k o) ∧
    (∀ (σ ρ : State sp) es, SysExec B σ es ρ → Guard.ChainFrom none (Guard.emitted es)) ∧
    (∀ (σ ρ : State sp) es m ms, SysExec B σ es ρ → Guard.emitted es = m :: ms →
      ∃ es' : List (SEvent (graph f)),
        es'.map SEvent.erase = .output (f m) :: Guard.storeEvs f ms ∧ CoordFree es' ∧
        SysExec (fun _ => False) (canon (graph f) m) es' (canon (graph f) (ms.getLastD m))) ∧
    (∀ (fam : List (State sp × State (Guard.comp sp f))), (∀ p ∈ fam, IsRun p.2) →
      (∀ p ∈ fam, ∀ k o, Guard.imgT f p.1.R k o → p.2.R k o) →
      ∀ j : I, (∀ p ∈ fam, p.2.cur ≼ j) →
      (∃ τ : State sp, τ.cur = j ∧ ∀ p ∈ fam, ∃ (B' : Basis sp) (es : List (SEvent sp)),
        SysExec B' p.1 es τ) →
      ConfluentAt (fam.map Prod.snd) j) :=
  ⟨fun _ _ _ hx => Guard.guarded_run hf hx,
   fun _ _ _ hx => Guard.emitted_chain hx none (fun _ h => by cases h),
   fun _ _ _ _ _ hx he => Guard.store_run hf hx he,
   fun fam hrun hsub j hj hP => Guard.guarded_confluent fam hrun hsub j hj hP⟩

/-- **Theorem `thm:irredundant-coordination`** (Irredundant Coordination):
"If `f` is monotone, the guarded composite is irredundant for every basis of
`𝒫`.  If moreover `𝒦 ∘ 𝒫` violates Lifted Monotonicity, some output `f(m)` of
the composite is not exposable at a canonical state, and `𝒫` must commit to
emit any output with that image there."  Lean: "must commit" is: no `m'` with
the same image is exposable at `σ_𝒫(i)`, and under the empty basis no output
event at `σ_𝒫(i)` emits one. -/
theorem «thm:irredundant-coordination» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {f : M → O} (hf : Monotone f) :
    (∀ B : Basis sp, Guard.Irredundant B f) ∧
      (¬ (Guard.comp sp f).LiftedMono →
        ∃ i m, sp.S i m ∧ ¬ Exposable (canon (Guard.comp sp f) i) (f m) ∧
          (∀ m', sp.S i m' → f m' = f m → ¬ Exposable (canon sp i) m') ∧
          ∀ γ m' τ, SysStep (fun _ => False) (canon sp i) (.output γ m') τ → f m' ≠ f m) :=
  ⟨Guard.guarded_irredundant hf, Guard.at_least_once_needed hf⟩

/-- "Every legal output event removes at least the rows its canonical event
removes (Lemma `lem:canonical-commitment-normal-form`), so every row that the
composite must seal or choose against has lost all its preimages to `𝒫`'s
commitments."  Lean: for a legal `Out_γ(m)` of `𝒫` under any basis and any
composite state whose table contains the image of `𝒫`'s; the covering argument
of Appendix `app:composition` is `«app:composition/coverage»`. -/
theorem «sec:irredundant-coordination/any-basis» {I M O : Type} [PO I] [PO M] [PO O]
    {sp : Spec I M} {f : M → O} (hf : Monotone f) {B : Basis sp} {σ τ : State sp}
    {γ : List (Commitment sp)} {m : M} (h : SysStep B σ (.output γ m) τ)
    {ρ : State (Guard.comp sp f)} (hsub : ∀ k o, Guard.imgT f σ.R k o → ρ.R k o) :
    ∃ σc, ApplySeq γ σ σc ∧
      ∀ k x, (Sealed ρ (f m) k x ∨ Rejected ρ (f m) k x) →
        ∀ m', σ.R k m' → f m' = x → ¬ σc.R k m' :=
  Guard.coverage_step hf h hsub

/-- **Proposition `prop:invisible-coordination`** (Invisible coordination):
"Let `f` be monotone, and let `𝒫` emit `m` at `σ` by `Out_γ(m)`.  If every row
that `γ` removes has a row with the same input and the same image that `γ`
keeps, then `f(m)` is exposable at `f(σ)`." -/
theorem «prop:invisible-coordination» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {f : M → O} (hf : Monotone f) {B : Basis sp} {σ τ : State sp} {γ : List (Commitment sp)}
    {m : M} (h : SysStep B σ (.output γ m) τ)
    (hinv : ∀ σc : State sp, ApplySeq γ σ σc →
      ∀ k m', σ.R k m' → ∃ m'', σc.R k m'' ∧ f m'' = f m') :
    Exposable (Guard.img f σ) (f m) :=
  Guard.invisible_step hf h hinv

/-- "Consider a store that answers each key from that key's commands, in log
order, and two commands `a` and `b` on different keys.  The log must order
them, since `[a,b]` and `[b,a]` have no common refinement.  The store's view of
both logs is the same, so the composite needs no commitment."  Lean: the
per-key view `Guard.perKey key` is monotone; with `𝒫 = Guard.abSpec a b`
(fiber `{[a,b],[b,a]}`), `[a,b]` is not exposable but its image is. -/
theorem «sec:irredundant-coordination/per-key» {Cmd K : Type} [DecidableEq K] (key : Cmd → K)
    {a b : Cmd} (hk : key a ≠ key b) :
    Monotone (Guard.perKey key) ∧ Guard.perKey key ⟨[a, b]⟩ = Guard.perKey key ⟨[b, a]⟩ ∧
      ¬ Exposable (canon (Guard.abSpec a b) Comp.Pt.pt) ⟨[a, b]⟩ ∧
      Exposable (canon (Guard.comp (Guard.abSpec a b) (Guard.perKey key)) Comp.Pt.pt)
        (Guard.perKey key ⟨[a, b]⟩) :=
  ⟨Guard.perKey_monotone key, Guard.perKey_swap key hk, Guard.commute_example key hk⟩

/-- **Example `ex:committed-log-composition`** (Replicated store), for any
deterministic state machine `δ` and two distinct commands: "Then `𝒫` is
non-monotone, since distinct next entries are incompatible outputs in one
fiber.  So is the key-value store `𝒦 ∘ 𝒫`, since concurrent commands ordered
oppositely give incompatible responses.  …  By Theorem
`thm:irredundant-coordination`, the store needs no commitment of its own, and
because the composite is not monotone, the log's commitments cannot be
dropped."  Lean: `𝒫 = Inst.smrS1` (`I = M = Inst.Pfx Cmd`, prefix order),
`f = Inst.execF δ σ₀` (monotone); for every basis `B` of `𝒫`. -/
theorem «ex:committed-log-composition» {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R) (σ0 : Stt)
    {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) (B : Basis (Inst.smrS1 (Cmd := Cmd))) :
    ¬ (Inst.smrS1 (Cmd := Cmd)).LiftedMono ∧
      ¬ (Guard.comp Inst.smrS1 (Inst.execF δ σ0)).LiftedMono ∧
      Monotone (Inst.execF δ σ0) ∧ Guard.Irredundant B (Inst.execF δ σ0) ∧
      ∃ i m, Inst.smrS1.S i m ∧
        ¬ Exposable (canon (Guard.comp Inst.smrS1 (Inst.execF δ σ0)) i) (Inst.execF δ σ0 m) ∧
        ∀ m', Inst.smrS1.S i m' → Inst.execF δ σ0 m' = Inst.execF δ σ0 m →
          ¬ Exposable (canon Inst.smrS1 i) m' :=
  Guard.smr_irredundant δ σ0 hne B

/-- "There, bare reads need no commitment of their own when each response
records the log position it read from, but they do when the specification
demands the latest value (Example `ex:bare-reads`)."  Lean: with
position-tagged responses (`Inst.bareG`) every output at every state reachable
without commitment is exposable; with latest-value responses (`Inst.latestG`)
some is not, once some command `c` changes what some read `r` returns.  See
`«ex:bare-reads»` in `Paper/AppD_Composition.lean`. -/
theorem «sec:composition/bare-reads» {Cmd Stt R Rd V : Type} (δ : Stt → Cmd → Stt × R)
    (rd : Stt → Rd → V) (σ0 : Stt) :
    (∀ τ : State (Inst.bareG δ rd σ0), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o) ∧
      ∀ {c : Cmd} {r : Rd}, rd (δ σ0 c).1 r ≠ rd σ0 r →
        ∃ τ : State (Inst.latestG δ rd σ0), ReachableCF τ ∧ ∃ o, τ.R τ.cur o ∧ ¬ Exposable τ o :=
  ⟨(exposure_boundary _).1 ((liftedMono_iff_commonExpansion _).1 (Inst.bareG_liftedMono δ rd σ0)),
    fun hc => Inst.latest_needs_store_commitment δ rd σ0 hc⟩

end Paper
end CC
