import CoordCriterion.Appendix.Guarded
import CoordCriterion.Appendix.JointMono
import CoordCriterion.Appendix.Components
import CoordCriterion.Appendix.Intersection
import CoordCriterion.Appendix.Tight

/-!
# Paper §5, "Composition and Tight Coordination" (`sections/composition.tex`)

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
the end of `Instances/Examples.lean` (namespace `CC.Inst`), composition behind
a sufficient guard in `Appendix/Guarded.lean` (namespace `CC.Guard`), and
necessary and tight guards in `Appendix/Tight.lean` (namespace `CC.Tight`).
The library predates the paper's names: "`𝒮₁` is a sufficient guard for
`𝒮₂`" is `Guard.Proper sp sk`, "necessary guard" is `Tight.Tight sp sk`, and
"tight guard" is their conjunction `«def:tight-guard»`.

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
`P₂ ∘ P₁ = π_{I,O}(P₁ ⋈_M P₂) = {(i,o) : ∃ m. (i,m) ∈ P₁ ∧ (m,o) ∈ P₂}`. -/
theorem «eq:spec-composition» {I M O : Type} (S1 : Table I M) (S2 : Table M O) (i : I) (o : O) :
    Comp.tcomp S1 S2 i o ↔ ∃ m, S1 i m ∧ S2 m o :=
  Iff.rfl

/-- "Every `i ∈ I` has a nonempty fiber in `P₂ ∘ P₁`, since `P₁` is total on
`I` and `P₂` is total on `M` (it has a row at every `m ∈ M`)."  Lean: the
composition is the specification `Comp.seq sp1 sp2`, whose table is
`tcomp`; totality is its `total` field. -/
theorem «sec:composition/seq-total» {I M O : Type} [PO I] [PO M] [PO O]
    (sp1 : Spec I M) (sp2 : Spec M O) :
    (Comp.seq sp1 sp2).P = Comp.tcomp sp1.P sp2.P ∧ ∀ i, ∃ o, Comp.tcomp sp1.P sp2.P i o :=
  ⟨rfl, (Comp.seq sp1 sp2).total⟩

/-- Totality of `P₂` on *all* of `M` is needed (not stated in the paper; it
explains the hypothesis above).  If `P₂` is total only on a proper subset of
`M`, Lemma `lem:composition` fails even when the composed table is total. -/
theorem «sec:composition/middle-totality-needed» :
    Comp.s1.LiftedMono ∧ (Comp.restrict Comp.t2).LiftedMono ∧
      (∀ i, ∃ o, Comp.tcomp Comp.s1.P Comp.t2 i o) ∧
      ¬ (Comp.restrict (Comp.tcomp Comp.s1.P Comp.t2)).LiftedMono :=
  Comp.restricted_middle_counterexample

/-- **Lemma `lem:composition`** (Composition): "If `Spec₁` and `Spec₂`
satisfy Lifted Monotonicity, then so does the I/O specification with
table `P₂ ∘ P₁`." -/
theorem «lem:composition» {I M O : Type} [PO I] [PO M] [PO O] {sp1 : Spec I M} {sp2 : Spec M O}
    (h1 : sp1.LiftedMono) (h2 : sp2.LiftedMono) : (Comp.seq sp1 sp2).LiftedMono :=
  Comp.seq_liftedMono h1 h2

/-- "By associativity the lemma extends to finite pipelines." -/
theorem «sec:composition/associativity» {I M O P : Type} (S1 : Table I M) (S2 : Table M O)
    (S3 : Table O P) :
    Comp.tcomp (Comp.tcomp S1 S2) S3 = Comp.tcomp S1 (Comp.tcomp S2 S3) :=
  Comp.tcomp_assoc S1 S2 S3

/-- "For a function `f`, its table `{(i,f(i))}` satisfies Lifted Monotonicity
exactly when `f` is monotone (Section `sec:lifted-monotonicity`)."  Lean: the
table of `f` satisfies Lifted Monotonicity iff `f` is monotone; also, the
composition of the tables of `f` and `g` is the table of `g ∘ f`. -/
theorem «sec:composition/function-tables» {I M O : Type} [PO I] [PO M] [PO O] (f : I → M) (g : M → O) :
    Comp.seq (graph f) (graph g) = graph (g ∘ f) ∧ ((graph f).LiftedMono ↔ Monotone f) :=
  ⟨Comp.seq_graph f g, Comp.graph_liftedMono_iff f⟩

/-! ## Tight Coordination (`sec:tight-coordination`) -/

/-- "We return to the replicated store of the opening.  The key-value store is
not monotone on its own, but it is monotone on what the log offers: a log
fixes the order of commands, and a longer log only extends the responses.  The
log issues a commitment to offer only such inputs, so the store need make no
commitments."  Lean, for any
deterministic state machine `δ` and two distinct commands: the key-value store
`𝒦 ∘ 𝒫` (`𝒫 = Inst.smrS1`, the log) is not Lifted-Monotone, execution
`Inst.execF δ σ₀` is monotone on logs, and the log is not Lifted-Monotone. -/
theorem «sec:tight-coordination/kvs-on-logs» {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R)
    (σ0 : Stt) {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) :
    ¬ (Guard.comp Inst.smrS1 (Inst.execF δ σ0)).LiftedMono ∧ Monotone (Inst.execF δ σ0) ∧
      ¬ (Inst.smrS1 (Cmd := Cmd)).LiftedMono :=
  let h := Guard.smr_proper δ σ0 hne
  ⟨h.2.1, h.2.2.1, h.1⟩

/-- **Definition `def:sufficient-guard`** (Sufficient guard): "`𝒮₁` is a
sufficient guard for `𝒮₂` when `𝒮₂|_{𝒮₁}` needs no commitment: every output at
every state it reaches without commitment is legal."  (Lean's name for this
property is `Guard.Proper`.)  And,
just before: "Write `𝒮₂|_{𝒮₁}` for `𝒮₂` restricted to the outputs of `𝒮₁`.
We say that `P₂` satisfies Lifted Monotonicity on a set `D ⊆ M` when its
restriction to inputs in `D` does."  "On `D`" is `Joint.CEOn`, equivalent to
Lifted Monotonicity of the restriction to `D` (`Joint.ceOn_iff_restrictTo`).
Lean: `𝒮₂|_{𝒮₁}` is `Guard.rest sp sk = Joint.restrictTo (Joint.Img sp) sk`,
whose inputs are the outputs of `sp` (a subtype of `M` with the order of `M`);
"needs no commitment" is `Guard.NeedsNoCommit`.  The definition does not
mention the system for `𝒮₁`. -/
theorem «def:sufficient-guard» {I M O : Type} [PO I] [PO M] [PO O] (sp : Spec I M)
    (sk : Spec M O) :
    (Guard.Proper sp sk ↔
      ∀ τ : State (Guard.rest sp sk), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o) ∧
      Guard.rest sp sk = Joint.restrictTo (Joint.Img sp) sk ∧
      ∀ (m : {m // Joint.Img sp m}) o, (Guard.rest sp sk).P m o ↔ sk.P m.1 o :=
  ⟨Iff.rfl, rfl, fun _ _ => Iff.rfl⟩

/-- **Proposition `prop:guard-test`** (Guard test): "`𝒮₁` is a sufficient
guard for `𝒮₂` exactly when `𝒮₂` satisfies Lifted Monotonicity on the outputs
of `𝒮₁`."  Lead-in: "Applying the No-commitment test (Proposition
`prop:exposure-boundary`) to `𝒮₂|_{𝒮₁}` gives a static test."  Lean:
`Guard.proper_iff` ("on the outputs" is `Joint.CEOn sk (Joint.Img sp)`), with
`Guard.proper_iff_consistent` (Complete CALM on `𝒮₂|_{𝒮₁}`). -/
theorem «prop:guard-test» {I M O : Type} [PO I] [PO M] [PO O] (sp : Spec I M)
    (sk : Spec M O) :
    (Guard.Proper sp sk ↔ Joint.CEOn sk (Joint.Img sp)) ∧
    (Guard.Proper sp sk ↔ (Guard.rest sp sk).Consistent) :=
  ⟨Guard.proper_iff, Guard.proper_iff_consistent⟩

/-- **Theorem `thm:sufficient-guards`** (Sufficient guards): "Suppose `𝒮₁` is
a sufficient guard for `𝒮₂`, and fix any system for `𝒮₁`.
Then `𝒮₂|_{𝒮₁}` answers each output of a run `ρ` of that system without
commitment, and the pipeline's runs are consistent whenever those of the
system for `𝒮₁` are.  Specifically, replacing each output of `ρ` by its
answers, and dropping the commitment events of `ρ`, gives a canonical run of
`P₂ ∘ P₁`, and such runs are confluent whenever the runs of the system for
`𝒮₁` are."  Lead-in: "A sufficient guard leaves no commitment to the
downstream stage."  Lean, for every run of `𝒮₁` under any basis `B` emitting
`m :: ms`: `Guard.proper_follows` (the empty-basis `𝒮₂|_{𝒮₁}` starts at
`σ(m)`, answers `m`, and receives and answers each later output, and the
result, `Guard.merge`, is a run of `P₂ ∘ P₁`; `merge` keeps the input events
of `ρ`, replaces each output by its answers, and drops commitment events);
`Guard.proper_run` (more generally, any empty-basis run of `𝒮₂|_{𝒮₁}` that
receives each output and answers it any number of times gives a run of
`P₂ ∘ P₁` whose table contains the join); and `Guard.proper_confluent`.  The
system for `𝒮₁` enters only through its basis, which is arbitrary. -/
theorem «thm:sufficient-guards» {I M O : Type} [PO I] [PO M] [PO O] (sp : Spec I M)
    (sk : Spec M O) :
    (Guard.Proper sp sk → ∀ (B : CommitmentBasis sp) i es (ρ : State sp) m ms,
      SysExec B (canon sp i) es ρ → Guard.emitted es = m :: ms →
      ∃ (hm : Joint.Img sp m) (o : O) (ps : List ({m // Joint.Img sp m} × O))
        (esK : List (SEvent (Guard.rest sp sk))) (ρK : State (Guard.rest sp sk)),
        ps.map (fun p => p.1.1) = ms ∧ esK.filterMap SEvent.erase = .output o :: Guard.storeTr ps ∧
        Guard.Produces (Guard.noStore (Guard.rest sp sk)) ⟨m, hm⟩ esK ρK ∧
        ∃ ρ' : State (Comp.seq sp sk),
          Exec (canon (Comp.seq sp sk) i) (Guard.merge es ([o] :: ps.map fun p => [p.2])) ρ' ∧
          ρ'.cur = ρ.cur) ∧
    (Guard.Proper sp sk → ∀ (B : CommitmentBasis sp) i es (ρ : State sp) (m : {m // Joint.Img sp m}) ms os
      (ps : List ({m // Joint.Img sp m} × List O)) esK (ρK : State (Guard.rest sp sk)),
      SysExec B (canon sp i) es ρ → Guard.emitted es = m.1 :: ms.map Subtype.val →
      ps.map Prod.fst = ms → SysExec (fun _ => False) (canon (Guard.rest sp sk) m) esK ρK →
      esK.filterMap SEvent.erase = os.map Event.output ++ Guard.blk ps →
      ∃ ρ' : State (Comp.seq sp sk),
        Exec (canon (Comp.seq sp sk) i) (Guard.merge es (os :: ps.map Prod.snd)) ρ' ∧
        ρ'.cur = ρ.cur ∧ (∀ k m x (h : Joint.Img sp m), ρ.R k m → ρK.R ⟨m, h⟩ x → ρ'.R k x) ∧
        IsRun ρK ∧ ∀ k m, ρ.R k m → ρK.cur.1 ≼ m) ∧
    (Guard.Proper sp sk →
      ∀ (fam : List (State sp × State (Guard.rest sp sk) × State (Comp.seq sp sk))),
      (∀ p ∈ fam, IsRun p.2.2) → (∀ p ∈ fam, IsRun p.2.1) →
      (∀ p ∈ fam, ∀ k m x (h : Joint.Img sp m), p.1.R k m → p.2.1.R ⟨m, h⟩ x → p.2.2.R k x) →
      (∀ p ∈ fam, ∀ k m, p.1.R k m → p.2.1.cur.1 ≼ m) →
      ∀ j : I, (∀ p ∈ fam, p.2.2.cur ≼ j) →
      (∃ τ : State sp, τ.cur = j ∧ ∀ p ∈ fam, ∃ (B : CommitmentBasis sp) (es : List (SEvent sp)),
        SysExec B p.1 es τ) →
      ConfluentAt (fam.map fun p => p.2.2) j) :=
  ⟨fun hP _ _ _ _ _ _ hx he => Guard.proper_follows hP hx he,
    fun hP _ _ _ _ _ _ _ _ _ _ hx he hps hK htr => Guard.proper_run hP hx he hps hK htr,
    fun hP fam h1 h2 h3 h4 j hj hS => Guard.proper_confluent hP fam h1 h2 h3 h4 j hj hS⟩

/-- **Corollary `cor:upstream-commitments`** (Upstream commitments): "If `𝒮₁`
is a sufficient guard for `𝒮₂` and the composite `P₂ ∘ P₁` is not lifted
monotone, some output of `𝒮₁` needs a commitment."  Lead-in: "Conversely, the upstream cannot do
without commitments when the composite is not monotone."  Lean proves the
stronger form of Appendix `app:composition` ("the output of `𝒮₁` that needs a
commitment can be taken at a canonical state"): `Guard.proper_needs_commit`
gives `i`, `m`, and an answer `o` not legal at the composite's canonical state
`σ_{P₂∘P₁}(i)`, such that no `m'` that the store answers with `o` is legal at
`σ_{𝒮₁}(i)`, and under the empty basis no output event there emits one. -/
theorem «cor:upstream-commitments» {I M O : Type} [PO I] [PO M] [PO O] (sp : Spec I M)
    (sk : Spec M O) :
    (Guard.Proper sp sk → ¬ (Comp.seq sp sk).LiftedMono →
      ∃ i m o, sp.P i m ∧ sk.P m o ∧ ¬ Exposable (canon (Comp.seq sp sk) i) o ∧
        (∀ m', sp.P i m' → sk.P m' o → ¬ Exposable (canon sp i) m') ∧
        ∀ m' τ, SysStep (fun _ => False) (canon sp i) (.output m') τ → ¬ sk.P m' o) :=
  fun hP hnot => Guard.proper_needs_commit hP hnot

/-- "This answers the opening puzzle.  By Proposition `prop:guard-test`, the
store restricted to logs needs no commitment, so locks in the store would be
pure overhead, and by Theorem `thm:sufficient-guards` the pipeline is
consistent whenever the log is.  The store as a whole is not monotone, so by
Corollary `cor:upstream-commitments` some output of the log needs a commitment:
the upstream log is where that belongs, and consensus provides it."  Lean: for the log `𝒫 = Inst.smrS1` and execution
`Inst.execF δ σ₀`, every log is an output of the log, and the log is a
sufficient guard, so the store restricted to logs needs no commitment (Proposition `prop:guard-test`); the
composite store is not Lifted-Monotone, and some output `m` of the log at a
canonical state is not exposable there, while every log output `m'` that the
store answers the same way is not exposable at the log's canonical state
either: that output of the log needs a commitment (Corollary `cor:upstream-commitments`,
`Guard.proper_needs_commit` via `Guard.smr_proper`).  "Consensus provides it"
names the mechanism and is prose. -/
theorem «sec:tight-coordination/locks-overhead» {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R)
    (σ0 : Stt) {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) :
    (∀ m, Joint.Img (Inst.smrS1 (Cmd := Cmd)) m) ∧
      (∀ τ : State (Guard.rest Inst.smrS1 (graph (Inst.execF δ σ0))), ReachableCF τ →
        ∀ o, τ.R τ.cur o → Exposable τ o) ∧
      ¬ (Guard.comp Inst.smrS1 (Inst.execF δ σ0)).LiftedMono ∧
      ∃ i m, Inst.smrS1.P i m ∧
        ¬ Exposable (canon (Guard.comp Inst.smrS1 (Inst.execF δ σ0)) i) (Inst.execF δ σ0 m) ∧
        ∀ m', Inst.smrS1.P i m' → Inst.execF δ σ0 m' = Inst.execF δ σ0 m →
          ¬ Exposable (canon Inst.smrS1 i) m' :=
  let h := Guard.smr_proper δ σ0 hne
  ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.1, h.2.2.2.2.2⟩

/-- "Longer pipelines nest: when `𝒮₁` is a sufficient guard for `𝒮₂`, the
composite `P₂ ∘ P₁` can itself guard a third stage, and the theorem applies again (Appendix
`app:composition`)."  The appendix result is Corollary `cor:pipelines`.  (Full
paper only; in the CIDR version this is folded into
the closing pointer to the full paper.)  Lean: the pipeline of a sufficient
guard and its downstream emits only canonical runs of `P₂ ∘ P₁` (`Guard.proper_pipeline_step`), so the
composite is again a guard, and Proposition `prop:guard-test` applies to the next
stage (`Guard.proper_iff`); this is `«cor:pipelines»`. -/
theorem «sec:tight-coordination/nesting» {I M O Q : Type} [PO I] [PO M] [PO O] [PO Q]
    {s1 : Spec I M} {s2 : Spec M O} (s3 : Spec O Q) (h12 : Guard.Proper s1 s2)
    (P : Guard.Sys s1) (K2 : Guard.Sys (Guard.rest s1 s2)) :
    (∀ l', Guard.GEmits (Guard.liftU P) K2 l' →
      (Guard.Sys.free (canonCommitmentBasis (Comp.seq s1 s2))).emits l') ∧
    (Guard.Proper (Comp.seq s1 s2) s3 ↔ Joint.CEOn s3 (Joint.Img (Comp.seq s1 s2))) :=
  ⟨fun _ h => Guard.proper_pipeline_step h12 h, Guard.proper_iff⟩

/-- "A downstream implementation may still take commitments the specs do not
require, as a store that takes locks behind a log would.  An implementation of
`𝒮₂` alone, rather than of `𝒮₂|_{𝒮₁}`, may also fail to answer some upstream
outputs (Appendix `app:components`)."  The components vocabulary (component,
admitted run, typed pipeline, contract- and implementation-sufficiency) is
defined only in Appendix `app:components`.
Lean: `Components.Component` (Def. `def:component`; systems as components are
`«app:components/system-is-component»`), `Components.Pipeline.sound` for the
rows; contract sufficiency is `Components.Pipeline.ContractProper`, equivalent
to `Guard.Proper` and stated on the specifications; implementation sufficiency
is `Components.Pipeline.ImplementationProper`; the locking store is
`Components.early_lock_component`, a downstream admitting too few runs is
`Components.threshold_component`; the empty-basis component for `𝒮₂|_{𝒮₁}`
is `Components.offered_available` (Prop. `prop:typed-pipelines`(3)–(5) in
`Paper/AppD_Composition.lean`). -/
theorem «sec:tight-coordination/components» {I M O : Type} [PO I] [PO M] [PO O]
    (sp : Spec I M) (sk : Spec M O) :
    (∀ (p : Components.Pipeline sp sk) obs, p.Accepts obs →
      (Comp.seq sp sk).P obs.input obs.output) ∧
    (∀ p : Components.Pipeline sp sk, p.ContractProper ↔ Guard.Proper sp sk) ∧
    (Guard.Proper sp sk → ∀ (C1 : Components.Component sp) r, C1.accepts r →
      let p := Components.Pipeline.offered (sk := sk) C1
        (Components.Component.ofCommitmentBasis (Components.emptyCommitmentBasis _))
      p.ImplementationProper ∧ ∃ w : Components.FeedWitness p.upstream p.downstream,
        w.upRun.input = r.input ∧ w.upRun.output.1 = r.output ∧
          CoordFree (canon (Guard.rest sp sk) w.downRun.input) w.downRun.events) :=
  ⟨fun p _ h => p.sound h, Components.contractProper_iff_guardProper,
    fun hP C1 _ h => Components.offered_available hP C1 h⟩

/-! ### Necessary and tight guards -/

/-- Before Theorem `thm:guard-tightening`: "Necessity compares the upstream's
canonical commitments with those the composite needs."  Rows `(i,m)` and
`(k,x)` of `P₁` with `i ≼ k` are inconsistent at `k` exactly when emitting `m`
at `σ_{P₁}(i)` removes `(k,x)` by canonical commitment (Appendix `app:tight`).
Lean: rows inconsistent at `k` under a
relation `r` on `M` is `Tight.Conf P r` (with `r = ≼_M` here, `⊑` in the
theorem); the removal by commitment is `Tight.excluded_canon_iff`. -/
theorem «sec:tight-coordination/inconsistent-rows» {I M : Type} [PO I] [PO M] (sp : Spec I M)
    {i : I} {m : M} (hm : sp.P i m) (k : I) (x : M) :
    Excluded (canon sp i) m k x ↔ Tight.Conf sp.P PO.le i m k x :=
  Tight.excluded_canon_iff sp hm k x

/-- **Definition `def:necessary-guard`** (Necessary guard): "`𝒮₁` is a
necessary guard for `𝒮₂` when it makes no unnecessary commitment: whenever
rows `(i,m)` and `(k,x)` of `P₁` with `i ≼ k` are inconsistent at `k` in `P₁`,
some rows `(i,o)` and `(k,y)` of `P₂ ∘ P₁`, with `o ∈ P₂(m)` and
`y ∈ P₂(x)`, are inconsistent at `k` in `P₂ ∘ P₁`."  Lean: `Tight.Tight`, unfolded; in
terms of canonical commitments it is `Tight.tight_iff_excluded`. -/
theorem «def:necessary-guard» {I M O : Type} [PO I] [PO M] [PO O] (sp : Spec I M) (sk : Spec M O) :
    Tight.Tight sp sk ↔ ∀ i m k x, Tight.Conf sp.P PO.le i m k x →
      ∃ o y, sk.P m o ∧ sk.P x y ∧ Tight.Conf (Comp.seq sp sk).P PO.le i o k y :=
  Iff.rfl

/-- **Definition `def:tight-guard`** (Tight guard): "`𝒮₁` is a tight guard for
`𝒮₂` when it is both a sufficient and a necessary guard, and the pipeline's
coordination is then tight." -/
def «def:tight-guard» {I M O : Type} [PO I] [PO M] [PO O] (sp : Spec I M)
    (sk : Spec M O) : Prop :=
  Guard.Proper sp sk ∧ Tight.Tight sp sk

/-- "Write `m ⊑ m'` when every finite set of outputs in `P₂(m)` has a common
extension in `P₂(m')`, and read consistency of rows of `P₁` under `⊑`, and the
canonical commitments that inconsistency calls for, with `⊑` in place of
`≼_M`.  For a functional downstream `f`, `m ⊑ m'` exactly when
`f(m) ≼ f(m')`."  And, after the theorem: "`⊑` is transitive but need not be
an order."  Lean: `⊑` is `Tight.dle`; `Tight.graph_dle_iff`,
`Tight.dle_trans`. -/
theorem «sec:tight-coordination/downstream-order» {M O : Type} [PO M] [PO O] (g : M → O)
    (P₂ : Table M O) :
    (∀ a b, Tight.dle (Comp.graph g).P a b ↔ g a ≼ g b) ∧
      (∀ a b c, Tight.dle P₂ a b → Tight.dle P₂ b c → Tight.dle P₂ a c) :=
  ⟨fun _ _ => Tight.graph_dle_iff, fun _ _ _ h1 h2 => Tight.dle_trans h1 h2⟩

/-- **Theorem `thm:guard-tightening`** (Guard Tightening): "Let `𝒮₁` guard
`𝒮₂`.  (1) `⊑` is the coarsest order on `M` under which `𝒮₁` is a sufficient
guard for `𝒮₂`, and the upstream's canonical commitments under `⊑` include
every commitment the composite needs.  (2) If each `P₂(m)` has a greatest
element, as when `𝒮₂` is functional, the upstream's canonical commitments
under `⊑` are exactly the composite's.  So a sufficient guard is tight exactly
when `≼_M` requires no more commitments than `⊑`."  A canonical commitment
removing `(k,x)` at `σ_{P₁}(i)` corresponds to a pair inconsistent at `k`
(`Tight.excluded_canon_iff`).  Lean: (1) `Tight.proper_iff_le_dle` (an order
makes `𝒮₁` a sufficient guard exactly when it is contained in `⊑` on the
outputs of `𝒮₁`; every other order is `«thm:guard-tightening/any-order»`) and
`Tight.dleConf_of_compConf`; (2) `Tight.dleConf_iff_compConf` and
`Tight.tight_iff` (a greatest element is `Tight.HasTop`).  The functional
case of (2) needs no sufficiency: `Tight.graph_conf_iff`. -/
theorem «thm:guard-tightening» {I M O : Type} [PO I] [PO M] [PO O] (sp : Spec I M)
    (sk : Spec M O) :
    (Guard.Proper sp sk ↔ ∀ m m', Joint.Img sp m → Joint.Img sp m' → m ≼ m' →
      Tight.dle sk.P m m') ∧
    (Guard.Proper sp sk → ∀ i m k x o y, sp.P i m → sp.P k x → sk.P m o → sk.P x y →
      Tight.Conf (Comp.seq sp sk).P PO.le i o k y → Tight.Conf sp.P (Tight.dle sk.P) i m k x) ∧
    (Guard.Proper sp sk → (∀ m, Joint.Img sp m → ∃ t, Tight.HasTop sk.P m t) →
      (∀ i m k x, sp.P i m → sp.P k x → (Tight.Conf sp.P (Tight.dle sk.P) i m k x ↔
        ∃ o y, sk.P m o ∧ sk.P x y ∧ Tight.Conf (Comp.seq sp sk).P PO.le i o k y)) ∧
      («def:tight-guard» sp sk ↔
        ∀ i m k x, Tight.Conf sp.P PO.le i m k x ↔ Tight.Conf sp.P (Tight.dle sk.P) i m k x)) :=
  ⟨Tight.proper_iff_le_dle sp sk,
   fun hP _ _ _ _ _ _ hi hk hm hx hc => Tight.dleConf_of_compConf hP hi hk hm hx hc,
   fun hP htop => ⟨fun _ _ _ _ hi hk => Tight.dleConf_iff_compConf hP htop hi hk,
     ⟨fun h => (Tight.tight_iff hP htop).1 h.2, fun h => ⟨hP, (Tight.tight_iff hP htop).2 h⟩⟩⟩⟩

/-- After Theorem `thm:guard-tightening`: "A greatest element of `P₂(m)` is one
answer to `m` that extends every other.  A functional downstream has one
trivially, and the gap example below, where `P₂(z) = ℕ`, has none."  Lean:
`g m` is greatest in the fiber of `graph g` at `m`; the gap example's `z` has
no greatest answer. -/
theorem «sec:tight-coordination/greatest» {M O : Type} [PO M] [PO O] (g : M → O) (m : M) :
    Tight.HasTop (Comp.graph g).P m (g m) ∧ ¬ ∃ t, Tight.HasTop Tight.Gap.down.P .z t :=
  ⟨⟨rfl, fun _ h => h ▸ PO.refl _⟩, fun ⟨t, _, ht⟩ => by
    have : t + 1 ≤ t := ht (t + 1) trivial
    omega⟩

/-- `thm:guard-tightening`, for every order: "Since every order under which `𝒮₁`
is a sufficient guard is contained in `⊑`, and a smaller order makes at least
as many pairs inconsistent, each such order requires at least the commitments
that `⊑` does.  At the other extreme, equality on `M` requires the most, since
every order on `M` contains it."  Lean: `Tight.conf_of_dleConf_under`; `inst`
is the other order on `M`, and `Joint.underOut`/`Joint.underIn` are the same
tables with `M` ordered by it.  Equality: `Tight.conf_mono`. -/
theorem «thm:guard-tightening/any-order» {I M O : Type} [PO I] [PO O] {_instM : PO M}
    (inst : PO M) (sp : @Spec I M _ _instM) (sk : @Spec M O _instM _) :
    (@Guard.Proper I M O _ inst _ (Joint.underOut inst sp) (Joint.underIn inst sk) →
      ∀ {i m k x}, Tight.Conf (@Spec.P I M _ _instM sp) (Tight.dle (@Spec.P M O _instM _ sk)) i m k x →
      Tight.Conf (@Spec.P I M _ _instM sp) (@PO.le M inst) i m k x) ∧
    (∀ {i m k x}, Tight.Conf (@Spec.P I M _ _instM sp) (@PO.le M inst) i m k x →
      Tight.Conf (@Spec.P I M _ _instM sp) (fun a b => a = b) i m k x) :=
  ⟨fun hP _ _ _ _ h => Tight.conf_of_dleConf_under inst sp sk hP h,
   fun h => Tight.conf_mono (fun a b _ _ e => e ▸ @PO.refl M inst a) h⟩

open Tight Tight.SMR in
/-- "When the store's responses record the commands that produced them, the
consensus log is a tight guard: execution is monotone and reflects the prefix
order, so every commitment the log makes is one the store's clients can
observe (Appendix `app:tight`)."  Lean: `Tight.SMR.log_tight_guard`, for any
deterministic state machine `δ`, whose execution `Inst.execF` records each
command with its response (`Tight.SMR.execF_reflects`). -/
theorem «sec:tight-coordination/consensus-log» {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R)
    (σ0 : Stt) :
    «def:tight-guard» (Inst.smrS1 (Cmd := Cmd)) (graph (Inst.execF δ σ0)) :=
  log_tight_guard δ σ0

open Tight Tight.Log Comp Guard in
/-- "The commuting log is a sufficient guard but not a necessary one:
`({A},[A])` and `({A,B},[B,A])` are inconsistent at `{A,B}` under the prefix
order but consistent there under `⊑`."  With the motivating paragraph:
"Suppose two commands `A` and `B` commute, and the store's outputs do not
record their order, as when it reports its state."  Lean:
`Tight.Log.commuting`, with two increments and the store answering a log with
its length (Appendix `app:tight`). -/
theorem «sec:tight-coordination/commuting-log» :
    Proper log (graph len) ∧ Conf log.P PO.le .a .a .ab .ba ∧
      ¬ Conf (seq log (graph len)).P PO.le .a 1 .ab 2 ∧
      ¬ Conf log.P (fun m m' => len m ≼ len m') .a .a .ab .ba ∧
      ¬ Tight log (graph len) ∧ ¬ log.LiftedMono ∧ (seq log (graph len)).LiftedMono :=
  Tight.Log.commuting

open Tight Tight.Log Comp Guard in
/-- "When commands commute and responses do not record their order, a log that
orders only non-commuting commands, as in Generalized Paxos and EPaxos,
restores tightness."  Lean, for the two commuting increments of the commuting
log: `Tight.Log.partial_order_log`, a log that records only which commands it
has logged, behind a store answering with their number, is a tight guard
(Appendix `app:tight`, Proposition `prop:tight-guards`(1)).  The general
claim for other command sets is illustrated by this example, not proved. -/
theorem «sec:tight-coordination/partial-order-log» :
    «def:tight-guard» plog (graph card) ∧ plog.LiftedMono :=
  ⟨⟨partial_order_log.1, partial_order_log.2.1⟩, partial_order_log.2.2⟩

open Tight Tight.Gap Comp Guard in
/-- "Without greatest answers, a gap can remain.  Let `𝒮₁` emit `z` at input
`lo` and any `n_k` at a larger input `hi`, and let `𝒮₂` answer `z` with any
number and `n_k` with `k`. … and so under every order on `M` under which `𝒮₁`
is a sufficient guard.  Yet the composite permits every number at both inputs
and needs no commitment."  Lean: `Tight.Gap.gap` (Appendix `app:tight`). -/
theorem «sec:tight-coordination/gap» :
    Proper up down ∧ Conf up.P (dle down.P) .lo .z .hi (.n 0) ∧
      (∀ inst : PO Mid, @Proper Lv Mid Nat _ inst _ (@Joint.underOut Lv Mid _ midPO inst up)
          (@Joint.underIn Mid Nat _ midPO inst down) →
        Conf upP (@PO.le Mid inst) .lo .z .hi (.n 0)) ∧
      (seq up down).LiftedMono ∧ ¬ Tight up down :=
  Tight.Gap.gap

/-! ## Composite CALM (`sec:composite-calm`) -/

/-- "Composite CALM asks a stronger question: when does a pipeline need no
commitment at any stage?  If every stage is monotone, the answer is immediate:
by Lemma `lem:composition` the composite is monotone too, and no stage needs a
commitment."  And, from the first case: "First, every stage is monotone, as
noted above."
Lean:
`Guard.pipeline_coordination_free` (the base case of the pipeline induction):
the composite is Lifted-Monotone, and the pipeline of an empty-basis upstream
and any system for the downstream emits only what the composite emits under
the empty basis, so it is again an empty-basis guard. -/
theorem «sec:composite-calm/all-monotone» {I M O : Type} [PO I] [PO M] [PO O]
    {sp : Spec I M} {sk : Spec M O} (hP : sp.LiftedMono) (hK : sk.LiftedMono) (K : Guard.Sys sk) :
    (Comp.seq sp sk).LiftedMono ∧
      ∀ l', Guard.GEmits (Guard.Sys.free (fun _ : Commitment sp => False)).emits K l' →
        (Guard.Sys.free (fun _ : Commitment (Comp.seq sp sk) => False)).emits l' :=
  ⟨Comp.seq_liftedMono hP hK, fun _ h => (Guard.pipeline_coordination_free hP hK h).2⟩

/-- "The composite is itself an I/O specification.  By Complete CALM,
its runs are consistent exactly when it satisfies Lifted
Monotonicity, and then no output needs a commitment (Theorem
`thm:complete-calm`, Proposition `prop:exposure-boundary`)." -/
theorem «sec:composite-calm/complete-calm» {I M O : Type} [PO I] [PO M] [PO O]
    (sp1 : Spec I M) (sp2 : Spec M O) :
    ((Comp.seq sp1 sp2).Consistent ↔ (Comp.seq sp1 sp2).LiftedMono) ∧
      ((Comp.seq sp1 sp2).LiftedMono →
        ∀ τ : State (Comp.seq sp1 sp2), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o) :=
  ⟨complete_calm _, fun h =>
    (exposure_boundary _).1 ((liftedMono_iff_commonExpansion _).1 h)⟩

/-- "The orders on `I` and `O` are part of the composite's contract with its
environment.  The order on `M` is not: the composite's table never mentions
it, and some order on `M` may make both stages monotone."  Lean:
`Joint.seq_under` (the composite of the stages read under another order `inst`
on `M` is the composite under the given order `instM`; the type `Spec I O`
does not mention `M`).  That some order on `M` may make both stages monotone
is the boolean toggle, `«sec:composite-calm/cancellation»`. -/
theorem «sec:composite-calm/middle-order» {I M O : Type} [PO I] [instM : PO M] [PO O]
    (inst : PO M) (sp1 : Spec I M) (sp2 : Spec M O) :
    @Comp.seq I M O _ inst _ (Joint.underOut inst sp1) (Joint.underIn inst sp2) =
      Comp.seq sp1 sp2 :=
  Joint.seq_under inst sp1 sp2

/-- "The CRDT observations of Section `sec:crdt-instance` have this shape.  A
client query `q` over the replica state `s` is the composition `q ∘ s`, and
compositions of monotone functions are monotone, so monotonicity of `q` on
the whole state domain suffices."  Lean: Corollary `cor:functional-composition` applied to `s = Inst.st s₀` (monotone by
`«sec:crdt-instance/state-monotone»`) and a monotone `q`. -/
theorem «sec:composite-calm/crdt-query» {D Y : Type} [PO D] [Inst.JSL D] [PO Y] (s0 : D)
    {q : D → Y} (hq : Monotone q) : Monotone (q ∘ (Inst.st s0 : Inst.FSet D → D)) :=
  Comp.functional_composition (Inst.st_mono s0) hq

/-- "Second, the upstream can filter out the inputs on which the downstream is
not monotone.  In the example above, the test fails monotonicity only when the
count passes from single to double digits, and the capped counter never does
so.  Restricted to the counts it does produce, the test always answers `false`;
it is constant, and so monotone under any output order, including equality.  By
Proposition `prop:guard-test`, the capped counter is a sufficient guard, and
since it is itself monotone, neither stage needs a commitment
(Proposition `prop:joint-monotone`(2)).  This is tight coordination in which
the upstream itself needs no commitment."  And, from the subsection's puzzle:
"Consider the spec for an incrementing counter that is capped at `9`, and
compose it with a downstream spec for a double-digit threshold test, which
outputs `false` for values up through `9` and `true` from `10` on. … Suppose
instead that every answer must be final: unchanging in the face of more input.  Then the output order is equality,
and the test cannot emit `false` without a commitment, since a later count of
`10` would contradict it.  Yet when composed after the capped counter, the pair
of stages needs no commitment."
Lean: `Joint.threshold`
(the test is not Lifted-Monotone, the composite is).  Lean also proves the
Appendix `app:composition` treatment of the test: it cannot emit under the empty basis below
`10`, and the capped counter is a sufficient guard (`Guard.Proper`). -/
theorem «sec:composite-calm/filtering» :
    ¬ Joint.thr.LiftedMono ∧
      (∀ m, m ≤ 9 → ∀ o τ, ¬ SysStep (fun _ => False) (canon Joint.thr m) (.output o) τ) ∧
      (Comp.seq Joint.up Joint.thr).LiftedMono ∧ Guard.Proper Joint.up Joint.thr :=
  Joint.threshold

/-- "Under the usual boolean order, as in LVars, `false` is only a lower bound,
and the test is monotone."  And, from the second case: "Restricted to the
counts it does produce, the test always answers `false`; it is constant, and so
monotone under any output order, including equality."  Lean: `Joint.twoDigit_orders`.  Under the lattice order
(`Joint.boolPO`, `false` below `true`) the test `n ↦ [10 ≤ n]` is
Lifted-Monotone, so it needs no commitment; under every partial order on the
booleans it is Lifted-Monotone on the counts `≤ 9` the capped counter offers
(`Joint.CEOn`), so by Proposition `prop:guard-test` the capped counter is a
sufficient guard whatever the output order. -/
theorem «sec:composite-calm/output-orders» :
    (Comp.graph (fun n : Nat => decide (10 ≤ n))).LiftedMono ∧
    ∀ inst : PO Bool, letI := inst;
      Joint.CEOn (Comp.graph (fun n : Nat => decide (10 ≤ n))) (fun m => ¬ Joint.Big m) :=
  Joint.twoDigit_orders

/-- "Third, a different order on `M` can make two non-monotone stages
monotone.  Consider two stages that each negate a boolean, so that their
composite is the identity.  We order the booleans with false below true for
`I`, `O`, and `M`.  Neither stage is monotone, since each maps true, the larger
value, to false.  Reversing the order on `M`, so that true lies below false,
makes both stages monotone, and the composite is the identity either way
(Appendix `app:composition`)."  Lean: `Joint.bool_toggle`
(`Bool` ordered by `Joint.boolPO`, `false ≼ true`; `Joint.Rev` is the reversed
order; the composite is the identity, and is unchanged by the reversal).  The
appendix's empty-basis behaviour of the first stage is
`«app:composition/boolean-toggle»`. -/
theorem «sec:composite-calm/cancellation» :
    ¬ (graph not).LiftedMono ∧
      Comp.seq (graph not) (graph not) = graph (id : Bool → Bool) ∧
      (graph (id : Bool → Bool)).LiftedMono ∧
      (Joint.pushOut (graph not) Joint.Rev.mk).LiftedMono ∧
      (Joint.pullIn (graph not) Joint.Rev.val).LiftedMono ∧
      Comp.seq (Joint.pushOut (graph not) Joint.Rev.mk) (Joint.pullIn (graph not) Joint.Rev.val) =
        Comp.seq (graph not) (graph not) :=
  Joint.bool_toggle

/-- **Proposition `prop:joint-monotone`** (Jointly monotone composites): "The
composite `P₂ ∘ P₁` satisfies Lifted Monotonicity, so its runs are consistent
and it needs no commitment, in each of the following cases.  (1) `𝒮₁` and `𝒮₂`
satisfy Lifted Monotonicity.  (2) `𝒮₁` satisfies Lifted Monotonicity; `𝒮₂`
satisfies it on `𝒮₁`'s outputs.  (3) `𝒮₁` and `𝒮₂` satisfy Lifted
Monotonicity via a different order on `M`."  Lean: the hypothesis is the
disjunction of the three cases; "satisfies it on" is `Joint.CEOn` (defined in
Section `sec:tight-coordination`; see `«def:sufficient-guard»`), and
"`𝒮₁`'s outputs" is
`Joint.Img sp1`.  In (3), `Joint.underOut inst sp1` and `Joint.underIn inst sp2`
are the same tables with `M` ordered by `inst`; "a different order" is any
partial order `inst` (it may coincide with `≼_M`, which is case (1)).  (1) `Comp.seq_liftedMono`;
(2) `Joint.seq_liftedMono_img`; (3) `Joint.seq_liftedMono_reorder`.
"Its runs are consistent and it needs no commitment" is
`«sec:composite-calm/complete-calm»`. -/
theorem «prop:joint-monotone» {I M O : Type} [PO I] [PO M] [PO O]
    (sp1 : Spec I M) (sp2 : Spec M O)
    (hcase : (sp1.LiftedMono ∧ sp2.LiftedMono) ∨
      (sp1.LiftedMono ∧ Joint.CEOn sp2 (Joint.Img sp1)) ∨
      ∃ inst : PO M, @Spec.LiftedMono I M _ inst (Joint.underOut inst sp1) ∧
        @Spec.LiftedMono M O inst _ (Joint.underIn inst sp2)) :
    (Comp.seq sp1 sp2).LiftedMono ∧ (Comp.seq sp1 sp2).Consistent ∧
      ∀ τ : State (Comp.seq sp1 sp2), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o := by
  have h : (Comp.seq sp1 sp2).LiftedMono := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨inst, h1, h2⟩
    · exact Comp.seq_liftedMono h1 h2
    · exact Joint.seq_liftedMono_img h1 h2
    · exact Joint.seq_liftedMono_reorder inst h1 h2
  exact ⟨h, («sec:composite-calm/complete-calm» sp1 sp2).1.2 h,
    («sec:composite-calm/complete-calm» sp1 sp2).2 h⟩

/-- "The three cases do not cover every monotone composite (Appendix
`app:composition`).  When no case applies, some stage may have to issue a commitment even though the composite is monotone."  Lean: `Joint.no_order_counterexample`
(`I` is the chain `Joint.C3`, `M = Joint.Mid`): under every partial order on
`M` the composite is Lifted-Monotone, the upstream is not (so case (3) fails,
and with it (1) and (2)), and its empty-basis system cannot emit at some
canonical state.  The appendix treatment is `«app:composition/reach»`. -/
theorem «sec:composite-calm/reach» :
    (∀ _inst : PO Joint.Mid, (Comp.seq (graph Joint.fz) (graph Joint.gz)).LiftedMono) ∧
      (∀ _inst : PO Joint.Mid, ¬ (graph Joint.fz).LiftedMono) ∧
      ∀ _inst : PO Joint.Mid, ∃ i, ∀ o τ,
        ¬ SysStep (fun _ => False) (canon (graph Joint.fz) i) (.output o) τ :=
  Joint.no_order_counterexample

/-! ## Intersection (`sec:intersection`) -/

/-- **Definition `def:intersection`** (Intersection): "Let `𝒮₁ = (I,≼_I,O,≼_O,P₁)`
and `𝒮₂ = (I,≼_I,O,≼_O,P₂)` share their ordered domains.  Their intersection
`𝒮₁ ∩ 𝒮₂` has table `P₁ ∩ P₂`.  It is an I/O specification when `P₁ ∩ P₂` is
total on `I`: every input has an output that both permit."  Lean: `Inter.inter`
takes the totality of the intersection as an argument. -/
theorem «def:intersection» {I O : Type} [PO I] [PO O] (s₁ s₂ : Spec I O)
    (htot : ∀ i, ∃ o, s₁.P i o ∧ s₂.P i o) (i : I) (o : O) :
    (Inter.inter s₁ s₂ htot).P i o ↔ s₁.P i o ∧ s₂.P i o :=
  Iff.rfl

/-- "Intersection does not preserve Lifted Monotonicity.  Let `a` and `b` be
incomparable outputs, each below both `c` and `d`, with `c` and `d`
incomparable, and let both specs have a single input.  The fiber `{a,b,c}` is
directed, since `c` extends each of its members, and so is `{a,b,d}`.  The
intersection of the two fibers, `{a,b}`, is not: no output in it extends both
`a` and `b`.  Two
specs that need no commitment can thus have an intersection that does."  Lean:
`Inter.not_closed` (outputs `Inter.Q4`, input `Unit`); the intersection is total
(`Inter.sCD_total`); "needs no commitment" and "does" are Lifted Monotonicity
and its failure, read through Proposition `prop:exposure-boundary`
(`exposure_boundary`): the intersection has a state reachable without
commitment with an output that is not legal. -/
theorem «sec:intersection/not-closed» :
    Inter.sC.LiftedMono ∧ Inter.sD.LiftedMono ∧
      ¬ (Inter.inter Inter.sC Inter.sD Inter.sCD_total).LiftedMono ∧
      ¬ ∀ τ : State (Inter.inter Inter.sC Inter.sD Inter.sCD_total), ReachableCF τ →
          ∀ o, τ.R τ.cur o → Exposable τ o := by
  obtain ⟨h1, h2, h3⟩ := Inter.not_closed
  exact ⟨h1, h2, h3 Inter.sCD_total, fun h => h3 Inter.sCD_total
    ((liftedMono_iff_commonExpansion _).2 ((exposure_boundary _).2 h))⟩

/-- **Proposition `prop:intersection-bound`** (Intersection under a monotone
bound): "Let `g : I → O` be monotone.  Suppose that every output `𝒮₁` permits
at an input `j` lies below `g(j)`, and that `𝒮₁` and `𝒮₂` both permit `g(j)` at
every `j`.  Then `𝒮₁ ∩ 𝒮₂` is an I/O specification and satisfies Lifted
Monotonicity."  Lean: `Inter.inter_liftedMono_of_bound`; totality is witnessed
by `g`. -/
theorem «prop:intersection-bound» {I O : Type} [PO I] [PO O] (s₁ s₂ : Spec I O) (g : I → O)
    (hg : Comp.Monotone g) (hb : ∀ j o, s₁.P j o → o ≼ g j) (h₁ : ∀ j, s₁.P j (g j))
    (h₂ : ∀ j, s₂.P j (g j)) :
    (Inter.inter s₁ s₂ fun j => ⟨g j, h₁ j, h₂ j⟩).LiftedMono :=
  Inter.inter_liftedMono_of_bound s₁ s₂ g hg hb h₁ h₂

end Paper
end CC
