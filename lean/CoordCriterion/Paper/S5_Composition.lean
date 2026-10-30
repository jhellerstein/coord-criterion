import CoordCriterion.Appendix.Guarded
import CoordCriterion.Appendix.JointMono
import CoordCriterion.Appendix.Components

/-!
# Paper §5, "Composition and Proper Coordination" (`sections/composition.tex`)

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
satisfy Lifted Monotonicity, then so does the ordered specification with
table `S₂ ∘ S₁`." -/
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

/-! ## Composite CALM (`sec:composite-calm`) -/

/-- "The composite is itself an ordered specification.  By Complete CALM,
specification `S₂ ∘ S₁` is consistent exactly when it satisfies Lifted
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

/-- "First, every stage is monotone.  By Lemma `lem:composition` the pipeline
is monotone, and no stage need make a commitment (Corollary `cor:pipelines`)."
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

/-- "The CRDT observations of Section `sec:crdt-instance` have this shape: a
client query `q` over the replica state `s` is the composition `q ∘ s`, and
compositions of monotone functions are monotone (Corollary
`cor:functional-composition`), so monotonicity of `q` on all of the state domain
suffices."  Lean: the
corollary applied to `s = Inst.st s₀` (monotone by
`«sec:crdt-instance/state-monotone»`) and a monotone `q`. -/
theorem «sec:composite-calm/crdt-query» {D Y : Type} [PO D] [Inst.JSL D] [PO Y] (s0 : D)
    {q : D → Y} (hq : Monotone q) : Monotone (q ∘ (Inst.st s0 : Inst.FSet D → D)) :=
  Comp.functional_composition (Inst.st_mono s0) hq

/-- "Second, the upstream can filter out the inputs on which the downstream is
not monotone.  Consider a counter capped at `9` that feeds a test of whether
the count is below `10`.  With counts ordered numerically and the answers yes
and no incomparable, the test is not monotone: it answers yes at `0` through
`9` and no at `10`.  But the counter never produces `10` or higher.  The
downstream need only be monotone on the values the upstream can produce."  Lean: `Joint.threshold`
(the test is not Lifted-Monotone, the composite is).  Lean also proves the
Appendix D treatment of the test: it cannot emit under the empty basis below
`10`, and the pipeline is proper (`Guard.Proper`). -/
theorem «sec:composite-calm/filtering» :
    ¬ Joint.thr.LiftedMono ∧
      (∀ m, m ≤ 9 → ∀ γ o τ, ¬ SysStep (fun _ => False) (canon Joint.thr m) (.output γ o) τ) ∧
      (Comp.seq Joint.up Joint.thr).LiftedMono ∧ Guard.Proper Joint.up Joint.thr :=
  Joint.threshold

/-- "Third, considering a different order on `M` can make two non-monotone
stages both monotone.  Order the booleans with false below true for `I`, `O`
and `M`.  Consider a double-toggle: two stages that each negate a boolean
compose to the identity.  Neither is monotone, but under the reversed order on
`M`, both are (Appendix `app:composition`)."  Lean: `Joint.bool_toggle`
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
composite `S₂ ∘ S₁` satisfies Lifted Monotonicity, and so is consistent and
needs no commitment, in each of the following cases.  (1) `𝒮₁` and `𝒮₂`
satisfy Lifted Monotonicity.  (2) `𝒮₁` satisfies Lifted Monotonicity; `𝒮₂`
satisfies it on `𝒮₁`'s outputs.  (3) `𝒮₁` and `𝒮₂` satisfy Lifted
Monotonicity via a different order on `M`."  And, just
before: "We say that `S₂` satisfies Lifted Monotonicity on a set `D ⊆ M` when
its restriction to inputs in `D` does."  Lean: the hypothesis is the
disjunction of the three cases; "on `D`" is `Joint.CEOn`, which is
equivalent to Lifted Monotonicity of the restriction to `D`
(`Joint.ceOn_iff_restrictTo`), and "`𝒮₁`'s outputs" is
`Joint.Img sp1`.  In (3), `Joint.underOut inst sp1` and `Joint.underIn inst sp2`
are the same tables with `M` ordered by `inst`; "a different order" is any
partial order `inst` (it may coincide with `≼_M`, which is case (1)).  (1) `Comp.seq_liftedMono`;
(2) `Joint.seq_liftedMono_img`; (3) `Joint.seq_liftedMono_reorder`.
"Consistent and needs no commitment" is `«sec:composite-calm/complete-calm»`. -/
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
      ∀ _inst : PO Joint.Mid, ∃ i, ∀ γ o τ,
        ¬ SysStep (fun _ => False) (canon (graph Joint.fz) i) (.output γ o) τ :=
  Joint.no_order_counterexample

/-! ## Proper Coordination (`sec:proper-coordination`) -/

/-- "The replicated store of the opening extends the filtering case of
Proposition `prop:joint-monotone`(2).  The key-value store is not monotone on
its own, but it is monotone on what the log offers: a log fixes the order of
commands, and a longer log only extends the responses.  Unlike the filtering
case, the upstream must issue a commitment to offer only such inputs."  Lean, for any
deterministic state machine `δ` and two distinct commands: the key-value store
`𝒦 ∘ 𝒫` (`𝒫 = Inst.smrS1`, the log) is not Lifted-Monotone, execution
`Inst.execF δ σ₀` is monotone on logs, and the log is not Lifted-Monotone. -/
theorem «sec:proper-coordination/kvs-on-logs» {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R)
    (σ0 : Stt) {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) :
    ¬ (Guard.comp Inst.smrS1 (Inst.execF δ σ0)).LiftedMono ∧ Monotone (Inst.execF δ σ0) ∧
      ¬ (Inst.smrS1 (Cmd := Cmd)).LiftedMono :=
  let h := Guard.smr_proper δ σ0 hne
  ⟨h.2.1, h.2.2.1, h.1⟩

/-- **Definition `def:proper-coordination`** (Proper Coordination): "A pipeline
in which `𝒮₁` guards `𝒮₂` is proper when `𝒮₂|_{𝒮₁}` needs no commitment:
every output at every state it reaches without commitment is exposable."  And,
just before: "Write `𝒮₂|_{𝒮₁}` for `𝒮₂` restricted to the outputs of `𝒮₁`."
Lean: `𝒮₂|_{𝒮₁}` is `Guard.rest sp sk = Joint.restrictTo (Joint.Img sp) sk`,
whose inputs are the outputs of `sp` (a subtype of `M` with the order of `M`);
"needs no commitment" is `Guard.NeedsNoCommit`.  The definition does not
mention the system for `𝒮₁`. -/
theorem «def:proper-coordination» {I M O : Type} [PO I] [PO M] [PO O] (sp : Spec I M)
    (sk : Spec M O) :
    (Guard.Proper sp sk ↔
      ∀ τ : State (Guard.rest sp sk), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o) ∧
      Guard.rest sp sk = Joint.restrictTo (Joint.Img sp) sk ∧
      ∀ (m : {m // Joint.Img sp m}) o, (Guard.rest sp sk).S m o ↔ sk.S m.1 o :=
  ⟨Iff.rfl, rfl, fun _ _ => Iff.rfl⟩

/-- **Theorem `thm:proper-coordination`** (Proper Coordination): "Fix any
system for `𝒮₁`.  (1) The pipeline is proper exactly when `𝒮₂` satisfies
Lifted Monotonicity on the outputs of `𝒮₁`.  (2) If it is proper, `𝒮₂|_{𝒮₁}`
under the empty basis follows every run of `𝒮₁`.  The result is a run of
`S₂ ∘ S₁`, and whenever runs of `𝒮₁` can be brought to a common state, the
composite runs are confluent.  (3) If it is proper and `S₂ ∘ S₁` violates
Lifted Monotonicity, `𝒮₁` cannot emit some output without a commitment."
Lean: (1) `Guard.proper_iff` ("on the outputs" is `Joint.CEOn sk (Joint.Img sp)`),
with `Guard.proper_iff_consistent` (Complete CALM on `𝒮₂|_{𝒮₁}`).  (2) For
every run of `𝒮₁` under any basis `B` emitting `m :: ms`:
`Guard.proper_follows` (the empty-basis `𝒮₂|_{𝒮₁}` starts at `σ(m)`, answers
`m`, and receives and answers each later output, and the result, `Guard.merge`,
is a run of `S₂ ∘ S₁`); `Guard.proper_run` (more generally, any empty-basis
run of `𝒮₂|_{𝒮₁}` that receives each output and answers it any number of
times gives a run of `S₂ ∘ S₁` whose table contains the join); and
`Guard.proper_confluent`.  (3) `Guard.proper_needs_commit` ("cannot emit": no
such `m'` is exposable at `σ_{𝒮₁}(i)`, and under the empty basis no output
event there emits one).  The system for `𝒮₁` enters only through its basis,
which is arbitrary. -/
theorem «thm:proper-coordination» {I M O : Type} [PO I] [PO M] [PO O] (sp : Spec I M)
    (sk : Spec M O) :
    (Guard.Proper sp sk ↔ Joint.CEOn sk (Joint.Img sp)) ∧
    (Guard.Proper sp sk ↔ (Guard.rest sp sk).Consistent) ∧
    (Guard.Proper sp sk → ∀ (B : Basis sp) i es (ρ : State sp) m ms,
      SysExec B (canon sp i) es ρ → Guard.emitted es = m :: ms →
      ∃ (hm : Joint.Img sp m) (o : O) (ps : List ({m // Joint.Img sp m} × O))
        (esK : List (SEvent (Guard.rest sp sk))) (ρK : State (Guard.rest sp sk)),
        ps.map (fun p => p.1.1) = ms ∧ esK.filterMap SEvent.erase = .output o :: Guard.storeTr ps ∧
        Guard.Produces (Guard.noStore (Guard.rest sp sk)) ⟨m, hm⟩ esK ρK ∧
        ∃ ρ' : State (Comp.seq sp sk),
          Exec (canon (Comp.seq sp sk) i) (Guard.merge es ([o] :: ps.map fun p => [p.2])) ρ' ∧
          ρ'.cur = ρ.cur) ∧
    (Guard.Proper sp sk → ∀ (B : Basis sp) i es (ρ : State sp) (m : {m // Joint.Img sp m}) ms os
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
      (∃ τ : State sp, τ.cur = j ∧ ∀ p ∈ fam, ∃ (B : Basis sp) (es : List (SEvent sp)),
        SysExec B p.1 es τ) →
      ConfluentAt (fam.map fun p => p.2.2) j) ∧
    (Guard.Proper sp sk → ¬ (Comp.seq sp sk).LiftedMono →
      ∃ i m o, sp.S i m ∧ sk.S m o ∧ ¬ Exposable (canon (Comp.seq sp sk) i) o ∧
        (∀ m', sp.S i m' → sk.S m' o → ¬ Exposable (canon sp i) m') ∧
        ∀ γ m' τ, SysStep (fun _ => False) (canon sp i) (.output γ m') τ → ¬ sk.S m' o) :=
  ⟨Guard.proper_iff, Guard.proper_iff_consistent,
    fun hP _ _ _ _ _ _ hx he => Guard.proper_follows hP hx he,
    fun hP _ _ _ _ _ _ _ _ _ _ hx he hps hK htr => Guard.proper_run hP hx he hps hK htr,
    fun hP fam h1 h2 h3 h4 j hj hS => Guard.proper_confluent hP fam h1 h2 h3 h4 j hj hS,
    fun hP hnot => Guard.proper_needs_commit hP hnot⟩

/-- "The theorem holds whatever basis `𝒮₁` uses, and a proper pipeline is
itself a guard for a further stage (Corollary `cor:pipelines`).  Locks in the
key-value store would be pure overhead: by (1), the store restricted to logs
needs no commitment."  Lean: for the log `𝒫 = Inst.smrS1` and execution
`Inst.execF δ σ₀`, every log is an output of the log, and the pipeline is
proper, so the store restricted to logs needs no commitment.  Being a guard
is `«cor:pipelines»`. -/
theorem «sec:proper-coordination/locks-overhead» {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R)
    (σ0 : Stt) {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) :
    (∀ m, Joint.Img (Inst.smrS1 (Cmd := Cmd)) m) ∧
      ∀ τ : State (Guard.rest Inst.smrS1 (graph (Inst.execF δ σ0))), ReachableCF τ →
        ∀ o, τ.R τ.cur o → Exposable τ o :=
  let h := Guard.smr_proper δ σ0 hne
  ⟨h.2.2.2.1, h.2.2.2.2.1⟩

/-- "We call a system for one specification, viewed through a chosen set of
sound boundary observations, a component.  A component may run as one process
or as a replicated cluster.  The stages around it observe only its admitted
boundary runs, each pairing an input with an emitted output permitted by its
specification.  Components with different specifications form typed pipelines
(Appendix `app:components`).  The pipeline hides the intermediate value and the two
component runs; every external pair it presents is a row of `S₂ ∘ S₁`.  A
typed pipeline is contract-proper when it is proper in the sense of
Definition `def:proper-coordination`.  Contract properness concerns the
specifications.  Implementation properness additionally concerns the runs
admitted by the selected downstream component.  A downstream implementation
may still take locks, or admit too few runs to follow its upstream.  The
maximally permissive empty-basis component for `𝒮₂|_{𝒮₁}` does neither."
Lean: `Components.Component` (Def. `def:component`; systems as components are
`«app:components/system-is-component»`), `Components.Pipeline.sound` for the
rows; contract properness is `Components.Pipeline.ContractProper`, equivalent
to `Guard.Proper` and stated on the specifications; implementation properness
is `Components.Pipeline.ImplementationProper`; the locking store is
`Components.early_lock_component`, a downstream admitting too few runs is
`Components.threshold_component`; the empty-basis component for `𝒮₂|_{𝒮₁}`
is `Components.offered_available` (Prop. `prop:typed-pipelines`(3)–(5) in
`Paper/AppD_Composition.lean`). -/
theorem «sec:proper-coordination/components» {I M O : Type} [PO I] [PO M] [PO O]
    (sp : Spec I M) (sk : Spec M O) :
    (∀ (p : Components.Pipeline sp sk) obs, p.Accepts obs →
      (Comp.seq sp sk).S obs.input obs.output) ∧
    (∀ p : Components.Pipeline sp sk, p.ContractProper ↔ Guard.Proper sp sk) ∧
    (Guard.Proper sp sk → ∀ (C1 : Components.Component sp) r, C1.accepts r →
      let p := Components.Pipeline.offered (sk := sk) C1
        (Components.Component.ofBasis (Components.emptyBasis _))
      p.ImplementationProper ∧ ∃ w : Components.FeedWitness p.upstream p.downstream,
        w.upRun.input = r.input ∧ w.upRun.output.1 = r.output ∧ CoordFree w.downRun.events) :=
  ⟨fun p _ h => p.sound h, Components.contractProper_iff_guardProper,
    fun hP C1 _ h => Components.offered_available hP C1 h⟩

end Paper
end CC
