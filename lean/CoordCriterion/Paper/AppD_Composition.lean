import CoordCriterion.Appendix.Guarded

/-!
# Paper App. D, "Proofs and Details for Composition" (`appendices/composition.tex`)

Statement layer for Appendix `app:composition`.  The results it proves are
stated in Section `sec:composition` and recorded in
`Paper/S5_Composition.lean`; this file holds what appears only in the
appendix: composition with independent inputs and its curried evaluation, the
component-commitment example, the covering argument and the counterexamples of
the Proper Coordination subsection, and Example `ex:bare-reads`.
Unlabeled claims are `«app:composition/<slug>»`.

Library: `Appendix/Composition.lean` (namespace `CC.Comp`), the examples at
the end of `Instances/Examples.lean` (namespace `CC.Inst`), and
`Appendix/Guarded.lean` (namespace `CC.Guard`).  Conventions as in
`Paper/S5_Composition.lean`.
-/

namespace CC
namespace Paper

open CC.Comp (Monotone graph)

/-! ## Sequential composition -/


/-- **Corollary `cor:functional-composition`** (Functional composition): "If
`f : (I,≼_I) → (M,≼_M)` and `g : (M,≼_M) → (O,≼_O)` are monotone, so is
`g ∘ f`."  (Proved in the library through tables of functions and
Lemma `lem:composition`, as in the paper.) -/
theorem «cor:functional-composition» {I M O : Type} [PO I] [PO M] [PO O] {f : I → M} {g : M → O}
    (hf : Monotone f) (hg : Monotone g) : Monotone (g ∘ f) :=
  Comp.functional_composition hf hg

/-! ## Composition with independent inputs (`sec:parameterized-composition`) -/

/-- Eq. `eq:parameterized-composition`:
`G ⋆ F = π_{I,J,A,C}(F ⋈_B G) = {((i,j,a),c) : ∃ b. ((i,a),b) ∈ F ∧ ((j,b),c) ∈ G}`,
"with the product order on `I × J × A`.  Since `F` is total on `I × A` and `G`
is total on `J × B`, every composed input has a nonempty fiber."  Lean: the
composed input `(i,j,a)` is `(i,(j,a))`; `Comp.par F G` is the specification
with table `ptable`. -/
theorem «eq:parameterized-composition» {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C]
    (F : Spec (I × A) B) (G : Spec (J × B) C) :
    (∀ (i : I) (j : J) (a : A) (c : C),
        (Comp.par F G).S (i, (j, a)) c ↔ ∃ b, F.S (i, a) b ∧ G.S (j, b) c) ∧
      ∀ x, ∃ c, (Comp.par F G).S x c :=
  ⟨fun _ _ _ _ => Iff.rfl, (Comp.par F G).total⟩

/-- **Lemma `lem:parameterized-composition`** (Independently parameterized
composition): "If `Spec_F` and `Spec_G` satisfy Lifted Monotonicity, then the
specification with table `G ⋆ F` satisfies Lifted Monotonicity." -/
theorem «lem:parameterized-composition» {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C]
    {F : Spec (I × A) B} {G : Spec (J × B) C} (hF : F.LiftedMono) (hG : G.LiftedMono) :
    (Comp.par F G).LiftedMono :=
  Comp.par_liftedMono hF hG

/-! ### Curried evaluation -/

/-- Eq. `eq:curried-fibers`: `F_i = π_{A,B}(F[I=i])`, `G_j = π_{B,C}(G[J=j])`. -/
theorem «eq:curried-fibers» {I J A B C : Type} (F : Table (I × A) B) (G : Table (J × B) C)
    (i : I) (j : J) (a : A) (b : B) (c : C) :
    (Comp.fiberF F i a b ↔ F (i, a) b) ∧ (Comp.fiberG G j b c ↔ G (j, b) c) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Eq. `eq:curried-query-plan`:
`⋃_{(i,j) ∈ I×J} {((i,j,a),c) : (a,c) ∈ π_{A,C}(F_i ⋈_B G_j)}`. -/
theorem «eq:curried-query-plan» {I J A B C : Type} (F : Table (I × A) B) (G : Table (J × B) C)
    (x : I × (J × A)) (c : C) :
    Comp.curriedPlan F G x c ↔
      ∃ p : I × J, x.1 = p.1 ∧ x.2.1 = p.2 ∧
        Comp.tcomp (Comp.fiberF F p.1) (Comp.fiberG G p.2) x.2.2 c :=
  Iff.rfl

/-- **Proposition `prop:curried-query-plan`** (Curried equijoin plan): "The
table in Equation `eq:parameterized-composition` equals
[Eq. `eq:curried-query-plan`]." -/
theorem «prop:curried-query-plan» {I J A B C : Type} (F : Table (I × A) B) (G : Table (J × B) C) :
    Comp.ptable F G = Comp.curriedPlan F G :=
  Comp.curried_query_plan F G

/-- Eq. `eq:curried-composition`: "For monotone `f : I × A → B` and
`g : J × B → C`, the instance of
Lemma `lem:parameterized-composition` for their tables says that `h(i,j,a) = g(j, f(i,a))`
is monotone; in curried form, `h^♯(i,j) = g^♯(j) ∘ f^♯(i)`, which is the plan
of Proposition `prop:curried-query-plan` on tables of functions."  Lean: (1) `G ⋆ F`
of tables of functions is the table of `h`; (2) `h` is monotone; (3) the curried
form; (4) the curried plan of the two tables of functions is the table of `h`. -/
theorem «eq:curried-composition» {I J A B C : Type} [PO I] [PO J] [PO A] [PO B] [PO C]
    (f : I × A → B) (g : J × B → C) :
    Comp.par (graph f) (graph g) = graph (fun x : I × (J × A) => g (x.2.1, f (x.1, x.2.2))) ∧
      (Monotone f → Monotone g → Monotone (fun x : I × (J × A) => g (x.2.1, f (x.1, x.2.2)))) ∧
      (∀ i j, (fun a => g (j, f (i, a))) = (fun b => g (j, b)) ∘ (fun a => f (i, a))) ∧
      Comp.curriedPlan (graph f).S (graph g).S =
        (graph (fun x : I × (J × A) => g (x.2.1, f (x.1, x.2.2)))).S :=
  ⟨Comp.parameterized_graph f g, fun hf hg => Comp.parameterized_functional_composition hf hg,
    Inst.curried_sharp f g, Inst.curried_plan_graph f g⟩

/-! ## Composite CALM and component commitments -/

/-- "Let `𝒫` have one input `*` and table `{(*,x),(*,y)}` with `x,y`
incomparable, and let `f` map both to one value.  The composite `𝒦 ∘ 𝒫` has
one row, so it satisfies Lifted Monotonicity. … every run of `𝒫` under the
empty basis stays at the canonical state and emits nothing."  Lean:
`𝒫 = Dist.spU`; the second conjunct of `Guard.composite_monotone_not_enough`
says such runs emit nothing; `Guard.noBasis_silent` is the run-level form. -/
theorem «app:composition/components-commit» :
    (Guard.comp Dist.spU (fun _ : Dist.B2 => ())).LiftedMono ∧
      (∀ o, ¬ Exposable (canon Dist.spU ()) o) ∧
      ∀ es ρ, SysExec Dist.noBasis (canon Dist.spU ()) es ρ → Guard.emitted es = [] :=
  ⟨Guard.composite_monotone_not_enough.1,
    Dist.spU_not_exposable _ (fun _ _ => ⟨trivial, trivial⟩),
    Guard.composite_monotone_not_enough.2⟩

/-! ## Proper Coordination -/

/-- "The image of the canonical state `σ_𝒫(i)` is the canonical state of
`𝒦 ∘ 𝒫` at `i`, since `P[in ⪰ i] ⋈ K` is the composite table restricted to
the expansions of `i`."  Lean: `Guard.imgK_canon`; the function case is
`Guard.img_canon`. -/
theorem «app:composition/image-canon» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    (sk : Spec M O) (f : M → O) (i : I) :
    Guard.imgK sk (canon sp i) = canon (Comp.seq sp sk) i ∧
      Guard.img f (canon sp i) = canon (Guard.comp sp f) i :=
  ⟨Guard.imgK_canon sk i, Guard.img_canon f i⟩

/-- "Two facts about a state `τ` that `𝒦` reaches without commitment carry the
proofs.  First, every input `j ⪰ τ.cur` has a row in `τ` … Second, every
output at the current input is exposable (Proposition
`prop:exposure-boundary`)."  Lean: both hold at every run state
(`Guard.row_at`, `commonExpansion_exposable`); states reached without
commitment are run states (`Guard.isRun_sysExec_empty`). -/
theorem «app:composition/store-facts» {M O : Type} [PO M] [PO O] {sk : Spec M O}
    (hK : sk.LiftedMono) :
    (∀ τ : State sk, IsRun τ → ∀ j, τ.cur ≼ j → ∃ u, τ.R j u) ∧
    (∀ τ : State sk, IsRun τ → ∀ o, τ.R τ.cur o → Exposable τ o) ∧
    (∀ (σ τ : State sk) es, SysExec (fun _ => False) σ es τ → IsRun σ → IsRun τ) := by
  have hC := (liftedMono_iff_commonExpansion sk).1 hK
  exact ⟨fun _ hτ _ hj => Guard.row_at hC hτ hj, fun _ hτ _ ho => commonExpansion_exposable hC hτ ho,
    fun _ _ _ h hσ => Guard.isRun_sysExec_empty h hσ⟩

/-- The induction of the proof of Theorem `thm:guarded-runs`(2): "Before `𝒫`'s
first output we keep `ρ.cur = σ.cur` and `R_σ ⋈ K ⊆ R_ρ` … Afterwards we keep
`R_σ ⋈ T ⊆ R_ρ`, with `T` the store's table, and every row `(k,m)` of `R_σ`
has `m` above the store's current input. … so the join stays inside the
composite's table."  Lean: `Guard.Inv`; before the first output
`Guard.merge_inputs`, afterwards `Guard.merge_lockstep`; assembled in
`Guard.composite_run`.  The function case is `Guard.guarded_lockstep`. -/
theorem «app:composition/guarded-lockstep» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {sk : Spec M O} (hK : sk.LiftedMono) {B : Basis sp} {σ ρ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es ρ) :
    (Guard.emitted es = [] → ∀ ρ' : State (Comp.seq sp sk), Guard.Inv σ sk.S ρ' →
      ∃ ρ'', Exec ρ' (Guard.merge es []) ρ'' ∧ Guard.Inv ρ sk.S ρ'') ∧
    (∀ (ps : List (M × O)) (τK ρK : State sk) (esK : List (SEvent sk))
      (ρ' : State (Comp.seq sp sk)), Guard.emitted es = ps.map Prod.fst →
      SysExec (fun _ => False) τK esK ρK → esK.map SEvent.erase = Guard.storeTr ps → IsRun τK →
      (∀ k m, σ.R k m → τK.cur ≼ m) → Guard.Inv σ τK.R ρ' →
      ∃ ρ'', Exec ρ' (Guard.merge es (ps.map Prod.snd)) ρ'' ∧ Guard.Inv ρ ρK.R ρ'' ∧
        ∀ k m, ρ.R k m → ρK.cur ≼ m) :=
  ⟨fun he ρ' hI => Guard.merge_inputs h he ρ' hI,
    Guard.merge_lockstep ((liftedMono_iff_commonExpansion sk).1 hK) h⟩

/-- Proof of Theorem `thm:guarded-runs`(1) for a function store: "At a
canonical state `σ_𝒦(m_r)`, every row `(k,f(k))` has `m_r ≼ k`, so
`f(m_r) ≼ f(k)`.  Hence `output(f(m_r))` removes nothing, `f(m_r)` is
exposable, and the state stays canonical."  (Function case, kept from the
earlier version; the general proof is `Guard.follow`.) -/
theorem «app:composition/store-steps» {M O : Type} [PO M] [PO O] {f : M → O}
    (hf : Monotone f) (a : M) {b : M} (hab : a ≼ b) :
    Step (canon (graph f) a) (.output (f a)) (canon (graph f) a) ∧
      Exposable (canon (graph f) a) (f a) ∧
      Step (canon (graph f) a) (.input b) (canon (graph f) b) :=
  ⟨(Guard.store_out hf a).1, (Guard.store_out hf a).2,
    Dist.step_canon_input (graph f) hab ⟨f b, rfl⟩⟩

/-- The covering argument: "For a function store, the guarded composite's
commitments are covered by `𝒫`'s. … Let `Out_γ(m)` be legal at `σ`, let `γ` leave
`σ_c`, and let `ρ` be a composite state with `f(R_σ) ⊆ R_ρ`.  No row
`(k,f(m'))` with `(k,m') ∈ R_{σ_c}` is in `Sealed_{f(m)}` or `Rejected_{f(m)}`
at `ρ`. … So every row that the composite's canonical event for `f(m)`
removes by commitment has had every preimage in `R_σ` removed by `γ`."
Lean: `Guard.coverage` (stated for any `σ_c` at which `m` is exposable and any
`ρ` containing `f(R_{σ_c})`) and `Guard.coverage_step`. -/
theorem «app:composition/coverage» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {f : M → O} (hf : Monotone f) :
    (∀ {σc : State sp} {m : M}, Exposable σc m → ∀ {ρ : State (Guard.comp sp f)},
      (∀ k o, Guard.imgT f σc.R k o → ρ.R k o) →
      ∀ k x, Guard.imgT f σc.R k x → ¬ Sealed ρ (f m) k x ∧ ¬ Rejected ρ (f m) k x) ∧
    ∀ {B : Basis sp} {σ τ : State sp} {γ : List (Commitment sp)} {m : M},
      SysStep B σ (.output γ m) τ → ∀ {ρ : State (Guard.comp sp f)},
      (∀ k o, Guard.imgT f σ.R k o → ρ.R k o) →
      ∃ σc, ApplySeq γ σ σc ∧
        ∀ k x, (Sealed ρ (f m) k x ∨ Rejected ρ (f m) k x) →
          ∀ m', σ.R k m' → f m' = x → ¬ σc.R k m' :=
  ⟨fun he _ hs => Guard.coverage hf he hs, fun h _ hs => Guard.coverage_step hf h hs⟩

/-- Proof of Theorem `thm:proper-coordination`(1)–(2): "For a function store
with current input `m`, every row `(k,f(k))` has `m ≼ k`, so `f(m) ≼ f(k)` and
nothing is ruled out, at every state. … Either way `(k,u)` is a row of `𝒦(σ)`
that retires `(k,x)`, so `o` is exposable.  When `ℬ_𝒦` is empty, every output
event of the store is some `Out_ε(o)`, which removes no row by commitment, so
the store does not coordinate redundantly."  Lean: `Guard.store_exposable`,
`Guard.cf_stepK`, `Guard.noStore_atMostOnce`. -/
theorem «app:composition/store-exposable» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {sk : Spec M O} (hK : sk.LiftedMono) :
    (∀ (f : M → O), Monotone f → ∀ σ : State (graph f), Exposable σ (f σ.cur)) ∧
    (∀ {σ : State sp} {m : M}, Exposable σ m → ∀ {o}, sk.S m o → Exposable (Guard.imgK sk σ) o) ∧
    ∀ U : List M → Prop, Guard.AtMostOnce U (Guard.noStore sk) :=
  ⟨fun _ hf σ => Guard.store_exposable hf σ,
    fun he _ ho => Guard.cf_stepK ((liftedMono_iff_commonExpansion sk).1 hK) he ho,
    fun U => Guard.noStore_atMostOnce U sk⟩

/-- Proof of Theorem `thm:proper-coordination`(3): "The proof of
Proposition `prop:exposure-boundary` derives the common-expansion condition
from exposability at canonical states alone." -/
theorem «app:composition/canonical-states-suffice» {I O : Type} [PO I] [PO O] :
    ∀ {sp : Spec I O}, (∀ i o, sp.S i o → Exposable (canon sp i) o) → sp.CommonExpansion :=
  fun h => Guard.canon_exposable_commonExpansion h

/-- Proof of Corollary `cor:empty-store`: "(1) Let `σ` be a state of the store
and `σ'` a state reached without commitment, with the same current input and
`R_σ ⊆ R_σ'`. … Both start at `σ_𝒦(m)`, so the containment holds after each
event.  The replacement's strategy allows each erased event, since the
original's allowed it before erasure.  (2) Call a row `(k,x)` used when some
run of `𝒦` on outputs `𝒫` can emit emits `x` at input `k`. … We build the
original's run event by event, with the same erasure, and keep two facts: the
current inputs agree, and every used row of the replacement's table is in the
original's. … By at most once, `δ'` is not contradicted, so it removes no used
row, and both facts persist."  Lean: (1) `Guard.erase_lockstep` (here) and
`Guard.compliant_eraseSys`; (2) used rows are `Guard.EmitsAt`, and the
induction is `Guard.reflect_aux`; a prefix of a store trace ending at an
output is the trace on a prefix of its inputs (`Guard.storeTr_prefix`), and
every input is followed by an output (`Guard.storeTr_next`). -/
theorem «app:composition/empty-store» {M O : Type} [PO M] [PO O] {sk : Spec M O}
    (hK : sk.LiftedMono) {BK : Basis sk} {σ ρ : State sk}
    {es : List (SEvent sk)} (h : SysExec BK σ es ρ) (σ' : State sk) (hr : IsRun σ')
    (hc : σ'.cur = σ.cur) (hs : ∀ k u, σ.R k u → σ'.R k u) :
    ∃ ρ', SysExec (fun _ => False) σ' (es.map Guard.eraseC) ρ' ∧ IsRun ρ' ∧ ρ'.cur = ρ.cur ∧
      ∀ k u, ρ.R k u → ρ'.R k u :=
  Guard.erase_lockstep ((liftedMono_iff_commonExpansion sk).1 hK) h σ' hr hc hs

/-- Proof of Corollary `cor:pipelines`: "By Corollary `cor:empty-store`(1),
every guarded composite run has one with an empty-basis store and the same
trace.  Theorem `thm:guarded-runs`(2), applied to it and a prefix of the run of
`𝒮_1`, gives a run of `𝒮_2 ∘ 𝒮_1`, and the canonical event for each output
(Lemma `lem:canonical-commitment-normal-form`) makes it a run under the
canonical basis that emits the store's outputs. … By induction this holds for
every stage of the pipeline."  Lean: `Guard.grun_composite`,
`Guard.pipeline_step` (via `exec_canonExec`, `canonExec_sysExec`), and the
step `«cor:pipelines»`; a prefix of `𝒫`'s run emitting a prefix of its
outputs is `Guard.emitted_prefix`. -/
theorem «app:composition/pipelines» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {sk : Spec M O} (hK : sk.LiftedMono) {P : Guard.Sys sp} {K : Guard.Sys sk} {l' : List O}
    (h : Guard.GEmits P.emits K l') : (Guard.Sys.free (canonBasis (Comp.seq sp sk))).emits l' :=
  Guard.pipeline_step ((liftedMono_iff_commonExpansion sk).1 hK) h

/-- "For the mutex store …, let `𝒫` be the log specification of Example
`ex:committed-log-composition`, under its canonical basis with a strategy that
allows every event, and `𝒦` the table of any monotone function `f` of the log.
For a set `Q` of logs, removing every row whose input is in `Q` is a
commitment of `𝒦` at any state whose current input is not in `Q` and which has
such a row.  It removes whole fibers, so it seals. … At a state whose current
log is nonempty, every remaining log has the same first command, so this
commitment is undefined there.  Let the store's strategy take the lock at its
first event when the log is empty, and apply nothing otherwise. … So the
commitment is contradicted, and the store coordinates redundantly.  Its
replacement gains behaviour. … The locking store must take the lock at `[]`,
which seals `[b]`, so it cannot receive `[b]`.  Let the strategy instead take
the lock only when its current log is nonempty.  The lock is undefined there,
so every output event the store performs is some `Out_ε(x)`.  The store
applies no commitment, so it does not coordinate redundantly.  Its strategy
depends only on the inputs it has received and always offers `Out_ε(x)`, so it
meets the hypotheses of Corollary `cor:empty-store`(2).  A strategy that
insists on the lock at a nonempty log also applies no commitment and ignores
commitments, but it stalls.  When `𝒫` emits `[b]` first, the store never
emits, while its replacement emits `f([b])`."  Lean: `Guard.sealIn Q` (for
any specification); `Guard.lock_after_log`; the early-lock runs are those of
`Guard.mutex_redundant` and `Guard.early_lock_strict`; the late lock is
`Guard.lateLock_eps` and `Guard.late_lock_proper`; the stalling lock is
`Guard.stall_lock`. -/
theorem «app:composition/mutex-store» {I' Cmd O : Type} [PO I'] [PO O] {f : Inst.Pfx Cmd → O}
    (hf : Monotone f) (b : Cmd) :
    (∀ (Q : Inst.Pfx Cmd → Prop) (σ τ : State (graph f)), (Guard.sealIn Q).app σ = some τ →
      ¬ Q σ.cur ∧ (∃ k x, σ.R k x ∧ Q k) ∧ ∀ k, Q k → ∀ x, ¬ τ.R k x) ∧
    (∀ σ : State (graph f), σ.cur.l ≠ [] → (Guard.sealIn (Guard.bFirst b)).app σ = none) ∧
    Guard.Redundant (Guard.Sys.free (canonBasis (Inst.smrS1 (Cmd := Cmd)))).emits
      (Guard.earlyLock b f) ∧
    (∀ m esK ρ, Guard.Produces (Guard.lateLock b f) m esK ρ →
      ∀ γ x, SEvent.output γ x ∈ esK → γ = []) ∧
    ∀ (sq : Spec I' (Inst.Pfx Cmd)) (P : Guard.Sys sq),
      Guard.Blind (Guard.lateLock b f) ∧ Guard.Live (Guard.lateLock b f) ∧
      ∀ l m tr, Guard.Obs P.emits (Guard.lateLock b f) l m tr ↔
        Guard.Obs P.emits (Guard.eraseSys (Guard.lateLock b f)) l m tr := by
  refine ⟨fun Q σ τ h => ?_, Guard.lock_after_log b, (Guard.mutex_redundant hf b).2.1,
    fun _ _ _ h => Guard.lateLock_eps b h, fun _ P => (Guard.late_lock_proper hf b P).2⟩
  obtain ⟨hn, hex, rfl⟩ := Guard.sealInApp_eq.1 h
  exact ⟨hn, hex, fun _ hQ _ hx => hx.2 hQ⟩

/-- "For the per-key store …, let `𝒫` have one input with fiber
`{[a,b],[b,a]}`, and let `f` send a log to the family of its subsequences on
each key.  The two logs are incomparable with no common refinement, so `[a,b]`
is not exposable.  When `a` and `b` are on different keys,
`f([a,b]) = f([b,a])`, the composite has one row, and `f([a,b])` is exposable." -/
theorem «app:composition/per-key» {Cmd K : Type} [DecidableEq K] (key : Cmd → K)
    {a b : Cmd} (hk : key a ≠ key b) :
    Guard.perKey key ⟨[a, b]⟩ = Guard.perKey key ⟨[b, a]⟩ ∧
      ¬ Exposable (canon (Guard.abSpec a b) Comp.Pt.pt) ⟨[a, b]⟩ ∧
      Exposable (canon (Guard.comp (Guard.abSpec a b) (Guard.perKey key)) Comp.Pt.pt)
        (Guard.perKey key ⟨[a, b]⟩) :=
  ⟨Guard.perKey_swap key hk, Guard.commute_example key hk⟩

/-- "The commitments of `𝒫` do not themselves push forward.  Let `𝒫` have one
input with fiber `{x,y}`, `x` and `y` incomparable, and `f(x) = lo ≼ hi = f(y)`.
The choice `c_y` removes `x` and keeps `y`.  Its image would remove `lo` and
keep `hi`, violating Equation `eq:commitment-excludes`, so no commitment of the
composite has that effect.  In the composite, `hi` is exposable at the
canonical state, since it retires `lo`." -/
theorem «app:composition/no-pushforward» :
    (∃ τ, (choiceC Comp.Two.y).app (canon Comp.anyS Comp.Pt.pt) = some τ ∧
      ∀ c : Commitment (Guard.comp Comp.anyS Guard.fLvl),
        c.app (Guard.img Guard.fLvl (canon Comp.anyS Comp.Pt.pt)) ≠ some (Guard.img Guard.fLvl τ)) ∧
    Exposable (canon (Guard.comp Comp.anyS Guard.fLvl) Comp.Pt.pt) Guard.Lvl.hi :=
  ⟨Guard.push_not_commitment, Guard.choice_becomes_retirement.2⟩

/-- "Monotonicity of `f` is needed.  Let `𝒫` be the table of the identity on
`M`, which needs no commitment.  For `m ≼ m'`, its run `output(m)`,
`input(m')`, `output(m')` maps to a run of the composite exactly when
`f(m) ≼ f(m')`." -/
theorem «app:composition/monotone-needed» {M O : Type} [PO M] [PO O] (f : M → O) {m m' : M}
    (hmm : m ≼ m') :
    ExecCF (canon (graph fun x : M => x) m) [.output m, .input m', .output m']
        (canon (graph fun x : M => x) m') ∧
      ((∃ ρ, Exec (canon (Guard.comp (graph fun x : M => x) f) m)
          [.output (f m), .input m', .output (f m')] ρ) ↔ f m ≼ f m') :=
  ⟨Guard.identity_cf hmm, Guard.monotone_necessary f hmm⟩

/-- "A store that must itself choose cannot delegate the choice either.  If
`𝒫` is the identity on one input, it admits no commitment at all.  If the
store relates that input to two incomparable outputs, every output event of
the composite at its canonical state applies a commitment, and that commitment
is the store's." -/
theorem «app:composition/store-choice» :
    (∀ (c : Commitment (graph fun x : Dist.U1 => x)) σ τ, c.app σ ≠ some τ) ∧
    ∀ (B : Basis (Comp.seq (graph fun x : Dist.U1 => x) Dist.spU)) γ o τ,
      SysStep B (canon _ ()) (.output γ o) τ → γ ≠ [] :=
  Guard.store_choice_not_delegable

/-- **Example `ex:bare-reads`** (Bare reads), position-tagged responses, for
any deterministic state machine `δ`, read function `rd`, and two distinct
commands: "As in Example `ex:committed-log-composition`, `F` and `G ⋆ F` are
non-monotone. … A longer log never contradicts such a response, so `G` is
monotone.  By Complete CALM and the exposure boundary, every output of `G` at
every state reachable without commitment is exposable, so bare reads need no
commitment of their own."  Lean: `I = B = Inst.Pfx Cmd`, `A = Comp.Pt`,
`J = Inst.Pfx Rd`; `logF`, `bareG δ rd σ₀`, whose outputs pair the executed
response log with a set (`Inst.Facts`) of tagged responses `(r, n, v)`, `v` the
value `rd` gives after the first `n ≤ |b|` entries.  "Responses are facts, so
a set of them may answer one read more than once." -/
theorem «ex:bare-reads» {Cmd Stt R Rd V : Type} (δ : Stt → Cmd → Stt × R) (rd : Stt → Rd → V)
    (σ0 : Stt) {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) :
    ¬ (Inst.logF (Cmd := Cmd)).LiftedMono ∧
      ¬ (Comp.par Inst.logF (Inst.bareG δ rd σ0)).LiftedMono ∧ (Inst.bareG δ rd σ0).LiftedMono ∧
      ∀ τ : State (Inst.bareG δ rd σ0), ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  Inst.bare_read_example δ rd σ0 hne

/-- Inside Example `ex:bare-reads`: "Suppose instead that the specification
demands the latest value, so that a read of `x` must return the value of `x`
after all of `b`.  Then a bare read can be contradicted by an entry it has not
seen, and `G` is not monotone.  By the exposure boundary some output of `G`
then needs a commitment of the store's own."  Lean: `latestG δ rd σ₀`
(untagged responses `(r, v)`, `v` the value after all of `b`); "an entry it has
not seen" is a command `c` that changes what read `r` returns. -/
theorem «ex:bare-reads/latest-value» {Cmd Stt R Rd V : Type} (δ : Stt → Cmd → Stt × R)
    (rd : Stt → Rd → V) (σ0 : Stt) {c : Cmd} {r : Rd} (hc : rd (δ σ0 c).1 r ≠ rd σ0 r) :
    ¬ (Inst.latestG δ rd σ0).LiftedMono ∧
      ∃ τ : State (Inst.latestG δ rd σ0), ReachableCF τ ∧ ∃ o, τ.R τ.cur o ∧ ¬ Exposable τ o :=
  ⟨Inst.latestG_not_liftedMono δ rd σ0 hc, Inst.latest_needs_store_commitment δ rd σ0 hc⟩

end Paper
end CC
