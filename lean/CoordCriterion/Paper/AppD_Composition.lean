import CoordCriterion.Appendix.Guarded

/-!
# Paper App. D, "Proofs and Details for Composition" (`appendices/composition.tex`)

Statement layer for Appendix `app:composition`.  The results it proves are
stated in Section `sec:composition` and recorded in
`Paper/S5_Composition.lean`; this file holds what appears only in the
appendix: composition with independent inputs and its curried evaluation, the
component-commitment example, the covering argument and the counterexamples of
the Irredundant Coordination subsection, and Example `ex:bare-reads`.
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

/-! ## Irredundant Coordination -/

/-- "The image of the canonical state `σ_𝒫(i)` is the canonical state of
`𝒦 ∘ 𝒫` at `i`." -/
theorem «app:composition/image-canon» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    (f : M → O) (i : I) : Guard.img f (canon sp i) = canon (Guard.comp sp f) i :=
  Guard.img_canon f i

/-- The induction of the proof of Theorem `thm:guarded-runs`(1): "if a state
`σ` of `𝒫` and a state `ρ` of the composite have the same current input and
`f(R_σ) ⊆ R_ρ`, the next event of `𝒫` has a matching event of the composite
that preserves both facts." -/
theorem «app:composition/guarded-lockstep» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {f : M → O} (hf : Monotone f) {B : Basis sp} {σ ρ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es ρ) (σ' : State (Guard.comp sp f)) (hc : σ'.cur = σ.cur)
    (hs : ∀ k o, Guard.imgT f σ.R k o → σ'.R k o) :
    ∃ ρ', Exec σ' (es.map (Guard.obs f)) ρ' ∧ ρ'.cur = ρ.cur ∧
      ∀ k o, Guard.imgT f ρ.R k o → ρ'.R k o :=
  Guard.guarded_lockstep hf h σ' hc hs

/-- Proof of Theorem `thm:guarded-runs`(2): "At a canonical state `σ_𝒦(m_r)`,
every row `(k,f(k))` has `m_r ≼ k`, so `f(m_r) ≼ f(k)`.  Hence
`output(f(m_r))` removes nothing, `f(m_r)` is exposable, and the state stays
canonical.  The input event `input(m_{r+1})` moves to `σ_𝒦(m_{r+1})`." -/
theorem «app:composition/store-steps» {M O : Type} [PO M] [PO O] {f : M → O}
    (hf : Monotone f) (a : M) {b : M} (hab : a ≼ b) :
    Step (canon (graph f) a) (.output (f a)) (canon (graph f) a) ∧
      Exposable (canon (graph f) a) (f a) ∧
      Step (canon (graph f) a) (.input b) (canon (graph f) b) :=
  ⟨(Guard.store_out hf a).1, (Guard.store_out hf a).2,
    Dist.step_canon_input (graph f) hab ⟨f b, rfl⟩⟩

/-- The covering argument: "Let `Out_γ(m)` be legal at `σ`, let `γ` leave
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

/-- Proof of Theorem `thm:irredundant-coordination`(1)–(2): "Let `(m,R)` be a
state of `𝒦`.  Its fiber at `m` is `{f(m)}`, and every row `(k,f(k)) ∈ R` has
`m ≼ k`, so `f(m) ≼ f(k)` by monotonicity.  No row is ruled out by `f(m)`, so
`f(m)` is exposable. … When `ℬ_𝒦` is empty, every output event of the store is
some `Out_ε(f(m))`, which removes no row by commitment, so the store does not
coordinate redundantly." -/
theorem «app:composition/store-exposable» {I M O : Type} [PO I] [PO M] [PO O] {sp : Spec I M}
    {f : M → O} (hf : Monotone f) :
    (∀ σ : State (graph f), Exposable σ (f σ.cur)) ∧
      ∀ B : Basis sp, Guard.AtMostOnce B (Guard.noStore f) :=
  ⟨Guard.store_exposable hf, fun B => Guard.noStore_atMostOnce B f⟩

/-- Proof of Theorem `thm:irredundant-coordination`(3): "The proof of
Proposition `prop:exposure-boundary` derives the common-expansion condition
from exposability at canonical states alone"; and the at-least-once step of
(2): if `m` is exposable at `σ`, then `f(m)` is exposable at `f(σ)`. -/
theorem «app:composition/canonical-states-suffice» {I M O : Type} [PO I] [PO M] [PO O] :
    (∀ {sp : Spec I O}, (∀ i o, sp.S i o → Exposable (canon sp i) o) → sp.CommonExpansion) ∧
    ∀ {sp : Spec I M} {f : M → O}, Monotone f → ∀ {σ : State sp} {m : M},
      Exposable σ m → Exposable (Guard.img f σ) (f m) :=
  ⟨fun h => Guard.canon_exposable_commonExpansion h, fun hf _ _ he => Guard.cf_step hf he⟩

/-- "For the mutex store …, let `𝒫` be the log specification of Example
`ex:committed-log-composition` under its canonical basis, and `f` any monotone
function of the log.  For a set `Q` of logs, removing every row whose input is
in `Q` is a commitment of `𝒦` at any state whose current input is not in `Q`
and which has such a row.  It removes whole fibers, so it seals. … At a
state whose current log is nonempty, every remaining log has the same first
command, so this commitment is undefined there. … So the commitment is
contradicted, and the store coordinates redundantly."  Lean: `Guard.sealIn Q`
(for any specification); `Guard.lock_after_log`; the runs are those of
`Guard.mutex_redundant`. -/
theorem «app:composition/mutex-store» {Cmd O : Type} [PO O] {f : Inst.Pfx Cmd → O}
    (hf : Monotone f) (b : Cmd) :
    (∀ (Q : Inst.Pfx Cmd → Prop) (σ τ : State (graph f)), (Guard.sealIn Q).app σ = some τ →
      ¬ Q σ.cur ∧ (∃ k x, σ.R k x ∧ Q k) ∧ ∀ k, Q k → ∀ x, ¬ τ.R k x) ∧
    (∀ σ : State (graph f), σ.cur.l ≠ [] → (Guard.sealIn (Guard.bFirst b)).app σ = none) ∧
    Guard.Redundant (canonBasis (Inst.smrS1 (Cmd := Cmd))) (Guard.mutexB b f) := by
  refine ⟨fun Q σ τ h => ?_, Guard.lock_after_log b, (Guard.mutex_redundant hf b).2.1⟩
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
