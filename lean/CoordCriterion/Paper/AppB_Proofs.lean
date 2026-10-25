import CoordCriterion.CALM.Examples

/-!
# Paper Appendix B: deferred proofs for §2–§3 (`appendices/proof-machinery.tex`)

Statement layer for Appendix `app:proofs`, except subsection
`app:iconfluence` (invariant confluence, handled with §6).

How to read this file: open `appendices/proof-machinery.tex` next to it.  The
headers are the appendix's subsections, in order.  For each "Proof of …"
paragraph there is a declaration `«proof:<label>»` whose statement is the
result proved, or the key step of the written proof, and whose Lean proof
follows the same route; the result itself is stated in
`Paper/S2_FunctionalCALM.lean` / `Paper/S3_CompleteCALM.lean`.  Lemma
`lem:reconciliation` is stated here, by its label.

Conventions as in `Paper/S2_FunctionalCALM.lean`.  A run with its witness is
`CALM.RunW sp` (start input, event list, final state, execution);
`CALM.emittedAll fam` lists the outputs emitted on any run of `fam`.
-/

namespace CC.Paper

open CC CC.CALM

/-! ## Proofs for Section 2 -/

/-- Proof of Lemma `lem:run-residual`: "Each input event `input(j)` keeps only
the rows with `in ⪰ j` …, and each output event `output(o)` keeps only the
rows with `out ⪰ o`. … One output condition remains for each emitted
output."  The inductive step: one event preserves the residual shape,
appending its output (if any) to the emitted list. -/
theorem «proof:lem:run-residual» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    {σ τ : State sp} {e : Event I O} {E : List O}
    (hσ : ∀ k u, σ.R k u ↔ (sp.S k u ∧ σ.cur ≼ k ∧ ∀ o ∈ E, o ≼ u)) (hs : Step σ e τ) :
    ∀ k u, τ.R k u ↔ (sp.S k u ∧ τ.cur ≼ k ∧ ∀ o ∈ E ++ outs [e], o ≼ u) :=
  residual_step hσ hs

/-- Proof of Prop. `prop:confluence`: "A common state with current input `j`
has a row at `j`, and since rows are never added, that row belongs to every
`R_r`.  Conversely … After `input(j)` and `output(u)`, the same lemma leaves
exactly `S[in ⪰ j, out ⪰ u]`, independent of the starting run."  The two
steps: events only remove rows; and the explicit continuation to
`meetState sp j u _ = (j, S[in ⪰ j, out ⪰ u])`. -/
theorem «proof:prop:confluence» {I O : Type} [PO I] [PO O] {sp : Spec I O} :
    (∀ {σ τ : State sp}, Reach σ τ → ∀ k u, τ.R k u → σ.R k u) ∧
      (∀ {σ : State sp}, IsRun σ → ∀ {j : I} {u : O} (hju : σ.R j u),
        Exec σ [.input j, .output u] (meetState sp j u (σ.sub _ _ hju))) :=
  ⟨reach_sub, fun h _ _ hju => survivor_exec h hju⟩

/-- Proof of Thm. `thm:functional-calm`: "By Prop. `prop:confluence`, a finite
family of runs is therefore confluent at a common expansion `j` exactly when
`f(j)` refines every output emitted on any of them.  If `f` is monotone, this
holds … If `f` is not monotone, some `i ≼ k` has `f(i) ⋠ f(k)`.  Of two runs
from `σ_S(i)`, one that emits `f(i)` no longer has the row `(k,f(k))`, while
one that accepts `input(k)` keeps it; no row at `k` survives in both, so they
are not confluent at `k`."  The theorem, along the library route. -/
theorem «proof:thm:functional-calm» {I O : Type} [PO I] [PO O] (sp : Spec I O)
    (hf : sp.Functional) : sp.Consistent ↔ sp.MonotoneF :=
  functional_calm hf

/-- Proof of Cor. `cor:state-by-input`: "By Functional CALM …, the
specification is monotone. … monotonicity gives `o_ℓ ≼ f(k)`, and the output
conditions remove nothing."  The key step: in a monotone specification every
run state is canonical. -/
theorem «proof:cor:state-by-input» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hm : sp.MonotoneF) {τ : State sp} (hτ : IsRun τ) : τ = canon sp τ.cur :=
  run_canon_of_mono hm hτ

/-- Proof of Prop. `prop:functional-exposure-boundary`: monotone ⇒ every
output at a state reachable without commitment is exposable (via
Cor. `cor:state-by-input`); conversely, exposability at `σ_S(i)`, reached by
the empty run, is monotonicity. -/
theorem «proof:prop:functional-exposure-boundary» {I O : Type} [PO I] [PO O]
    (sp : Spec I O) (hf : sp.Functional) :
    sp.MonotoneF ↔ ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  functional_exposure_boundary hf

/-! ## Proofs for Section 3 -/

/-- Proof of Prop. `prop:common-expansion-form`: "Suppose Lifted
Monotonicity … Relational Monotonicity gives, for each `r`, a `u_r ∈ S(j)`
with `o_r ≼ u_r`.  The `u_r` all lie in the one fiber `S(j)`, which is
directed, so some `u ∈ S(j)` refines every `u_r`, hence every `o_r`.
Conversely, … the rows `{(i,x) : x ∈ X}` have common expansion `j`, so some
`u ∈ S(j)` refines all of `X`."  Both directions. -/
theorem «proof:prop:common-expansion-form» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.LiftedMono ↔ sp.CommonExpansion :=
  liftedMono_iff_commonExpansion sp

/-- **Lemma `lem:reconciliation`** (Reconciliation).  "Let runs end at
`(i_r,R_r)`, `r = 1,…,m`, let `j` be a common expansion of the `i_r`, and let
`E` be the set of outputs emitted on any of them.  The runs are confluent at
`j` if and only if some `u ∈ S(j)` refines every output in `E`."

Lean: the runs are a list `fam` of runs with their events, `E` is
`emittedAll fam`. -/
theorem «lem:reconciliation» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (fam : List (RunW sp)) (j : I) (hj : ∀ r ∈ fam, r.fin.cur ≼ j) :
    ConfluentAt (fam.map RunW.fin) j ↔ ∃ u, sp.S j u ∧ ∀ o ∈ emittedAll fam, o ≼ u :=
  reconciliation fam j hj

/-- Lemma `lem:reconciliation` quantifies over runs with their events;
Def. `def:consistency` over run end states.  The two readings of consistency
agree. -/
theorem «lem:reconciliation/consistency-over-runs» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} :
    sp.Consistent ↔ ∀ fam : List (RunW sp), ∀ j : I,
      (∀ r ∈ fam, r.fin.cur ≼ j) → ConfluentAt (fam.map RunW.fin) j :=
  consistent_iff_runs

/-- Proof of Thm. `thm:complete-calm`, (⇐): "Each output `o` emitted on a run
was emitted at some input `i_o ≼ j`, so `(i_o,o)` is a row of `S`; the
condition supplies `u ∈ S(j)` refining all of them, and
Lemma `lem:reconciliation` gives confluence." -/
theorem «proof:thm:complete-calm/if» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hC : sp.CommonExpansion) : sp.Consistent :=
  consistent_of_ce_paper hC

/-- Proof of Thm. `thm:complete-calm`, (⇒): "Given rows `(i_r,o_r)` with
common expansion `j`, apply consistency and Lemma `lem:reconciliation` to the
runs that start at `σ_S(i_r)` and emit `o_r`; for the empty family, totality
gives `S(j) ≠ ∅`."  (Lean needs no separate empty case: consistency of the
empty family and the lemma already give `S(j) ≠ ∅`.) -/
theorem «proof:thm:complete-calm/only-if» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hc : sp.Consistent) : sp.CommonExpansion :=
  ce_of_consistent_paper hc

/-- Proof of Thm. `thm:complete-calm`, assembled along the paper's route
(both forms, via Prop. `prop:common-expansion-form`). -/
theorem «proof:thm:complete-calm» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    (sp.Consistent ↔ sp.CommonExpansion) ∧ (sp.Consistent ↔ sp.LiftedMono) :=
  ⟨complete_calm_paper sp, complete_calm_paper_lm sp⟩

/-- Proof of Prop. `prop:exposure-boundary`, (⇒): "Let `(i,R)` be reached by a
run (commitment-free or not) … Extend the run in two ways: by `output(o)`,
and by `input(j)` followed by `output(x)`.  By consistency the two extended
runs are confluent at `j` … the exposure test makes `o` exposable."  Stated,
as in the proof, at every run state. -/
theorem «proof:prop:exposure-boundary/only-if» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hc : sp.Consistent) {τ : State sp} (hτ : IsRun τ) {o : O} (ho : τ.R τ.cur o) :
    Exposable τ o :=
  exposable_of_consistent hc hτ ho

/-- Proof of Prop. `prop:exposure-boundary`, both directions; the converse is
the paper's: "By totality pick `u₀ ∈ S(j)`.  For `r = 1,…,k` in turn, the
exposure test for `o_r` at `σ_S(i_r)`, applied with `x = u_{r-1}`, gives
`u_r ∈ S(j)` refining both `o_r` and `u_{r-1}`." -/
theorem «proof:prop:exposure-boundary» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.CommonExpansion ↔
      ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  exposure_boundary_paper sp

/-! ### Pairs suffice for the common-expansion condition (`app:pairs-suffice`) -/

/-- `app:pairs-suffice`: "If every two rows with a common expansion `j` have a
common refinement in `S(j)`, the condition holds for every finite family:
replace the first two rows by a row `(j,u)` at `j` and repeat; a single row is
paired with any row at `j`."  `CALM.Pairs sp` is the pair condition over all
rows of `S`; it is equivalent to the common-expansion condition. -/
theorem «app:pairs-suffice» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    (∀ i₁ o₁ i₂ o₂ j, sp.S i₁ o₁ → sp.S i₂ o₂ → i₁ ≼ j → i₂ ≼ j →
        ∃ u, sp.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u) ↔ sp.CommonExpansion :=
  pairs_iff_commonExpansion sp

/-- `app:pairs-suffice`: "The pairs must range over all rows of `S`, including
those at `j`."  On a four-input specification, every two rows at inputs other
than the common expansion are compatible there, but the common-expansion
condition fails. -/
theorem «app:pairs-suffice/rows-at-j» :
    (∀ i₁ o₁ i₂ o₂ j, i₁ ≠ j → i₂ ≠ j → spec4.S i₁ o₁ → spec4.S i₂ o₂ → i₁ ≼ j → i₂ ≼ j →
        ∃ u, spec4.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u) ∧ ¬ spec4.CommonExpansion :=
  rowsAtJ_needed

/-- `app:pairs-suffice`: "Restricting the families to rows at single-proposal
inputs does not suffice, even `k` rows at a time: in the `k`-set agreement
example …, every family of at most `k` rows at such inputs is compatible at
each common expansion, but the `k+1` proposal rows are not."

Lean: `k`-set agreement with participants and values `Fin (k+1)`
(`CALM.KSet.spec k`, one instance suffices for the counterexample), `k ≥ 1`.
A row at a single-proposal input `{(p,v)}` is a triple `(p, v, o)`. -/
theorem «app:pairs-suffice/k-at-a-time» (k : Nat) (hk : 1 ≤ k) :
    (∀ (rows : List (Fin (k+1) × Fin (k+1) × PMap (k+1))), rows.length ≤ k →
        (∀ r ∈ rows, (KSet.spec k).S (KSet.atom r.1 r.2.1) r.2.2) →
        ∀ j : PMap (k+1), (∀ r ∈ rows, KSet.atom r.1 r.2.1 ≼ j) →
          ∃ u, (KSet.spec k).S j u ∧ ∀ r ∈ rows, r.2.2 ≼ u) ∧
      (∀ r : Fin (k+1), (KSet.spec k).S (KSet.atom r r) (KSet.atom r r) ∧
        KSet.atom r r ≼ KSet.J (k+1)) ∧
      ¬ ∃ u, (KSet.spec k).S (KSet.J (k+1)) u ∧ ∀ r : Fin (k+1), KSet.atom r r ≼ u :=
  ⟨KSet.atomic_k_at_a_time k, fun r => ⟨KSet.proposal_row k hk r, KSet.J_common k r⟩,
   KSet.not_all_compatible k⟩

/-- Consequence for `app:pairs-suffice`: the `k`-set agreement specification
fails the common-expansion condition, hence is not monotone. -/
theorem «app:pairs-suffice/k-set-not-monotone» (k : Nat) (hk : 1 ≤ k) :
    ¬ (KSet.spec k).CommonExpansion ∧ ¬ (KSet.spec k).LiftedMono :=
  ⟨KSet.not_commonExpansion k hk, KSet.not_liftedMono k hk⟩

end CC.Paper
