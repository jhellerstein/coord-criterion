import CoordCriterion.CALM.Examples
import CoordCriterion.CompleteCALM.Legality

/-!
# Paper Appendices B and C: proofs for §2–§3 (`appendices/functional-calm.tex`, `appendices/complete-calm.tex`)

Statement layer for Appendices `app:proofs-sec2` and `app:proofs-sec3` (the
proofs; invariant confluence, `app:iconfluence`, is handled with §6).

How to read this file: open `appendices/functional-calm.tex` and `appendices/complete-calm.tex` next to it.  The
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
    (hσ : ∀ k u, σ.R k u ↔ (sp.P k u ∧ σ.cur ≼ k ∧ ∀ o ∈ E, o ≼ u)) (hs : Step σ e τ) :
    ∀ k u, τ.R k u ↔ (sp.P k u ∧ τ.cur ≼ k ∧ ∀ o ∈ E ++ outs [e], o ≼ u) :=
  residual_step hσ hs

/-- Proof of Prop. `prop:confluence`: "First assume the runs are confluent at
`j`.  The common state has a row at `j`, and since rows are never added, that
row belongs to every `R_r`.  Now assume `(j,u)` belongs to every `R_r`. … so
after `input(j)` and `output(u)` the same lemma leaves exactly
`P[in ⪰ j, out ⪰ u]`, independent of the starting run."  The two
steps: events only remove rows; and the explicit continuation to
`meetState sp j u _ = (j, P[in ⪰ j, out ⪰ u])`. -/
theorem «proof:prop:confluence» {I O : Type} [PO I] [PO O] {sp : Spec I O} :
    (∀ {σ τ : State sp}, Reach σ τ → ∀ k u, τ.R k u → σ.R k u) ∧
      (∀ {σ : State sp}, IsRun σ → ∀ {j : I} {u : O} (hju : σ.R j u),
        Exec σ [.input j, .output u] (meetState sp j u (σ.sub _ _ hju))) :=
  ⟨reach_sub, fun h _ _ hju => survivor_exec h hju⟩

/-- Proof of Lemma `lem:confluence-legality`.  "We use legality in a form that
covers both functional and nondeterministic specs: `o` is legal at `(i,R)`
when, for every row `(k,x) ∈ R`, some `u ∈ R(k)` extends both `o` and `x`. …
An output event `output(o)` from `(i,R)` applies a commitment exactly when `o`
is not legal at `(i,R)`, so the lemma's condition says that every output a run
can emit is legal at the state where it is emitted."
(⇒) "First assume the runs are consistent, and suppose, for contradiction,
that an output event of some run applies a commitment.  The run ends at
`(i,R)` before that event, and `o ∈ R(i)` is not legal there, so some
`(k,x) ∈ R` has no `u ∈ R(k)` extending both `o` and `x`.  We extend the
run in two ways: by `output(o)`, and by `input(k)` followed by `output(x)` …
By Proposition `prop:confluence`, the two runs are not confluent at `k`,
contradicting consistency."
(⇐) "Now assume no output event applies a commitment, so every output that a run
can emit is legal … Each `R_r` keeps a row at its current input, say `(i_r,u_r)` … `u_r` is
legal [at `σ_P(i_r)`].  By totality there is some `v₀ ∈ P(j)`.  For
`r = 1,…,m` in turn, `(j,v_{r-1})` is a row of `σ_P(i_r)` … so legality of
`u_r` gives `v_r ∈ P(j)` extending both `u_r` and `v_{r-1}`. … Proposition
`prop:confluence` gives confluence at `j`."

Lean: `Exposable σ o` is this form of legality.  The first conjunct is (⇒) at
every run state (`exposable_of_consistent`); the second is (⇐)
(`consistent_iff_runsLegal`, whose proof builds the common extension from
legality at canonical states, `exposure_boundary`, and applies the survivor
test, `commonExpansion_consistent`). -/
theorem «proof:lem:confluence-legality» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    (sp.Consistent → ∀ τ : State sp, IsRun τ → ∀ o, τ.R τ.cur o → Exposable τ o) ∧
      (sp.RunsLegal → sp.Consistent) :=
  ⟨fun hc _ hτ _ ho => exposable_of_consistent hc hτ ho, (consistent_iff_runsLegal sp).2⟩

/-- Proof of Cor. `cor:state-by-input`: "By Lemma `lem:run-residual`, the run's
remainder table is `P[in ⪰ i, out ⪰ o₁, …, out ⪰ o_m]` … monotonicity gives
`o_ℓ ≼ f(k)`, and the output conditions remove nothing."  The key step: in a
monotone specification every run state is canonical. -/
theorem «proof:cor:state-by-input» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hm : sp.MonotoneF) {τ : State sp} (hτ : IsRun τ) : τ = canon sp τ.cur :=
  run_canon_of_mono hm hτ

/-- Proof of Prop. `prop:functional-exposure-boundary`: monotone ⇒ every
output at a state reachable without commitment is a legal output (via
Cor. `cor:state-by-input`); conversely, legality at `σ_P(i)`, reached by
the empty run, is monotonicity. -/
theorem «proof:prop:functional-exposure-boundary» {I O : Type} [PO I] [PO O]
    (sp : Spec I O) (hf : sp.Functional) :
    sp.MonotoneF ↔ ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  functional_exposure_boundary hf

/-- Proof of Thm. `thm:functional-calm`: "By Lemma `lem:confluence-legality`,
the runs are consistent exactly when no output event of a run applies a
commitment, that is, when every output that a run can emit is legal.  This
condition is equivalent to legality at every state reachable
without commitment. … assume every output at every state reachable without
commitment is legal.  By induction along any run, each of its output events is
then legal, so the run is commitment-free, every state it reaches is reachable
without commitment, and every output it can emit is legal.  By Proposition
`prop:functional-exposure-boundary`, legality at every state reachable without
commitment holds exactly when `f` is monotone."  The first conjunct is the
bridge (`runsLegal_iff_legalReachLegal`, by induction along the run,
`reachableCF_of_exec`); the second is the theorem along this route. -/
theorem «proof:thm:functional-calm» {I O : Type} [PO I] [PO O] (sp : Spec I O)
    (hf : sp.Functional) :
    (sp.RunsLegal ↔ sp.LegalReachLegal) ∧ (sp.Consistent ↔ sp.MonotoneF) :=
  ⟨runsLegal_iff_legalReachLegal sp, functional_calm_via_legality hf⟩

/-! ## Proofs for Section 3 -/

/-- Proof of Prop. `prop:common-expansion-form`: "First assume Lifted
Monotonicity … Relational Monotonicity gives, for each `r`, a `u_r ∈ P(j)`
with `o_r ≼ u_r`.  The `u_r` all lie in the one fiber `P(j)`, which is
directed, so some `u ∈ P(j)` extends every `u_r`, hence every `o_r`.
Now assume the common-extension condition, … the rows `{(i,x) : x ∈ X}` have common input extension `j`, so some
`u ∈ P(j)` extends all of `X`."  Both directions. -/
theorem «proof:prop:common-expansion-form» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.LiftedMono ↔ sp.CommonExpansion :=
  liftedMono_iff_commonExpansion sp

/-- **Lemma `lem:reconciliation`** (Reconciliation).  "Let runs end at
`(i_r,R_r)`, `r = 1,…,m`, let `j` be a common input extension of the `i_r`, and let
`X` be the set of outputs emitted on any of them.  The runs are confluent at
`j` if and only if some `u ∈ P(j)` extends every output in `X`."

Lean: the runs are a list `fam` of runs with their events, `X` is
`emittedAll fam`. -/
theorem «lem:reconciliation» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (fam : List (RunW sp)) (j : I) (hj : ∀ r ∈ fam, r.fin.cur ≼ j) :
    ConfluentAt (fam.map RunW.fin) j ↔ ∃ u, sp.P j u ∧ ∀ o ∈ emittedAll fam, o ≼ u :=
  reconciliation fam j hj

/-- Lemma `lem:reconciliation` quantifies over runs with their events;
Def. `def:consistency` over run end states.  The two readings of consistency
agree. -/
theorem «lem:reconciliation/consistency-over-runs» {I O : Type} [PO I] [PO O]
    {sp : Spec I O} :
    sp.Consistent ↔ ∀ fam : List (RunW sp), ∀ j : I,
      (∀ r ∈ fam, r.fin.cur ≼ j) → ConfluentAt (fam.map RunW.fin) j :=
  consistent_iff_runs

/-- Proof of Prop. `prop:exposure-boundary`, (⇒): "First assume it holds.  Let
`(i,R)` be reached by a run (commitment-free or not), and let `o ∈ R(i)`,
`j ⪰ i` legal, and `x ∈ R(j)`.  The rows `(i,o)` and `(j,x)` of `P` have common
input extension `j`, so the condition supplies `u ∈ P(j)` extending both `o`
and `x`.  By Lemma `lem:run-residual`, `(j,u) ∈ R` … and the legal-output test
makes `o` a legal output."  Stated, as in the proof, at every run state; it
uses the rows-remaining lemma (`run_survive`), not consistency. -/
theorem «proof:prop:exposure-boundary/only-if» {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hC : sp.CommonExpansion) {τ : State sp} (hτ : IsRun τ) {o : O} (ho : τ.R τ.cur o) :
    Exposable τ o :=
  commonExpansion_exposable hC hτ ho

/-- Proof of Prop. `prop:exposure-boundary`, both directions; the converse is
the paper's: "By totality there is some `u₀ ∈ P(j)`.  For `r = 1,…,k` in turn, the
legal-output test for `o_r` at `σ_P(i_r)`, applied with `x = u_{r-1}`, gives
`u_r ∈ P(j)` extending both `o_r` and `u_{r-1}`." -/
theorem «proof:prop:exposure-boundary» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    sp.CommonExpansion ↔
      ∀ τ : State sp, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o :=
  exposure_boundary_paper sp

/-- Proof of Thm. `thm:complete-calm`: "The proof of Lemma
`lem:confluence-legality` covers nondeterministic specs, so the runs are
consistent exactly when no output event of a run applies a commitment, that is,
when every output that a run can emit is legal.  As in the
proof of Theorem `thm:functional-calm`, this holds exactly when every output at
every state reachable without commitment is legal.  By Proposition
`prop:exposure-boundary`, that holds exactly when the spec satisfies Lifted
Monotonicity."  The three steps and their composite. -/
theorem «proof:thm:complete-calm» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    (sp.Consistent ↔ sp.RunsLegal) ∧ (sp.RunsLegal ↔ sp.LegalReachLegal) ∧
      (sp.LegalReachLegal ↔ sp.LiftedMono) ∧ (sp.Consistent ↔ sp.LiftedMono) :=
  ⟨consistent_iff_runsLegal sp, runsLegal_iff_legalReachLegal sp,
    legalReachLegal_iff_liftedMono sp, complete_calm_via_legality sp⟩

/-! ### Pairs suffice for the common-extension condition (`app:pairs-suffice`) -/

/-- `app:pairs-suffice`: "Suppose every two rows with a common input extension
`j` have a common output extension in `P(j)`.  Then the condition holds for
every finite family of rows with common input extension `j`.  We replace the
first two rows of the family by a row `(j,u)` whose output `u` extends both, and
repeat until one row remains; a single row, paired with any row at `j`, has an
output extension in `P(j)`."   `CALM.Pairs sp` is the pair condition over all
rows of `P`; it is equivalent to the common-extension condition. -/
theorem «app:pairs-suffice» {I O : Type} [PO I] [PO O] (sp : Spec I O) :
    (∀ i₁ o₁ i₂ o₂ j, sp.P i₁ o₁ → sp.P i₂ o₂ → i₁ ≼ j → i₂ ≼ j →
        ∃ u, sp.P j u ∧ o₁ ≼ u ∧ o₂ ≼ u) ↔ sp.CommonExpansion :=
  pairs_iff_commonExpansion sp

/-- `app:pairs-suffice`: "The pairwise hypothesis must cover all rows of `P`,
including rows at `j` itself, since the replacement rows are at `j`."   On a four-input specification, every two rows at inputs other
than the common input extension are compatible there, but the common-extension
condition fails. -/
theorem «app:pairs-suffice/rows-at-j» :
    (∀ i₁ o₁ i₂ o₂ j, i₁ ≠ j → i₂ ≠ j → spec4.P i₁ o₁ → spec4.P i₂ o₂ → i₁ ≼ j → i₂ ≼ j →
        ∃ u, spec4.P j u ∧ o₁ ≼ u ∧ o₂ ≼ u) ∧ ¬ spec4.CommonExpansion :=
  rowsAtJ_needed

/-- `app:pairs-suffice`: "Checking only rows at single-proposal inputs does
not suffice, even with families of up to `k` rows.  In the `k`-set agreement
example …, every family of at most `k` rows at such inputs is compatible at
each common input extension, but the `k+1` proposal rows are not."

Lean: `k`-set agreement with participants and values `Fin (k+1)`
(`CALM.KSet.spec k`, one instance suffices for the counterexample), `k ≥ 1`.
A row at a single-proposal input `{(p,v)}` is a triple `(p, v, o)`. -/
theorem «app:pairs-suffice/k-at-a-time» (k : Nat) (hk : 1 ≤ k) :
    (∀ (rows : List (Fin (k+1) × Fin (k+1) × PMap (k+1))), rows.length ≤ k →
        (∀ r ∈ rows, (KSet.spec k).P (KSet.atom r.1 r.2.1) r.2.2) →
        ∀ j : PMap (k+1), (∀ r ∈ rows, KSet.atom r.1 r.2.1 ≼ j) →
          ∃ u, (KSet.spec k).P j u ∧ ∀ r ∈ rows, r.2.2 ≼ u) ∧
      (∀ r : Fin (k+1), (KSet.spec k).P (KSet.atom r r) (KSet.atom r r) ∧
        KSet.atom r r ≼ KSet.J (k+1)) ∧
      ¬ ∃ u, (KSet.spec k).P (KSet.J (k+1)) u ∧ ∀ r : Fin (k+1), KSet.atom r r ≼ u :=
  ⟨KSet.atomic_k_at_a_time k, fun r => ⟨KSet.proposal_row k hk r, KSet.J_common k r⟩,
   KSet.not_all_compatible k⟩

/-- Consequence for `app:pairs-suffice`: the `k`-set agreement specification
fails the common-extension condition, hence is not monotone. -/
theorem «app:pairs-suffice/k-set-not-monotone» (k : Nat) (hk : 1 ≤ k) :
    ¬ (KSet.spec k).CommonExpansion ∧ ¬ (KSet.spec k).LiftedMono :=
  ⟨KSet.not_commonExpansion k hk, KSet.not_liftedMono k hk⟩

end CC.Paper
