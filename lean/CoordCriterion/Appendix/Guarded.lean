import CoordCriterion.Appendix.Composition
import CoordCriterion.Distributed.Systems
import CoordCriterion.Instances.Examples

/-!
# Guarded composition and Irredundant Coordination (Section 5, Appendix D)

Namespace `CC.Guard`.  An upstream specification `𝒫 : Spec I M` (e.g. a log
authority, Paxos) feeds a downstream store `𝒦 = graph f` with `f : M → O`
(e.g. deterministic execution of the log).  The environment observes only the
composite `𝒦 ∘ 𝒫 = comp 𝒫 f`.  In the *guarded* composite, `𝒫` runs as a
system under an arbitrary basis `B` (Paxos's own commitments), and the store
runs with the empty basis, emitting `f m` whenever `𝒫` emits `m`.  We say
"`𝒫` guards `𝒦`", or "`𝒦` delegates commitment to `𝒫`".

* `img`, `imgT`, `img_canon`            — the composite table seen through `f`.
* `push_not_commitment`                 — the pushforward of a `𝒫`-commitment
  need not be a commitment of the composite: a `𝒫`-choice can become a
  retirement (`choice_becomes_retirement`).
* `guarded_lockstep`, `guarded_run`     — **pushforward of runs**: if `f` is
  monotone, every run of `𝒫` under *any* basis, read through `f`, is a run of
  the composite in the transition system of Sections 2–3, whose table contains
  the image of `𝒫`'s table after every event.
* `emitted_chain`, `store_cf`, `store_run` — the store's own run (inputs: the
  logs `𝒫` emits; outputs: their images) is commitment-free, i.e. a run under
  the empty basis.
* `coverage`, `coverage_step`           — **absorption**: every row the
  composite's canonical output event must seal or choose against has all of
  its preimages removed by `𝒫`'s commitments.
* `invisible_step`, `cf_step`           — **invisible coordination**: if `𝒫`'s
  commitments remove only rows with a surviving `f`-equivalent row, the
  composite event is commitment-free.
* `SysConsistent`, `GuardedRuns`, `guarded_consistent` — **delegation**: if
  the runs of the `𝒫`-system are consistent (confluent under arbitrary
  continuations), so are the guarded composite runs, judged on the composite.
* Limits: `monotone_necessary` (`f` must be monotone), `store_choice_not_delegable`
  (a store that must choose cannot delegate it), `composite_monotone_not_enough`
  (Lifted Monotonicity of `𝒦 ∘ 𝒫` does not let `𝒫` drop its commitments).
* `PK`, `perKey`, `perKey_monotone`, `commute_example` — a per-key store:
  `𝒫` must choose the order of commands on different keys, the composite
  needs no commitment.
* `AtMostOnce`, `AtLeastOnce`, `Irredundant`, `guarded_irredundant`,
  `at_least_once_needed` — Def./Thm. Irredundant Coordination.
* `smr_irredundant` — Example `ex:committed-log-composition`.
-/

namespace CC
namespace Guard

open Comp Classical

variable {I M O : Type} [PO I] [PO M] [PO O]

/-! ### The composite seen through `f` -/

/-- `𝒦 ∘ 𝒫` for the store `𝒦 = graph f`. -/
abbrev comp (sp : Spec I M) (f : M → O) : Spec I O := seq sp (graph f)

theorem comp_S {sp : Spec I M} {f : M → O} {i : I} {o : O} :
    (comp sp f).S i o ↔ ∃ m, sp.S i m ∧ o = f m := Iff.rfl

/-- Image of a table under `f`. -/
def imgT (f : M → O) (R : Table I M) : Table I O := fun k o => ∃ m, R k m ∧ o = f m

omit [PO I] [PO M] [PO O] in
theorem imgT_mono {f : M → O} {R R' : Table I M} (h : ∀ k m, R k m → R' k m) :
    ∀ k o, imgT f R k o → imgT f R' k o :=
  fun _ _ ⟨m, hm, ho⟩ => ⟨m, h _ _ hm, ho⟩

variable {sp : Spec I M} {f : M → O}

/-- Image of a `𝒫`-state: a state of the composite. -/
def img (f : M → O) (σ : State sp) : State (comp sp f) where
  cur := σ.cur
  R := imgT f σ.R
  sub := fun k _ ⟨m, hm, ho⟩ => ⟨m, σ.sub k m hm, ho⟩
  hasCur := let ⟨m, hm⟩ := σ.hasCur; ⟨f m, m, hm, rfl⟩
  above := fun k _ ⟨m, hm, _⟩ => σ.above k m hm

/-- The image of the canonical state is the canonical state. -/
theorem img_canon (f : M → O) (i : I) : img f (canon sp i) = canon (comp sp f) i := by
  refine State.ext' rfl ?_
  funext k o; apply propext
  show (∃ m, (sp.S k m ∧ i ≼ k) ∧ o = f m) ↔ ((∃ m, sp.S k m ∧ o = f m) ∧ i ≼ k)
  exact ⟨fun ⟨m, ⟨h, hk⟩, ho⟩ => ⟨⟨m, h, ho⟩, hk⟩, fun ⟨⟨m, h, ho⟩, hk⟩ => ⟨m, ⟨h, hk⟩, ho⟩⟩

/-! ### Erasing to the composite -/

/-- What the environment observes of a `𝒫`-event, through the store:
`input j` stays, `Out_γ(m)` becomes `output (f m)`. -/
def obs (f : M → O) : SEvent sp → Event I O
  | .input j => .input j
  | .output _ m => .output (f m)

/-! ### Pushforward of runs -/

/-- **Pushforward of runs (lockstep form).**  If `f` is monotone, from any
composite state `σ'` with the same current input whose table contains the
image of `σ`'s, every execution of `𝒫` under any basis `B`, read through `f`,
is an execution of the composite (in the transition system of Sections 2–3),
and the containment persists. -/
theorem guarded_lockstep (hf : Monotone f) {B : Basis sp} {σ ρ : State sp}
    {es : List (SEvent sp)} (h : SysExec B σ es ρ) :
    ∀ σ' : State (comp sp f), σ'.cur = σ.cur → (∀ k o, imgT f σ.R k o → σ'.R k o) →
      ∃ ρ', Exec σ' (es.map (obs f)) ρ' ∧ ρ'.cur = ρ.cur ∧
        ∀ k o, imgT f ρ.R k o → ρ'.R k o := by
  induction h with
  | nil σ => exact fun σ' hc hs => ⟨σ', Exec.nil _, hc, hs⟩
  | @cons σ τ ρ e es hs _ ih =>
    intro σ' hc hsub
    cases e with
    | input j =>
      match hs with
      | .input (.input _ _ _ hleg hcur hR) =>
        obtain ⟨u, hu⟩ := hleg
        let τ' : State (comp sp f) :=
          { cur := j
            R := inputTable σ' j
            sub := fun k x h => σ'.sub k x h.1
            hasCur := ⟨f u, hsub _ _ ⟨u, hu, rfl⟩, PO.refl j⟩
            above := fun _ _ h => h.2 }
        have hst : Step σ' (.input j) τ' :=
          Step.input σ' τ' j ⟨f u, hsub _ _ ⟨u, hu, rfl⟩⟩ rfl rfl
        have hsub' : ∀ k o, imgT f τ.R k o → τ'.R k o := by
          rintro k o ⟨m, hm, rfl⟩
          rw [hR] at hm
          exact ⟨hsub _ _ ⟨m, hm.1, rfl⟩, hm.2⟩
        obtain ⟨ρ', hx, hc', hs'⟩ := ih τ' hcur.symm hsub'
        exact ⟨ρ', Exec.cons hst hx, hc', hs'⟩
    | output γ m =>
      obtain ⟨hcur, hm, hin, _⟩ := containment hs
      have hm' : σ'.R σ'.cur (f m) := by rw [hc]; exact hsub _ _ ⟨m, hm, rfl⟩
      let τ' := outState σ' (f m) hm'
      have hst : Step σ' (.output (f m)) τ' := Step.output σ' τ' (f m) hm' rfl rfl
      have hsub' : ∀ k o, imgT f τ.R k o → τ'.R k o := by
        rintro k o ⟨m', hm'', rfl⟩
        obtain ⟨a, b⟩ := hin k m' hm''
        exact ⟨hsub _ _ ⟨m', a, rfl⟩, hf _ _ b⟩
      obtain ⟨ρ', hx, hc', hs'⟩ := ih τ' (by rw [hcur]; exact hc) hsub'
      exact ⟨ρ', Exec.cons hst hx, hc', hs'⟩

/-- **Pushforward of runs.**  If `f` is monotone, every run of `𝒫` under any
basis, read through `f`, is a run of the composite from the same canonical
state, and its final table contains the image of `𝒫`'s final table. -/
theorem guarded_run (hf : Monotone f) {B : Basis sp} {i : I} {es : List (SEvent sp)}
    {ρ : State sp} (h : SysExec B (canon sp i) es ρ) :
    ∃ ρ', Exec (canon (comp sp f) i) (es.map (obs f)) ρ' ∧ ρ'.cur = ρ.cur ∧
      ∀ k o, imgT f ρ.R k o → ρ'.R k o :=
  guarded_lockstep hf h _ rfl (by rw [← img_canon f i]; exact fun _ _ h => h)

/-! ### Absorption: the composite's commitments are covered by `𝒫`'s -/

/-- **Coverage.**  Let `σc` be the state `𝒫`'s commitments leave before it
emits `m` (so `m ∈ R_c(i)` is exposable there), and let `ρ` be a composite
state whose table contains the image of `σc`'s.  If `f` is monotone, no row of
that image is sealed or rejected by `f m` at `ρ`: the composite's canonical
event for `f m` removes by commitment only rows outside the image. -/
theorem coverage (hf : Monotone f) {σc : State sp} {m : M} (hexp : Exposable σc m)
    {ρ : State (comp sp f)} (hsub : ∀ k o, imgT f σc.R k o → ρ.R k o) :
    ∀ k x, imgT f σc.R k x → ¬ Sealed ρ (f m) k x ∧ ¬ Rejected ρ (f m) k x := by
  rintro k x ⟨m', hm', rfl⟩
  by_cases hmm : m ≼ m'
  · exact ⟨fun hs => hs.2 ⟨f m', hsub _ _ ⟨m', hm', rfl⟩, hf _ _ hmm⟩,
      fun hr => hr.2.1 (hf _ _ hmm)⟩
  · obtain ⟨u, hu, hmu, hm'u⟩ := hexp k m' hm' hmm
    have hρu : ρ.R k (f u) := hsub _ _ ⟨u, hu, rfl⟩
    exact ⟨fun hs => hs.2 ⟨f u, hρu, hf _ _ hmu⟩,
      fun hr => hr.2.2.2 ⟨hr.1, hr.2.1, f u, hρu, hf _ _ hmu, hf _ _ hm'u⟩⟩

/-- **Absorption, for an output event of `𝒫`.**  Let `Out_γ(m)` be a legal
output event of `𝒫` under any basis, from `σ`, and `ρ` a composite state
containing the image of `σ`'s table.  Every row `(k,x)` that the composite's
canonical event for `f m` must seal or choose against at `ρ` has had every
preimage in `σ` removed by `γ`. -/
theorem coverage_step (hf : Monotone f) {B : Basis sp} {σ τ : State sp}
    {γ : List (Commitment sp)} {m : M} (h : SysStep B σ (.output γ m) τ)
    {ρ : State (comp sp f)} (hsub : ∀ k o, imgT f σ.R k o → ρ.R k o) :
    ∃ σc, ApplySeq γ σ σc ∧
      ∀ k x, (Sealed ρ (f m) k x ∨ Rejected ρ (f m) k x) →
        ∀ m', σ.R k m' → f m' = x → ¬ σc.R k m' := by
  match h with
  | .output (σc := σc) _ hγ _ hexp _ _ =>
    refine ⟨σc, hγ, fun k x hx m' _ hfx hc => ?_⟩
    have hsub' : ∀ k o, imgT f σc.R k o → ρ.R k o :=
      fun k o h' => hsub k o (imgT_mono hγ.sub k o h')
    have := coverage hf hexp hsub' k x ⟨m', hc, hfx.symm⟩
    rcases hx with hs | hr
    · exact this.1 hs
    · exact this.2 hr

/-- **Invisible coordination.**  If every row that `𝒫`'s commitments `γ`
remove has an `f`-equivalent row (same input, same image) that they keep, then
at the image state the composite emits `f m` with no commitment: `γ` is
coordination inside `𝒫` that the composite does not see. -/
theorem invisible_step (hf : Monotone f) {B : Basis sp} {σ τ : State sp}
    {γ : List (Commitment sp)} {m : M} (h : SysStep B σ (.output γ m) τ)
    (hinv : ∀ (σc : State sp), ApplySeq γ σ σc →
      ∀ k m', σ.R k m' → ∃ m'', σc.R k m'' ∧ f m'' = f m') :
    Exposable (img f σ) (f m) := by
  obtain ⟨σc, hγ, hcov⟩ := coverage_step hf h (ρ := img f σ) (fun _ _ h => h)
  rw [exposable_iff_empty]
  have key : ∀ k x, (Sealed (img f σ) (f m) k x ∨ Rejected (img f σ) (f m) k x) → False := by
    intro k x hx
    have hR : (img f σ).R k x := by rcases hx with h | h <;> exact h.1
    obtain ⟨m', hm', rfl⟩ := hR
    obtain ⟨m'', hm'', he⟩ := hinv σc hγ k m' hm'
    exact hcov k _ hx m'' (hγ.sub _ _ hm'') he hm''
  exact ⟨fun ⟨k, x, hs⟩ => key k x (Or.inl hs), fun ⟨k, x, hr⟩ => key k x (Or.inr hr)⟩

/-- A commitment-free output event of `𝒫` maps to a commitment-free output
event of the composite. -/
theorem cf_step (hf : Monotone f) {σ : State sp} {m : M} (hexp : Exposable σ m) :
    Exposable (img f σ) (f m) := by
  rw [exposable_iff_empty]
  have key := coverage hf hexp (ρ := img f σ) (fun _ _ h => h)
  exact ⟨fun ⟨k, x, hs⟩ => (key k x hs.1).1 hs, fun ⟨k, x, hr⟩ => (key k x hr.1).2 hr⟩

/-! ### The store runs with the empty basis -/

/-- The outputs a list of system events emits, in order. -/
def emitted : List (SEvent sp) → List M
  | [] => []
  | .input _ :: es => emitted es
  | .output _ m :: es => m :: emitted es

/-- `l` is a chain starting above the optional lower bound. -/
def ChainFrom : Option M → List M → Prop
  | _, [] => True
  | none, b :: l => ChainFrom (some b) l
  | some a, b :: l => a ≼ b ∧ ChainFrom (some b) l

/-- **The outputs of a run under any basis form a chain**, each refining the
ones before it. -/
theorem emitted_chain {B : Basis sp} {σ ρ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es ρ) :
    ∀ lo : Option M, (∀ a, lo = some a → ∀ k u, σ.R k u → a ≼ u) →
      ChainFrom lo (emitted es) := by
  induction h with
  | nil => intro lo _; cases lo <;> trivial
  | @cons σ τ ρ e es hs _ ih =>
    intro lo hlo
    cases e with
    | input j =>
      exact ih lo (fun a ha k u hu => hlo a ha k u (hs.sub k u hu))
    | output γ m =>
      obtain ⟨_, hm, hin, _⟩ := containment hs
      have hrest := ih (some m) (fun a ha k u hu => by cases ha; exact (hin k u hu).2)
      cases lo with
      | none => exact hrest
      | some a => exact ⟨hlo a rfl _ _ hm, hrest⟩

/-- The store's events for upstream outputs `ms`: receive each, emit its image. -/
def storeEvs (f : M → O) : List M → List (Event M O)
  | [] => []
  | m :: ms => .input m :: .output (f m) :: storeEvs f ms

/-- At the store's canonical state at `a`, emitting `f a` is commitment-free
and returns to the same state. -/
theorem store_out (hf : Monotone f) (a : M) :
    Step (canon (graph f) a) (.output (f a)) (canon (graph f) a) ∧
      Exposable (canon (graph f) a) (f a) := by
  refine ⟨Step.output _ _ _ ⟨rfl, PO.refl a⟩ rfl ?_, ?_⟩
  · funext k u; apply propext
    show (u = f k ∧ a ≼ k) ↔ ((u = f k ∧ a ≼ k) ∧ f a ≼ u)
    exact ⟨fun h => ⟨h, h.1 ▸ hf _ _ h.2⟩, fun h => h.1⟩
  · intro k x hx hnx
    obtain ⟨hx1, hx2⟩ := hx
    exact absurd (hx1 ▸ hf _ _ hx2 : f a ≼ x) hnx

/-- **The store's run is commitment-free.**  Fed a chain of upstream outputs,
the store moves through its canonical states, emitting each image by an
exposable output. -/
theorem store_cf (hf : Monotone f) :
    ∀ (a : M) (ms : List M), ChainFrom (some a) ms →
      ExecCF (canon (graph f) a) (storeEvs f ms) (canon (graph f) (ms.getLastD a))
  | a, [], _ => ExecCF.nil _
  | a, b :: ms, ⟨hab, hc⟩ => by
    have hin : Step (canon (graph f) a) (.input b) (canon (graph f) b) :=
      Dist.step_canon_input (graph f) hab ⟨f b, rfl⟩
    obtain ⟨hout, hexp⟩ := store_out hf b
    have := store_cf hf b ms hc
    rw [List.getLastD_cons]
    exact ExecCF.input hin (ExecCF.output hout hexp this)

/-- **The store runs with the empty basis.**  For any run of `𝒫` under any
basis that emits `m :: ms`, the store's run — start at `m`, emit `f m`, then
receive and answer each later output — is a run under the empty basis that
applies no commitment. -/
theorem store_run (hf : Monotone f) {B : Basis sp} {σ ρ : State sp}
    {es : List (SEvent sp)} (h : SysExec B σ es ρ) {m : M} {ms : List M}
    (he : emitted es = m :: ms) :
    ∃ es' : List (SEvent (graph f)),
      es'.map SEvent.erase = .output (f m) :: storeEvs f ms ∧ CoordFree es' ∧
      SysExec (fun _ => False) (canon (graph f) m) es' (canon (graph f) (ms.getLastD m)) := by
  have hc : ChainFrom (some m) ms := by
    have := emitted_chain h none (fun _ h => by cases h)
    rw [he] at this; exact this
  obtain ⟨hout, hexp⟩ := store_out hf m
  exact execCF_coordFree _ (ExecCF.output hout hexp (store_cf hf m ms hc))

/-! ### Delegation: consistency of the guarded composite -/

/-- A set `R` of run endpoints of a `𝒫`-system is **consistent** when every
finite family of them can be brought, under arbitrary continuations (any
basis), to one common state at each common expansion of their inputs. -/
def SysConsistent (R : State sp → Prop) : Prop :=
  ∀ fam : List (State sp), (∀ σ ∈ fam, R σ) → ∀ j : I, (∀ σ ∈ fam, σ.cur ≼ j) →
    ∃ τ : State sp, τ.cur = j ∧ ∀ σ ∈ fam, ∃ (B : Basis sp) (es : List (SEvent sp)),
      SysExec B σ es τ

/-- For the canonical runs of a specification, this is consistency. -/
theorem sysConsistent_isRun_iff (sp : Spec I M) : SysConsistent (IsRun (sp := sp)) ↔ sp.Consistent := by
  constructor
  · intro h fam hrun j hj
    obtain ⟨τ, hτ, hall⟩ := h fam hrun j hj
    obtain ⟨u, hu⟩ := τ.hasCur
    rw [hτ] at hu
    refine (survivor_test fam hrun j hj).2 ⟨u, τ.sub _ _ hu, fun σ hσ => ?_⟩
    obtain ⟨B, es, hx⟩ := hall σ hσ
    exact hx.sub _ _ hu
  · intro h fam hrun j hj
    obtain ⟨τ, hτ, hall⟩ := h fam hrun j hj
    refine ⟨τ, hτ, fun σ hσ => ?_⟩
    obtain ⟨es, hx⟩ := hall σ hσ
    obtain ⟨es', _, hc⟩ := exec_canonExec hx
    exact ⟨canonBasis sp, es', canonExec_sysExec hc⟩

/-- Runs of `𝒫` under basis `B`. -/
def SysRuns (B : Basis sp) (σ : State sp) : Prop := ∃ i es, SysExec B (canon sp i) es σ

/-- The guarded composite runs over `R`: composite runs whose table contains
the image of the table of some `σ ∈ R` at the same current input. -/
def GuardedRuns (R : State sp → Prop) (f : M → O) (ρ : State (comp sp f)) : Prop :=
  IsRun ρ ∧ ∃ σ, R σ ∧ σ.cur = ρ.cur ∧ ∀ k o, imgT f σ.R k o → ρ.R k o

/-- **Guarded consistency.**  If the runs `R` of a `𝒫`-system are consistent,
then every finite family of guarded composite runs is confluent at every
common expansion, in the composite's own transition system.  No
monotonicity of `𝒫`, and no commitment of the composite, is assumed. -/
theorem guarded_consistent {R : State sp → Prop} (h : SysConsistent R) :
    ∀ fam : List (State (comp sp f)), (∀ ρ ∈ fam, GuardedRuns R f ρ) →
      ∀ j : I, (∀ ρ ∈ fam, ρ.cur ≼ j) → ConfluentAt fam j := by
  intro fam hfam j hj
  obtain ⟨L, hL1, hL2⟩ := choose_list
    (fun (ρ : State (comp sp f)) (σ : State sp) =>
      R σ ∧ σ.cur = ρ.cur ∧ ∀ k o, imgT f σ.R k o → ρ.R k o) fam
    (fun ρ hρ => (hfam ρ hρ).2)
  obtain ⟨τ, hτ, hall⟩ := h (L.map Prod.snd)
    (fun σ hσ => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hσ; exact (hL2 p hp).2.1)
    j (fun σ hσ => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hσ
      rw [(hL2 p hp).2.2.1]; exact hj _ (hL2 p hp).1)
  obtain ⟨m, hm⟩ := τ.hasCur
  rw [hτ] at hm
  refine (survivor_test fam (fun ρ hρ => (hfam ρ hρ).1) j hj).2
    ⟨f m, ⟨m, τ.sub _ _ hm, rfl⟩, fun ρ hρ => ?_⟩
  obtain ⟨σ, hσ⟩ := hL1 ρ hρ
  obtain ⟨B, es, hx⟩ := hall σ (List.mem_map.2 ⟨_, hσ, rfl⟩)
  exact (hL2 _ hσ).2.2.2 _ _ ⟨m, hx.sub _ _ hm, rfl⟩

/-- **Delegation (`𝒫` guards `𝒦`).**  Let `f` be monotone and `R` a
consistent set of runs of a `𝒫`-system with any basis `B`.  Then:
1. every run in `R`, read through `f`, is a composite run with a guarded
   composite endpoint (the composite table contains the image of `𝒫`'s);
2. the store's part of every such run is a run of `𝒦` under the empty basis;
3. the guarded composite runs are consistent. -/
theorem delegation (hf : Monotone f) (B : Basis sp) {R : State sp → Prop}
    (hcons : SysConsistent R) :
    (∀ i es ρ, SysExec B (canon sp i) es ρ → R ρ →
      ∃ ρ', Exec (canon (comp sp f) i) (es.map (obs f)) ρ' ∧ GuardedRuns R f ρ') ∧
    (∀ i es ρ m ms, SysExec B (canon sp i) es ρ → emitted es = m :: ms →
      ∃ es' : List (SEvent (graph f)), es'.map SEvent.erase = .output (f m) :: storeEvs f ms ∧
        CoordFree es' ∧
        SysExec (fun _ => False) (canon (graph f) m) es' (canon (graph f) (ms.getLastD m))) ∧
    (∀ fam : List (State (comp sp f)), (∀ ρ ∈ fam, GuardedRuns R f ρ) →
      ∀ j : I, (∀ ρ ∈ fam, ρ.cur ≼ j) → ConfluentAt fam j) := by
  refine ⟨fun i es ρ hx hρ => ?_, fun _ _ _ _ _ hx he => store_run hf hx he,
    guarded_consistent hcons⟩
  obtain ⟨ρ', hx', hc, hs⟩ := guarded_run hf hx
  exact ⟨ρ', hx', ⟨i, _, hx'⟩, ρ, hρ, hc.symm, hs⟩

/-- **Guarded confluence, per family.**  Let `σ_r` be states of `𝒫` and `ρ_r`
composite runs whose tables contain their images.  If the `σ_r` can be
continued (under any bases) to one state with current input `j`, then the
`ρ_r` are confluent at `j` in the composite. -/
theorem guarded_confluent (fam : List (State sp × State (comp sp f)))
    (hrun : ∀ p ∈ fam, IsRun p.2) (hsub : ∀ p ∈ fam, ∀ k o, imgT f p.1.R k o → p.2.R k o)
    (j : I) (hj : ∀ p ∈ fam, p.2.cur ≼ j)
    (hP : ∃ τ : State sp, τ.cur = j ∧ ∀ p ∈ fam, ∃ (B : Basis sp) (es : List (SEvent sp)),
      SysExec B p.1 es τ) :
    ConfluentAt (fam.map Prod.snd) j := by
  obtain ⟨τ, hτ, hall⟩ := hP
  obtain ⟨m, hm⟩ := τ.hasCur
  rw [hτ] at hm
  have hrun' : ∀ ρ ∈ fam.map Prod.snd, IsRun ρ := by
    intro ρ hρ; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hρ; exact hrun p hp
  have hj' : ∀ ρ ∈ fam.map Prod.snd, ρ.cur ≼ j := by
    intro ρ hρ; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hρ; exact hj p hp
  refine (survivor_test _ hrun' j hj').2 ⟨f m, ⟨m, τ.sub _ _ hm, rfl⟩, fun ρ hρ => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hρ
  obtain ⟨B, es, hx⟩ := hall p hp
  exact hsub p hp _ _ ⟨m, hx.sub _ _ hm, rfl⟩

/-! ### Irredundant Coordination -/

/-- **At most once.**  `𝒫` under basis `B` guards the store `graph f`: every
run of `𝒫` under `B`, read through `f`, is a composite run whose table
contains the image of `𝒫`'s, and the store's own part of the run is a run of
`graph f` under the empty basis. -/
def AtMostOnce (B : Basis sp) (f : M → O) : Prop :=
  (∀ i es ρ, SysExec B (canon sp i) es ρ →
    ∃ ρ', Exec (canon (comp sp f) i) (es.map (obs f)) ρ' ∧ ρ'.cur = ρ.cur ∧
      ∀ k o, imgT f ρ.R k o → ρ'.R k o) ∧
  (∀ (σ ρ : State sp) es m ms, SysExec B σ es ρ → emitted es = m :: ms →
    ∃ es' : List (SEvent (graph f)), es'.map SEvent.erase = .output (f m) :: storeEvs f ms ∧
      CoordFree es' ∧
      SysExec (fun _ => False) (canon (graph f) m) es' (canon (graph f) (ms.getLastD m)))

/-- **At least once.**  Whenever the composite needs a commitment to emit
`f m` at the image of `𝒫`'s state, `𝒫`'s output event for `m` applies one:
`𝒫`'s commitments cannot be dropped. -/
def AtLeastOnce (B : Basis sp) (f : M → O) : Prop :=
  ∀ (σ τ : State sp) γ m, SysStep B σ (.output γ m) τ →
    ¬ Exposable (img f σ) (f m) → γ ≠ []

/-- **Irredundant Coordination**: the guarded composite coordinates at most
once (the store applies no commitment) and at least once (every commitment
the composite needs is applied by `𝒫`). -/
def Irredundant (B : Basis sp) (f : M → O) : Prop := AtMostOnce B f ∧ AtLeastOnce B f

/-- **Theorem (Irredundant Coordination).**  If `f` is monotone, then for any
basis `B` of `𝒫` the guarded composite is irredundant. -/
theorem guarded_irredundant (hf : Monotone f) (B : Basis sp) : Irredundant B f := by
  refine ⟨⟨fun _ _ _ hx => guarded_run hf hx, fun _ _ _ _ _ hx he => store_run hf hx he⟩, ?_⟩
  intro σ τ γ m hs hne hγ
  subst hγ
  exact hne (cf_step hf (eps_step_iff.1 hs).2.1)

/-- Exposability at canonical states alone gives the common-expansion
condition (the reverse direction of the exposure boundary uses only them). -/
theorem canon_exposable_commonExpansion {I O : Type} [PO I] [PO O] {sp : Spec I O}
    (hE : ∀ i o, sp.S i o → Exposable (canon sp i) o) : sp.CommonExpansion := by
  intro rows
  induction rows with
  | nil =>
    intro _ j _
    obtain ⟨u, hu⟩ := sp.total j
    exact ⟨u, hu, by simp⟩
  | cons r rs ih =>
    intro hS j hJ
    obtain ⟨u1, hu1, hall⟩ := ih (fun r' h => hS r' (List.mem_cons_of_mem _ h)) j
      (fun r' h => hJ r' (List.mem_cons_of_mem _ h))
    have hr := hS r (List.mem_cons_self ..)
    have hrj := hJ r (List.mem_cons_self ..)
    obtain ⟨u, hu, hou, h1u⟩ :=
      (lifted_exposure_test _ _).1 (hE r.1 r.2 hr) j hrj u1 ⟨hu1, hrj⟩
    refine ⟨u, hu.1, fun r' hr' => ?_⟩
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact hou
    · exact PO.trans (hall r' hr') h1u

/-- **At least once is not vacuous.**  If `𝒦 ∘ 𝒫` violates Lifted
Monotonicity, some composite output `f m` is not exposable at the canonical
state at `i`, and every `𝒫`-output with that image needs a commitment there.
So a guarded composite in which `𝒫` runs under the empty basis can never emit
`f m` from the state it is in right after receiving `i`. -/
theorem at_least_once_needed (hf : Monotone f) (hnot : ¬ (comp sp f).LiftedMono) :
    ∃ i m, sp.S i m ∧ ¬ Exposable (canon (comp sp f) i) (f m) ∧
      (∀ m', sp.S i m' → f m' = f m → ¬ Exposable (canon sp i) m') ∧
      ∀ γ m' τ, SysStep (fun _ => False) (canon sp i) (.output γ m') τ → f m' ≠ f m := by
  have hall : ¬ ∀ i o, (comp sp f).S i o → Exposable (canon (comp sp f) i) o := fun h =>
    hnot ((liftedMono_iff_commonExpansion _).2 (canon_exposable_commonExpansion h))
  obtain ⟨i, o, ⟨m, hm, rfl⟩, hne⟩ : ∃ i o, (comp sp f).S i o ∧
      ¬ Exposable (canon (comp sp f) i) o :=
    Classical.byContradiction fun hn =>
      hall fun i o h => Classical.byContradiction fun he => hn ⟨i, o, h, he⟩
  have hcf : ∀ m', Exposable (canon sp i) m' → Exposable (canon (comp sp f) i) (f m') := by
    intro m' he; rw [← img_canon f i]; exact cf_step hf he
  refine ⟨i, m, hm, hne, fun m' _ he hx => hne (he ▸ hcf m' hx), ?_⟩
  intro γ m' τ hs he
  cases γ with
  | cons c _ =>
    cases hs with
    | output hb _ _ _ _ _ => exact hb c (List.mem_cons_self ..)
  | nil => exact hne (he ▸ hcf m' (eps_step_iff.1 hs).2.1)

/-! ### The pushforward of a commitment need not be a commitment -/

section Push

/-- Two levels, `lo ≼ hi`. -/
inductive Lvl where
  | lo | hi
  deriving DecidableEq

instance : PO Lvl where
  le a b := a = .lo ∨ b = .hi
  refl a := by cases a <;> simp
  trans := by intro a b c h1 h2; cases a <;> cases b <;> cases c <;> simp_all
  antisymm := by intro a b h1 h2; cases a <;> cases b <;> simp_all

/-- `x ↦ lo`, `y ↦ hi`: monotone, since `Two` is discrete. -/
def fLvl : Two → Lvl
  | .x => .lo
  | .y => .hi

theorem fLvl_monotone : Monotone fLvl := fun _ _ h => by cases h; exact PO.refl _

theorem anyS_rejected_x : Rejected (canon anyS Pt.pt) Two.y Pt.pt Two.x := by
  refine ⟨⟨trivial, trivial⟩, fun h => Two.noConfusion h, fun hs => hs.2 ⟨.y, ⟨trivial, trivial⟩, rfl⟩, ?_⟩
  rintro ⟨_, _, u, _, hyu, hxu⟩
  have h1 : Two.y = u := hyu
  have h2 : Two.x = u := hxu
  exact Two.noConfusion (h2.trans h1.symm)

/-- **The pushforward of a commitment need not be a commitment.**  At the
canonical state of `anyS` (one input, outputs `x`, `y` incomparable), the
canonical choice `c_y` is a commitment of `𝒫`: it removes `x` and keeps `y`.
Its image removes `lo` and keeps `hi ≽ lo`, so no commitment of the composite
takes the image state to the image of the result. -/
theorem push_not_commitment :
    ∃ τ, (choiceC Two.y).app (canon anyS Pt.pt) = some τ ∧
      ∀ c : Commitment (comp anyS fLvl), c.app (img fLvl (canon anyS Pt.pt)) ≠ some (img fLvl τ) := by
  refine ⟨cmChooseState (canon anyS Pt.pt) Two.y,
    chooseApp_eq.2 ⟨⟨trivial, trivial⟩, ⟨_, _, anyS_rejected_x⟩, rfl⟩, ?_⟩
  intro c hc
  have hlo : (img fLvl (canon anyS Pt.pt)).R Pt.pt Lvl.lo := ⟨.x, ⟨trivial, trivial⟩, rfl⟩
  have hnlo : ¬ (img fLvl (cmChooseState (canon anyS Pt.pt) Two.y)).R Pt.pt Lvl.lo := by
    rintro ⟨m, ⟨_, hr⟩, hm⟩
    cases m with
    | x => exact hr anyS_rejected_x
    | y => exact Lvl.noConfusion hm
  have hhi : (img fLvl (cmChooseState (canon anyS Pt.pt) Two.y)).R Pt.pt Lvl.hi :=
    ⟨.y, ⟨⟨trivial, trivial⟩, not_rejected_of_ge (PO.refl _)⟩, rfl⟩
  exact c.excludes _ _ hc Pt.pt Lvl.lo Lvl.hi hlo hnlo hhi (Or.inl rfl)

/-- **A choice of `𝒫` can become a retirement.**  In the composite, `hi` is
exposable at the canonical state: `lo` is retired, not chosen against. -/
theorem choice_becomes_retirement :
    ¬ Exposable (canon anyS Pt.pt) Two.y ∧
      Exposable (canon (comp anyS fLvl) Pt.pt) Lvl.hi := by
  refine ⟨fun he => ?_, ?_⟩
  · obtain ⟨u, _, hyu, hxu⟩ := he Pt.pt Two.x ⟨trivial, trivial⟩ (fun h => Two.noConfusion h)
    have h1 : Two.y = u := hyu
    have h2 : Two.x = u := hxu
    exact Two.noConfusion (h2.trans h1.symm)
  · intro k x _ _
    exact ⟨.hi, ⟨⟨.y, trivial, rfl⟩, trivial⟩, PO.refl _, Or.inr rfl⟩

end Push

/-! ### Limits -/

section Limits

/-- The state `(j, R[in ⪰ j])` after a legal input. -/
def inState {I O : Type} [PO I] [PO O] {sp : Spec I O} (σ : State sp) (j : I) (u : O)
    (hu : σ.R j u) : State sp where
  cur := j
  R := inputTable σ j
  sub := fun k x h => σ.sub k x h.1
  hasCur := ⟨u, hu, PO.refl j⟩
  above := fun _ _ h => h.2

/-- **`f` must be monotone.**  Take `𝒫` to be the identity on `M` (which needs
no commitment).  For `m ≼ m'`, its run `output m, input m', output m'`, read
through `f`, is a run of the composite exactly when `f m ≼ f m'`. -/
theorem monotone_necessary (f : M → O) {m m' : M} (hmm : m ≼ m') :
    (∃ ρ, Exec (canon (comp (graph fun x : M => x) f) m)
        [.output (f m), .input m', .output (f m')] ρ) ↔ f m ≼ f m' := by
  constructor
  · rintro ⟨ρ, hx⟩
    match hx with
    | .cons (.output _ τ1 _ _ hc1 hR1) (.cons (.input _ τ2 _ _ hc2 hR2)
        (.cons (.output _ _ _ ho3 _ _) _)) =>
      rw [hR2, hc2] at ho3
      have := ho3.1
      rw [hR1] at this
      exact this.2
  · intro hf
    let C := comp (graph fun x : M => x) f
    have r0 : (canon C m).R m (f m) := ⟨⟨m, rfl, rfl⟩, PO.refl m⟩
    let τ1 := outState (canon C m) (f m) r0
    have r1 : τ1.R m' (f m') := ⟨⟨⟨m', rfl, rfl⟩, hmm⟩, hf⟩
    let τ2 := inState τ1 m' (f m') r1
    have r2 : τ2.R τ2.cur (f m') := ⟨r1, PO.refl m'⟩
    exact ⟨outState τ2 (f m') r2,
      .cons (Step.output _ τ1 _ r0 rfl rfl)
        (.cons (Step.input τ1 τ2 m' ⟨_, r1⟩ rfl rfl)
          (.cons (Step.output τ2 (outState τ2 (f m') r2) _ r2 rfl rfl) (.nil _)))⟩

/-- … and the identity `𝒫` runs it without commitment. -/
theorem identity_cf {m m' : M} (hmm : m ≼ m') :
    ExecCF (canon (graph fun x : M => x) m) [.output m, .input m', .output m']
      (canon (graph fun x : M => x) m') := by
  have hid : Monotone (fun x : M => x) := fun _ _ h => h
  obtain ⟨o1, e1⟩ := store_out hid m
  obtain ⟨o2, e2⟩ := store_out hid m'
  exact .output o1 e1 (.input (Dist.step_canon_input _ hmm ⟨m', rfl⟩) (.output o2 e2 (.nil _)))

open Dist (U1 B2 spU noBasis u1_eq) in
/-- **A store that must choose cannot delegate the choice.**  With the
identity upstream on one input (which admits no commitment at all) and the
store `spU` (two incomparable outputs), every output event of the composite at
its canonical state applies a commitment, under any basis.  That commitment
is the store's own. -/
theorem store_choice_not_delegable :
    (∀ (c : Commitment (graph fun x : U1 => x)) σ τ, c.app σ ≠ some τ) ∧
    ∀ (B : Basis (seq (graph fun x : U1 => x) spU)) γ o τ,
      SysStep B (canon _ ()) (.output γ o) τ → γ ≠ [] := by
  refine ⟨fun c σ τ h => ?_, fun B γ o τ hs hγ => ?_⟩
  · obtain ⟨k, u, _, hnu⟩ := c.removes σ τ h
    obtain ⟨w, hw⟩ := τ.hasCur
    rw [u1_eq k τ.cur, u1_eq u w] at hnu
    exact hnu hw
  · subst hγ
    obtain ⟨_, hexp, _, _⟩ := eps_step_iff.1 hs
    have hne : o ≠ (!o : Bool) := by cases o <;> (intro h; cases h)
    obtain ⟨u, _, h1, h2⟩ := hexp () (!o : Bool) ⟨⟨(), rfl, trivial⟩, trivial⟩ hne
    have e1 : o = u := h1
    have e2 : (!o : Bool) = u := h2
    exact hne (e1.trans e2.symm)

open Dist (U1 B2 spU noBasis u1_eq spU_not_exposable noBasis_full) in
/-- Under the empty basis, `spU` never emits. -/
theorem noBasis_silent {σ ρ : State spU} {es : List (SEvent spU)}
    (h : SysExec noBasis σ es ρ) (hfull : ∀ k u, σ.R k u) :
    ∀ γ o, SEvent.output γ o ∉ es := by
  induction h with
  | nil => intro _ _ h; cases h
  | @cons σ τ ρ e es hs hrest ih =>
    intro γ o hm
    have hτ : ∀ k u, τ.R k u := noBasis_full (.cons hs (.nil _)) hfull
    rcases List.mem_cons.1 hm with he | hm
    · subst he
      cases hs with
      | output hb hγ _ hleg _ _ =>
        cases γ with
        | cons c _ => exact hb c (List.mem_cons_self ..)
        | nil => cases hγ; exact spU_not_exposable σ hfull _ hleg
    · exact ih hτ γ o hm

open Dist (U1 B2 spU noBasis u1_eq) in
/-- **Lifted Monotonicity of the composite does not let `𝒫` drop its
commitments.**  With `𝒫 = spU` and a constant store, `𝒦 ∘ 𝒫` satisfies Lifted
Monotonicity, yet `𝒫` under the empty basis never emits, so the store never
receives anything.  `𝒫`'s choice is invisible in the composite but still
necessary for this implementation. -/
theorem composite_monotone_not_enough :
    (comp spU (fun _ : B2 => ())).LiftedMono ∧
      ∀ es ρ, SysExec noBasis (canon spU ()) es ρ → emitted es = [] := by
  refine ⟨fun i j _ X _ _ => ⟨(), ⟨true, trivial, rfl⟩, fun x _ => trivial⟩, ?_⟩
  intro es ρ hx
  have hs := noBasis_silent hx (fun _ _ => ⟨trivial, trivial⟩)
  clear hx
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | input j => exact ih (fun γ o h => hs γ o (List.mem_cons_of_mem _ h))
    | output γ o => exact absurd (List.mem_cons_self ..) (hs γ o)

end Limits

/-! ### A per-key store: ordering commands on different keys is invisible -/

section PerKey
open Inst (Pfx)

/-- Per-key logs, ordered pointwise by prefix. -/
structure PK (K α : Type) where
  get : K → Pfx α

instance (K α : Type) : PO (PK K α) where
  le p q := ∀ k, p.get k ≼ q.get k
  refl p _ := PO.refl _
  trans h h' k := PO.trans (h k) (h' k)
  antisymm := by
    rintro ⟨p⟩ ⟨q⟩ h h'
    congr; funext k; exact PO.antisymm (h k) (h' k)

variable {Cmd K : Type} [DecidableEq K] (key : Cmd → K)

/-- The store's view of a log: its commands on each key, in log order. -/
def perKey (b : Pfx Cmd) : PK K Cmd := ⟨fun k => ⟨b.l.filter fun c => decide (key c = k)⟩⟩

theorem perKey_monotone : Monotone (perKey key) := by
  rintro b b' ⟨t, ht⟩ k
  exact ⟨t.filter fun c => decide (key c = k), by
    show (b'.l.filter _) = (b.l.filter _) ++ _
    rw [ht, List.filter_append]⟩

/-- Two orders of commands on different keys look the same, key by key. -/
theorem perKey_swap {a b : Cmd} (hk : key a ≠ key b) :
    perKey key ⟨[a, b]⟩ = perKey key ⟨[b, a]⟩ := by
  unfold perKey; congr; funext k; congr 1
  by_cases ha : key a = k <;> by_cases hb : key b = k
  · exact absurd (ha.trans hb.symm) hk
  all_goals simp [List.filter, ha, hb]

/-- `𝒫` on one input: the log is `[a,b]` or `[b,a]`. -/
def abSpec (a b : Cmd) : Spec Pt (Pfx Cmd) :=
  ⟨fun _ l => l = ⟨[a, b]⟩ ∨ l = ⟨[b, a]⟩, fun _ => ⟨_, Or.inl rfl⟩⟩

theorem pfx_swap {a b : Cmd} (hab : a ≠ b) : ¬ ((⟨[a, b]⟩ : Pfx Cmd) ≼ ⟨[b, a]⟩) := by
  rintro ⟨t, ht⟩
  simp only [List.cons_append, List.cons.injEq] at ht
  exact hab ht.1.symm

/-- **Commuting commands.**  For commands `a`, `b` on different keys, `𝒫` must
choose an order (emitting `[a,b]` is not exposable), but the per-key store
sees one row, and emitting its image is exposable: the order is coordination
inside `𝒫` that the composite does not see. -/
theorem commute_example {a b : Cmd} (hk : key a ≠ key b) :
    ¬ Exposable (canon (abSpec a b) Pt.pt) ⟨[a, b]⟩ ∧
      Exposable (canon (comp (abSpec a b) (perKey key)) Pt.pt) (perKey key ⟨[a, b]⟩) := by
  have hab : a ≠ b := fun h => hk (congrArg key h)
  refine ⟨fun he => ?_, ?_⟩
  · obtain ⟨u, hu, h1, h2⟩ := he Pt.pt ⟨[b, a]⟩ ⟨Or.inr rfl, trivial⟩ (pfx_swap hab)
    rcases hu.1 with rfl | rfl
    · exact pfx_swap hab.symm h2
    · exact pfx_swap hab h1
  · intro k x hx hnx
    obtain ⟨⟨m, hm, rfl⟩, _⟩ := hx
    rcases hm with rfl | rfl
    · exact absurd (PO.refl _) hnx
    · exact absurd (perKey_swap key hk ▸ PO.refl _) hnx

end PerKey

/-! ### Example `ex:committed-log-composition`: the replicated store -/

section SMR
open Inst (Pfx smrS1 execF)

/-- **The replicated store coordinates exactly once.**  For any deterministic
state machine and two distinct commands, the log specification `𝒫 = smrS1`
and the composite violate Lifted Monotonicity, execution is monotone, and for
every basis of `𝒫` (Multi-Paxos's, or any other) the guarded composite is
irredundant; some composite output needs a commitment, which `𝒫` must make. -/
theorem smr_irredundant {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R) (σ0 : Stt)
    {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) (B : Basis (smrS1 (Cmd := Cmd))) :
    ¬ (smrS1 (Cmd := Cmd)).LiftedMono ∧ ¬ (comp smrS1 (execF δ σ0)).LiftedMono ∧
      Monotone (execF δ σ0) ∧ Irredundant B (execF δ σ0) ∧
      ∃ i m, smrS1.S i m ∧ ¬ Exposable (canon (comp smrS1 (execF δ σ0)) i) (execF δ σ0 m) ∧
        ∀ m', smrS1.S i m' → execF δ σ0 m' = execF δ σ0 m → ¬ Exposable (canon smrS1 i) m' := by
  obtain ⟨h1, h2, hf, _⟩ := Inst.smr_example δ σ0 hne
  obtain ⟨i, m, hm, hne', hall, _⟩ := at_least_once_needed hf h2
  exact ⟨h1, h2, hf, guarded_irredundant hf B, i, m, hm, hne', hall⟩

end SMR

end Guard
end CC
