import CoordCriterion.Appendix.Composition
import CoordCriterion.Distributed.Systems
import CoordCriterion.Instances.Examples

/-!
# Guarded composition and Proper Coordination (Section 5, Appendix D)

Namespace `CC.Guard`.  An upstream specification `𝒫 : Spec I M` (e.g. a log
authority, Paxos) feeds a downstream store `𝒦 = graph f` with `f : M → O`
(e.g. deterministic execution of the log).  The environment observes only the
composite `𝒦 ∘ 𝒫 = comp 𝒫 f`.  In the *guarded* composite, `𝒫` runs as a
system under an arbitrary basis `B` (Paxos's own commitments), and the store
runs as a system of its own, e.g. with the empty basis, answering whenever `𝒫`
emits.  The first sections treat a function store `graph f`; section
`General` treats any Lifted-Monotone store.  We say
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
* `Sys`, `Produces`, `Sys.free`, `Sys.emits` — a system for one participant
  (a basis and a strategy), the runs it produces, and the output sequences it
  emits.
* General stores (section `General`): the store is any Lifted-Monotone
  `sk : Spec M O`, the upstream any behaviour `U : List M → Prop`.
  `imgK`, `cf_stepK`, `row_at`, `store_follows`, `noStore_follows`,
  `composite_run`, `guarded_confluentK` — Thm. Guarded runs.
  `GRun`, `SRun`, `Accepts`, `EmitsAt`, `Contradicted`, `Redundant`,
  `AtMostOnce`, `AtLeastOnce`, `Proper`, `proper_iff`, `at_least_once`,
  `guarded_proper`, `composite_needs_commit` — Def./Thm. Proper Coordination.
  `eraseSys`, `Blind`, `Live`, `Obs`, `erase_simulates`, `erase_reflects`,
  `empty_storeU`, `empty_store` — Cor. Empty store.
  `grun_composite`, `GEmits`, `pipeline_step`, `pipeline_coordination_free` —
  Cor. Pipelines.
* `store_exposable`, `store_eps` — function stores: every output is exposable
  at every state.
* `sealIn`, `mutexB`, `earlyLock`, `lateLock`, `stallLock`, `mutex_redundant`,
  `early_lock_strict`, `late_lock_proper`, `stall_lock` — lock strategies in
  the store behind the log.
* `smr_proper` — Example `ex:committed-log-composition`.
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

/-! ### A store with its own commitments -/

section SealIn
variable {J P : Type} [PO J] [PO P] {sq : Spec J P}

/-- `(i, R ∖ R[in ∈ Q])`, for `Q` false at the current input. -/
def sealInState (σ : State sq) (Q : J → Prop) (h : ¬ Q σ.cur) : State sq where
  cur := σ.cur
  R := fun k x => σ.R k x ∧ ¬ Q k
  sub := fun k x hx => σ.sub k x hx.1
  hasCur := let ⟨o, ho⟩ := σ.hasCur; ⟨o, ho, h⟩
  above := fun k x hx => σ.above k x hx.1

noncomputable def sealInApp (Q : J → Prop) (σ : State sq) : Option (State sq) :=
  if h : ¬ Q σ.cur ∧ ∃ k x, σ.R k x ∧ Q k then some (sealInState σ Q h.1) else none

theorem sealInApp_eq {Q : J → Prop} {σ τ : State sq} :
    sealInApp Q σ = some τ ↔ ∃ h : ¬ Q σ.cur, (∃ k x, σ.R k x ∧ Q k) ∧ sealInState σ Q h = τ := by
  unfold sealInApp
  split
  · rename_i h
    simp only [Option.some.injEq]
    exact ⟨fun e => ⟨h.1, h.2, e⟩, fun ⟨_, _, e⟩ => e⟩
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h1, h2, _⟩
    exact h ⟨h1, h2⟩

/-- **Sealing the inputs in `Q`** (defined when `Q` is false at the current
input and some remaining row has its input in `Q`) is a commitment. -/
noncomputable def sealIn (Q : J → Prop) : Commitment sq where
  app := sealInApp Q
  cur_eq := by intro σ τ h; obtain ⟨_, _, rfl⟩ := sealInApp_eq.1 h; rfl
  sub := by intro σ τ h k u hu; obtain ⟨_, _, rfl⟩ := sealInApp_eq.1 h; exact hu.1
  removes := by
    intro σ τ h
    obtain ⟨_, ⟨k, x, hx, hQ⟩, rfl⟩ := sealInApp_eq.1 h
    exact ⟨k, x, hx, fun h' => h'.2 hQ⟩
  excludes := by
    intro σ τ h k u w hu hnu hw _
    obtain ⟨_, _, rfl⟩ := sealInApp_eq.1 h
    exact hnu ⟨hu, hw.2⟩

end SealIn

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

/-! ### Systems and strategies -/

/-- Commitments applied in an execution under `B` come from `B`. -/
theorem sysExec_basis {I O : Type} [PO I] [PO O] {sp : Spec I O} {B : Basis sp}
    {σ ρ : State sp} {es : List (SEvent sp)} (h : SysExec B σ es ρ) :
    ∀ γ o, SEvent.output γ o ∈ es → ∀ c ∈ γ, B c := by
  induction h with
  | nil => intro _ _ h; cases h
  | cons hs _ ih =>
    intro γ o hm
    rcases List.mem_cons.1 hm with he | hm
    · subst he
      cases hs with
      | output hb _ _ _ _ _ => exact hb
    · exact ih γ o hm

/-- The state `(j, R[in ⪰ j])` after a legal input. -/
def inState {I O : Type} [PO I] [PO O] {sp : Spec I O} (σ : State sp) (j : I) (u : O)
    (hu : σ.R j u) : State sp where
  cur := j
  R := inputTable σ j
  sub := fun k x h => σ.sub k x h.1
  hasCur := ⟨u, hu, PO.refl j⟩
  above := fun _ _ h => h.2

section Systems
variable {J X : Type} [PO J] [PO X] {sq : Spec J X}

/-- **A system for one participant** (Defs. `def:strategy`, `def:system`): a
commitment basis and a nondeterministic strategy.  `strat i a e` says that,
started at the canonical state at `i`, after local history `a` the participant
may perform the output event `e`.  Input events come from the environment. -/
structure Sys (sq : Spec J X) where
  basis : Basis sq
  strat : J → List (SEvent sq) → SEvent sq → Prop

/-- The events a system allows after local history `a`: every input, and the
output events its strategy chooses. -/
def Allowed (S : Sys sq) (i : J) (a : List (SEvent sq)) : SEvent sq → Prop
  | .input _ => True
  | .output γ o => S.strat i a (.output γ o)

/-- Every event of `l` is allowed given its prefix. -/
def Compliant {E : Type} (A : List E → E → Prop) (l : List E) : Prop :=
  ∀ a e b, l = a ++ e :: b → A a e

/-- **Produced runs**: executions under the basis from a canonical state whose
output events the strategy chooses. -/
def Produces (S : Sys sq) (i : J) (es : List (SEvent sq)) (ρ : State sq) : Prop :=
  SysExec S.basis (canon sq i) es ρ ∧ Compliant (Allowed S i) es

/-- The system with basis `B` whose strategy allows every event. -/
def Sys.free (B : Basis sq) : Sys sq := ⟨B, fun _ _ _ => True⟩

theorem compliant_nil {E : Type} {A : List E → E → Prop} : Compliant A [] := by
  intro a e b h; simp at h

theorem compliant_snoc {E : Type} {A : List E → E → Prop} {l : List E} {e : E}
    (hl : Compliant A l) (he : A l e) : Compliant A (l ++ [e]) := by
  intro a e' b h
  rcases List.eq_nil_or_concat b with rfl | ⟨b', x, rfl⟩
  · obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
    cases h2; exact he
  · have h' : l ++ [e] = (a ++ e' :: b') ++ [x] := by rw [h]; simp
    obtain ⟨rfl, _⟩ := List.append_inj' h' rfl
    exact hl a e' b' rfl

theorem compliant_free {B : Basis sq} {i : J} (es : List (SEvent sq)) :
    Compliant (Allowed (Sys.free B) i) es := by
  intro a e _ _; cases e <;> trivial

theorem produces_free {B : Basis sq} {i : J} {es : List (SEvent sq)} {ρ : State sq} :
    Produces (Sys.free B) i es ρ ↔ SysExec B (canon sq i) es ρ :=
  ⟨fun h => h.1, fun h => ⟨h, compliant_free es⟩⟩

theorem sysExec_snoc {B : Basis sq} {σ τ ρ : State sq} {a : List (SEvent sq)} {e : SEvent sq}
    (h : SysExec B σ a τ) (hs : SysStep B τ e ρ) : SysExec B σ (a ++ [e]) ρ := by
  induction h with
  | nil => exact .cons hs (.nil _)
  | cons h1 _ ih => exact .cons h1 (ih hs)

theorem sysExec_append_inv {B : Basis sq} :
    ∀ {a b : List (SEvent sq)} {σ ρ : State sq}, SysExec B σ (a ++ b) ρ →
      ∃ τ, SysExec B σ a τ ∧ SysExec B τ b ρ
  | [], _, σ, _, h => ⟨σ, .nil σ, h⟩
  | _ :: _, _, _, _, .cons hs hr =>
    let ⟨τ, h1, h2⟩ := sysExec_append_inv hr
    ⟨τ, .cons hs h1, h2⟩

/-- Drop the commitments of an output event: `Out_δ(o) ↦ Out_ε(o)`. -/
def eraseC : SEvent sq → SEvent sq
  | .input j => .input j
  | .output _ o => .output [] o

theorem erase_eraseC (e : SEvent sq) : (eraseC e).erase = e.erase := by cases e <;> rfl

theorem eraseC_eraseC (e : SEvent sq) : eraseC (eraseC e) = eraseC e := by cases e <;> rfl

theorem map_erase_eraseC (l : List (SEvent sq)) :
    (l.map eraseC).map SEvent.erase = l.map SEvent.erase := by
  induction l with
  | nil => rfl
  | cons e l ih => simp only [List.map_cons, erase_eraseC, ih]

theorem map_erase_of_eraseC {l l' : List (SEvent sq)} (h : l.map eraseC = l'.map eraseC) :
    l.map SEvent.erase = l'.map SEvent.erase := by
  rw [← map_erase_eraseC l, h, map_erase_eraseC]

/-- **Commitment-erased replacement.**  Same strategy, empty basis, and each
`Out_δ(o)` replaced by `Out_ε(o)`: after a local history, it allows an event
when the original allows one with the same erasure after a history with the
same erasure. -/
def eraseSys (S : Sys sq) : Sys sq where
  basis := fun _ => False
  strat i a' e' := ∃ a e, a.map eraseC = a'.map eraseC ∧ eraseC e = eraseC e' ∧ S.strat i a e

/-- The strategy **ignores commitments**: it depends on the local history only
through its erasure. -/
def Blind (S : Sys sq) : Prop :=
  ∀ i a b e, a.map eraseC = b.map eraseC → S.strat i a e → S.strat i b e

/-- The strategy **never stalls**: whenever it offers an output after a
produced history, and the output is still in the table, it also offers a
legal output event emitting it. -/
def Live (S : Sys sq) : Prop :=
  ∀ i a σ δ o, Produces S i a σ → S.strat i a (.output δ o) → σ.R σ.cur o →
    ∃ δ' τ, S.strat i a (.output δ' o) ∧ SysStep S.basis σ (.output δ' o) τ

theorem compliant_eraseSys {S : Sys sq} {i : J} {es : List (SEvent sq)}
    (h : Compliant (Allowed S i) es) : Compliant (Allowed (eraseSys S) i) (es.map eraseC) := by
  intro a' e' b' hm
  obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.map_eq_append_iff.1 hm
  obtain ⟨e, l, rfl, he, _⟩ := List.map_eq_cons_iff.1 h2
  have hA := h l₁ e l rfl
  subst h1 he
  cases e with
  | input j => trivial
  | output δ o =>
    exact ⟨l₁, .output δ o, by rw [List.map_map]; exact (List.map_congr_left
      (fun e _ => (eraseC_eraseC e).symm)), rfl, hA⟩

/-- The empty-basis system applies no commitment. -/
theorem eraseSys_eps {S : Sys sq} {i : J} {es : List (SEvent sq)} {ρ : State sq}
    (h : Produces (eraseSys S) i es ρ) : ∀ γ o, SEvent.output γ o ∈ es → γ = [] := by
  intro γ o hm
  cases γ with
  | nil => rfl
  | cons c _ => exact (sysExec_basis h.1 _ _ hm c List.mem_cons_self).elim

/-- Current input after a history: the last input, or the initial one. -/
def lastIn : J → List (SEvent sq) → J
  | i, [] => i
  | _, .input j :: l => lastIn j l
  | i, .output _ _ :: l => lastIn i l

theorem lastIn_eraseC (i : J) (l : List (SEvent sq)) : lastIn i (l.map eraseC) = lastIn i l := by
  induction l generalizing i with
  | nil => rfl
  | cons e l ih => cases e <;> exact ih _

theorem sysExec_lastIn {B : Basis sq} {σ ρ : State sq} {es : List (SEvent sq)}
    (h : SysExec B σ es ρ) : ρ.cur = lastIn σ.cur es := by
  induction h with
  | nil => rfl
  | @cons σ τ ρ e es hs _ ih =>
    cases e with
    | input j =>
      match hs with
      | .input (.input _ _ _ _ hc _) => rw [ih, hc]; rfl
    | output γ o => rw [ih, (containment hs).1]; rfl

end Systems

/-! ### General stores: Proper Coordination

From here on the store is any ordered relational specification
`sk : Spec M O` satisfying Lifted Monotonicity (used through the
common-expansion condition).  The function case is `sk = graph f` with `f`
monotone (`graph_commonExpansion`). -/

section General
variable {sk : Spec M O}

theorem graph_commonExpansion (hf : Monotone f) : (graph f).CommonExpansion :=
  (liftedMono_iff_commonExpansion _).1 ((graph_liftedMono_iff f).2 hf)

/-- Image of a `𝒫`-state through the store: the composite state whose table
joins `𝒫`'s table with `𝒦`'s, `{(k,x) : ∃ m, (k,m) ∈ R ∧ (m,x) ∈ K}`. -/
def imgK (sk : Spec M O) (σ : State sp) : State (seq sp sk) where
  cur := σ.cur
  R := fun k x => ∃ m, σ.R k m ∧ sk.S m x
  sub := fun k _ ⟨m, hm, hx⟩ => ⟨m, σ.sub k m hm, hx⟩
  hasCur := let ⟨m, hm⟩ := σ.hasCur; let ⟨x, hx⟩ := sk.total m; ⟨x, m, hm, hx⟩
  above := fun k _ ⟨m, hm, _⟩ => σ.above k m hm

/-- The image of the canonical state is the canonical state. -/
theorem imgK_canon (sk : Spec M O) (i : I) : imgK sk (canon sp i) = canon (seq sp sk) i := by
  refine State.ext' rfl ?_
  funext k o; apply propext
  show (∃ m, (sp.S k m ∧ i ≼ k) ∧ sk.S m o) ↔ ((∃ m, sp.S k m ∧ sk.S m o) ∧ i ≼ k)
  exact ⟨fun ⟨m, ⟨h, hk⟩, ho⟩ => ⟨⟨m, h, ho⟩, hk⟩, fun ⟨⟨m, h, ho⟩, hk⟩ => ⟨m, ⟨h, hk⟩, ho⟩⟩

/-- **A commitment-free output of `𝒫` maps to commitment-free outputs of the
composite.**  If `𝒦` satisfies the common-expansion condition and `m` is
exposable at `σ`, every `o ∈ K(m)` is exposable at the image of `σ`. -/
theorem cf_stepK (hC : sk.CommonExpansion) {σ : State sp} {m : M} (hexp : Exposable σ m)
    {o : O} (ho : sk.S m o) : Exposable (imgK sk σ) o := by
  rintro k x ⟨m', hm', hx⟩ _
  have hrows : ∀ r ∈ [(m, o), (m', x)], sk.S r.1 r.2 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ho
    · exact hx
  have hbd : ∀ j, m ≼ j → m' ≼ j → ∀ r ∈ [(m, o), (m', x)], r.1 ≼ j := by
    intro j h1 h2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h1
    · exact h2
  have h1 : (m, o) ∈ [(m, o), (m', x)] := List.mem_cons_self
  have h2 : (m', x) ∈ [(m, o), (m', x)] := List.mem_cons_of_mem _ List.mem_cons_self
  by_cases hmm : m ≼ m'
  · obtain ⟨u, hu, hall⟩ := hC _ hrows m' (hbd m' hmm (PO.refl _))
    exact ⟨u, ⟨m', hm', hu⟩, hall _ h1, hall _ h2⟩
  · obtain ⟨w, hw, hmw, hm'w⟩ := hexp k m' hm' hmm
    obtain ⟨u, hu, hall⟩ := hC _ hrows w (hbd w hmw hm'w)
    exact ⟨u, ⟨w, hw, hu⟩, hall _ h1, hall _ h2⟩

/-- **The store finds a row at every later input.**  At a run state of a
specification satisfying the common-expansion condition, every input above
the current one has a surviving row. -/
theorem row_at (hC : sk.CommonExpansion) {τ : State sk} (hτ : IsRun τ) {j : M}
    (hj : τ.cur ≼ j) : ∃ u, τ.R j u := by
  obtain ⟨v, hv⟩ := τ.hasCur
  obtain ⟨u, hu, hall⟩ := hC [(τ.cur, v)]
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact τ.sub _ _ hv) j
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hj)
  exact ⟨u, run_survive hτ hj hu hv (hall _ List.mem_cons_self)⟩

theorem isRun_step {J X : Type} [PO J] [PO X] {sq : Spec J X} {τ ρ : State sq} {e : Event J X}
    (h : IsRun τ) (hs : Step τ e ρ) : IsRun ρ := by
  obtain ⟨i, es, hx⟩ := h
  exact ⟨i, es ++ [e], (Dist.exec_append _ _).2 ⟨τ, hx, .cons hs (.nil _)⟩⟩

theorem sysStep_output_inv {J X : Type} [PO J] [PO X] {sq : Spec J X} {B : Basis sq}
    {σ τ : State sq} {γ : List (Commitment sq)} {o : X} (h : SysStep B σ (.output γ o) τ) :
    ∃ σc, (∀ c ∈ γ, B c) ∧ ApplySeq γ σ σc ∧ σc.R σc.cur o ∧ Exposable σc o ∧
      τ.cur = σ.cur ∧ τ.R = outputTable σc o := by
  cases h with
  | output hB hγ ho hexp hc hR => exact ⟨_, hB, hγ, ho, hexp, hc, hR⟩

/-- An empty-basis step is a step of the transition system of Sections 2–3. -/
theorem sysStep_empty_step {J X : Type} [PO J] [PO X] {sq : Spec J X} {σ τ : State sq}
    {e : SEvent sq} (h : SysStep (fun _ => False) σ e τ) : Step σ e.erase τ := by
  cases h with
  | input hs => exact hs
  | output hb hγ ho _ hcur hR =>
    cases hγ with
    | nil => exact Step.output _ _ _ ho hcur hR
    | cons _ _ => exact (hb _ List.mem_cons_self).elim

theorem sysExec_empty_exec {J X : Type} [PO J] [PO X] {sq : Spec J X} {σ τ : State sq}
    {es : List (SEvent sq)} (h : SysExec (fun _ => False) σ es τ) :
    Exec σ (es.map SEvent.erase) τ := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (sysStep_empty_step hs) ih

theorem isRun_sysExec_empty {J X : Type} [PO J] [PO X] {sq : Spec J X} {σ τ : State sq}
    {es : List (SEvent sq)} (h : SysExec (fun _ => False) σ es τ) (hσ : IsRun σ) : IsRun τ := by
  induction h with
  | nil => exact hσ
  | cons hs _ ih => exact ih (isRun_step hσ (sysStep_empty_step hs))

/-! #### Guarded composite runs -/

/-- The store's trace after its first output: for each later upstream output
`m`, receive it and answer with `o`. -/
def storeTr : List (M × O) → List (Event M O)
  | [] => []
  | (m, o) :: ps => .input m :: .output o :: storeTr ps

/-- `tr` is a store trace on upstream outputs `l`: starting at the first
output `m`, it answers `m`, then receives and answers each later output, up to
a prefix of `l`. -/
def Shaped (l : List M) (m : M) (tr : List (Event M O)) : Prop :=
  ∃ o ps, (m :: ps.map Prod.fst) <+: l ∧ tr = .output o :: storeTr ps

/-- **Guarded composite run.**  The upstream can emit `l` (`U l`), which starts
with `m`, and the store's system produces a run from `σ_𝒦(m)` on a prefix of
`l`.  For an upstream system `P`, `U = P.emits`. -/
def GRun (U : List M → Prop) (K : Sys sk) (l : List M) (m : M) (esK : List (SEvent sk)) : Prop :=
  U l ∧ Shaped l m (esK.map SEvent.erase) ∧ ∃ ρK, Produces K m esK ρK

/-- The output sequences that a system's produced runs emit. -/
def Sys.emits (P : Sys sp) (l : List M) : Prop := ∃ i es ρ, Produces P i es ρ ∧ emitted es = l

/-- The store's reference runs `𝓡`: runs of the specification `𝒦` on output
sequences the upstream can emit. -/
def SRun (U : List M → Prop) (sk : Spec M O) (m : M) (tr : List (Event M O)) : Prop :=
  ∃ l τ, U l ∧ Shaped l m tr ∧ Exec (canon sk m) tr τ

/-- Some reference run accepts the input `k`. -/
def Accepts (U : List M → Prop) (sk : Spec M O) (k : M) : Prop :=
  ∃ m tr, SRun U sk m tr ∧ (k = m ∨ Event.input k ∈ tr)

/-- Some reference run emits `x` at the input `k`. -/
def EmitsAt (U : List M → Prop) (sk : Spec M O) (k : M) (x : O) : Prop :=
  ∃ m tr₁ tr₂ τ, SRun U sk m (tr₁ ++ .output x :: tr₂) ∧ Exec (canon sk m) tr₁ τ ∧ τ.cur = k

/-- Commitments taking the store from `σ` to `σc` are **contradicted**
(Def. `def:coordination`, with `𝓡` the runs of `𝒦` on what the upstream can
emit): they seal an input some reference run accepts, or remove an output
some reference run emits at that input. -/
def Contradicted (U : List M → Prop) (σ σc : State sk) : Prop :=
  (∃ k, (∃ x, σ.R k x) ∧ (∀ x, ¬ σc.R k x) ∧ Accepts U sk k) ∨
  (∃ k x, σ.R k x ∧ ¬ σc.R k x ∧ EmitsAt U sk k x)

/-- **The store coordinates redundantly**: in some guarded composite run, a
store output event `Out_δ(x)` applies commitments that are contradicted. -/
def Redundant (U : List M → Prop) (K : Sys sk) : Prop :=
  ∃ l m esK a δ x b σ σc, GRun U K l m esK ∧ esK = a ++ .output δ x :: b ∧
    SysExec K.basis (canon sk m) a σ ∧ ApplySeq δ σ σc ∧ Contradicted U σ σc

/-- **At most once**: the store does not coordinate redundantly. -/
def AtMostOnce (U : List M → Prop) (K : Sys sk) : Prop := ¬ Redundant U K

/-- **At least once.**  Whenever the composite needs a commitment to emit some
`o ∈ K(m)` at the image of `𝒫`'s state, `𝒫`'s output event for `m` applies
one. -/
def AtLeastOnce (B : Basis sp) (sk : Spec M O) : Prop :=
  ∀ (σ τ : State sp) γ m, SysStep B σ (.output γ m) τ → ∀ o, sk.S m o →
    ¬ Exposable (imgK sk σ) o → γ ≠ []

/-- **Proper Coordination**: the store coordinates at most once and `𝒫` at
least once. -/
def Proper (P : Sys sp) (K : Sys sk) : Prop := AtMostOnce P.emits K ∧ AtLeastOnce P.basis sk

/-- **At least once always holds** when `𝒦` satisfies Lifted Monotonicity,
under any basis of `𝒫`. -/
theorem at_least_once (hC : sk.CommonExpansion) (B : Basis sp) : AtLeastOnce B sk := by
  intro σ τ γ m hs o ho hne hγ
  subst hγ
  exact hne (cf_stepK hC (eps_step_iff.1 hs).2.1 ho)

/-- With `𝒦` Lifted-Monotone, Proper Coordination is exactly at most once. -/
theorem proper_iff (hC : sk.CommonExpansion) (P : Sys sp) (K : Sys sk) :
    Proper P K ↔ AtMostOnce P.emits K :=
  ⟨fun h => h.1, fun h => ⟨h, at_least_once hC P.basis⟩⟩

theorem grun_mono {U U' : List M → Prop} (hU : ∀ l, U l → U' l) {K : Sys sk} {l : List M}
    {m : M} {esK : List (SEvent sk)} (h : GRun U K l m esK) : GRun U' K l m esK :=
  ⟨hU l h.1, h.2⟩

/-- A store whose produced runs apply no commitment never coordinates
redundantly. -/
theorem atMostOnce_of_eps {U : List M → Prop} {K : Sys sk}
    (h : ∀ m esK ρ, Produces K m esK ρ → ∀ γ x, SEvent.output γ x ∈ esK → γ = []) :
    AtMostOnce U K := by
  rintro ⟨l, m, esK, a, δ, x, b, σ, σc, ⟨_, _, ρK, hK⟩, rfl, _, hδ, hc⟩
  have := h m _ _ hK δ x (List.mem_append_right _ List.mem_cons_self)
  subst this
  cases hδ
  rcases hc with ⟨k, ⟨x, h1⟩, h2, _⟩ | ⟨k, x, h1, h2, _⟩
  · exact h2 x h1
  · exact h2 h1

/-- The empty-basis store, whose strategy allows every event. -/
def noStore (sk : Spec M O) : Sys sk := Sys.free (fun _ => False)

/-- A store under the empty basis never coordinates redundantly. -/
theorem noStore_atMostOnce (U : List M → Prop) (sk : Spec M O) : AtMostOnce U (noStore sk) :=
  atMostOnce_of_eps fun _ _ _ hK γ _ hm => by
    cases γ with
    | nil => rfl
    | cons c _ => exact (sysExec_basis hK.1 _ _ hm c List.mem_cons_self).elim

/-- The outputs a system emits form a chain. -/
theorem emits_chain {P : Sys sp} {l : List M} (h : P.emits l) : ChainFrom none l := by
  obtain ⟨_, es, _, hP, rfl⟩ := h
  exact emitted_chain hP.1 none (fun _ h => by cases h)

/-- From a run state, the store answers every chain of later inputs without
commitment. -/
theorem follow (hC : sk.CommonExpansion) :
    ∀ (ms : List M) (τ : State sk), IsRun τ → ChainFrom (some τ.cur) ms →
      ∃ ps ρ, ps.map Prod.fst = ms ∧ ExecCF τ (storeTr ps) ρ ∧ IsRun ρ
  | [], τ, hτ, _ => ⟨[], τ, rfl, .nil _, hτ⟩
  | m' :: ms, τ, hτ, ⟨hle, hc⟩ => by
    obtain ⟨u, hu⟩ := row_at hC hτ hle
    let τ1 := inState τ m' u hu
    have h1 : Step τ (.input m') τ1 := Step.input τ τ1 m' ⟨u, hu⟩ rfl rfl
    have hr1 : IsRun τ1 := isRun_step hτ h1
    obtain ⟨o, ho⟩ := τ1.hasCur
    let τ2 := outState τ1 o ho
    have h2 : Step τ1 (.output o) τ2 := Step.output τ1 τ2 o ho rfl rfl
    obtain ⟨ps, ρ, hps, hx, hρ⟩ := follow hC ms τ2 (isRun_step hr1 h2) hc
    exact ⟨(m', o) :: ps, ρ, by simp [hps],
      .input h1 (.output h2 (commonExpansion_exposable hC hr1 ho) hx), hρ⟩

/-- **The empty-basis store follows every chain.**  Fed a chain `m :: ms`, it
answers `m` and every later input without commitment. -/
theorem store_follows (hC : sk.CommonExpansion) {m : M} {ms : List M}
    (hc : ChainFrom (some m) ms) :
    ∃ o ps esK ρ, ps.map Prod.fst = ms ∧ esK.map SEvent.erase = .output o :: storeTr ps ∧
      Produces (noStore sk) m esK ρ ∧ IsRun ρ := by
  have hr0 : IsRun (canon sk m) := ⟨m, [], .nil _⟩
  obtain ⟨o, ho⟩ := (canon sk m).hasCur
  let τ := outState (canon sk m) o ho
  have h0 : Step (canon sk m) (.output o) τ := Step.output _ τ o ho rfl rfl
  obtain ⟨ps, ρ, hps, hx, hρ⟩ := follow hC ms τ (isRun_step hr0 h0) hc
  obtain ⟨esK, he, _, hK⟩ := execCF_coordFree (fun _ => False)
    (.output h0 (commonExpansion_exposable hC hr0 ho) hx)
  exact ⟨o, ps, esK, ρ, hps, he, ⟨hK, compliant_free _⟩, hρ⟩

/-- **The empty-basis store follows the upstream**: for every output sequence
`m :: ms` the upstream can emit, if it is a chain, there is a guarded composite
run in which the store answers every output. -/
theorem noStore_follows (hC : sk.CommonExpansion) {U : List M → Prop} {m : M} {ms : List M}
    (hU : U (m :: ms)) (hc : ChainFrom none (m :: ms)) :
    ∃ esK o ps, GRun U (noStore sk) (m :: ms) m esK ∧ ps.map Prod.fst = ms ∧
      esK.map SEvent.erase = .output o :: storeTr ps := by
  obtain ⟨o, ps, esK, ρ, hps, he, hK, _⟩ := store_follows hC (sk := sk) hc
  exact ⟨esK, o, ps, ⟨hU, ⟨o, ps, by rw [hps]; exact List.prefix_refl _, he⟩, ρ, hK⟩, hps, he⟩

/-- **Theorem (Proper Coordination).**  If `𝒦` satisfies Lifted Monotonicity,
then for any system of `𝒫` the guarded composite with the empty-basis store
is proper. -/
theorem guarded_proper (hC : sk.CommonExpansion) (P : Sys sp) : Proper P (noStore sk) :=
  ⟨noStore_atMostOnce _ sk, at_least_once hC P.basis⟩

/-- **`𝒫` must commit when the composite is not monotone.**  If `𝒦` satisfies
Lifted Monotonicity and `𝒦 ∘ 𝒫` does not, some composite output `o` is not
exposable at a canonical state `σ(i)`, and no `m` with `o ∈ K(m)` is exposable
at `σ_𝒫(i)`: under the empty basis `𝒫` can never emit one there. -/
theorem composite_needs_commit (hC : sk.CommonExpansion) (hnot : ¬ (seq sp sk).LiftedMono) :
    ∃ i m o, sp.S i m ∧ sk.S m o ∧ ¬ Exposable (canon (seq sp sk) i) o ∧
      (∀ m', sp.S i m' → sk.S m' o → ¬ Exposable (canon sp i) m') ∧
      ∀ γ m' τ, SysStep (fun _ => False) (canon sp i) (.output γ m') τ → ¬ sk.S m' o := by
  have hall : ¬ ∀ i o, (seq sp sk).S i o → Exposable (canon (seq sp sk) i) o := fun h =>
    hnot ((liftedMono_iff_commonExpansion _).2 (canon_exposable_commonExpansion h))
  obtain ⟨i, o, ⟨m, hm, hmo⟩, hne⟩ : ∃ i o, (seq sp sk).S i o ∧
      ¬ Exposable (canon (seq sp sk) i) o :=
    Classical.byContradiction fun hn =>
      hall fun i o h => Classical.byContradiction fun he => hn ⟨i, o, h, he⟩
  have hcf : ∀ m', Exposable (canon sp i) m' → sk.S m' o → Exposable (canon (seq sp sk) i) o := by
    intro m' he ho; rw [← imgK_canon sk i]; exact cf_stepK hC he ho
  refine ⟨i, m, o, hm, hmo, hne, fun m' _ ho he => hne (hcf m' he ho), ?_⟩
  intro γ m' τ hs ho
  cases γ with
  | cons c _ =>
    cases hs with
    | output hb _ _ _ _ _ => exact hb c List.mem_cons_self
  | nil => exact hne (hcf m' (eps_step_iff.1 hs).2.1 ho)

/-! #### Guarded composite runs are runs of the composite -/

/-- The composite trace: `𝒫`'s events, with its `r`-th output replaced by the
store's `r`-th output. -/
def merge : List (SEvent sp) → List O → List (Event I O)
  | [], _ => []
  | .input j :: es, os => .input j :: merge es os
  | .output _ _ :: es, o :: os => .output o :: merge es os
  | .output _ _ :: es, [] => merge es []

/-- Lockstep invariant: same current input, and the composite table contains
the join of `𝒫`'s table with the table `T`. -/
def Inv (σ : State sp) (T : Table M O) (ρ : State (seq sp sk)) : Prop :=
  ρ.cur = σ.cur ∧ ∀ k m x, σ.R k m → T m x → ρ.R k x

theorem emitted_split : ∀ {es : List (SEvent sp)} {m : M} {ms : List M},
    emitted es = m :: ms → ∃ es₀ γ es₁, es = es₀ ++ .output γ m :: es₁ ∧ emitted es₀ = [] ∧
      emitted es₁ = ms
  | [], _, _, h => by cases h
  | .input j :: es, m, ms, h => by
    obtain ⟨es₀, γ, es₁, rfl, h0, h1⟩ := emitted_split (es := es) h
    exact ⟨.input j :: es₀, γ, es₁, rfl, h0, h1⟩
  | .output γ m' :: es, m, ms, h => by
    simp only [emitted, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], γ, es, rfl, rfl, rfl⟩

theorem emitted_prefix : ∀ {es : List (SEvent sp)} {l : List M}, l <+: emitted es →
    ∃ es₀ es₁, es = es₀ ++ es₁ ∧ emitted es₀ = l
  | [], l, h => ⟨[], [], rfl, (List.prefix_nil.1 h).symm⟩
  | .input j :: es, l, h => by
    obtain ⟨es₀, es₁, rfl, h0⟩ := emitted_prefix (es := es) h
    exact ⟨.input j :: es₀, es₁, rfl, h0⟩
  | .output γ m :: es, [], _ => ⟨[], _, rfl, rfl⟩
  | .output γ m :: es, a :: l, h => by
    obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.1 h
    obtain ⟨es₀, es₁, rfl, h0⟩ := emitted_prefix (es := es) h'
    exact ⟨.output γ a :: es₀, es₁, rfl, by simp [emitted, h0]⟩

omit [PO O] in
theorem merge_split : ∀ {es₀ : List (SEvent sp)} (γ : List (Commitment sp)) (m : M)
    (es₁ : List (SEvent sp)) (o : O) (os : List O), emitted es₀ = [] →
    merge (es₀ ++ .output γ m :: es₁) (o :: os) = merge es₀ [] ++ .output o :: merge es₁ os
  | [], _, _, _, _, _, _ => rfl
  | .input j :: es₀, γ, m, es₁, o, os, h => by
    simp only [List.cons_append, merge]
    rw [merge_split (es₀ := es₀) γ m es₁ o os h]
  | .output _ _ :: _, _, _, _, _, _, h => by cases h

/-- Phase before `𝒫`'s first output: the composite follows `𝒫`'s inputs. -/
theorem merge_inputs {B : Basis sp} {σ ρ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es ρ) (he : emitted es = []) :
    ∀ ρ' : State (seq sp sk), Inv σ sk.S ρ' →
      ∃ ρ'', Exec ρ' (merge es []) ρ'' ∧ Inv ρ sk.S ρ'' := by
  induction h with
  | nil σ => exact fun ρ' hI => ⟨ρ', .nil _, hI⟩
  | @cons σ τ ρ e es hs _ ih =>
    intro ρ' ⟨hc, hI⟩
    cases e with
    | output γ m => cases he
    | input j =>
      match hs with
      | .input (.input _ _ _ hleg hcur hR) =>
        obtain ⟨m, hm⟩ := hleg
        obtain ⟨x, hx⟩ := sk.total m
        have hρ : ρ'.R j x := hI j m x hm hx
        let ρ1 := inState ρ' j x hρ
        have hst : Step ρ' (.input j) ρ1 := Step.input ρ' ρ1 j ⟨x, hρ⟩ rfl rfl
        have hI' : Inv τ sk.S ρ1 := by
          refine ⟨hcur.symm, fun k m' x' hk hx' => ?_⟩
          rw [hR] at hk
          exact ⟨hI k m' x' hk.1 hx', hk.2⟩
        obtain ⟨ρ'', hx2, hI''⟩ := ih he ρ1 hI'
        exact ⟨ρ'', .cons hst hx2, hI''⟩

/-- Phase after the store has started: lockstep of `𝒫`, the empty-basis
store, and the composite. -/
theorem merge_lockstep (hC : sk.CommonExpansion) {B : Basis sp} {σ ρ : State sp}
    {es : List (SEvent sp)} (h : SysExec B σ es ρ) :
    ∀ (ps : List (M × O)) (τK ρK : State sk) (esK : List (SEvent sk)) (ρ' : State (seq sp sk)),
      emitted es = ps.map Prod.fst → SysExec (fun _ => False) τK esK ρK →
      esK.map SEvent.erase = storeTr ps → IsRun τK → (∀ k m, σ.R k m → τK.cur ≼ m) →
      Inv σ τK.R ρ' →
      ∃ ρ'', Exec ρ' (merge es (ps.map Prod.snd)) ρ'' ∧ Inv ρ ρK.R ρ'' ∧
        ∀ k m, ρ.R k m → ρK.cur ≼ m := by
  induction h with
  | nil σ =>
    intro ps τK ρK esK ρ' he hK htr _ habove hI
    have hps : ps = [] := by
      cases ps with
      | nil => rfl
      | cons _ _ => cases he
    subst hps
    have : esK = [] := List.map_eq_nil_iff.1 htr
    subst this
    cases hK
    exact ⟨ρ', .nil _, hI, habove⟩
  | @cons σ τ ρ e es hs _ ih =>
    intro ps τK ρK esK ρ' he hK htr hτK habove ⟨hc, hI⟩
    cases e with
    | input j =>
      match hs with
      | .input (.input _ _ _ hleg hcur hR) =>
        obtain ⟨m, hm⟩ := hleg
        obtain ⟨x, hx⟩ := row_at hC hτK (habove j m hm)
        have hρ : ρ'.R j x := hI j m x hm hx
        let ρ1 := inState ρ' j x hρ
        have hst : Step ρ' (.input j) ρ1 := Step.input ρ' ρ1 j ⟨x, hρ⟩ rfl rfl
        have hI' : Inv τ τK.R ρ1 := by
          refine ⟨hcur.symm, fun k m' x' hk hx' => ?_⟩
          rw [hR] at hk
          exact ⟨hI k m' x' hk.1 hx', hk.2⟩
        have habove' : ∀ k m, τ.R k m → τK.cur ≼ m := by
          intro k m hk; rw [hR] at hk; exact habove k m hk.1
        obtain ⟨ρ'', hx2, hI'', hab⟩ := ih ps τK ρK esK ρ1 he hK htr hτK habove' hI'
        exact ⟨ρ'', .cons hst hx2, hI'', hab⟩
    | output γ m =>
      obtain ⟨hcurτ, hσm, hin, _⟩ := containment hs
      cases ps with
      | nil => cases he
      | cons p ps =>
        obtain ⟨m₀, o⟩ := p
        simp only [emitted, List.map_cons, List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        obtain ⟨e1, esK1, rfl, he1, htr1⟩ := List.map_eq_cons_iff.1 htr
        obtain ⟨e2, esK2, rfl, he2, htr2⟩ := List.map_eq_cons_iff.1 htr1
        cases e1 with
        | output _ _ => cases he1
        | input m1 =>
        cases he1
        cases e2 with
        | input _ => cases he2
        | output γ2 o2 =>
        cases he2
        cases hK with
        | @cons _ τ1 _ _ _ hs1 hK1 =>
        cases hK1 with
        | @cons _ τ2 _ _ _ hs2 hK2 =>
        have st1 : Step τK (.input m) τ1 := sysStep_empty_step hs1
        have st2 : Step τ1 (.output o) τ2 := sysStep_empty_step hs2
        have ⟨hc1, hR1⟩ : τ1.cur = m ∧ τ1.R = inputTable τK m := by
          cases st1 with
          | input _ _ _ hc hR => exact ⟨hc, hR⟩
        have ⟨ho2, hc2, hR2⟩ : τ1.R τ1.cur o ∧ τ2.cur = τ1.cur ∧ τ2.R = outputTable τ1 o := by
          cases st2 with
          | output _ _ ho hc hR => exact ⟨ho, hc, hR⟩
        have hmo : τK.R m o := by
          have := ho2; rw [hR1, hc1] at this; exact this.1
        have hρo : ρ'.R ρ'.cur o := by rw [hc]; exact hI _ _ _ hσm hmo
        let ρ1 := outState ρ' o hρo
        have hst : Step ρ' (.output o) ρ1 := Step.output ρ' ρ1 o hρo rfl rfl
        have hI' : Inv τ τ2.R ρ1 := by
          refine ⟨by show ρ'.cur = τ.cur; rw [hc, hcurτ], fun k m' x hk hx => ?_⟩
          obtain ⟨hk1, _⟩ := hin k m' hk
          rw [hR2] at hx
          obtain ⟨hx1, hox⟩ := hx
          rw [hR1] at hx1
          exact ⟨hI k m' x hk1 hx1.1, hox⟩
        have habove' : ∀ k m', τ.R k m' → τ2.cur ≼ m' := by
          intro k m' hk; rw [hc2, hc1]; exact (hin k m' hk).2
        have hr2 : IsRun τ2 := isRun_step (isRun_step hτK st1) st2
        obtain ⟨ρ'', hx2, hI'', hab⟩ := ih ps τ2 ρK esK2 ρ1 he hK2 htr2 hr2 habove' hI'
        exact ⟨ρ'', .cons hst hx2, hI'', hab⟩

/-- **Guarded runs are runs of the composite.**  Let `𝒦` satisfy Lifted
Monotonicity, let `𝒫` run under any basis from `σ_𝒫(i)`, emitting `m :: ms`,
and let the store run under the empty basis from `σ_𝒦(m)`, answering `m`
with `o` and each later output. Then `𝒫`'s run, with its outputs replaced by
the store's answers, is a run of `𝒦 ∘ 𝒫` from `σ(i)`.  Its table contains
the join of `𝒫`'s final table with the store's, and the store's state is a run
state below every remaining output of `𝒫`. -/
theorem composite_run (hC : sk.CommonExpansion) {B : Basis sp} {i : I} {es : List (SEvent sp)}
    {ρ : State sp} (hP : SysExec B (canon sp i) es ρ) {m : M} {ms : List M}
    (he : emitted es = m :: ms) {o : O} {ps : List (M × O)} (hps : ps.map Prod.fst = ms)
    {esK : List (SEvent sk)} {ρK : State sk} (hK : SysExec (fun _ => False) (canon sk m) esK ρK)
    (htr : esK.map SEvent.erase = .output o :: storeTr ps) :
    ∃ ρ', Exec (canon (seq sp sk) i) (merge es (o :: ps.map Prod.snd)) ρ' ∧ ρ'.cur = ρ.cur ∧
      (∀ k m x, ρ.R k m → ρK.R m x → ρ'.R k x) ∧ IsRun ρK ∧ ∀ k m, ρ.R k m → ρK.cur ≼ m := by
  obtain ⟨es₀, γ, es₁, rfl, h0, h1⟩ := emitted_split he
  obtain ⟨σ₀, hx0, hx1⟩ := sysExec_append_inv hP
  cases hx1 with
  | @cons _ τ₀ _ _ _ hs hx1 =>
  have hI0 : Inv (canon sp i) sk.S (canon (seq sp sk) i) :=
    ⟨rfl, fun k m' x hk hx => ⟨⟨m', hk.1, hx⟩, hk.2⟩⟩
  obtain ⟨ρ₀, hxA, hc0, hIA⟩ := merge_inputs (sk := sk) hx0 h0 _ hI0
  obtain ⟨hcurτ, hσm, hin, _⟩ := containment hs
  obtain ⟨e1, esK1, rfl, he1, htr1⟩ := List.map_eq_cons_iff.1 htr
  cases e1 with
  | input _ => cases he1
  | output γ1 o1 =>
  cases he1
  cases hK with
  | @cons _ τK _ _ _ hs1 hK1 =>
  match sysStep_empty_step hs1 with
  | .output _ _ _ ho1 hc1 hR1 =>
    have hρo : ρ₀.R ρ₀.cur o := by rw [hc0]; exact hIA _ _ _ hσm ho1.1
    let ρ1 := outState ρ₀ o hρo
    have hst : Step ρ₀ (.output o) ρ1 := Step.output ρ₀ ρ1 o hρo rfl rfl
    have hI1 : Inv τ₀ τK.R ρ1 := by
      refine ⟨by show ρ₀.cur = τ₀.cur; rw [hc0, hcurτ], fun k m' x hk hx => ?_⟩
      obtain ⟨hk1, _⟩ := hin k m' hk
      rw [hR1] at hx
      exact ⟨hIA k m' x hk1 hx.1.1, hx.2⟩
    have hab1 : ∀ k m', τ₀.R k m' → τK.cur ≼ m' := by
      intro k m' hk; rw [hc1]; exact (hin k m' hk).2
    have hr1 : IsRun τK := isRun_step ⟨m, [], .nil _⟩ (sysStep_empty_step hs1)
    obtain ⟨ρ', hxB, ⟨hcB, hIB⟩, hab⟩ :=
      merge_lockstep hC hx1 ps τK ρK esK1 ρ1 (by rw [h1, hps]) hK1 htr1 hr1 hab1 hI1
    refine ⟨ρ', ?_, hcB, hIB, isRun_sysExec_empty hK1 hr1, hab⟩
    rw [merge_split γ m es₁ o _ h0]
    exact (Dist.exec_append _ _).2 ⟨ρ₀, hxA, .cons hst hxB⟩

/-- **Guarded confluence.**  Let `𝒦` satisfy Lifted Monotonicity.  Given
triples of a `𝒫`-state, a store run state below every output in `𝒫`'s table,
and a composite run state containing the join of their tables: if the
`𝒫`-states can be continued (under any bases) to one state with current input
`j`, the composite states are confluent at `j`. -/
theorem guarded_confluentK (hC : sk.CommonExpansion)
    (fam : List (State sp × State sk × State (seq sp sk)))
    (hrun : ∀ p ∈ fam, IsRun p.2.2) (hK : ∀ p ∈ fam, IsRun p.2.1)
    (hsub : ∀ p ∈ fam, ∀ k m x, p.1.R k m → p.2.1.R m x → p.2.2.R k x)
    (habove : ∀ p ∈ fam, ∀ k m, p.1.R k m → p.2.1.cur ≼ m)
    (j : I) (hj : ∀ p ∈ fam, p.2.2.cur ≼ j)
    (hP : ∃ τ : State sp, τ.cur = j ∧ ∀ p ∈ fam, ∃ (B : Basis sp) (es : List (SEvent sp)),
      SysExec B p.1 es τ) :
    ConfluentAt (fam.map fun p => p.2.2) j := by
  obtain ⟨τ, hτ, hall⟩ := hP
  obtain ⟨m, hm⟩ := τ.hasCur
  rw [hτ] at hm
  have hm' : ∀ p ∈ fam, p.1.R j m := fun p hp => by
    obtain ⟨B, es, hx⟩ := hall p hp; exact hx.sub _ _ hm
  let pick : State sp × State sk × State (seq sp sk) → M × O :=
    fun p => (p.2.1.cur, p.2.1.hasCur.choose)
  obtain ⟨u, hu, hallu⟩ := hC (fam.map pick)
    (by
      intro r hr
      obtain ⟨p, _, rfl⟩ := List.mem_map.1 hr
      exact p.2.1.sub _ _ p.2.1.hasCur.choose_spec)
    m (by
      intro r hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
      exact habove p hp j m (hm' p hp))
  have hrun' : ∀ ρ ∈ fam.map (fun p => p.2.2), IsRun ρ := by
    intro ρ hρ; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hρ; exact hrun p hp
  have hj' : ∀ ρ ∈ fam.map (fun p => p.2.2), ρ.cur ≼ j := by
    intro ρ hρ; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hρ; exact hj p hp
  refine (survivor_test _ hrun' j hj').2 ⟨u, ⟨m, τ.sub _ _ hm, hu⟩, fun ρ hρ => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hρ
  have hv := p.2.1.hasCur.choose_spec
  have hpu : p.2.1.R m u :=
    run_survive (hK p hp) (habove p hp j m (hm' p hp)) hu hv
      (hallu (pick p) (List.mem_map.2 ⟨p, hp, rfl⟩))
  exact hsub p hp j m u (hm' p hp) hpu

/-! #### Replacing the store by one with the empty basis -/

/-- What the environment can observe of the store, given an upstream output
sequence `l` starting with `m`: the erased traces of the store parts of
guarded runs. -/
def Obs (U : List M → Prop) (K : Sys sk) (l : List M) (m : M) (tr : List (Event M O)) : Prop :=
  ∃ esK, GRun U K l m esK ∧ esK.map SEvent.erase = tr

/-- **Erasure, lockstep.**  If `𝒦` satisfies the common-expansion condition,
then from any run state `σ'` with the same current input whose table contains
`σ`'s, every store execution under any basis, with its commitments erased, is
an execution under the empty basis, and the containment persists after each
event. -/
theorem erase_lockstep (hC : sk.CommonExpansion) {BK : Basis sk} {σ ρ : State sk}
    {es : List (SEvent sk)} (h : SysExec BK σ es ρ) :
    ∀ σ' : State sk, IsRun σ' → σ'.cur = σ.cur → (∀ k u, σ.R k u → σ'.R k u) →
      ∃ ρ', SysExec (fun _ => False) σ' (es.map eraseC) ρ' ∧ IsRun ρ' ∧ ρ'.cur = ρ.cur ∧
        ∀ k u, ρ.R k u → ρ'.R k u := by
  induction h with
  | nil σ => exact fun σ' hr hc hs => ⟨σ', .nil _, hr, hc, hs⟩
  | @cons σ τ ρ e es hs _ ih =>
    intro σ' hr hc hsub
    cases e with
    | input j =>
      match hs with
      | .input (.input _ _ _ hleg hcur hR) =>
        obtain ⟨u, hu⟩ := hleg
        let τ' := inState σ' j u (hsub _ _ hu)
        have st : Step σ' (.input j) τ' := Step.input σ' τ' j ⟨u, hsub _ _ hu⟩ rfl rfl
        have hs' : ∀ k v, τ.R k v → τ'.R k v := by
          intro k v hv; rw [hR] at hv; exact ⟨hsub _ _ hv.1, hv.2⟩
        obtain ⟨ρ', hx, hr', hc', hs''⟩ := ih τ' (isRun_step hr st) hcur.symm hs'
        exact ⟨ρ', .cons (.input st) hx, hr', hc', hs''⟩
    | output γ x =>
      obtain ⟨hcur, hx, hin, _⟩ := containment hs
      have hx' : σ'.R σ'.cur x := by rw [hc]; exact hsub _ _ hx
      let τ' := outState σ' x hx'
      have st : Step σ' (.output x) τ' := Step.output σ' τ' x hx' rfl rfl
      have hst : SysStep (fun _ => False) σ' (.output [] x) τ' :=
        eps_step_iff.2 ⟨hx', commonExpansion_exposable hC hr hx', rfl, rfl⟩
      have hs' : ∀ k v, τ.R k v → τ'.R k v := by
        intro k v hv; obtain ⟨a, b⟩ := hin k v hv; exact ⟨hsub _ _ a, b⟩
      obtain ⟨ρ', hx2, hr', hc', hs''⟩ :=
        ih τ' (isRun_step hr st) (by show σ'.cur = τ.cur; rw [hc, hcur]) hs'
      exact ⟨ρ', .cons hst hx2, hr', hc', hs''⟩

/-- **(a) The replacement emits everything the original does.**  If `𝒦`
satisfies Lifted Monotonicity, every guarded composite run of a store system
`K` has, on the same upstream output sequence, a guarded composite run of
`eraseSys K` with the same observable trace, whose table contains the
original's.  Proper coordination is not needed. -/
theorem erase_simulates (hC : sk.CommonExpansion) {U : List M → Prop} {K : Sys sk}
    {l : List M} {m : M} {esK : List (SEvent sk)} (h : GRun U K l m esK) :
    GRun U (eraseSys K) l m (esK.map eraseC) ∧
      (esK.map eraseC).map SEvent.erase = esK.map SEvent.erase ∧
      ∀ ρK, Produces K m esK ρK → ∃ ρ', Produces (eraseSys K) m (esK.map eraseC) ρ' ∧
        IsRun ρ' ∧ ∀ k u, ρK.R k u → ρ'.R k u := by
  obtain ⟨hU, hS, ρK, hK⟩ := h
  have main : ∀ ρK, Produces K m esK ρK → ∃ ρ', Produces (eraseSys K) m (esK.map eraseC) ρ' ∧
      IsRun ρ' ∧ ∀ k u, ρK.R k u → ρ'.R k u := by
    intro ρK hK
    obtain ⟨ρ', hx, hr, _, hs⟩ := erase_lockstep hC hK.1 _ ⟨m, [], .nil _⟩ rfl (fun _ _ h => h)
    exact ⟨ρ', ⟨hx, compliant_eraseSys hK.2⟩, hr, hs⟩
  obtain ⟨ρ', hK', _⟩ := main ρK hK
  exact ⟨⟨hU, by rw [map_erase_eraseC]; exact hS, ρ', hK'⟩, map_erase_eraseC _, main⟩

theorem erase_obs (hC : sk.CommonExpansion) {U : List M → Prop} {K : Sys sk} {l : List M}
    {m : M} {tr : List (Event M O)} (h : Obs U K l m tr) : Obs U (eraseSys K) l m tr := by
  obtain ⟨esK, hg, rfl⟩ := h
  exact ⟨_, (erase_simulates hC hg).1, map_erase_eraseC _⟩

omit [PO M] [PO O] in
theorem mem_storeTr {j : M} : ∀ {ps : List (M × O)}, Event.input j ∈ storeTr ps →
    j ∈ ps.map Prod.fst
  | [], h => by cases h
  | (m₁, o₁) :: ps, h => by
    simp only [storeTr, List.mem_cons, Event.input.injEq, reduceCtorEq, false_or] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_storeTr h)

omit [PO M] [PO O] in
/-- A prefix of the store's trace ending at an output is the trace on a prefix
of its inputs. -/
theorem storeTr_prefix : ∀ (ps : List (M × O)) (o : O) (p : List (Event M O)) (x : O)
    (q : List (Event M O)), (Event.output o :: storeTr ps) = p ++ .output x :: q →
    ∃ ps₀ ps₁, ps = ps₀ ++ ps₁ ∧ p ++ [.output x] = .output o :: storeTr ps₀
  | ps, o, [], x, q, h => by
    simp only [List.nil_append, List.cons.injEq, Event.output.injEq] at h
    exact ⟨[], ps, rfl, by rw [h.1]; rfl⟩
  | [], o, e :: p, x, q, h => by simp [storeTr] at h
  | (m₁, o₁) :: ps, o, e :: p, x, q, h => by
    simp only [storeTr, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    cases p with
    | nil => simp at h
    | cons e₂ p =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨ps₀, ps₁, rfl, h'⟩ := storeTr_prefix ps o₁ p x q h
      exact ⟨(m₁, o₁) :: ps₀, ps₁, rfl, by simp only [List.cons_append, storeTr, h']⟩

omit [PO M] [PO O] in
/-- In a store trace every input is followed by an output. -/
theorem storeTr_next : ∀ (ps : List (M × O)) (o : O) (p : List (Event M O)) (j : M)
    (q : List (Event M O)), (Event.output o :: storeTr ps) = p ++ .input j :: q →
    ∃ x q', q = .output x :: q'
  | ps, o, [], j, q, h => by simp at h
  | [], o, e :: p, j, q, h => by simp [storeTr] at h
  | (m₁, o₁) :: ps, o, e :: p, j, q, h => by
    simp only [storeTr, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    cases p with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      exact ⟨o₁, _, h.2.symm⟩
    | cons e₂ p =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact storeTr_next ps o₁ p j q h

/-- The induction behind `erase_reflects`: follow the replacement's events,
building the original's, as long as the original never removes a row that a
reference run uses. -/
theorem reflect_aux {U : List M → Prop} {K : Sys sk} (hb : Blind K) (hl : Live K)
    (hirr : AtMostOnce U K) {l : List M} (hU : U l) {m : M} :
    ∀ (rest' a a' : List (SEvent sk)) (σ σ' ρ' : State sk),
      SysExec (fun _ => False) σ' rest' ρ' →
      Compliant (Allowed (eraseSys K) m) (a' ++ rest') →
      (∀ p γ x q, rest' = p ++ .output γ x :: q → ∀ τ, SysExec (fun _ => False) σ' p τ →
        EmitsAt U sk τ.cur x) →
      (∀ p j q, rest' = p ++ .input j :: q → ∃ γ x q', q = .output γ x :: q') →
      (∀ p e q, rest' = p ++ e :: q → (∃ γ x, e = .output γ x) →
        Shaped l m ((a' ++ (p ++ [e])).map SEvent.erase)) →
      SysExec K.basis (canon sk m) a σ → Compliant (Allowed K m) a →
      a.map eraseC = a'.map eraseC → σ.cur = σ'.cur →
      (∀ k x, EmitsAt U sk k x → σ'.R k x → σ.R k x) →
      ∃ rest ρ, SysExec K.basis σ rest ρ ∧ Compliant (Allowed K m) (a ++ rest) ∧
        rest.map eraseC = rest'.map eraseC := by
  intro rest'
  induction rest' with
  | nil =>
    intro a a' σ _ _ _ _ _ _ _ _ hc _ _ _
    exact ⟨[], σ, .nil σ, by simpa using hc, rfl⟩
  | cons e' rest'' ih =>
    intro a a' σ σ' ρ' hx' hc' hemit hnext hshape hx hc hac hcur hinv
    cases hx' with
    | @cons _ τ' _ _ _ hs' hrest' =>
    have hA : Allowed (eraseSys K) m a' e' := hc' a' e' rest'' rfl
    have hc'' : Compliant (Allowed (eraseSys K) m) ((a' ++ [e']) ++ rest'') := by
      rw [List.append_assoc]; exact hc'
    have hemit' : ∀ p γ x q, rest'' = p ++ .output γ x :: q →
        ∀ τ, SysExec (fun _ => False) τ' p τ → EmitsAt U sk τ.cur x :=
      fun p γ x q hq τ hp => hemit (e' :: p) γ x q (by rw [hq]; rfl) τ (.cons hs' hp)
    have hnext' : ∀ p j q, rest'' = p ++ .input j :: q → ∃ γ x q', q = .output γ x :: q' :=
      fun p j q hq => hnext (e' :: p) j q (by rw [hq]; rfl)
    have hshape' : ∀ p e q, rest'' = p ++ e :: q → (∃ γ x, e = .output γ x) →
        Shaped l m (((a' ++ [e']) ++ (p ++ [e])).map SEvent.erase) := by
      intro p e q hq hout
      have := hshape (e' :: p) e q (by rw [hq]; rfl) hout
      simpa using this
    have hae : a.map SEvent.erase = a'.map SEvent.erase := map_erase_of_eraseC hac
    cases e' with
    | input j =>
      cases hs' with
      | input hst =>
      match hst with
      | .input _ _ _ _ hcurτ hR =>
        obtain ⟨γ, x, q', rfl⟩ := hnext [] j rest'' rfl
        have hx2 : τ'.R τ'.cur x := by
          cases hrest' with
          | cons hs2 _ => exact (containment hs2).2.1
        rw [hcurτ, hR] at hx2
        have hE : EmitsAt U sk j x := by
          have := hemit [.input j] γ x q' rfl τ' (.cons (.input hst) (.nil _))
          rwa [hcurτ] at this
        have hσ : σ.R j x := hinv j x hE hx2.1
        let τ := inState σ j x hσ
        have hst' : SysStep K.basis σ (.input j) τ := .input (Step.input σ τ j ⟨_, hσ⟩ rfl rfl)
        have hinv' : ∀ k y, EmitsAt U sk k y → τ'.R k y → τ.R k y := by
          intro k y hk h; rw [hR] at h; exact ⟨hinv k y hk h.1, h.2⟩
        obtain ⟨rest, ρ, hx1, hc1, he1⟩ := ih (a ++ [SEvent.input j]) (a' ++ [SEvent.input j])
          τ τ' ρ' hrest' hc'' hemit' hnext' hshape' (sysExec_snoc hx hst')
          (compliant_snoc (e := SEvent.input j) hc trivial)
          (by simp only [List.map_append, hac]) hcurτ.symm hinv'
        refine ⟨.input j :: rest, ρ, .cons hst' hx1, ?_, ?_⟩
        · rw [List.append_assoc] at hc1; exact hc1
        · simp only [List.map_cons, he1]
    | output γ' x =>
      obtain ⟨pre, e₀, hpre, he₀, hK⟩ := hA
      cases e₀ with
      | input j => cases he₀
      | output δ x₀ =>
        simp only [eraseC, SEvent.output.injEq, true_and] at he₀
        subst he₀
        have hK' : K.strat m a (.output δ x₀) := hb m pre a _ (hpre.trans hac.symm) hK
        obtain ⟨hτ'cur, hx', hin', _⟩ := containment hs'
        have hE : EmitsAt U sk σ'.cur x₀ := hemit [] γ' x₀ rest'' rfl σ' (.nil _)
        have hσx : σ.R σ.cur x₀ := by rw [hcur]; exact hinv _ _ hE hx'
        obtain ⟨δ', τ, hK'', hst'⟩ := hl m a σ δ x₀ ⟨hx, hc⟩ hK' hσx
        obtain ⟨σc, hB, hδ, hσc, hexp, hτcur, hτR⟩ := sysStep_output_inv hst'
        have hst'' : SysStep K.basis σ (.output δ' x₀) τ := hst'
        have hshp : Shaped l m ((a ++ [SEvent.output δ' x₀]).map SEvent.erase) := by
          have := hshape [] (SEvent.output γ' x₀) rest'' rfl ⟨γ', x₀, rfl⟩
          simpa [hae, SEvent.erase] using this
        have hkeep : ∀ k y, EmitsAt U sk k y → σ.R k y → σc.R k y := by
          intro k y hk h
          refine Classical.byContradiction fun hn => hirr ?_
          exact ⟨l, m, a ++ [SEvent.output δ' x₀], a, δ', x₀, [], σ, σc,
            ⟨hU, hshp, τ, sysExec_snoc hx hst'', compliant_snoc (e := SEvent.output δ' x₀) hc hK''⟩,
            rfl, hx, hδ, Or.inr ⟨k, y, h, hn, hk⟩⟩
        have hinv' : ∀ k y, EmitsAt U sk k y → τ'.R k y → τ.R k y := by
          intro k y hk h
          obtain ⟨h1, h2⟩ := hin' k _ h
          rw [hτR]; exact ⟨hkeep k y hk (hinv k y hk h1), h2⟩
        obtain ⟨rest, ρ, hx1, hc1, he1⟩ := ih (a ++ [SEvent.output δ' x₀])
          (a' ++ [SEvent.output γ' x₀]) τ τ' ρ' hrest' hc'' hemit' hnext' hshape'
          (sysExec_snoc hx hst'') (compliant_snoc (e := SEvent.output δ' x₀) hc hK'')
          (by simp only [List.map_append, hac]; rfl)
          (by rw [hτcur, hcur, hτ'cur]) hinv'
        refine ⟨.output δ' x₀ :: rest, ρ, .cons hst'' hx1, ?_, ?_⟩
        · rw [List.append_assoc] at hc1; exact hc1
        · simp only [List.map_cons, he1]; rfl

/-- **(b) Proper coordination gives the converse.**  Let the store system `K`
coordinate at most once, with a strategy that ignores commitments (`Blind`)
and never stalls (`Live`).  Then every guarded composite run of `eraseSys K`
has, on the same upstream output sequence, a guarded composite run of `K` with
the same observable trace.  No monotonicity is needed. -/
theorem erase_reflects {U : List M → Prop} {K : Sys sk} (hb : Blind K) (hl : Live K)
    (hirr : AtMostOnce U K) {l : List M} {m : M} {esK' : List (SEvent sk)}
    (h : GRun U (eraseSys K) l m esK') :
    ∃ esK, GRun U K l m esK ∧ esK.map SEvent.erase = esK'.map SEvent.erase := by
  obtain ⟨hU, ⟨o, ps, hpre, hsh⟩, ρ', hx', hc'⟩ := h
  have hemit : ∀ p γ x q, esK' = p ++ .output γ x :: q →
      ∀ τ, SysExec (fun _ => False) (canon sk m) p τ → EmitsAt U sk τ.cur x := by
    rintro p γ x q rfl τ hp
    refine ⟨m, p.map SEvent.erase, q.map SEvent.erase, τ, ⟨l, ρ', hU, ⟨o, ps, hpre, ?_⟩, ?_⟩,
      sysExec_empty_exec hp, rfl⟩
    · rw [← hsh]; simp [SEvent.erase]
    · have := sysExec_empty_exec hx'; simpa [SEvent.erase] using this
  have hnext : ∀ p j q, esK' = p ++ .input j :: q → ∃ γ x q', q = .output γ x :: q' := by
    rintro p j q rfl
    rw [List.map_append, List.map_cons] at hsh
    obtain ⟨x, q'', hq⟩ := storeTr_next ps o _ j _ hsh.symm
    obtain ⟨e, q₀, rfl, he, _⟩ := List.map_eq_cons_iff.1 hq
    cases e with
    | input _ => cases he
    | output γ x' => exact ⟨γ, x', q₀, rfl⟩
  have hshape : ∀ p e q, esK' = p ++ e :: q → (∃ γ x, e = .output γ x) →
      Shaped l m (([] ++ (p ++ [e])).map SEvent.erase) := by
    rintro p e q rfl ⟨γ, x, rfl⟩
    rw [List.map_append, List.map_cons] at hsh
    obtain ⟨ps₀, ps₁, hps, heq⟩ := storeTr_prefix ps o _ x _ hsh.symm
    refine ⟨o, ps₀, List.IsPrefix.trans ⟨ps₁.map Prod.fst, by rw [hps]; simp⟩ hpre, ?_⟩
    simpa [SEvent.erase] using heq
  obtain ⟨rest, ρ, hx, hc, he⟩ := reflect_aux hb hl hirr hU esK' [] [] (canon _ m)
    (canon _ m) ρ' hx' (by simpa using hc') hemit hnext hshape (.nil _) compliant_nil rfl rfl
    (fun _ _ _ h => h)
  refine ⟨rest, ⟨hU, ⟨o, ps, hpre, ?_⟩, ρ, hx, by simpa using hc⟩, map_erase_of_eraseC he⟩
  rw [map_erase_of_eraseC he]; exact hsh

/-- **Corollary (empty store), for any upstream behaviour `U`.**  Let `𝒦`
satisfy Lifted Monotonicity and the store system `K` coordinate at most once,
with a strategy that ignores commitments and never stalls.  Its
commitment-erased replacement coordinates at most once, and it has exactly the
same observable behaviour. -/
theorem empty_storeU (hC : sk.CommonExpansion) {U : List M → Prop} {K : Sys sk}
    (hirr : AtMostOnce U K) (hb : Blind K) (hl : Live K) :
    AtMostOnce U (eraseSys K) ∧ ∀ l m tr, Obs U K l m tr ↔ Obs U (eraseSys K) l m tr := by
  refine ⟨atMostOnce_of_eps fun _ _ _ hK => eraseSys_eps hK, fun l m tr => ⟨erase_obs hC, ?_⟩⟩
  rintro ⟨esK', hg, rfl⟩
  obtain ⟨esK, hg', he⟩ := erase_reflects hb hl hirr hg
  exact ⟨esK, hg', he⟩

/-- **Corollary (empty store).**  For an upstream system `P`: if the guarded
composite is proper and the store's strategy ignores commitments and never
stalls, the replacement is proper with the same observable behaviour. -/
theorem empty_store (hC : sk.CommonExpansion) {P : Sys sp} {K : Sys sk} (hirr : Proper P K)
    (hb : Blind K) (hl : Live K) :
    Proper P (eraseSys K) ∧ ∀ l m tr, Obs P.emits K l m tr ↔ Obs P.emits (eraseSys K) l m tr :=
  let ⟨h1, h2⟩ := empty_storeU hC hirr.1 hb hl
  ⟨⟨h1, hirr.2⟩, h2⟩

/-! #### Pipelines -/

/-- The outputs of an event list, in order. -/
def outs : List (Event I O) → List O
  | [] => []
  | .input _ :: es => outs es
  | .output o :: es => o :: outs es

omit [PO M] [PO O] in
theorem outs_storeTr' : ∀ ps : List (M × O), outs (storeTr ps) = ps.map Prod.snd
  | [] => rfl
  | (_, _) :: ps => congrArg _ (outs_storeTr' ps)

omit [PO M] [PO O] in
theorem outs_storeTr (o : O) (ps : List (M × O)) :
    outs (Event.output o :: storeTr ps) = o :: ps.map Prod.snd :=
  congrArg _ (outs_storeTr' ps)

theorem emitted_eq_outs {J X : Type} [PO J] [PO X] {sq : Spec J X} :
    ∀ es : List (SEvent sq), emitted es = outs (es.map SEvent.erase)
  | [] => rfl
  | .input _ :: es => emitted_eq_outs es
  | .output _ _ :: es => congrArg _ (emitted_eq_outs es)

omit [PO O] in
theorem outs_merge : ∀ (es : List (SEvent sp)) (os : List O),
    (emitted es).length = os.length → outs (merge es os) = os
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | .input _ :: es, os, h => outs_merge es os h
  | .output _ _ :: es, o :: os, h => congrArg _ (outs_merge es os (by simpa [emitted] using h))
  | .output _ _ :: es, [], h => by cases h

/-- The output sequences that the store parts of guarded composite runs emit:
the guarded composite's behaviour as an upstream for a further stage. -/
def GEmits (U : List M → Prop) (K : Sys sk) (l' : List O) : Prop :=
  ∃ l m esK, GRun U K l m esK ∧ outs (esK.map SEvent.erase) = l'

/-- **Every guarded composite run is a run of the composite.**  Let `𝒦`
satisfy Lifted Monotonicity, `P` be any system of `𝒫`, and `K` any store
system.  For every guarded composite run, some run that `P` produces has a
prefix whose events, with outputs replaced by the store's outputs, form a run
of `𝒦 ∘ 𝒫` from a canonical state. -/
theorem grun_composite (hC : sk.CommonExpansion) {P : Sys sp} {K : Sys sk} {l : List M}
    {m : M} {esK : List (SEvent sk)} (h : GRun P.emits K l m esK) :
    ∃ i es₀ σ₀ ρ', SysExec P.basis (canon sp i) es₀ σ₀ ∧ emitted es₀ <+: l ∧
      (emitted es₀).length = (outs (esK.map SEvent.erase)).length ∧
      Exec (canon (seq sp sk) i) (merge es₀ (outs (esK.map SEvent.erase))) ρ' := by
  obtain ⟨hR, _, _⟩ := erase_simulates hC h
  obtain ⟨⟨i, es, ρ, hP, rfl⟩, ⟨o, ps, hpre, hsh⟩, ρK, hK, _⟩ := hR
  rw [map_erase_eraseC] at hsh
  obtain ⟨es₀, es₁, rfl, h0⟩ := emitted_prefix hpre
  obtain ⟨σ₀, hx0, _⟩ := sysExec_append_inv hP.1
  obtain ⟨ρ', hx, _⟩ := composite_run hC hx0 h0 rfl hK (by rw [map_erase_eraseC]; exact hsh)
  refine ⟨i, es₀, σ₀, ρ', hx0, by rw [h0]; exact hpre, ?_, ?_⟩
  · rw [hsh, outs_storeTr, h0]; simp
  · rw [hsh, outs_storeTr]; exact hx

/-- **Pipeline step.**  The guarded composite of `𝒫` (any system) and a
Lifted-Monotone `𝒦` (any store system) emits only what `𝒦 ∘ 𝒫` emits under its
canonical basis.  So the guarded composite is itself an upstream system for a
further stage, every result above applies to that stage with
`U = GEmits P.emits K`, and by induction to every stage of a pipeline whose
stages after the first satisfy Lifted Monotonicity. -/
theorem pipeline_step (hC : sk.CommonExpansion) {P : Sys sp} {K : Sys sk} {l' : List O}
    (h : GEmits P.emits K l') : (Sys.free (canonBasis (seq sp sk))).emits l' := by
  obtain ⟨l, m, esK, hg, rfl⟩ := h
  obtain ⟨i, es₀, σ₀, ρ', _, _, hlen, hx⟩ := grun_composite hC hg
  obtain ⟨es', he', hc⟩ := exec_canonExec hx
  refine ⟨i, es', ρ', produces_free.2 (canonExec_sysExec hc), ?_⟩
  rw [emitted_eq_outs, he']
  exact outs_merge es₀ _ hlen

/-- Under the common-expansion condition, every execution from a run state
is commitment-free. -/
theorem exec_execCF {J X : Type} [PO J] [PO X] {sq : Spec J X} (hC : sq.CommonExpansion)
    {σ τ : State sq} {es : List (Event J X)} (h : Exec σ es τ) (hσ : IsRun σ) :
    ExecCF σ es τ := by
  induction h with
  | nil => exact .nil _
  | @cons σ τ ρ e es hs _ ih =>
    cases e with
    | input j => exact .input hs (ih (isRun_step hσ hs))
    | output o =>
      have ho : σ.R σ.cur o := by cases hs with | output _ _ ho _ _ => exact ho
      exact .output hs (commonExpansion_exposable hC hσ ho) (ih (isRun_step hσ hs))

/-- **A monotone pipeline needs no commitment anywhere** (the base case of the
pipeline induction).  If `𝒫` and `𝒦` both satisfy Lifted Monotonicity, so
does `𝒦 ∘ 𝒫`, and the guarded composite of `𝒫` under the empty basis with any
store system emits only what `𝒦 ∘ 𝒫` emits under the empty basis: it is again
an upstream with the empty basis. -/
theorem pipeline_coordination_free (hP : sp.LiftedMono) (hK : sk.LiftedMono)
    {K : Sys sk} {l' : List O}
    (h : GEmits (Sys.free (fun _ : Commitment sp => False)).emits K l') :
    (seq sp sk).LiftedMono ∧
      (Sys.free (fun _ : Commitment (seq sp sk) => False)).emits l' := by
  have hL := seq_liftedMono hP hK
  have hC := (liftedMono_iff_commonExpansion _).1 hK
  have hCs := (liftedMono_iff_commonExpansion _).1 hL
  refine ⟨hL, ?_⟩
  obtain ⟨l, m, esK, hg, rfl⟩ := h
  obtain ⟨i, es₀, σ₀, ρ', _, _, hlen, hx⟩ := grun_composite hC hg
  obtain ⟨es', he', _, hx'⟩ := execCF_coordFree (fun _ => False) (exec_execCF hCs hx ⟨i, [], .nil _⟩)
  refine ⟨i, es', ρ', produces_free.2 hx', ?_⟩
  rw [emitted_eq_outs, he']
  exact outs_merge es₀ _ hlen

end General


/-! ### Function stores -/

/-- **Every output of a function store is exposable.**  If `f` is monotone, at
every state of the store, run or not, `f(cur)` (its only output there) is
exposable. -/
theorem store_exposable (hf : Monotone f) (σ : State (graph f)) : Exposable σ (f σ.cur) := by
  intro k x hx hnx
  have e : x = f k := σ.sub k x hx
  exact absurd (e ▸ hf _ _ (σ.above k x hx)) hnx

/-- **A store commitment is never needed.**  If `f` is monotone, wherever the
store's `Out_δ(x)` is legal, so is `Out_ε(x)`, and it keeps at least the same
rows. -/
theorem store_eps (hf : Monotone f) {BK : Basis (graph f)} {σ τ : State (graph f)}
    {δ : List (Commitment (graph f))} {x : O} (h : SysStep BK σ (.output δ x) τ) :
    ∃ τ', SysStep BK σ (.output [] x) τ' ∧ ∀ k u, τ.R k u → τ'.R k u := by
  obtain ⟨_, ho, hin, _⟩ := containment h
  have e : x = f σ.cur := σ.sub _ _ ho
  refine ⟨outState σ x ho, eps_step_iff.2 ⟨ho, e ▸ store_exposable hf σ, rfl, rfl⟩,
    fun k u hu => hin k u hu⟩

/-- The image through a function store is the image through its table. -/
theorem img_eq_imgK (f : M → O) (σ : State sp) : img f σ = imgK (graph f) σ := rfl

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
every system of `𝒫` (Multi-Paxos's, or any other) the guarded composite with
the empty-basis store is proper; some composite output needs a
commitment, which `𝒫` must make. -/
theorem smr_proper {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R) (σ0 : Stt)
    {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) (P : Sys (smrS1 (Cmd := Cmd))) :
    ¬ (smrS1 (Cmd := Cmd)).LiftedMono ∧ ¬ (comp smrS1 (execF δ σ0)).LiftedMono ∧
      Monotone (execF δ σ0) ∧ Proper P (noStore (graph (execF δ σ0))) ∧
      ∃ i m, smrS1.S i m ∧ ¬ Exposable (canon (comp smrS1 (execF δ σ0)) i) (execF δ σ0 m) ∧
        ∀ m', smrS1.S i m' → execF δ σ0 m' = execF δ σ0 m → ¬ Exposable (canon smrS1 i) m' := by
  obtain ⟨h1, h2, hf, _⟩ := Inst.smr_example δ σ0 hne
  obtain ⟨i, m, hm, hne', hall, _⟩ := at_least_once_needed hf h2
  exact ⟨h1, h2, hf, guarded_proper (graph_commonExpansion hf) P, i, m, hm, hne', hall⟩

/-- A lock granted to `a` over `b` on one key: the logs in which `b` comes
first. -/
def bFirst {Cmd : Type} (b : Cmd) (k : Pfx Cmd) : Prop := k.l.head? = some b

/-- The mutex store's basis: its only commitment seals the logs in which `b`
comes first. -/
noncomputable def mutexB {Cmd O : Type} [PO O] (b : Cmd) (f : Pfx Cmd → O) : Basis (graph f) :=
  fun c => c = sealIn (bFirst b)

/-- **Early lock.**  The store's strategy takes the lock at its first event if
the log is still empty, and applies nothing otherwise. -/
noncomputable def earlyLock {Cmd O : Type} [PO O] (b : Cmd) (f : Pfx Cmd → O) : Sys (graph f) where
  basis := mutexB b f
  strat m a e := ∀ δ x, e = .output δ x →
    ((a = [] ∧ m = ⟨[]⟩) → δ = [sealIn (bFirst b)]) ∧ (¬ (a = [] ∧ m = ⟨[]⟩) → δ = [])

/-- **Late lock.**  The store's strategy takes the lock only once its current
log is nonempty, and may also apply nothing. -/
noncomputable def lateLock {Cmd O : Type} [PO O] (b : Cmd) (f : Pfx Cmd → O) : Sys (graph f) where
  basis := mutexB b f
  strat m a e := ∀ δ x, e = .output δ x → δ = [] ∨ (lastIn m a).l ≠ []

/-- **An uncontended lock decides nothing.**  Once the store's current log is
nonempty, every log it can still receive has the same first command, so
sealing the logs in which `b` comes first removes no row: it is not a
commitment there (the partial function is undefined). -/
theorem lock_after_log {Cmd O : Type} [PO O] {f : Pfx Cmd → O} (b : Cmd)
    (σ : State (graph f)) (h : σ.cur.l ≠ []) : (sealIn (bFirst b)).app σ = none := by
  cases hc : (sealIn (bFirst b)).app σ with
  | none => rfl
  | some τ =>
    obtain ⟨hn, ⟨k, x, hx, hQ⟩, _⟩ := sealInApp_eq.1 hc
    obtain ⟨t, ht⟩ := σ.above k x hx
    obtain ⟨c, l, hl⟩ := List.exists_cons_of_ne_nil h
    exfalso; apply hn
    unfold bFirst at hQ ⊢
    rw [ht, hl] at hQ; rw [hl]
    simpa using hQ

/-- A store with the lock basis whose strategy offers a commitment only at a
nonempty log applies no commitment in any run it produces: its lock events
are never legal. -/
theorem lock_eps {Cmd O : Type} [PO O] {f : Pfx Cmd → O} (b : Cmd) {K : Sys (graph f)}
    (hB : K.basis = mutexB b f)
    (hS : ∀ m a δ x, K.strat m a (.output δ x) → δ = [] ∨ (lastIn m a).l ≠ []) {m : Pfx Cmd}
    {esK : List (SEvent (graph f))} {ρ : State (graph f)} (h : Produces K m esK ρ) :
    ∀ γ x, SEvent.output γ x ∈ esK → γ = [] := by
  intro γ x hm
  obtain ⟨a, c, rfl⟩ := List.append_of_mem hm
  obtain ⟨σ, ha, hb⟩ := sysExec_append_inv h.1
  have hs : K.strat m a (.output γ x) := h.2 a _ c rfl
  rcases hS m a γ x hs with hγ | hne
  · exact hγ
  · cases hb with
    | cons hst _ =>
      cases hst with
      | output hB' hγ _ _ _ _ =>
        cases γ with
        | nil => rfl
        | cons c0 cs =>
          have hc0 : c0 = sealIn (bFirst b) := by
            have := hB' c0 List.mem_cons_self; rw [hB] at this; exact this
          subst hc0
          cases hγ with
          | cons happ _ =>
            have hcur : σ.cur = lastIn m a := sysExec_lastIn ha
            rw [lock_after_log b σ (by rw [hcur]; exact hne)] at happ
            cases happ

/-- Every run the late-lock store produces applies no commitment. -/
theorem lateLock_eps {Cmd O : Type} [PO O] {f : Pfx Cmd → O} (b : Cmd) {m : Pfx Cmd}
    {esK : List (SEvent (graph f))} {ρ : State (graph f)} (h : Produces (lateLock b f) m esK ρ) :
    ∀ γ x, SEvent.output γ x ∈ esK → γ = [] :=
  lock_eps (K := lateLock b f) b rfl (fun _ _ δ x h => h δ x rfl) h

/-- **Stalling lock.**  The store's strategy insists on the lock at a nonempty
log, and applies nothing at the empty log. -/
noncomputable def stallLock {Cmd O : Type} [PO O] (b : Cmd) (f : Pfx Cmd → O) : Sys (graph f) where
  basis := mutexB b f
  strat m a e := ∀ δ x, e = .output δ x →
    ((lastIn m a).l = [] → δ = []) ∧ ((lastIn m a).l ≠ [] → δ = [sealIn (bFirst b)])

/-- **The strategy hypothesis `Live` is needed.**  The stalling-lock store is
proper and its strategy ignores commitments, yet its commitment-erased
replacement follows a run of `𝒫 = smrS1` that it cannot: fed `[b]` first, the
store must take a lock that is undefined there, and never emits. -/
theorem stall_lock {Cmd O : Type} [PO O] {f : Pfx Cmd → O} (hf : Monotone f) (b : Cmd) :
    Proper (Sys.free (canonBasis (smrS1 (Cmd := Cmd)))) (stallLock b f) ∧ Blind (stallLock b f) ∧
      ∃ l m tr, Obs (Sys.free (canonBasis (smrS1 (Cmd := Cmd)))).emits (eraseSys (stallLock b f)) l m tr ∧
        ¬ Obs (Sys.free (canonBasis (smrS1 (Cmd := Cmd)))).emits (stallLock b f) l m tr := by
  have hS : ∀ m a δ x, (stallLock b f).strat m a (.output δ x) → δ = [] ∨ (lastIn m a).l ≠ [] := by
    intro m a δ x h
    by_cases hl : (lastIn m a).l = []
    · exact Or.inl ((h δ x rfl).1 hl)
    · exact Or.inr hl
  refine ⟨(proper_iff (graph_commonExpansion hf) _ _).2
    (atMostOnce_of_eps fun _ _ _ h => lock_eps b rfl hS h), ?_, ?_⟩
  · intro i a a2 e hae h δ x he
    rw [← lastIn_eraseC i a2, ← hae, lastIn_eraseC]
    exact h δ x he
  let kb : Pfx Cmd := ⟨[b]⟩
  let σP := canon (smrS1 (Cmd := Cmd)) kb
  have ho : σP.R σP.cur kb := ⟨fun _ h => h, PO.refl _⟩
  have hP : SysExec (canonBasis smrS1) σP [.output (kappa σP kb) kb] (outState σP kb ho) :=
    .cons (canonical_support σP kb ho) (.nil _)
  let σ0 := canon (graph f) kb
  have h0 : σ0.R σ0.cur (f kb) := ⟨rfl, PO.refl _⟩
  have hK : SysExec (fun _ => False) σ0 [.output [] (f kb)] (outState σ0 (f kb) h0) :=
    .cons (τ := outState σ0 (f kb) h0) (eps_step_iff.2 ⟨h0, store_exposable hf σ0, rfl, rfl⟩)
      (.nil _)
  have hcK : Compliant (Allowed (eraseSys (stallLock b f)) kb) [.output [] (f kb)] := by
    have h1 : Allowed (eraseSys (stallLock b f)) kb [] (.output [] (f kb)) :=
      ⟨[], .output [sealIn (bFirst b)] (f kb), rfl, rfl, by
        intro δ x h; cases h
        exact ⟨fun h => absurd h (List.cons_ne_nil _ _), fun _ => rfl⟩⟩
    exact compliant_snoc (l := []) compliant_nil h1
  refine ⟨[kb], kb, [.output (f kb)],
    ⟨_, ⟨⟨kb, _, _, produces_free.2 hP, rfl⟩, ⟨f kb, [], List.prefix_refl _, rfl⟩, _, hK, hcK⟩,
      rfl⟩, ?_⟩
  rintro ⟨esK, ⟨_, _, ρ, hx, hc⟩, hl⟩
  rcases esK with _ | ⟨e1, _ | ⟨e2, t⟩⟩
  all_goals try (simp at hl; done)
  cases e1 with
  | input j => simp [SEvent.erase] at hl
  | output δ₀ x₀ =>
  have hδ : δ₀ = [sealIn (bFirst b)] :=
    ((hc [] _ [] rfl : (stallLock b f).strat kb [] (.output δ₀ x₀)) δ₀ x₀ rfl).2
      (List.cons_ne_nil _ _)
  subst hδ
  cases hx with
  | cons hs1 _ =>
  cases hs1 with
  | output _ hγ _ _ _ _ =>
  cases hγ with
  | cons happ _ =>
  rw [lock_after_log b σ0 (List.cons_ne_nil _ _)] at happ
  cases happ

/-- **A late lock is proper.**  For any upstream system `P` emitting logs
and any monotone `f`, the late-lock store applies no commitment in any run, so
it is proper; its strategy ignores commitments and never stalls, so it
has the same observable behaviour as its commitment-erased replacement. -/
theorem late_lock_proper {I' Cmd O : Type} [PO I'] [PO O] {sq : Spec I' (Pfx Cmd)}
    {f : Pfx Cmd → O} (hf : Monotone f) (b : Cmd) (P : Sys sq) :
    Proper P (lateLock b f) ∧ Blind (lateLock b f) ∧ Live (lateLock b f) ∧
      ∀ l m tr, Obs P.emits (lateLock b f) l m tr ↔ Obs P.emits (eraseSys (lateLock b f)) l m tr := by
  have hirr : Proper P (lateLock b f) :=
    (proper_iff (graph_commonExpansion hf) P _).2 (atMostOnce_of_eps fun _ _ _ h => lateLock_eps b h)
  have hb : Blind (lateLock b f) := by
    intro i a a2 e hae h δ x he
    rcases h δ x he with h | h
    · exact Or.inl h
    · right; rw [← lastIn_eraseC i a2, ← hae, lastIn_eraseC]; exact h
  have hl : Live (lateLock b f) := by
    intro i a σ δ o _ _ ho
    have e : o = f σ.cur := σ.sub _ _ ho
    refine ⟨[], outState σ o ho, ?_, eps_step_iff.2 ⟨ho, e ▸ store_exposable hf σ, rfl, rfl⟩⟩
    intro δ' x he; cases he; exact Or.inl rfl
  exact ⟨hirr, hb, hl, (empty_store (graph_commonExpansion hf) hirr hb hl).2⟩

/-- **An early lock behind the log coordinates redundantly.**  Let the store
run `smrS1`'s logs through any monotone `f`, with the early-lock strategy: at
the empty log it seals every log in which `b` comes first, before emitting.
`𝒫` runs under its canonical basis with every strategy.  The store's output
was exposable without the lock (`store_exposable`), yet `𝒫` can feed the
store the log `[b]`, contradicting the lock.  So this composite is not
proper, while the same `𝒫` with the empty-basis store is. -/
theorem mutex_redundant {Cmd O : Type} [PO O] {f : Pfx Cmd → O} (hf : Monotone f) (b : Cmd) :
    (∃ σ : State (graph f), σ.cur = ⟨[]⟩ ∧ Exposable σ (f ⟨[]⟩) ∧
      ∃ σc, ApplySeq [sealIn (bFirst b)] σ σc ∧
        Contradicted (Sys.free (canonBasis (smrS1 (Cmd := Cmd)))).emits σ σc) ∧
    Redundant (Sys.free (canonBasis (smrS1 (Cmd := Cmd)))).emits (earlyLock b f) ∧
    ¬ Proper (Sys.free (canonBasis (smrS1 (Cmd := Cmd)))) (earlyLock b f) ∧
    Proper (Sys.free (canonBasis (smrS1 (Cmd := Cmd)))) (noStore (graph f)) := by
  let e : Pfx Cmd := ⟨[]⟩
  let kb : Pfx Cmd := ⟨[b]⟩
  let σ := canon (graph f) e
  have hne : ¬ bFirst b σ.cur := fun h => by cases h
  have happ : (sealIn (bFirst b)).app σ = some (sealInState σ (bFirst b) hne) :=
    sealInApp_eq.2 ⟨hne, ⟨kb, f kb, ⟨rfl, ⟨[b], rfl⟩⟩, rfl⟩, rfl⟩
  let σc := sealInState σ (bFirst b) hne
  have hγ : ApplySeq [sealIn (bFirst b)] σ σc := .cons happ (.nil _)
  -- a reference run accepts `[b]`: `𝒫` emits `[b]` and the store answers it
  have hacc : Accepts (Sys.free (canonBasis (smrS1 (Cmd := Cmd)))).emits (graph f) kb := by
    let σP := canon (smrS1 (Cmd := Cmd)) kb
    have ho : σP.R σP.cur kb := ⟨fun _ h => h, PO.refl _⟩
    have hP : SysExec (canonBasis smrS1) σP [.output (kappa σP kb) kb] (outState σP kb ho) :=
      .cons (canonical_support σP kb ho) (.nil _)
    let σK := canon (graph f) kb
    have hoK : σK.R σK.cur (f kb) := ⟨rfl, PO.refl _⟩
    exact ⟨kb, [.output (f kb)], ⟨[kb], _, ⟨kb, _, _, produces_free.2 hP, rfl⟩,
      ⟨f kb, [], List.prefix_refl _, rfl⟩,
      .cons (Step.output σK (outState σK (f kb) hoK) _ hoK rfl rfl) (.nil _)⟩, Or.inl rfl⟩
  have hcon : Contradicted (Sys.free (canonBasis (smrS1 (Cmd := Cmd)))).emits σ σc :=
    Or.inl ⟨kb, ⟨f kb, rfl, ⟨[b], rfl⟩⟩, fun _ h => h.2 rfl, hacc⟩
  -- the guarded run in which the store takes the lock
  have hred : Redundant (Sys.free (canonBasis (smrS1 (Cmd := Cmd)))).emits (earlyLock b f) := by
    let σP := canon (smrS1 (Cmd := Cmd)) e
    have ho : σP.R σP.cur e := ⟨fun _ h => (nomatch h), PO.refl _⟩
    have hexpP : Exposable σP e := fun _ x _ hn => absurd ⟨x.l, rfl⟩ hn
    have hP : SysExec (canonBasis smrS1) σP [.output [] e] (outState σP e ho) :=
      .cons (τ := outState σP e ho) (eps_step_iff.2 ⟨ho, hexpP, rfl, rfl⟩) (.nil _)
    have hoc : σc.R σc.cur (f e) := ⟨⟨rfl, PO.refl _⟩, hne⟩
    have hK : SysExec (mutexB b f) σ [.output [sealIn (bFirst b)] (f e)] (outState σc (f e) hoc) :=
      .cons (τ := outState σc (f e) hoc) (.output (fun c hc => by simp at hc; exact hc) hγ hoc
        (store_exposable hf σc) rfl rfl) (.nil _)
    have hcK : Compliant (Allowed (earlyLock b f) e) [.output [sealIn (bFirst b)] (f e)] :=
      compliant_snoc (l := []) (e := SEvent.output [sealIn (bFirst b)] (f e)) compliant_nil (by
        intro δ x h; cases h; exact ⟨fun _ => rfl, fun hn => absurd ⟨rfl, rfl⟩ hn⟩)
    exact ⟨[e], e, _, [], _, _, [], σ, σc, ⟨⟨e, _, _, produces_free.2 hP, rfl⟩,
      ⟨f e, [], List.prefix_refl _, rfl⟩, _, hK, hcK⟩, rfl, .nil _, hγ, hcon⟩
  exact ⟨⟨σ, rfl, store_exposable hf σ, σc, hγ, hcon⟩, hred, fun h => h.1 hred,
    guarded_proper (graph_commonExpansion hf) _⟩

/-- **A redundant store can lose behaviour.**  With `𝒫 = smrS1` under its
canonical basis, `𝒫` can emit `[]` and then `[b]`.  The commitment-erased
replacement of the early-lock store follows this run, emitting `f []`,
receiving `[b]`, and emitting `f [b]`.  The early-lock store cannot: its lock
at `[]` seals `[b]`. -/
theorem early_lock_strict {Cmd O : Type} [PO O] {f : Pfx Cmd → O} (hf : Monotone f) (b : Cmd) :
    ∃ l m tr, Obs (Sys.free (canonBasis (smrS1 (Cmd := Cmd)))).emits (eraseSys (earlyLock b f)) l m tr ∧
      ¬ Obs (Sys.free (canonBasis (smrS1 (Cmd := Cmd)))).emits (earlyLock b f) l m tr := by
  let e : Pfx Cmd := ⟨[]⟩
  let kb : Pfx Cmd := ⟨[b]⟩
  -- `𝒫`, at input `[b]`, emits `[]` and then `[b]`
  let σP := canon (smrS1 (Cmd := Cmd)) kb
  have ho : σP.R σP.cur e := ⟨fun _ h => (nomatch h), PO.refl _⟩
  have hexpP : Exposable σP e := fun _ x _ hn => absurd ⟨x.l, rfl⟩ hn
  let τ1 := outState σP e ho
  have ho2 : τ1.R τ1.cur kb := ⟨⟨fun _ h => h, PO.refl _⟩, ⟨[b], rfl⟩⟩
  have hP : SysExec (canonBasis smrS1) σP [.output [] e, .output (kappa τ1 kb) kb]
      (outState τ1 kb ho2) :=
    .cons (τ := τ1) (eps_step_iff.2 ⟨ho, hexpP, rfl, rfl⟩)
      (.cons (canonical_support τ1 kb ho2) (.nil _))
  -- the replacement store emits `f []`, receives `[b]`, emits `f [b]`
  let σ0 := canon (graph f) e
  have h0 : σ0.R σ0.cur (f e) := ⟨rfl, PO.refl _⟩
  let τa := outState σ0 (f e) h0
  have hr : τa.R kb (f kb) := ⟨⟨rfl, ⟨[b], rfl⟩⟩, hf _ _ ⟨[b], rfl⟩⟩
  let τb := inState τa kb (f kb) hr
  have hb3 : τb.R τb.cur (f kb) := ⟨hr, PO.refl _⟩
  have hK : SysExec (fun _ => False) σ0 [.output [] (f e), .input kb, .output [] (f kb)]
      (outState τb (f kb) hb3) :=
    .cons (τ := τa) (eps_step_iff.2 ⟨h0, store_exposable hf σ0, rfl, rfl⟩)
      (.cons (τ := τb) (.input (Step.input τa τb kb ⟨_, hr⟩ rfl rfl))
        (.cons (τ := outState τb (f kb) hb3)
          (eps_step_iff.2 ⟨hb3, store_exposable hf τb, rfl, rfl⟩) (.nil _)))
  have hcK : Compliant (Allowed (eraseSys (earlyLock b f)) e)
      [.output [] (f e), .input kb, .output [] (f kb)] := by
    have h1 : Allowed (eraseSys (earlyLock b f)) e [] (.output [] (f e)) :=
      ⟨[], .output [sealIn (bFirst b)] (f e), rfl, rfl, by
        intro δ x h; cases h; exact ⟨fun _ => rfl, fun hn => absurd ⟨rfl, rfl⟩ hn⟩⟩
    have h3 : Allowed (eraseSys (earlyLock b f)) e [.output [] (f e), .input kb]
        (.output [] (f kb)) :=
      ⟨[.output [sealIn (bFirst b)] (f e), .input kb], .output [] (f kb), rfl, rfl, by
        intro δ x h; cases h; exact ⟨fun h => absurd h.1 (List.cons_ne_nil _ _), fun _ => rfl⟩⟩
    exact compliant_snoc (l := [SEvent.output [] (f e), SEvent.input kb])
      (compliant_snoc (l := [SEvent.output [] (f e)]) (e := SEvent.input kb)
        (compliant_snoc (l := []) compliant_nil h1) trivial) h3
  refine ⟨[e, kb], e, [.output (f e), .input kb, .output (f kb)],
    ⟨_, ⟨⟨kb, _, _, produces_free.2 hP, rfl⟩, ⟨f e, [(kb, f kb)], List.prefix_refl _, rfl⟩, _, hK,
      hcK⟩, rfl⟩, ?_⟩
  rintro ⟨esK, ⟨_, _, ρ, hx, hc⟩, hl⟩
  rcases esK with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, _ | ⟨e4, t⟩⟩⟩⟩
  all_goals try (simp at hl; done)
  cases e1 with
  | input j => simp [SEvent.erase] at hl
  | output δ₀ x₀ =>
  cases e2 with
  | output γ y => simp [SEvent.erase] at hl
  | input j =>
  have hj : j = kb := by simp [SEvent.erase] at hl; exact hl.2.1
  subst hj
  have hδ : δ₀ = [sealIn (bFirst b)] :=
    ((hc [] _ [_, e3] rfl : (earlyLock b f).strat e [] (.output δ₀ x₀)) δ₀ x₀ rfl).1 ⟨rfl, rfl⟩
  subst hδ
  cases hx with
  | cons hs1 hr1 =>
  cases hr1 with
  | cons hs2 _ =>
  cases hs1 with
  | output _ hγ _ _ _ hR =>
  cases hγ with
  | cons happ hnil =>
  cases hnil
  obtain ⟨_, _, rfl⟩ := sealInApp_eq.1 happ
  cases hs2 with
  | input hst =>
  match hst with
  | .input _ _ _ hleg _ _ =>
    obtain ⟨u, hu⟩ := hleg
    rw [hR] at hu
    exact hu.1.2 rfl

end SMR

end Guard
end CC
