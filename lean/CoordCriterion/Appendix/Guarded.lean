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
  `imgK`, `cf_stepK`, `cf_stepK_on`, `row_at`, `store_follows`,
  `noStore_follows`, `composite_run`, `guarded_confluentK` — runs of the
  pipeline as runs of the composite.  `GRun`, `Shaped`, `blk` — a run of the
  pipeline: the store receives each upstream output and answers it any number
  of times, possibly never.  `eraseSys`, `Obs`, `erase_simulates` — the
  commitment-erased replacement.  `grun_composite`, `GEmits`, `pipeline_step`,
  `pipeline_coordination_free` — pipelines.
* Proper Coordination (section `ProperCoord`): `rest sp sk` is `𝒮₂|_{𝒮₁}`,
  `NeedsNoCommit`, `Proper` (Def.); `proper_iff`, `proper_iff_consistent`
  (Thm. (1)); `proper_follows`, `proper_run`, `proper_confluent` (Thm. (2), via
  `core`, `core_lockstep`, `seq_core`); `proper_needs_commit` (Thm. (3));
  `proper_erase` (Cor. Empty store); `liftU`, `proper_pipeline_step` (Cor.
  Pipelines).
* `store_exposable`, `store_eps` — function stores: every output is exposable
  at every state.
* `sealIn`, `mutexB`, `earlyLock`, `lateLock`, `lateLock_eps`,
  `early_lock_strict` — lock strategies in the store behind the log.
* `smr_proper` — Example `ex:committed-log-composition`.
-/

namespace CC

/-! ### Restriction to the upstream's outputs (namespace `CC.Joint`)

`𝒮₂|_{𝒮₁}` is `restrictTo (Img 𝒮₁) 𝒮₂`.  These definitions are shared with
`Appendix/JointMono.lean`. -/

namespace Joint

open Comp Classical

section Filter
variable {I M O : Type} [PO I] [PO M] [PO O]

/-- The middle values `𝒮₁` can produce. -/
def Img (sp : Spec I M) (m : M) : Prop := ∃ i, sp.S i m

/-- **Common expansion on `D`**: the common-expansion condition for rows whose
inputs lie in `D`, at expansions in `D`. -/
def CEOn (sp : Spec M O) (D : M → Prop) : Prop :=
  ∀ rows : List (M × O), (∀ r ∈ rows, D r.1 ∧ sp.S r.1 r.2) →
    ∀ j, D j → (∀ r ∈ rows, r.1 ≼ j) → ∃ u, sp.S j u ∧ ∀ r ∈ rows, r.2 ≼ u

theorem ceOn_of_ce {sp : Spec M O} (h : sp.CommonExpansion) (D : M → Prop) : CEOn sp D :=
  fun rows hr j _ hj => h rows (fun r h' => (hr r h').2) j hj

theorem ceOn_mono {sp : Spec M O} {D D' : M → Prop} (h : ∀ m, D m → D' m)
    (hC : CEOn sp D') : CEOn sp D :=
  fun rows hr j hj hle => hC rows (fun r h' => ⟨h _ (hr r h').1, (hr r h').2⟩) j (h _ hj) hle

/-- A function store is Lifted-Monotone on `D` when it is monotone on `D`. -/
theorem graph_ceOn {g : M → O} {D : M → Prop}
    (hg : ∀ a b, D a → D b → a ≼ b → g a ≼ g b) : CEOn (graph g) D :=
  fun rows hr j hj hle => ⟨g j, rfl, fun r h => by
    have e : r.2 = g r.1 := (hr r h).2
    rw [e]; exact hg _ _ (hr r h).1 hj (hle r h)⟩

/-- The subtype order. -/
instance subPO (D : M → Prop) : PO {m // D m} where
  le x y := x.1 ≼ y.1
  refl x := PO.refl x.1
  trans h h' := PO.trans h h'
  antisymm h h' := Subtype.ext (PO.antisymm h h')

/-- `𝒮` read as a specification on the inputs in `D`. -/
def restrictTo (D : M → Prop) (sp : Spec M O) : Spec {m // D m} O :=
  ⟨fun m o => sp.S m.1 o, fun m => sp.total m.1⟩

/-- `CEOn sp D` says exactly that `sp` restricted to `D` satisfies Lifted
Monotonicity. -/
theorem ceOn_iff_restrictTo (D : M → Prop) (sp : Spec M O) :
    CEOn sp D ↔ (restrictTo D sp).LiftedMono := by
  rw [liftedMono_iff_commonExpansion]
  constructor
  · intro h rows hr j hj
    obtain ⟨u, hu, hall⟩ := h (rows.map fun r => (r.1.1, r.2))
      (by
        intro r hr'
        obtain ⟨r', h', rfl⟩ := List.mem_map.1 hr'
        exact ⟨r'.1.2, hr r' h'⟩)
      j.1 j.2
      (by
        intro r hr'
        obtain ⟨r', h', rfl⟩ := List.mem_map.1 hr'
        exact hj r' h')
    exact ⟨u, hu, fun r h' => hall _ (List.mem_map.2 ⟨r, h', rfl⟩)⟩
  · intro h rows hr j hDj hj
    obtain ⟨L, hL1, hL2⟩ := choose_list (fun (r : M × O) (d : {m // D m}) => d.1 = r.1) rows
      (fun r hr' => ⟨⟨r.1, (hr r hr').1⟩, rfl⟩)
    obtain ⟨u, hu, hall⟩ := h (L.map fun p => (p.2, p.1.2))
      (by
        intro r hr'
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
        show sp.S p.2.1 p.1.2
        rw [(hL2 p hp).2]
        exact (hr p.1 (hL2 p hp).1).2)
      ⟨j, hDj⟩
      (by
        intro r hr'
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
        show p.2.1 ≼ j
        rw [(hL2 p hp).2]
        exact hj p.1 (hL2 p hp).1)
    refine ⟨u, hu, fun r hr' => ?_⟩
    obtain ⟨b, hb⟩ := hL1 r hr'
    exact hall (b, r.2) (List.mem_map.2 ⟨(r, b), hb, rfl⟩)

end Filter
end Joint

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
`input j` stays, `Out_γ(m)` becomes `output (f m)`, and a commit event is
unobservable. -/
def obs (f : M → O) : SEvent sp → Option (Event I O)
  | .input j => some (.input j)
  | .output _ m => some (.output (f m))
  | .commit _ => none

/-! ### Pushforward of runs -/

/-- **Pushforward of runs (lockstep form).**  If `f` is monotone, from any
composite state `σ'` with the same current input whose table contains the
image of `σ`'s, every execution of `𝒫` under any basis `B`, read through `f`,
is an execution of the composite (in the transition system of Sections 2–3),
and the containment persists. -/
theorem guarded_lockstep (hf : Monotone f) {B : Basis sp} {σ ρ : State sp}
    {es : List (SEvent sp)} (h : SysExec B σ es ρ) :
    ∀ σ' : State (comp sp f), σ'.cur = σ.cur → (∀ k o, imgT f σ.R k o → σ'.R k o) →
      ∃ ρ', Exec σ' (es.filterMap (obs f)) ρ' ∧ ρ'.cur = ρ.cur ∧
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
    | commit γ =>
      -- unobservable: the composite stays put
      obtain ⟨ρ', hx, hc', hs'⟩ := ih σ' (by rw [hs.commit_cur]; exact hc)
        (fun k o h' => hsub k o (imgT_mono hs.sub k o h'))
      exact ⟨ρ', hx, hc', hs'⟩

/-- **Pushforward of runs.**  If `f` is monotone, every run of `𝒫` under any
basis, read through `f`, is a run of the composite from the same canonical
state, and its final table contains the image of `𝒫`'s final table. -/
theorem guarded_run (hf : Monotone f) {B : Basis sp} {i : I} {es : List (SEvent sp)}
    {ρ : State sp} (h : SysExec B (canon sp i) es ρ) :
    ∃ ρ', Exec (canon (comp sp f) i) (es.filterMap (obs f)) ρ' ∧ ρ'.cur = ρ.cur ∧
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
  | .commit _ :: es => emitted es

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
    | commit γ =>
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
      es'.filterMap SEvent.erase = .output (f m) :: storeEvs f ms ∧ CoordFree es' ∧
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
      ∃ ρ', Exec (canon (comp sp f) i) (es.filterMap (obs f)) ρ' ∧ GuardedRuns R f ρ') ∧
    (∀ i es ρ m ms, SysExec B (canon sp i) es ρ → emitted es = m :: ms →
      ∃ es' : List (SEvent (graph f)), es'.filterMap SEvent.erase = .output (f m) :: storeEvs f ms ∧
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
  | .commit γ => S.strat i a (.commit γ)

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

/-- Drop the commitments: `Out_δ(o) ↦ Out_ε(o)`, and commit events are dropped
(a list `l` erases to `l.filterMap eraseC`). -/
def eraseC : SEvent sq → Option (SEvent sq)
  | .input j => some (.input j)
  | .output _ o => some (.output [] o)
  | .commit _ => none

theorem erase_eraseC (e : SEvent sq) : (eraseC e).bind SEvent.erase = e.erase := by
  cases e <;> rfl

theorem eraseC_eraseC (e : SEvent sq) : (eraseC e).bind eraseC = eraseC e := by cases e <;> rfl

theorem eraseC_idem {e e' : SEvent sq} (h : eraseC e = some e') : eraseC e' = some e' := by
  cases e <;> cases h <;> rfl

theorem filterMap_eraseC_idem (l : List (SEvent sq)) :
    (l.filterMap eraseC).filterMap eraseC = l.filterMap eraseC := by
  rw [List.filterMap_filterMap]
  exact congrArg (fun g => List.filterMap g l) (funext eraseC_eraseC)

theorem map_erase_eraseC (l : List (SEvent sq)) :
<<<<<<< HEAD
    (l.filterMap eraseC).filterMap SEvent.erase = l.filterMap SEvent.erase := by
  rw [List.filterMap_filterMap]
  exact congrArg (fun g => List.filterMap g l) (funext erase_eraseC)

theorem map_erase_of_eraseC {l l' : List (SEvent sq)}
    (h : l.filterMap eraseC = l'.filterMap eraseC) :
=======
    (l.map eraseC).filterMap SEvent.erase = l.filterMap SEvent.erase := by
  induction l with
  | nil => rfl
  | cons e l ih => simp only [List.map_cons, erase_eraseC, ih]

theorem map_erase_of_eraseC {l l' : List (SEvent sq)} (h : l.map eraseC = l'.map eraseC) :
>>>>>>> sandbox-20e053a6-1144-45e4-ad0f-e8cf14292186
    l.filterMap SEvent.erase = l'.filterMap SEvent.erase := by
  rw [← map_erase_eraseC l, h, map_erase_eraseC]

/-- **Commitment-erased replacement.**  Same strategy, empty basis, and each
`Out_δ(o)` replaced by `Out_ε(o)`: after a local history, it allows an event
when the original allows one with the same erasure after a history with the
same erasure. -/
def eraseSys (S : Sys sq) : Sys sq where
  basis := fun _ => False
  strat i a' e' := ∃ a e, a.filterMap eraseC = a'.filterMap eraseC ∧ eraseC e = eraseC e' ∧
    S.strat i a e

theorem compliant_eraseSys {S : Sys sq} {i : J} {es : List (SEvent sq)}
    (h : Compliant (Allowed S i) es) :
    Compliant (Allowed (eraseSys S) i) (es.filterMap eraseC) := by
  intro a' e' b' hm
  obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.filterMap_eq_append_iff.1 hm
  obtain ⟨n, e, l, rfl, hn, he, _⟩ := List.filterMap_eq_cons_iff.1 h2
  have hA := h (l₁ ++ n) e l (by simp)
  have hfn : n.filterMap eraseC = [] := List.filterMap_eq_nil_iff.2 hn
  subst h1
  cases e with
  | input j => cases he; trivial
  | commit _ => cases he
  | output δ o =>
    cases he
    exact ⟨l₁ ++ n, .output δ o, by rw [List.filterMap_append, hfn, List.append_nil,
      filterMap_eraseC_idem], rfl, hA⟩

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
  | i, .commit _ :: l => lastIn i l

theorem lastIn_eraseC (i : J) (l : List (SEvent sq)) :
    lastIn i (l.filterMap eraseC) = lastIn i l := by
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
    | commit γ => rw [ih, hs.commit_cur]; rfl

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

/-- `cf_stepK` relative to `D`: if `𝒦` is Lifted-Monotone on `D` and `σ`'s
outputs lie in `D`, every image of an exposable `m ∈ D` is exposable at the
image state. -/
theorem cf_stepK_on {D : M → Prop} (hC : Joint.CEOn sk D) {σ : State sp}
    (hσ : ∀ k m, σ.R k m → D m) {m : M} (hm : D m) (hexp : Exposable σ m)
    {o : O} (ho : sk.S m o) : Exposable (imgK sk σ) o := by
  rintro k x ⟨m', hm', hx⟩ _
  have hrows : ∀ r ∈ [(m, o), (m', x)], D r.1 ∧ sk.S r.1 r.2 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨hm, ho⟩
    · exact ⟨hσ _ _ hm', hx⟩
  have hbd : ∀ j, m ≼ j → m' ≼ j → ∀ r ∈ [(m, o), (m', x)], r.1 ≼ j := by
    intro j h1 h2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h1
    · exact h2
  have h1 : (m, o) ∈ [(m, o), (m', x)] := List.mem_cons_self
  have h2 : (m', x) ∈ [(m, o), (m', x)] := List.mem_cons_of_mem _ List.mem_cons_self
  by_cases hmm : m ≼ m'
  · obtain ⟨u, hu, hall⟩ := hC _ hrows m' (hσ _ _ hm') (hbd m' hmm (PO.refl _))
    exact ⟨u, ⟨m', hm', hu⟩, hall _ h1, hall _ h2⟩
  · obtain ⟨w, hw, hmw, hm'w⟩ := hexp k m' hm' hmm
    obtain ⟨u, hu, hall⟩ := hC _ hrows w (hσ _ _ hw) (hbd w hmw hm'w)
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

/-- An empty-basis step is observable (no commit event is legal under the empty
basis) and is a step of the transition system of Sections 2–3. -/
theorem sysStep_empty_erase {J X : Type} [PO J] [PO X] {sq : Spec J X} {σ τ : State sq}
    {e : SEvent sq} (h : SysStep (fun _ => False) σ e τ) :
    ∃ e', e.erase = some e' ∧ Step σ e' τ := by
  cases h with
  | input hs => exact ⟨_, rfl, hs⟩
  | output hb hγ ho _ hcur hR =>
    cases hγ with
    | nil => exact ⟨_, rfl, Step.output _ _ _ ho hcur hR⟩
    | cons _ _ => exact (hb _ List.mem_cons_self).elim
  | @commit _ _ γ hb hne _ =>
    cases γ with
    | nil => exact absurd rfl hne
    | cons c _ => exact (hb c List.mem_cons_self).elim

/-- An empty-basis step is a step of the transition system of Sections 2–3. -/
theorem sysStep_empty_step {J X : Type} [PO J] [PO X] {sq : Spec J X} {σ τ : State sq}
    {e : SEvent sq} {e' : Event J X} (h : SysStep (fun _ => False) σ e τ)
    (he : e.erase = some e') : Step σ e' τ := by
  obtain ⟨e'', h1, h2⟩ := sysStep_empty_erase h
  rw [he] at h1; cases h1; exact h2

theorem sysExec_empty_exec {J X : Type} [PO J] [PO X] {sq : Spec J X} {σ τ : State sq}
    {es : List (SEvent sq)} (h : SysExec (fun _ => False) σ es τ) :
    Exec σ (es.filterMap SEvent.erase) τ := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih =>
    obtain ⟨e', he, st⟩ := sysStep_empty_erase hs
    rw [List.filterMap_cons_some he]
    exact .cons st ih

theorem isRun_sysExec_empty {J X : Type} [PO J] [PO X] {sq : Spec J X} {σ τ : State sq}
    {es : List (SEvent sq)} (h : SysExec (fun _ => False) σ es τ) (hσ : IsRun σ) : IsRun τ := by
  induction h with
  | nil => exact hσ
  | cons hs _ ih =>
    obtain ⟨e', _, st⟩ := sysStep_empty_erase hs
    exact ih (isRun_step hσ st)

/-- Under the empty basis, an execution whose erasure is empty is empty. -/
theorem sysExec_empty_nil {J X : Type} [PO J] [PO X] {sq : Spec J X} {σ τ : State sq}
    {es : List (SEvent sq)} (h : SysExec (fun _ => False) σ es τ)
    (he : es.filterMap SEvent.erase = []) : es = [] := by
  cases h with
  | nil => rfl
  | cons hs _ =>
    obtain ⟨e', h1, _⟩ := sysStep_empty_erase hs
    rw [List.filterMap_cons_some h1] at he; cases he

/-- Under the empty basis, an execution whose erasure starts with `a` starts
with an event erasing to `a`. -/
theorem sysExec_empty_cons {J X : Type} [PO J] [PO X] {sq : Spec J X} {σ τ : State sq}
    {es : List (SEvent sq)} {a : Event J X} {L : List (Event J X)}
    (h : SysExec (fun _ => False) σ es τ) (he : es.filterMap SEvent.erase = a :: L) :
    ∃ e es', es = e :: es' ∧ e.erase = some a ∧ es'.filterMap SEvent.erase = L := by
  cases h with
  | nil => cases he
  | @cons _ _ _ e es' hs _ =>
    obtain ⟨e', h1, _⟩ := sysStep_empty_erase hs
    rw [List.filterMap_cons_some h1] at he
    cases he
    exact ⟨e, es', rfl, h1, rfl⟩

/-! #### Guarded composite runs -/

/-- The store's trace after its first output: for each later upstream output
`m`, receive it and answer with `o`. -/
def storeTr : List (M × O) → List (Event M O)
  | [] => []
  | (m, o) :: ps => .input m :: .output o :: storeTr ps

/-- The store's trace after its first input, in blocks: for each later
upstream output `m`, receive it, then emit any number of answers `os`. -/
def blk : List (M × List O) → List (Event M O)
  | [] => []
  | (m, os) :: ps => .input m :: (os.map Event.output ++ blk ps)

omit [PO M] [PO O] in
theorem storeTr_blk : ∀ ps : List (M × O), storeTr ps = blk (ps.map fun p => (p.1, [p.2]))
  | [] => rfl
  | (m, o) :: ps => by
    show Event.input m :: Event.output o :: storeTr ps = Event.input m :: Event.output o :: _
    rw [storeTr_blk ps]; rfl

/-- `tr` is a store trace on upstream outputs `l`: starting at the first
output `m`, it emits any number of answers, then receives each later output and
emits any number of answers, up to a prefix of `l`.  The store need not answer
every input, and may emit nothing. -/
def Shaped (l : List M) (m : M) (tr : List (Event M O)) : Prop :=
  ∃ (os : List O) (ps : List (M × List O)), (m :: ps.map Prod.fst) <+: l ∧
    tr = os.map Event.output ++ blk ps

/-- **Guarded composite run.**  The upstream can emit `l` (`U l`), which starts
with `m`, and the store's system produces a run from `σ_𝒦(m)` on a prefix of
`l`.  For an upstream system `P`, `U = P.emits`. -/
def GRun (U : List M → Prop) (K : Sys sk) (l : List M) (m : M) (esK : List (SEvent sk)) : Prop :=
  U l ∧ Shaped l m (esK.filterMap SEvent.erase) ∧ ∃ ρK, Produces K m esK ρK

/-- The output sequences that a system's produced runs emit. -/
def Sys.emits (P : Sys sp) (l : List M) : Prop := ∃ i es ρ, Produces P i es ρ ∧ emitted es = l

theorem grun_mono {U U' : List M → Prop} (hU : ∀ l, U l → U' l) {K : Sys sk} {l : List M}
    {m : M} {esK : List (SEvent sk)} (h : GRun U K l m esK) : GRun U' K l m esK :=
  ⟨hU l h.1, h.2⟩

/-- The empty-basis store, whose strategy allows every event. -/
def noStore (sk : Spec M O) : Sys sk := Sys.free (fun _ => False)

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
    ∃ o ps esK ρ, ps.map Prod.fst = ms ∧ esK.filterMap SEvent.erase = .output o :: storeTr ps ∧
      Produces (noStore sk) m esK ρ ∧ IsRun ρ := by
  have hr0 : IsRun (canon sk m) := ⟨m, [], .nil _⟩
  obtain ⟨o, ho⟩ := (canon sk m).hasCur
  let τ := outState (canon sk m) o ho
  have h0 : Step (canon sk m) (.output o) τ := Step.output _ τ o ho rfl rfl
  obtain ⟨ps, ρ, hps, hx, hρ⟩ := follow hC ms τ (isRun_step hr0 h0) hc
  obtain ⟨esK, he, _, hK⟩ := execCF_coordFree (fun _ => False)
    (.output h0 (commonExpansion_exposable hC hr0 ho) hx)
  exact ⟨o, ps, esK, ρ, hps, he, ⟨hK, compliant_free _⟩, hρ⟩

omit [PO M] [PO O] in
theorem map_fst_single : ∀ ps : List (M × O),
    (ps.map fun p => (p.1, [p.2])).map Prod.fst = ps.map Prod.fst
  | [] => rfl
  | _ :: ps => congrArg _ (map_fst_single ps)

/-- **The empty-basis store follows the upstream**: for every output sequence
`m :: ms` the upstream can emit, if it is a chain, there is a guarded composite
run in which the store answers every output. -/
theorem noStore_follows (hC : sk.CommonExpansion) {U : List M → Prop} {m : M} {ms : List M}
    (hU : U (m :: ms)) (hc : ChainFrom none (m :: ms)) :
    ∃ esK o ps, GRun U (noStore sk) (m :: ms) m esK ∧ ps.map Prod.fst = ms ∧
      esK.filterMap SEvent.erase = .output o :: storeTr ps := by
  obtain ⟨o, ps, esK, ρ, hps, he, hK, _⟩ := store_follows hC (sk := sk) hc
  refine ⟨esK, o, ps, ⟨hU, ⟨[o], ps.map fun p => (p.1, [p.2]), ?_, ?_⟩, ρ, hK⟩, hps, he⟩
  · rw [map_fst_single, hps]; exact List.prefix_refl _
  · rw [he, storeTr_blk]; rfl

/-- **`𝒫` must commit when the composite is not monotone.**  If `𝒦` satisfies
Lifted Monotonicity on the outputs of `𝒫` and `𝒦 ∘ 𝒫` does not, some composite
output `o` is not exposable at a canonical state `σ(i)`, and no `m` with
`o ∈ K(m)` is exposable at `σ_𝒫(i)`: under the empty basis `𝒫` can never emit
one there. -/
theorem composite_needs_commit (hC : Joint.CEOn sk (Joint.Img sp))
    (hnot : ¬ (seq sp sk).LiftedMono) :
    ∃ i m o, sp.S i m ∧ sk.S m o ∧ ¬ Exposable (canon (seq sp sk) i) o ∧
      (∀ m', sp.S i m' → sk.S m' o → ¬ Exposable (canon sp i) m') ∧
      ∀ γ m' τ, SysStep (fun _ => False) (canon sp i) (.output γ m') τ → ¬ sk.S m' o := by
  have hall : ¬ ∀ i o, (seq sp sk).S i o → Exposable (canon (seq sp sk) i) o := fun h =>
    hnot ((liftedMono_iff_commonExpansion _).2 (canon_exposable_commonExpansion h))
  obtain ⟨i, o, ⟨m, hm, hmo⟩, hne⟩ : ∃ i o, (seq sp sk).S i o ∧
      ¬ Exposable (canon (seq sp sk) i) o :=
    Classical.byContradiction fun hn =>
      hall fun i o h => Classical.byContradiction fun he => hn ⟨i, o, h, he⟩
  have hcf : ∀ m', sp.S i m' → Exposable (canon sp i) m' → sk.S m' o →
      Exposable (canon (seq sp sk) i) o := by
    intro m' hm' he ho; rw [← imgK_canon sk i]
    exact cf_stepK_on hC (fun k m h => ⟨k, (canon sp i).sub k m h⟩) ⟨i, hm'⟩ he ho
  refine ⟨i, m, o, hm, hmo, hne, fun m' hm' ho he => hne (hcf m' hm' he ho), ?_⟩
  intro γ m' τ hs ho
  cases γ with
  | cons c _ =>
    cases hs with
    | output hb _ _ _ _ _ => exact hb c List.mem_cons_self
  | nil =>
    obtain ⟨hm', he, _, _⟩ := eps_step_iff.1 hs
    exact hne (hcf m' hm'.1 he ho)

/-! #### Guarded composite runs are runs of the composite -/

/-- The composite trace: `𝒫`'s events, with its `r`-th output replaced by the
store's answers to it (any number of them). -/
def merge : List (SEvent sp) → List (List O) → List (Event I O)
  | [], _ => []
  | .input j :: es, oss => .input j :: merge es oss
  | .output _ _ :: es, os :: oss => os.map Event.output ++ merge es oss
  | .output _ _ :: es, [] => merge es []
  | .commit _ :: es, oss => merge es oss

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
  | .commit δ :: es, m, ms, h => by
    obtain ⟨es₀, γ, es₁, rfl, h0, h1⟩ := emitted_split (es := es) h
    exact ⟨.commit δ :: es₀, γ, es₁, rfl, h0, h1⟩
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
  | .commit δ :: es, l, h => by
    obtain ⟨es₀, es₁, rfl, h0⟩ := emitted_prefix (es := es) h
    exact ⟨.commit δ :: es₀, es₁, rfl, h0⟩
  | .output γ m :: es, [], _ => ⟨[], _, rfl, rfl⟩
  | .output γ m :: es, a :: l, h => by
    obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.1 h
    obtain ⟨es₀, es₁, rfl, h0⟩ := emitted_prefix (es := es) h'
    exact ⟨.output γ a :: es₀, es₁, rfl, by simp [emitted, h0]⟩

omit [PO O] in
theorem merge_split : ∀ {es₀ : List (SEvent sp)} (γ : List (Commitment sp)) (m : M)
    (es₁ : List (SEvent sp)) (os : List O) (oss : List (List O)), emitted es₀ = [] →
    merge (es₀ ++ .output γ m :: es₁) (os :: oss) =
      merge es₀ [] ++ (os.map Event.output ++ merge es₁ oss)
  | [], _, _, _, _, _, _ => rfl
  | .input j :: es₀, γ, m, es₁, os, oss, h => by
    simp only [List.cons_append, merge]
    rw [merge_split (es₀ := es₀) γ m es₁ os oss h]
  | .commit δ :: es₀, γ, m, es₁, os, oss, h => by
    simp only [List.cons_append, merge]
    rw [merge_split (es₀ := es₀) γ m es₁ os oss h]
  | .output _ _ :: _, _, _, _, _, _, h => by cases h

/-- The store's answers to one input, in the composite: with `𝒫` at `σ`
holding the row `(cur, τK.cur)`, each answer of the empty-basis store is an
output event of the composite, and the join stays inside the composite's
table. -/
theorem answer_run {σ : State sp} : ∀ (os : List O) {τK ρK : State sk} {esK : List (SEvent sk)}
    (ρ' : State (seq sp sk)), SysExec (fun _ => False) τK esK ρK →
    esK.filterMap SEvent.erase = os.map Event.output → σ.R σ.cur τK.cur → Inv σ τK.R ρ' →
    ∃ ρ'', Exec ρ' (os.map Event.output) ρ'' ∧ Inv σ ρK.R ρ'' ∧ ρK.cur = τK.cur
  | [], _, _, esK, ρ', hK, htr, _, hI => by
    have : esK = [] := sysExec_empty_nil hK htr
    subst this; cases hK; exact ⟨ρ', .nil _, hI, rfl⟩
  | o :: os, τK, ρK, esK, ρ', hK, htr, hm, ⟨hc, hI⟩ => by
    obtain ⟨e, esK', rfl, he, htr'⟩ := sysExec_empty_cons hK htr
    cases e with
    | input _ => cases he
    | commit _ => cases he
    | output γ o' =>
    cases he
    cases hK with
    | @cons _ τ2 _ _ _ hs hK' =>
    match sysStep_empty_step hs rfl with
    | .output _ _ _ ho hc2 hR2 =>
      have hρo : ρ'.R ρ'.cur o := by rw [hc]; exact hI _ _ _ hm ho
      let ρ1 := outState ρ' o hρo
      have hst : Step ρ' (.output o) ρ1 := Step.output ρ' ρ1 o hρo rfl rfl
      have hI1 : Inv σ τ2.R ρ1 := by
        refine ⟨hc, fun k m' x hk hx => ?_⟩
        rw [hR2] at hx
        exact ⟨hI k m' x hk hx.1, hx.2⟩
      obtain ⟨ρ'', hx, hI'', hcur⟩ := answer_run os ρ1 hK' htr' (by rw [hc2]; exact hm) hI1
      exact ⟨ρ'', .cons hst hx, hI'', hcur.trans hc2⟩

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
    | commit γ =>
      have hI' : Inv τ sk.S ρ' :=
        ⟨hc.trans hs.commit_cur.symm, fun k m x hk hx => hI k m x (hs.sub _ _ hk) hx⟩
      exact ih he ρ' hI'
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

/-- Phase after the store has started: `𝒫`, the empty-basis store, and the
composite.  Each output of `𝒫` is received by the store, which answers it any
number of times. -/
theorem merge_lockstep (hC : sk.CommonExpansion) {B : Basis sp} {σ ρ : State sp}
    {es : List (SEvent sp)} (h : SysExec B σ es ρ) :
    ∀ (ps : List (M × List O)) (τK ρK : State sk) (esK : List (SEvent sk))
      (ρ' : State (seq sp sk)),
      emitted es = ps.map Prod.fst → SysExec (fun _ => False) τK esK ρK →
      esK.filterMap SEvent.erase = blk ps → IsRun τK → (∀ k m, σ.R k m → τK.cur ≼ m) →
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
    have : esK = [] := sysExec_empty_nil hK htr
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
    | commit γ =>
      have hI' : Inv τ τK.R ρ' :=
        ⟨hc.trans hs.commit_cur.symm, fun k m x hk hx => hI k m x (hs.sub _ _ hk) hx⟩
      exact ih ps τK ρK esK ρ' he hK htr hτK (fun k m hk => habove k m (hs.sub _ _ hk)) hI'
    | output γ m =>
      obtain ⟨σc, _, hγ, hσc, _, hcurτ, hRτ⟩ := sysStep_output_inv hs
      obtain ⟨_, _, hin, _⟩ := containment hs
      cases ps with
      | nil => cases he
      | cons p ps =>
        obtain ⟨m₀, os⟩ := p
        simp only [emitted, List.map_cons, List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        obtain ⟨e1, esK1, rfl, he1, htr1⟩ := sysExec_empty_cons hK htr
        cases e1 with
        | output _ _ => cases he1
        | commit _ => cases he1
        | input m1 =>
        cases he1
        obtain ⟨A, Bk, rfl, hA, hB⟩ := List.filterMap_eq_append_iff.1 htr1
        cases hK with
        | @cons _ τ1 _ _ _ hs1 hK1 =>
        obtain ⟨τA, hxA, hxB⟩ := sysExec_append_inv hK1
        have st1 : Step τK (.input m) τ1 := sysStep_empty_step hs1 rfl
        have ⟨hc1, hR1⟩ : τ1.cur = m ∧ τ1.R = inputTable τK m := by
          cases st1 with
          | input _ _ _ hc hR => exact ⟨hc, hR⟩
        have hτm : τ.R τ.cur τ1.cur := by
          rw [hRτ, hcurτ, hc1, ← hγ.cur_eq]; exact ⟨hσc, PO.refl m⟩
        have hI1 : Inv τ τ1.R ρ' := by
          refine ⟨hc.trans hcurτ.symm, fun k m' x hk hx => ?_⟩
          rw [hR1] at hx
          exact hI k m' x (hin k m' hk).1 hx.1
        obtain ⟨ρ1, hx1, hI2, hcA⟩ := answer_run os ρ' hxA hA hτm hI1
        have hrA : IsRun τA := isRun_sysExec_empty hxA (isRun_step hτK st1)
        have habove' : ∀ k m', τ.R k m' → τA.cur ≼ m' := by
          intro k m' hk; rw [hcA, hc1]; exact (hin k m' hk).2
        obtain ⟨ρ'', hx2, hI'', hab⟩ := ih ps τA ρK Bk ρ1 he hxB hB hrA habove' hI2
        exact ⟨ρ'', (Dist.exec_append _ _).2 ⟨ρ1, hx1, hx2⟩, hI'', hab⟩

/-- **Guarded runs are runs of the composite.**  Let `𝒦` satisfy Lifted
Monotonicity, let `𝒫` run under any basis from `σ_𝒫(i)`, emitting `m :: ms`,
and let the store run under the empty basis from `σ_𝒦(m)`, answering `m`
with `os` and each later output with a block of answers (possibly empty).
Then `𝒫`'s run, with each output replaced by the store's answers to it, is a
run of `𝒦 ∘ 𝒫` from `σ(i)`.  Its table contains the join of `𝒫`'s final table
with the store's, and the store's state is a run state below every remaining
output of `𝒫`. -/
theorem composite_run (hC : sk.CommonExpansion) {B : Basis sp} {i : I} {es : List (SEvent sp)}
    {ρ : State sp} (hP : SysExec B (canon sp i) es ρ) {m : M} {ms : List M}
    (he : emitted es = m :: ms) {os : List O} {ps : List (M × List O)}
    (hps : ps.map Prod.fst = ms) {esK : List (SEvent sk)} {ρK : State sk}
    (hK : SysExec (fun _ => False) (canon sk m) esK ρK)
    (htr : esK.filterMap SEvent.erase = os.map Event.output ++ blk ps) :
    ∃ ρ', Exec (canon (seq sp sk) i) (merge es (os :: ps.map Prod.snd)) ρ' ∧ ρ'.cur = ρ.cur ∧
      (∀ k m x, ρ.R k m → ρK.R m x → ρ'.R k x) ∧ IsRun ρK ∧ ∀ k m, ρ.R k m → ρK.cur ≼ m := by
  obtain ⟨es₀, γ, es₁, rfl, h0, h1⟩ := emitted_split he
  obtain ⟨σ₀, hx0, hx1⟩ := sysExec_append_inv hP
  cases hx1 with
  | @cons _ τ₀ _ _ _ hs hx1 =>
  have hI0 : Inv (canon sp i) sk.S (canon (seq sp sk) i) :=
    ⟨rfl, fun k m' x hk hx => ⟨⟨m', hk.1, hx⟩, hk.2⟩⟩
  obtain ⟨ρ₀, hxA, hc0, hIA⟩ := merge_inputs (sk := sk) hx0 h0 _ hI0
  obtain ⟨σc, _, hγ, hσc, _, hcurτ, hRτ⟩ := sysStep_output_inv hs
  obtain ⟨_, _, hin, _⟩ := containment hs
  obtain ⟨A, Bk, rfl, hA, hB⟩ := List.filterMap_eq_append_iff.1 htr
  obtain ⟨τA, hxA', hxB⟩ := sysExec_append_inv hK
  have hτm : τ₀.R τ₀.cur (canon sk m).cur := by
    show τ₀.R τ₀.cur m
    rw [hRτ, hcurτ, ← hγ.cur_eq]; exact ⟨hσc, PO.refl m⟩
  have hI1 : Inv τ₀ (canon sk m).R ρ₀ :=
    ⟨hc0.trans hcurτ.symm, fun k m' x hk hx => hIA k m' x (hin k m' hk).1 hx.1⟩
  obtain ⟨ρ1, hx1', hI2, hcA⟩ := answer_run os ρ₀ hxA' hA hτm hI1
  have hrA : IsRun τA := isRun_sysExec_empty hxA' ⟨m, [], .nil _⟩
  have hab1 : ∀ k m', τ₀.R k m' → τA.cur ≼ m' := by
    intro k m' hk; rw [hcA]; exact (hin k m' hk).2
  obtain ⟨ρ', hxB', ⟨hcB, hIB⟩, hab⟩ :=
    merge_lockstep hC hx1 ps τA ρK Bk ρ1 (by rw [h1, hps]) hxB hB hrA hab1 hI2
  refine ⟨ρ', ?_, hcB, hIB, isRun_sysExec_empty hxB hrA, hab⟩
  rw [merge_split γ m es₁ os _ h0]
  exact (Dist.exec_append _ _).2 ⟨ρ₀, hxA, (Dist.exec_append _ _).2 ⟨ρ1, hx1', hxB'⟩⟩

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
  ∃ esK, GRun U K l m esK ∧ esK.filterMap SEvent.erase = tr

/-- **Erasure, lockstep.**  If `𝒦` satisfies the common-expansion condition,
then from any run state `σ'` with the same current input whose table contains
`σ`'s, every store execution under any basis, with its commitments erased, is
an execution under the empty basis, and the containment persists after each
event. -/
theorem erase_lockstep (hC : sk.CommonExpansion) {BK : Basis sk} {σ ρ : State sk}
    {es : List (SEvent sk)} (h : SysExec BK σ es ρ) :
    ∀ σ' : State sk, IsRun σ' → σ'.cur = σ.cur → (∀ k u, σ.R k u → σ'.R k u) →
      ∃ ρ', SysExec (fun _ => False) σ' (es.filterMap eraseC) ρ' ∧ IsRun ρ' ∧ ρ'.cur = ρ.cur ∧
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
    | commit γ =>
      -- dropped by the erasure
      exact ih σ' hr (by rw [hc, hs.commit_cur]) (fun k u hu => hsub _ _ (hs.sub _ _ hu))

/-- **(a) The replacement emits everything the original does.**  If `𝒦`
satisfies Lifted Monotonicity, every guarded composite run of a store system
`K` has, on the same upstream output sequence, a guarded composite run of
`eraseSys K` with the same observable trace, whose table contains the
original's.  Proper coordination is not needed. -/
theorem erase_simulates (hC : sk.CommonExpansion) {U : List M → Prop} {K : Sys sk}
    {l : List M} {m : M} {esK : List (SEvent sk)} (h : GRun U K l m esK) :
<<<<<<< HEAD
    GRun U (eraseSys K) l m (esK.filterMap eraseC) ∧
      (esK.filterMap eraseC).filterMap SEvent.erase = esK.filterMap SEvent.erase ∧
      ∀ ρK, Produces K m esK ρK → ∃ ρ', Produces (eraseSys K) m (esK.filterMap eraseC) ρ' ∧
=======
    GRun U (eraseSys K) l m (esK.map eraseC) ∧
      (esK.map eraseC).filterMap SEvent.erase = esK.filterMap SEvent.erase ∧
      ∀ ρK, Produces K m esK ρK → ∃ ρ', Produces (eraseSys K) m (esK.map eraseC) ρ' ∧
>>>>>>> sandbox-20e053a6-1144-45e4-ad0f-e8cf14292186
        IsRun ρ' ∧ ∀ k u, ρK.R k u → ρ'.R k u := by
  obtain ⟨hU, hS, ρK, hK⟩ := h
  have main : ∀ ρK, Produces K m esK ρK → ∃ ρ', Produces (eraseSys K) m (esK.filterMap eraseC) ρ' ∧
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

/-! #### Pipelines -/

/-- The outputs of an event list, in order. -/
def outs : List (Event I O) → List O
  | [] => []
  | .input _ :: es => outs es
  | .output o :: es => o :: outs es

theorem emitted_eq_outs {J X : Type} [PO J] [PO X] {sq : Spec J X} :
    ∀ es : List (SEvent sq), emitted es = outs (es.filterMap SEvent.erase)
  | [] => rfl
  | .input _ :: es => emitted_eq_outs es
  | .output _ _ :: es => congrArg _ (emitted_eq_outs es)
  | .commit _ :: es => emitted_eq_outs es

omit [PO M] [PO O] in
theorem outs_append : ∀ a b : List (Event M O), outs (a ++ b) = outs a ++ outs b
  | [], _ => rfl
  | .input _ :: a, b => outs_append a b
  | .output _ :: a, b => congrArg _ (outs_append a b)

omit [PO M] [PO O] in
theorem outs_output : ∀ os : List O, outs (os.map (Event.output (I := M))) = os
  | [] => rfl
  | _ :: os => congrArg _ (outs_output os)

omit [PO M] [PO O] in
theorem outs_blk : ∀ ps : List (M × List O), outs (blk ps) = (ps.map Prod.snd).flatten
  | [] => rfl
  | (_, os) :: ps => by
    show outs (os.map Event.output ++ blk ps) = os ++ (ps.map Prod.snd).flatten
    rw [outs_append, outs_output, outs_blk ps]

omit [PO O] in
theorem outs_merge : ∀ (es : List (SEvent sp)) (oss : List (List O)),
    (emitted es).length = oss.length → outs (merge es oss) = oss.flatten
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | .input _ :: es, oss, h => outs_merge es oss h
  | .commit _ :: es, oss, h => outs_merge es oss h
  | .output _ _ :: es, os :: oss, h => by
    show outs (os.map Event.output ++ merge es oss) = os ++ oss.flatten
    rw [outs_append, outs_output, outs_merge es oss (by simpa [emitted] using h)]
  | .output _ _ :: es, [], h => by cases h

/-- The output sequences that the store parts of guarded composite runs emit:
the guarded composite's behaviour as an upstream for a further stage. -/
def GEmits (U : List M → Prop) (K : Sys sk) (l' : List O) : Prop :=
  ∃ l m esK, GRun U K l m esK ∧ outs (esK.filterMap SEvent.erase) = l'

/-- **Every guarded composite run is a run of the composite.**  Let `𝒦`
satisfy Lifted Monotonicity, `P` be any system of `𝒫`, and `K` any store
system.  For every guarded composite run, some run that `P` produces has a
prefix whose events, with each output replaced by the store's answers to it,
form a run of `𝒦 ∘ 𝒫` from a canonical state. -/
theorem grun_composite (hC : sk.CommonExpansion) {P : Sys sp} {K : Sys sk} {l : List M}
    {m : M} {esK : List (SEvent sk)} (h : GRun P.emits K l m esK) :
    ∃ i es₀ σ₀ ρ' oss, SysExec P.basis (canon sp i) es₀ σ₀ ∧ emitted es₀ <+: l ∧
      (emitted es₀).length = oss.length ∧ oss.flatten = outs (esK.filterMap SEvent.erase) ∧
      Exec (canon (seq sp sk) i) (merge es₀ oss) ρ' := by
  obtain ⟨hR, _, _⟩ := erase_simulates hC h
  obtain ⟨⟨i, es, ρ, hP, rfl⟩, ⟨os, ps, hpre, hsh⟩, ρK, hK, _⟩ := hR
  have hsh' := hsh
  rw [map_erase_eraseC] at hsh'
  obtain ⟨es₀, es₁, rfl, h0⟩ := emitted_prefix hpre
  obtain ⟨σ₀, hx0, _⟩ := sysExec_append_inv hP.1
  obtain ⟨ρ', hx, _⟩ := composite_run hC hx0 h0 rfl hK hsh
  refine ⟨i, es₀, σ₀, ρ', os :: ps.map Prod.snd, hx0, by rw [h0]; exact hpre, ?_, ?_, hx⟩
  · rw [h0]; simp
  · rw [hsh', outs_append, outs_output, outs_blk]; rfl

/-- **Pipeline step.**  The guarded composite of `𝒫` (any system) and a
Lifted-Monotone `𝒦` (any store system) emits only what `𝒦 ∘ 𝒫` emits under its
canonical basis.  So the guarded composite is itself an upstream system for a
further stage. -/
theorem pipeline_step (hC : sk.CommonExpansion) {P : Sys sp} {K : Sys sk} {l' : List O}
    (h : GEmits P.emits K l') : (Sys.free (canonBasis (seq sp sk))).emits l' := by
  obtain ⟨l, m, esK, hg, rfl⟩ := h
  obtain ⟨i, es₀, σ₀, ρ', oss, _, _, hlen, hfl, hx⟩ := grun_composite hC hg
  obtain ⟨es', he', hc⟩ := exec_canonExec hx
  refine ⟨i, es', ρ', produces_free.2 (canonExec_sysExec hc), ?_⟩
  rw [emitted_eq_outs, he', outs_merge es₀ _ hlen, hfl]

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
  obtain ⟨i, es₀, σ₀, ρ', oss, _, _, hlen, hfl, hx⟩ := grun_composite hC hg
  obtain ⟨es', he', _, hx'⟩ := execCF_coordFree (fun _ => False) (exec_execCF hCs hx ⟨i, [], .nil _⟩)
  refine ⟨i, es', ρ', produces_free.2 hx', ?_⟩
  rw [emitted_eq_outs, he', outs_merge es₀ _ hlen, hfl]

end General

/-! ### Proper Coordination

`𝒮₁ = sp` guards `𝒮₂ = sk`.  `𝒮₂|_{𝒮₁}` is `rest sp sk`, the downstream
restricted to the outputs of the upstream (`Joint.restrictTo (Joint.Img sp)`).
The pipeline is proper when `𝒮₂|_{𝒮₁}` needs no commitment.  The definition
does not mention the system that runs `𝒮₁`, so every result below holds for
every system for `𝒮₁`. -/

section ProperCoord
open Joint
variable {sk : Spec M O}

/-- `𝒮₂|_{𝒮₁}`: the downstream restricted to the outputs of the upstream. -/
abbrev rest (sp : Spec I M) (sk : Spec M O) : Spec {m // Img sp m} O :=
  restrictTo (Img sp) sk

/-- A specification **needs no commitment**: every output at every state it
reaches without commitment is exposable. -/
def NeedsNoCommit {J X : Type} [PO J] [PO X] (sq : Spec J X) : Prop :=
  ∀ τ : State sq, ReachableCF τ → ∀ o, τ.R τ.cur o → Exposable τ o

/-- **Definition (Proper Coordination).**  The pipeline in which `𝒮₁` guards
`𝒮₂` is proper when `𝒮₂|_{𝒮₁}` needs no commitment. -/
def Proper (sp : Spec I M) (sk : Spec M O) : Prop := NeedsNoCommit (rest sp sk)

/-- Proper means the common-expansion condition for `𝒮₂|_{𝒮₁}` (the exposure
boundary). -/
theorem proper_iff_ce : Proper sp sk ↔ (rest sp sk).CommonExpansion :=
  (exposure_boundary _).symm

/-- **Theorem (Proper Coordination) (1).**  The pipeline is proper exactly
when `𝒮₂` satisfies Lifted Monotonicity on the outputs of `𝒮₁`. -/
theorem proper_iff : Proper sp sk ↔ CEOn sk (Img sp) := by
  rw [proper_iff_ce, ← liftedMono_iff_commonExpansion, ← ceOn_iff_restrictTo]

/-- By Complete CALM, proper also means that `𝒮₂|_{𝒮₁}` is consistent. -/
theorem proper_iff_consistent : Proper sp sk ↔ (rest sp sk).Consistent := by
  rw [proper_iff_ce, complete_calm_commonExpansion]

/-- A Lifted-Monotone downstream makes every pipeline proper. -/
theorem proper_of_ce (hC : sk.CommonExpansion) : Proper sp sk :=
  proper_iff.2 (ceOn_of_ce hC _)

/-! #### Following the upstream: `𝒮₁` with its outputs typed as such -/

/-- `𝒮₁` with its outputs typed as outputs of `𝒮₁`. -/
def core (sp : Spec I M) : Spec I {m // Img sp m} :=
  ⟨fun i m => sp.S i m.1, fun i => let ⟨m, h⟩ := sp.total i; ⟨⟨m, i, h⟩, h⟩⟩

/-- The composite through `core 𝒮₁` and `𝒮₂|_{𝒮₁}` is `S₂ ∘ S₁`. -/
theorem seq_core (sp : Spec I M) (sk : Spec M O) : seq (core sp) (rest sp sk) = seq sp sk := by
  apply Spec.ext'
  funext i o; apply propext
  exact ⟨fun ⟨m, h1, h2⟩ => ⟨m.1, h1, h2⟩, fun ⟨m, h1, h2⟩ => ⟨⟨m, i, h1⟩, h1, h2⟩⟩

/-- The input skeleton of a system event: `some (some j)` for an input,
`some none` for an output, and nothing for a commit event. -/
def skel {J X : Type} [PO J] [PO X] {sq : Spec J X} : SEvent sq → Option (Option J)
  | .input j => some (some j)
  | .output _ _ => some none
  | .commit _ => none

omit [PO O] in
/-- The composite trace depends only on where `𝒫`'s inputs and outputs are. -/
theorem merge_congr {N : Type} [PO N] {sq : Spec I N} :
    ∀ (es : List (SEvent sp)) (es' : List (SEvent sq)) (oss : List (List O)),
      es.filterMap skel = es'.filterMap skel → merge es oss = merge es' oss
  | [], [], _, _ => rfl
  | .commit _ :: es, es', oss, h => by
    simp only [merge]; exact merge_congr es es' oss (by simpa [skel] using h)
  | es, .commit _ :: es', oss, h => by
    simp only [merge]; exact merge_congr es es' oss (by simpa [skel] using h)
  | [], .input _ :: _, _, h => by simp [skel] at h
  | [], .output _ _ :: _, _, h => by simp [skel] at h
  | .input _ :: _, [], _, h => by simp [skel] at h
  | .output _ _ :: _, [], _, h => by simp [skel] at h
  | .input j :: es, .input j' :: es', oss, h => by
    simp only [List.filterMap_cons, skel, List.cons.injEq, Option.some.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [merge]; rw [merge_congr es es' oss h]
  | .input _ :: _, .output _ _ :: _, _, h => by simp [skel] at h
  | .output _ _ :: _, .input _ :: _, _, h => by simp [skel] at h
  | .output _ _ :: es, .output _ _ :: es', os :: oss, h => by
    simp only [List.filterMap_cons, skel, List.cons.injEq, true_and] at h
    simp only [merge]; rw [merge_congr es es' oss h]
  | .output _ _ :: es, .output _ _ :: es', [], h => by
    simp only [List.filterMap_cons, skel, List.cons.injEq, true_and] at h
    simp only [merge]; exact merge_congr es es' [] h
termination_by es es' => es.length + es'.length

/-- **Runs of `𝒮₁` are runs of `core 𝒮₁`.**  Every execution of `𝒮₁` under
any basis is matched, event for event, by an execution of `core 𝒮₁` under its
canonical basis from any state with the same current input and a larger table;
the containment persists. -/
theorem core_lockstep {B : Basis sp} {σ ρ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es ρ) :
    ∀ σ' : State (core sp), σ'.cur = σ.cur → (∀ k m, σ.R k m.1 → σ'.R k m) →
      ∃ es' ρ', SysExec (canonBasis (core sp)) σ' es' ρ' ∧ es'.filterMap skel = es.filterMap skel ∧
        (emitted es').map Subtype.val = emitted es ∧ ρ'.cur = ρ.cur ∧
        ∀ k m, ρ.R k m.1 → ρ'.R k m := by
  induction h with
  | nil σ => exact fun σ' hc hs => ⟨[], σ', .nil _, rfl, rfl, hc, hs⟩
  | @cons σ τ ρ e es hs _ ih =>
    intro σ' hc hsub
    cases e with
    | input j =>
      match hs with
      | .input (.input _ _ _ hleg hcur hR) =>
        obtain ⟨u, hu⟩ := hleg
        have hu' : σ'.R j ⟨u, j, σ.sub _ _ hu⟩ := hsub j ⟨u, _⟩ hu
        let τ' := inState σ' j _ hu'
        have st : Step σ' (.input j) τ' := Step.input σ' τ' j ⟨_, hu'⟩ rfl rfl
        obtain ⟨es', ρ', hx, hsk, hem, hcρ, hsρ⟩ := ih τ' hcur.symm (fun k m hk => by
          rw [hR] at hk; exact ⟨hsub k m hk.1, hk.2⟩)
        exact ⟨.input j :: es', ρ', .cons (.input st) hx, by simp [skel, hsk], hem, hcρ, hsρ⟩
    | output γ m =>
      obtain ⟨hcurτ, hσm, hin, _⟩ := containment hs
      have hm' : σ'.R σ'.cur ⟨m, σ.cur, σ.sub _ _ hσm⟩ := by rw [hc]; exact hsub _ ⟨m, _⟩ hσm
      obtain ⟨es', ρ', hx, hsk, hem, hcρ, hsρ⟩ := ih (outState σ' _ hm')
        (by show σ'.cur = τ.cur; rw [hc, hcurτ])
        (fun k m' hk => by
          obtain ⟨h1, h2⟩ := hin k m'.1 hk
          exact ⟨hsub k m' h1, h2⟩)
      exact ⟨.output _ _ :: es', ρ', .cons (canonical_support σ' _ hm') hx, by simp [skel, hsk],
        by simp [emitted, hem], hcρ, hsρ⟩
    | commit γ =>
      obtain ⟨es', ρ', hx, hsk, hem, hcρ, hsρ⟩ := ih σ' (by rw [hs.commit_cur]; exact hc)
        (fun k m hk => hsub k m (hs.sub _ _ hk))
      exact ⟨es', ρ', hx, by simpa [skel] using hsk, hem, hcρ, hsρ⟩

/-- Transport a run along an equality of specifications. -/
theorem exec_cast {J X : Type} [PO J] [PO X] {sq sq' : Spec J X} (h : sq = sq') {i : J}
    {tr : List (Event J X)} {ρ : State sq} (hx : Exec (canon sq i) tr ρ) :
    ∃ ρ' : State sq', Exec (canon sq' i) tr ρ' ∧ ρ'.cur = ρ.cur ∧ ∀ k x, ρ.R k x → ρ'.R k x := by
  subst h; exact ⟨ρ, hx, rfl, fun _ _ h => h⟩

omit [PO M] in
theorem map_val_inj {D : M → Prop} :
    ∀ {l l' : List {m // D m}}, l.map Subtype.val = l'.map Subtype.val → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Subtype.ext h.1, map_val_inj h.2]

omit [PO M] in
theorem lift_list {D : M → Prop} :
    ∀ l : List M, (∀ x ∈ l, D x) → ∃ l' : List {m // D m}, l'.map Subtype.val = l
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨l', hl⟩ := lift_list l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨⟨a, h a List.mem_cons_self⟩ :: l', by simp [hl]⟩

theorem chain_lift {D : M → Prop} :
    ∀ {a : {m // D m}} {l : List {m // D m}},
      ChainFrom (some a.1) (l.map Subtype.val) → ChainFrom (some a) l
  | _, [], _ => trivial
  | _, _ :: _, ⟨h1, h2⟩ => ⟨h1, chain_lift h2⟩

/-- Everything a system emits is in the image of its specification. -/
theorem emitted_img {B : Basis sp} {σ ρ : State sp} {es : List (SEvent sp)}
    (h : SysExec B σ es ρ) : ∀ m ∈ emitted es, Img sp m := by
  induction h with
  | nil => intro m hm; cases hm
  | @cons σ τ ρ e es hs _ ih =>
    cases e with
    | input j => intro m hm; exact ih m hm
    | commit γ => intro m hm; exact ih m hm
    | output γ m' =>
      intro m hm
      rcases List.mem_cons.1 hm with rfl | hm
      · exact ⟨σ.cur, σ.sub _ _ (containment hs).2.1⟩
      · exact ih m hm

/-- **Theorem (Proper Coordination) (2), the composite run.**  In a proper
pipeline, let `𝒮₁` run under any basis, emitting `m :: ms`, and let
`𝒮₂|_{𝒮₁}` run under the empty basis from `σ(m)`, receiving each later output
and answering any number of times (possibly never).  Then `𝒮₁`'s run, with
each output replaced by the answers to it, is a run of `S₂ ∘ S₁`.  Its table
contains the join of the two tables, and the downstream's current input is
below every output still in `𝒮₁`'s table. -/
theorem proper_run (hP : Proper sp sk) {B : Basis sp} {i : I} {es : List (SEvent sp)}
    {ρ : State sp} (hx : SysExec B (canon sp i) es ρ) {m : {m // Img sp m}}
    {ms : List {m // Img sp m}} (he : emitted es = m.1 :: ms.map Subtype.val) {os : List O}
    {ps : List ({m // Img sp m} × List O)} (hps : ps.map Prod.fst = ms)
    {esK : List (SEvent (rest sp sk))} {ρK : State (rest sp sk)}
    (hK : SysExec (fun _ => False) (canon (rest sp sk) m) esK ρK)
    (htr : esK.filterMap SEvent.erase = os.map Event.output ++ blk ps) :
    ∃ ρ' : State (seq sp sk), Exec (canon (seq sp sk) i) (merge es (os :: ps.map Prod.snd)) ρ' ∧
      ρ'.cur = ρ.cur ∧ (∀ k m x (h : Img sp m), ρ.R k m → ρK.R ⟨m, h⟩ x → ρ'.R k x) ∧
      IsRun ρK ∧ ∀ k m, ρ.R k m → ρK.cur.1 ≼ m := by
  have hC := proper_iff_ce.1 hP
  obtain ⟨es', ρc, hxc, hsk, hem, hcρ, hsρ⟩ :=
    core_lockstep hx (canon (core sp) i) rfl (fun _ _ h => h)
  have he' : emitted es' = m :: ms := map_val_inj (by rw [hem, he]; rfl)
  obtain ⟨ρ1, hx1, hc1, hj1, hr1, hab1⟩ := composite_run hC hxc he' hps hK htr
  obtain ⟨ρ', hx', hc', hs'⟩ := exec_cast (seq_core sp sk) hx1
  refine ⟨ρ', ?_, hc'.trans (hc1.trans hcρ),
    fun k m x h hk hxK => hs' _ _ (hj1 k ⟨m, h⟩ x (hsρ k ⟨m, h⟩ hk) hxK), hr1,
    fun k m hk => hab1 k ⟨m, k, ρ.sub _ _ hk⟩ (hsρ k ⟨m, k, ρ.sub _ _ hk⟩ hk)⟩
  rw [merge_congr es es' _ hsk.symm]; exact hx'

/-- **Theorem (Proper Coordination) (2), following.**  In a proper pipeline,
`𝒮₂|_{𝒮₁}` under the empty basis follows every run of `𝒮₁` under any basis:
it starts at the first output `m`, answers it, and receives and answers each
later output, with no commitment.  The result is a run of `S₂ ∘ S₁`. -/
theorem proper_follows (hP : Proper sp sk) {B : Basis sp} {i : I} {es : List (SEvent sp)}
    {ρ : State sp} (hx : SysExec B (canon sp i) es ρ) {m : M} {ms : List M}
    (he : emitted es = m :: ms) :
    ∃ (hm : Img sp m) (o : O) (ps : List ({m // Img sp m} × O))
      (esK : List (SEvent (rest sp sk))) (ρK : State (rest sp sk)),
      ps.map (fun p => p.1.1) = ms ∧ esK.filterMap SEvent.erase = .output o :: storeTr ps ∧
      Produces (noStore (rest sp sk)) ⟨m, hm⟩ esK ρK ∧
      ∃ ρ' : State (seq sp sk),
        Exec (canon (seq sp sk) i) (merge es ([o] :: ps.map fun p => [p.2])) ρ' ∧ ρ'.cur = ρ.cur := by
  have hC := proper_iff_ce.1 hP
  have himg := emitted_img hx
  rw [he] at himg
  have hm : Img sp m := himg m List.mem_cons_self
  obtain ⟨ms', hms'⟩ := lift_list ms (fun x hx => himg x (List.mem_cons_of_mem _ hx))
  have hc : ChainFrom (some m) ms := by
    have := emitted_chain hx none (fun _ h => by cases h)
    rw [he] at this; exact this
  have hc' : ChainFrom (some (⟨m, hm⟩ : {m // Img sp m})) ms' :=
    chain_lift (by rw [hms']; exact hc)
  obtain ⟨o, ps, esK, ρK, hps, htr, hK, _⟩ := store_follows hC hc'
  have hps' : ps.map (fun p => p.1.1) = ms := by
    rw [← hms', ← hps, List.map_map]; rfl
  obtain ⟨ρ', hx', hc'', _⟩ := proper_run hP hx (m := ⟨m, hm⟩) (ms := ms')
    (by rw [he, hms']) (os := [o]) (ps := ps.map fun p => (p.1, [p.2]))
    (by rw [map_fst_single, hps]) hK.1 (by rw [htr, storeTr_blk]; rfl)
  refine ⟨hm, o, ps, esK, ρK, hps', htr, hK, ρ', ?_, hc''⟩
  have e : (ps.map fun p => (p.1, [p.2])).map Prod.snd = ps.map fun p => [p.2] := by
    rw [List.map_map]; rfl
  rw [← e]; exact hx'

/-- **Theorem (Proper Coordination) (2), confluence.**  In a proper pipeline,
consider triples of a state of `𝒮₁`, a run state of `𝒮₂|_{𝒮₁}` below every
output in `𝒮₁`'s table, and a run state of `S₂ ∘ S₁` containing the join of
their tables.  If the states of `𝒮₁` can be continued (under any bases) to one
state with current input `j`, the composite states are confluent at `j`. -/
theorem proper_confluent (hP : Proper sp sk)
    (fam : List (State sp × State (rest sp sk) × State (seq sp sk)))
    (hrun : ∀ p ∈ fam, IsRun p.2.2) (hK : ∀ p ∈ fam, IsRun p.2.1)
    (hsub : ∀ p ∈ fam, ∀ k m x (h : Img sp m), p.1.R k m → p.2.1.R ⟨m, h⟩ x → p.2.2.R k x)
    (habove : ∀ p ∈ fam, ∀ k m, p.1.R k m → p.2.1.cur.1 ≼ m)
    (j : I) (hj : ∀ p ∈ fam, p.2.2.cur ≼ j)
    (hS : ∃ τ : State sp, τ.cur = j ∧ ∀ p ∈ fam, ∃ (B : Basis sp) (es : List (SEvent sp)),
      SysExec B p.1 es τ) :
    ConfluentAt (fam.map fun p => p.2.2) j := by
  have hC := proper_iff_ce.1 hP
  obtain ⟨τ, hτ, hall⟩ := hS
  obtain ⟨m, hm⟩ := τ.hasCur
  rw [hτ] at hm
  have hI : Img sp m := ⟨j, τ.sub _ _ hm⟩
  have hm' : ∀ p ∈ fam, p.1.R j m := fun p hp => by
    obtain ⟨B, es, hx⟩ := hall p hp; exact hx.sub _ _ hm
  let pick : State sp × State (rest sp sk) × State (seq sp sk) → {m // Img sp m} × O :=
    fun p => (p.2.1.cur, p.2.1.hasCur.choose)
  obtain ⟨u, hu, hallu⟩ := hC (fam.map pick)
    (by
      intro r hr
      obtain ⟨p, _, rfl⟩ := List.mem_map.1 hr
      exact p.2.1.sub _ _ p.2.1.hasCur.choose_spec)
    ⟨m, hI⟩ (by
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
  have hpu : p.2.1.R ⟨m, hI⟩ u :=
    run_survive (hK p hp) (habove p hp j m (hm' p hp)) hu hv
      (hallu (pick p) (List.mem_map.2 ⟨p, hp, rfl⟩))
  exact hsub p hp j m u hI (hm' p hp) hpu

/-- **Theorem (Proper Coordination) (3).**  In a proper pipeline, if
`S₂ ∘ S₁` violates Lifted Monotonicity, some composite output `o` is not
exposable at a canonical state `σ(i)`, and `𝒮₁` must commit to emit any `m`
with `o ∈ S₂(m)` there: no such `m` is exposable at `σ_{𝒮₁}(i)`, and under the
empty basis no output event there emits one. -/
theorem proper_needs_commit (hP : Proper sp sk) (hnot : ¬ (seq sp sk).LiftedMono) :
    ∃ i m o, sp.S i m ∧ sk.S m o ∧ ¬ Exposable (canon (seq sp sk) i) o ∧
      (∀ m', sp.S i m' → sk.S m' o → ¬ Exposable (canon sp i) m') ∧
      ∀ γ m' τ, SysStep (fun _ => False) (canon sp i) (.output γ m') τ → ¬ sk.S m' o :=
  composite_needs_commit (proper_iff.1 hP) hnot

/-- A proper pipeline's downstream can drop its commitments: for any system
`K` for `𝒮₂|_{𝒮₁}`, its commitment-erased replacement has every guarded run of
`K`, with the same trace and a larger table. -/
theorem proper_erase (hP : Proper sp sk) {U : List {m // Img sp m} → Prop}
    {K : Sys (rest sp sk)} {l : List {m // Img sp m}} {m : {m // Img sp m}}
    {esK : List (SEvent (rest sp sk))} (h : GRun U K l m esK) :
<<<<<<< HEAD
    GRun U (eraseSys K) l m (esK.filterMap eraseC) ∧
      (esK.filterMap eraseC).filterMap SEvent.erase = esK.filterMap SEvent.erase ∧
      ∀ ρK, Produces K m esK ρK → ∃ ρ', Produces (eraseSys K) m (esK.filterMap eraseC) ρ' ∧
=======
    GRun U (eraseSys K) l m (esK.map eraseC) ∧
      (esK.map eraseC).filterMap SEvent.erase = esK.filterMap SEvent.erase ∧
      ∀ ρK, Produces K m esK ρK → ∃ ρ', Produces (eraseSys K) m (esK.map eraseC) ρ' ∧
>>>>>>> sandbox-20e053a6-1144-45e4-ad0f-e8cf14292186
        IsRun ρ' ∧ ∀ k u, ρK.R k u → ρ'.R k u :=
  erase_simulates (proper_iff_ce.1 hP) h

/-! #### Pipelines -/

/-- The output sequences of a system for `𝒮₁`, typed as inputs of
`𝒮₂|_{𝒮₁}`. -/
def liftU (P : Sys sp) (l : List {m // Img sp m}) : Prop := P.emits (l.map Subtype.val)

/-- **Pipeline step.**  In a proper pipeline, with any system `P` for `𝒮₁` and
any system `K` for `𝒮₂|_{𝒮₁}`, the pipeline emits only what `S₂ ∘ S₁` emits
under its canonical basis.  So a proper pipeline is itself a guard for a
further stage. -/
theorem proper_pipeline_step (hP : Proper sp sk) {P : Sys sp} {K : Sys (rest sp sk)}
    {l' : List O} (h : GEmits (liftU P) K l') : (Sys.free (canonBasis (seq sp sk))).emits l' := by
  have hC := proper_iff_ce.1 hP
  obtain ⟨l, m, esK, hg, rfl⟩ := h
  obtain ⟨hR, _, _⟩ := erase_simulates hC hg
  obtain ⟨⟨i, es, ρ, hPr, hel⟩, ⟨os, ps, hpre, hsh⟩, ρK, hK, _⟩ := hR
  have hsh' := hsh
  rw [map_erase_eraseC] at hsh'
  have hpre' : (m :: ps.map Prod.fst).map Subtype.val <+: emitted es := by
    rw [hel]; exact hpre.map _
  obtain ⟨es₀, es₁, rfl, h0⟩ := emitted_prefix hpre'
  obtain ⟨σ₀, hx0, _⟩ := sysExec_append_inv hPr.1
  obtain ⟨ρ', hx, _⟩ := proper_run hP hx0 (m := m) (ms := ps.map Prod.fst) (by rw [h0]; rfl) rfl
    hK hsh
  obtain ⟨es', he', hc⟩ := exec_canonExec hx
  refine ⟨i, es', ρ', produces_free.2 (canonExec_sysExec hc), ?_⟩
  rw [emitted_eq_outs, he', outs_merge es₀ _ (by rw [h0]; simp), hsh', outs_append, outs_output,
    outs_blk]
  rfl

end ProperCoord


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

/-- Every log is an output of the log specification (at itself). -/
theorem smr_img {Cmd : Type} (m : Pfx Cmd) : Joint.Img (smrS1 (Cmd := Cmd)) m := ⟨m, fun _ h => h⟩

/-- **The replicated store coordinates exactly once.**  For any deterministic
state machine and two distinct commands, the log specification `𝒫 = smrS1`
and the composite violate Lifted Monotonicity, execution is monotone, and the
pipeline is proper; some composite output needs a commitment, which `𝒫` must
make.  Every log is an output of `𝒫`, so the restriction to its outputs
removes no input. -/
theorem smr_proper {Cmd Stt R : Type} (δ : Stt → Cmd → Stt × R) (σ0 : Stt)
    {c₁ c₂ : Cmd} (hne : c₁ ≠ c₂) :
    ¬ (smrS1 (Cmd := Cmd)).LiftedMono ∧ ¬ (comp smrS1 (execF δ σ0)).LiftedMono ∧
      Monotone (execF δ σ0) ∧ (∀ m, Joint.Img (smrS1 (Cmd := Cmd)) m) ∧
      Proper smrS1 (graph (execF δ σ0)) ∧
      ∃ i m, smrS1.S i m ∧ ¬ Exposable (canon (comp smrS1 (execF δ σ0)) i) (execF δ σ0 m) ∧
        ∀ m', smrS1.S i m' → execF δ σ0 m' = execF δ σ0 m → ¬ Exposable (canon smrS1 i) m' := by
  obtain ⟨h1, h2, hf, _⟩ := Inst.smr_example δ σ0 hne
  obtain ⟨i, m, hm, hne', hall, _⟩ := at_least_once_needed hf h2
  exact ⟨h1, h2, hf, smr_img, proper_of_ce (graph_commonExpansion hf), i, m, hm, hne', hall⟩

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
    ⟨_, ⟨⟨kb, _, _, produces_free.2 hP, rfl⟩, ⟨[f e], [(kb, [f kb])], List.prefix_refl _, rfl⟩, _, hK,
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
