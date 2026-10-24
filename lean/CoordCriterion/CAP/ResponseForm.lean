import CoordCriterion.CAP.CompleteCAP

/-!
# Response form of Complete CAP (Appendix `app:cap-response`)

* Def. `def:response-availability` / Response Partition Consistency
  (`ResponseAvailability`, `ResponsePC`, `RPCAt`);
* replicated systems, obligations and response interfaces;
* the canonical commitment `κ_u` (seal and choice applied together);
* Theorem `thm:complete-cap-response` in both directions
  (`complete_cap_response`).

Lemma `lem:forced-answer` and the remaining claims of the appendix are in
`CAP/ResponseAvailability.lean`; the register instance behind Corollary
`cor:gilbert-lynch` is in `CAP/Register.lean`.

Precise reading: the continuations of Response Availability are required to
be produced by the system (as for interface-form Availability); without that
the (1)⇒(2) proof cannot place the emissions it obtains into partitioned
histories of the system.
-/

namespace CC
namespace CAP

variable {I O : Type} [PO I] [PO O]
variable {sp : Spec I O} {D : Type} {n : Nat}

/-! ## Appendix `app:cap-response`: response availability

Precise reading chosen: Def. `def:response-availability` does not say that
its continuations are *produced by the system*; without that the (1)⇒(2)
proof of Theorem `thm:complete-cap-response` cannot place the emissions it
obtains into "partitioned histories of the system".  We require it, as the
interface-form Availability does. -/

/-- Def. `def:response-availability`, for a (possibly per-participant)
obligation `Q n p`. -/
def ResponseAvailability (Sys : System sp D) (Q : (n : Nat) → Fin n → Table I O) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ c, IsCut H c →
    ∀ (p : Fin n) (σ : State sp), LRun (canon sp (init p)) ((H p).take (c p)) σ →
      -- Answering
      (∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
        Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
        (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ j, LEv.inp j ∉ ext p) ∧
        ∃ γ o, Q n p σ.cur o ∧ LEv.out γ o ∈ ext p) ∧
      -- Input acceptance
      (∀ j, σ.cur ≼ j → ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
        Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
        (∀ q, comp q ≠ comp p → ext q = []) ∧ LEv.inp j ∈ ext p)

/-- Response Partition Consistency of a cut at `j`
(Def. `def:response-partition-consistency`). -/
def RPCAt (H : History sp D n) (c : Fin n → Nat) (j : I) : Prop :=
  ∃ u, sp.S j u ∧ ∀ p γ o, LEv.out γ o ∈ (H p).take (c p) → o ≼ u

def ResponsePC (Sys : System sp D) : Prop :=
  ∀ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat),
    WF init H → Produced Sys n init H → Partitioned H comp →
    ∀ c, IsCut H c →
    ∀ j : I, (∀ p σ, LRun (canon sp (init p)) ((H p).take (c p)) σ → σ.cur ≼ j) →
    RPCAt H c j

/-! ## Response form of Complete CAP (Theorem `thm:complete-cap-response`)

### Replicated systems, obligations, response interfaces -/

/-- Participant-independent local events (receives name the sender by number). -/
inductive LEvN (sp : Spec I O) (D : Type) where
  | inp (j : I)
  | out (γ : List (Commitment sp)) (o : O)
  | send (j : Option I) (d : D)
  | recv (q : Nat) (k : Nat) (j : Option I) (d : D)

def LEv.erase : LEv sp D n → LEvN sp D
  | .inp j => .inp j
  | .out γ o => .out γ o
  | .send j d => .send j d
  | .recv q k j d => .recv q.val k j d

/-- A replicated system gives every participant the same strategy, depending
only on its own initial input and local history — not on its identity, the
number of participants, or other participants' initial inputs. -/
def System.Replicated (Sys : System sp D) : Prop :=
  ∃ F : I → List (LEvN sp D) → LEvN sp D → Prop,
    ∀ n init p pre e, Sys.strat n init p pre e ↔ F (init p) (pre.map LEv.erase) e.erase

/-- Def. `def:response-obligation` (uniform case). -/
structure Obligation (sp : Spec I O) where
  Q : Table I O
  sub : ∀ i o, Q i o → sp.S i o
  total : ∀ i, ∃ o, Q i o
  up : ∀ i o u, Q i o → sp.S i u → o ≼ u → Q i u

/-- Def. `def:response-interface`. -/
def ResponseInterface (Q : Obligation sp) (T : Table I O) : Prop :=
  (∀ i o, T i o → Q.Q i o) ∧ (∀ i, ∃ o, T i o) ∧
  ∀ i o j, T i o → i ≼ j → ∃ u, T j u ∧ o ≼ u

/-- `S` is consistent on `T`. -/
def ConsistentOn (sp : Spec I O) (T : Table I O) : Prop :=
  ∀ rows : List (I × O), (∀ r ∈ rows, T r.1 r.2) →
    ∀ j, (∀ r ∈ rows, r.1 ≼ j) → ∃ u, sp.S j u ∧ ∀ r ∈ rows, r.2 ≼ u

theorem consistentOn_outs {T : Table I O} (hc : ConsistentOn sp T) {j : I} (L : List O)
    (hL : ∀ o ∈ L, ∃ i, T i o ∧ i ≼ j) : ∃ u, sp.S j u ∧ ∀ o ∈ L, o ≼ u := by
  let rows : List (I × O) := L.attach.map (fun o => (Classical.choose (hL o.1 o.2), o.1))
  obtain ⟨u, hu, hall⟩ := hc rows
    (by intro r hr; simp only [rows, List.mem_map] at hr
        obtain ⟨o, _, rfl⟩ := hr; exact (Classical.choose_spec (hL o.1 o.2)).1) j
    (by intro r hr; simp only [rows, List.mem_map] at hr
        obtain ⟨o, _, rfl⟩ := hr; exact (Classical.choose_spec (hL o.1 o.2)).2)
  exact ⟨u, hu, fun o ho => hall _ (by
    simp only [rows, List.mem_map]; exact ⟨⟨o, ho⟩, List.mem_attach _ _, rfl⟩)⟩

/-! ### The canonical commitment `κ_u` (seal and choice applied together) -/

/-- Rows the canonical event for `u` removes by commitment. -/
def Rm (σ : State sp) (u : O) (k : I) (x : O) : Prop := Sealed σ u k x ∨ Rejected σ u k x

theorem not_rm_of_le {σ : State sp} {u : O} {k : I} {x : O} (hx : σ.R k x) (h : u ≼ x) :
    ¬ Rm σ u k x := by
  rintro (⟨_, hs⟩ | ⟨_, hn, _⟩)
  · exact hs ⟨x, hx, h⟩
  · exact hn h

/-- A kept row that does not expand `u` is retired. -/
theorem retired_of_not_rm {σ : State sp} {u : O} {k : I} {x : O} (hx : σ.R k x)
    (hrm : ¬ Rm σ u k x) (hn : ¬ u ≼ x) : ∃ v, σ.R k v ∧ u ≼ v ∧ x ≼ v := by
  apply Classical.byContradiction
  intro hv
  apply hrm
  by_cases hs : ∃ v, σ.R k v ∧ u ≼ v
  · exact Or.inr ⟨hx, hn, fun ⟨_, h⟩ => h hs, fun ⟨_, _, h⟩ => hv h⟩
  · exact Or.inl ⟨hx, hs⟩

def kcState (σ : State sp) (u : O) (hu : σ.R σ.cur u) : State sp where
  cur := σ.cur
  R := fun k x => σ.R k x ∧ ¬ Rm σ u k x
  sub := fun k x h => σ.sub k x h.1
  hasCur := ⟨u, hu, not_rm_of_le hu (PO.refl u)⟩
  above := fun k x h => σ.above k x h.1

open Classical in
/-- The canonical commitment for `u`: defined when `u` is in the current fiber
and some row must be removed by commitment; it removes `Sealed_u ∪ Rejected_u`.
That this is a commitment (Eq. `commitment-excludes`) is checked here. -/
noncomputable def kc (u : O) : Commitment sp where
  f := fun σ => if h : σ.R σ.cur u ∧ ∃ k x, Rm σ u k x then some (kcState σ u h.1) else none
  cur_eq := by
    intro σ τ h; split at h
    · cases h; rfl
    · cases h
  sub := by
    intro σ τ h; split at h
    · cases h; exact fun k x h => h.1
    · cases h
  strict := by
    intro σ τ h; split at h
    · rename_i hh; cases h
      obtain ⟨k, x, hr⟩ := hh.2
      have hx : σ.R k x := by rcases hr with h | h; exact h.1; exact h.1
      exact ⟨k, x, hx, fun h => h.2 hr⟩
    · cases h
  excl := by
    intro σ τ h; split at h
    · cases h
      intro k x w hx hnx hw hxw
      have hrx : Rm σ u k x := Classical.byContradiction fun h => hnx ⟨hx, h⟩
      obtain ⟨hw1, hw2⟩ := hw
      -- some row at `k` expands both `u` and `w`
      have hv : ∃ v, σ.R k v ∧ u ≼ v ∧ w ≼ v := by
        by_cases huw : u ≼ w
        · exact ⟨w, hw1, huw, PO.refl w⟩
        · exact retired_of_not_rm hw1 hw2 huw
      obtain ⟨v, hv1, hv2, hv3⟩ := hv
      rcases hrx with ⟨_, hs⟩ | ⟨_, hn, _, hret⟩
      · exact hs ⟨v, hv1, hv2⟩
      · exact hret ⟨hx, hn, v, hv1, hv2, PO.trans hxw hv3⟩
    · cases h

theorem kc_apply_some {σ : State sp} {u : O} {σc : State sp}
    (h : applySeq σ [kc u] = some σc) :
    ∃ hu : σ.R σ.cur u, σc = kcState σ u hu := by
  simp only [applySeq] at h
  split at h
  · rename_i τ1 h1
    cases h
    simp only [kc] at h1
    split at h1
    · rename_i hh; cases h1; exact ⟨hh.1, rfl⟩
    · cases h1
  · cases h

/-- The canonical event for `u` is legal at any state with `u` in the current
fiber (Lemma `lem:canonical-commitment-normal-form`(2)). -/
theorem kc_legal {σ : State sp} {u : O} (hu : σ.R σ.cur u) :
    ∃ γ σc, (γ = [] ∨ γ = [kc u]) ∧ applySeq σ γ = some σc ∧ σc.R σc.cur u ∧
      Exposable σc u := by
  by_cases hrm : ∃ k x, Rm σ u k x
  · refine ⟨[kc u], kcState σ u hu, Or.inr rfl, ?_, ⟨hu, not_rm_of_le hu (PO.refl u)⟩, ?_⟩
    · simp only [applySeq, kc]; rw [dite_eq_left_of_eq_true (eq_true ⟨hu, hrm⟩)]
    · intro k x hx hn
      obtain ⟨v, hv1, hv2, hv3⟩ := retired_of_not_rm hx.1 hx.2 hn
      exact ⟨v, ⟨hv1, not_rm_of_le hv1 hv2⟩, hv2, hv3⟩
  · refine ⟨[], σ, Or.inl rfl, rfl, hu, ?_⟩
    intro k x hx hn
    exact retired_of_not_rm hx (fun h => hrm ⟨k, x, h⟩) hn

/-- Effect of a canonical event: it ends at `R[out ⪰ u]`. -/
theorem kc_effect {σ σc τ : State sp} {u : O} {γ : List (Commitment sp)}
    (hγ : γ = [] ∨ γ = [kc u]) (ha : applySeq σ γ = some σc) (hs : Step σc (.output u) τ) :
    Step σ (.output u) τ := by
  rcases hγ with rfl | rfl
  · simp [applySeq] at ha; subst ha; exact hs
  · obtain ⟨hu, rfl⟩ := kc_apply_some ha
    obtain ⟨_, hc, hR⟩ := step_output_inv hs
    refine Step.output σ τ u hu hc ?_
    rw [hR]; funext k x; apply propext
    simp only [outputTable, kcState]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, not_rm_of_le h.1 h.2⟩, h.2⟩⟩

/-! ### The replicated system of (2)⇒(1) -/

def curOf (i0 : I) : List (LEvN sp D) → I
  | [] => i0
  | .inp j :: l => curOf j l
  | .out _ _ :: l => curOf i0 l
  | .send _ _ :: l => curOf i0 l
  | .recv _ _ _ _ :: l => curOf i0 l

def emittedOf : List (LEvN sp D) → List O
  | [] => []
  | .out _ o :: l => o :: emittedOf l
  | .inp _ :: l => emittedOf l
  | .send _ _ :: l => emittedOf l
  | .recv _ _ _ _ :: l => emittedOf l

theorem curOf_append (a b : List (LEvN sp D)) (i0 : I) :
    curOf i0 (a ++ b) = curOf (curOf i0 a) b := by
  induction a generalizing i0 with
  | nil => rfl
  | cons e a ih => cases e <;> simp [curOf, ih]

theorem emittedOf_append (a b : List (LEvN sp D)) :
    emittedOf (a ++ b) = emittedOf a ++ emittedOf b := by
  induction a with
  | nil => rfl
  | cons e a ih => cases e <;> simp [emittedOf, ih]

theorem mem_emittedOf {L : List (LEv sp D n)} {γ : List (Commitment sp)} {o : O}
    (h : LEv.out γ o ∈ L) : o ∈ emittedOf (L.map LEv.erase) := by
  induction L with
  | nil => cases h
  | cons e L ih =>
    rcases List.mem_cons.1 h with rfl | h'
    · simp [LEv.erase, emittedOf]
    · cases e <;> simp [LEv.erase, emittedOf, ih h']

/-- The strategy: ignore messages, never send; emit, by the canonical event,
some `u ∈ T(i)` at the current input `i` that expands every earlier output. -/
noncomputable def respF (T : Table I O) (i0 : I) (pre : List (LEvN sp D)) : LEvN sp D → Prop
  | .out γ u => (γ = [] ∨ γ = [kc u]) ∧ T (curOf i0 pre) u ∧ ∀ o ∈ emittedOf pre, o ≼ u
  | _ => False

noncomputable def respSystem (T : Table I O) : System sp D where
  basis := fun c => ∃ u, c = kc u
  strat := fun _ init p pre e => respF T (init p) (pre.map LEv.erase) e.erase

/-- Invariant of participant runs of `respSystem T`. -/
def RInv (T : Table I O) (i0 : I) (pre : List (LEvN sp D)) (σ : State sp) : Prop :=
  σ.cur = curOf i0 pre ∧ Residual σ (emittedOf pre) ∧
  (∀ o ∈ emittedOf pre, ∃ i, T i o ∧ i ≼ σ.cur) ∧
  (emittedOf pre = [] ∨ ∃ i om, T i om ∧ i ≼ σ.cur ∧ ∀ o ∈ emittedOf pre, o ≼ om)

theorem rinv_run (T : Table I O) {N : Nat} {init : Fin N → I} {p : Fin N} :
    ∀ {σ τ : State sp} {L : List (LEv sp D N)}, LRun σ L τ →
    ∀ pre : List (LEv sp D N),
    (∀ a e b, L = a ++ e :: b → Allowed (respSystem T) N init p (pre ++ a) e) →
    RInv T (init p) (pre.map LEv.erase) σ → RInv T (init p) ((pre ++ L).map LEv.erase) τ := by
  intro σ τ L h
  induction h with
  | nil => intro pre _ hi; simpa using hi
  | @inp σ τ' ρ j es hs _ ih =>
    intro pre hc hi
    have := ih (pre ++ [.inp j]) (fun a e b hab => by
      have := hc (.inp j :: a) e b (by simp [hab]); simpa using this)
    simp only [List.append_assoc, List.singleton_append] at this
    apply this
    obtain ⟨⟨w, hw⟩, hcur, _⟩ := step_input_inv hs
    have hle : σ.cur ≼ τ'.cur := by rw [hcur]; exact σ.above _ _ hw
    obtain ⟨h1, h2, h3, h4⟩ := hi
    have hE : emittedOf ((pre ++ [LEv.inp j]).map LEv.erase) = emittedOf (pre.map LEv.erase) := by
      simp [emittedOf_append, LEv.erase, emittedOf]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [curOf_append, LEv.erase, curOf, hcur]
    · rw [hE]; have := residual_step h2 hs; simpa [outs] using this
    · rw [hE]; intro o ho; obtain ⟨i, hi1, hi2⟩ := h3 o ho; exact ⟨i, hi1, PO.trans hi2 hle⟩
    · rw [hE]; rcases h4 with h4 | ⟨i, om, hom, hi, hall⟩
      · exact Or.inl h4
      · exact Or.inr ⟨i, om, hom, PO.trans hi hle, hall⟩
  | @out σ σc τ' ρ γ u es ha hs _ _ ih =>
    intro pre hc hi
    have hA := hc [] (.out γ u) es (by simp)
    simp only [List.append_nil] at hA
    obtain ⟨_, hγ, hT, hge⟩ := hA
    have hstep := kc_effect hγ ha hs
    have := ih (pre ++ [.out γ u]) (fun a e b hab => by
      have := hc (.out γ u :: a) e b (by simp [hab]); simpa using this)
    simp only [List.append_assoc, List.singleton_append] at this
    apply this
    obtain ⟨hu, hcur, _⟩ := step_output_inv hstep
    obtain ⟨h1, h2, h3, h4⟩ := hi
    have hE : emittedOf ((pre ++ [LEv.out γ u]).map LEv.erase) =
        emittedOf (pre.map LEv.erase) ++ [u] := by
      simp [emittedOf_append, LEv.erase, emittedOf]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [curOf_append, LEv.erase, curOf, hcur, h1]
    · rw [hE]; have := residual_step h2 hstep; simpa [outs] using this
    · rw [hE]; intro o ho
      rcases List.mem_append.1 ho with ho | ho
      · obtain ⟨i, hi1, hi2⟩ := h3 o ho; exact ⟨i, hi1, hcur ▸ hi2⟩
      · simp at ho; subst ho; exact ⟨σ.cur, h1 ▸ hT, hcur ▸ PO.refl _⟩
    · rw [hE]; refine Or.inr ⟨σ.cur, u, h1 ▸ hT, hcur ▸ PO.refl _, ?_⟩
      intro o ho
      rcases List.mem_append.1 ho with ho | ho
      · exact hge o ho
      · simp at ho; subst ho; exact PO.refl _
  | @send σ ρ j d es _ _ =>
    intro pre hc _
    have := hc [] (.send j d) es rfl
    simp [Allowed, respSystem, respF, LEv.erase] at this
  | @recv σ ρ q k j d es _ _ =>
    intro pre hc _
    have := hc [] (.recv q k j d) es rfl
    simp [Allowed, respSystem, respF, LEv.erase] at this

theorem rinv_of_produced (T : Table I O) {N : Nat} {init : Fin N → I} {p : Fin N}
    {L : List (LEv sp D N)} {σ : State sp} (hc : Compliant (Allowed (respSystem T) N init p) L)
    (h : LRun (canon sp (init p)) L σ) : RInv T (init p) (L.map LEv.erase) σ := by
  have := rinv_run T h [] (fun a e b hab => by simpa using hc a e b hab)
    ⟨rfl, residual_canon sp _, by simp [emittedOf], Or.inl rfl⟩
  simpa using this

/-- Extend a history at a cut by one event at one participant. -/
theorem extend_single (Sys : System sp D) {init : Fin n → I} {H : History sp D n}
    {comp : Fin n → Nat} {c : Fin n → Nat} (hwf : WF init H) (hprod : Produced Sys n init H)
    (hpart : Partitioned H comp) (hcut : IsCut H c) {p : Fin n} {σ τ : State sp}
    (hσ : LRun (canon sp (init p)) ((H p).take (c p)) σ) {e : LEv sp D n}
    (hnr : ∀ q k j d, e ≠ .recv q k j d) (he : LRun σ [e] τ)
    (hA : Allowed Sys n init p ((H p).take (c p)) e) :
    ∃ (H' : History sp D n) (ext : Fin n → List (LEv sp D n)),
      Extends H c H' ext ∧ WF init H' ∧ Produced Sys n init H' ∧ Partitioned H' comp ∧
      ext p = [e] ∧ (∀ q, q ≠ p → ext q = []) := by
  classical
  let ext : Fin n → List (LEv sp D n) := fun q => if q = p then [e] else []
  have hnr' : ∀ p' q k j d, LEv.recv q k j d ∉ ext p' := by
    intro p' q k j d; simp only [ext]; split
    · simp only [List.mem_singleton]; exact fun h => hnr q k j d h.symm
    · simp
  have hext : Extends H c (fun q => (H q).take (c q) ++ ext q) ext := fun _ => rfl
  have hp : ext p = [e] := by simp [ext]
  have hq : ∀ q, q ≠ p → ext q = [] := fun q h => by simp [ext, h]
  refine ⟨_, ext, hext, ⟨?_, recvMatched_extend hwf.2 hcut hext hnr'⟩, ?_,
    partitioned_extend hpart hext hnr', hp, hq⟩
  · intro q
    by_cases hqp : q = p
    · subst hqp; exact ⟨τ, lrun_append.2 ⟨σ, hσ, by rw [hp]; exact he⟩⟩
    · obtain ⟨τq, hq'⟩ := hwf.1 q
      obtain ⟨σq, hσq⟩ := lrun_take hq' (c q)
      refine ⟨σq, ?_⟩
      show LRun _ ((H q).take (c q) ++ ext q) σq
      rw [hq q hqp, List.append_nil]; exact hσq
  · intro q
    apply compliant_append (compliant_take (hprod q) (c q))
    intro a e' b hab
    by_cases hqp : q = p
    · subst hqp
      rw [hp] at hab
      cases a with
      | nil => simp at hab; obtain ⟨rfl, _⟩ := hab; simpa using hA
      | cons _ _ => simp at hab
    · rw [hq q hqp] at hab; simp at hab

/-- (2)⇒(1) of Theorem `thm:complete-cap-response`. -/
theorem response_sufficient (Q : Obligation sp) (T : Table I O)
    (hT : ResponseInterface Q T) (hcons : ConsistentOn sp T) :
    (respSystem (sp := sp) (D := D) T).Replicated ∧
    ResponseAvailability (respSystem (sp := sp) (D := D) T) (fun _ _ => Q.Q) ∧
    ResponsePC (respSystem (sp := sp) (D := D) T) := by
  obtain ⟨hTQ, hTtot, hTcont⟩ := hT
  refine ⟨⟨respF T, fun _ _ _ _ _ => Iff.rfl⟩, ?_, ?_⟩
  · intro N init H comp hwf hprod hpart c hcut p σ hσ
    obtain ⟨h1, h2, _, h4⟩ := rinv_of_produced T (compliant_take (hprod p) (c p)) hσ
    -- rows available at any `k ⪰ σ.cur` in `T`, expanding every emitted output
    have havail : ∀ k, σ.cur ≼ k → ∃ u, T k u ∧ ∀ o ∈ emittedOf (((H p).take (c p)).map LEv.erase), o ≼ u := by
      intro k hk
      rcases h4 with h4 | ⟨i, om, hom, hi, hall⟩
      · obtain ⟨u, hu⟩ := hTtot k; exact ⟨u, hu, by rw [h4]; simp⟩
      · obtain ⟨u, hu, hle⟩ := hTcont i om k hom (PO.trans hi hk)
        exact ⟨u, hu, fun o ho => PO.trans (hall o ho) hle⟩
    constructor
    · -- Answering
      obtain ⟨u, hu, hge⟩ := havail σ.cur (PO.refl _)
      have hRu : σ.R σ.cur u :=
        (h2 _ _).2 ⟨Q.sub _ _ (hTQ _ _ hu), PO.refl _, hge⟩
      obtain ⟨γ, σc, hγ, ha, hcu, hexp⟩ := kc_legal hRu
      have hcc : σc.cur = σ.cur := (applySeq_spec γ σ σc ha).1
      let τ : State sp :=
        { cur := σc.cur, R := outputTable σc u, sub := fun k x h => σc.sub k x h.1,
          hasCur := ⟨u, hcu, PO.refl u⟩, above := fun k x h => σc.above k x h.1 }
      have hstep : Step σc (.output u) τ := Step.output σc τ u hcu rfl rfl
      obtain ⟨H', ext, hext, hwf', hprod', hpart', hp, hq⟩ :=
        extend_single (respSystem T) hwf hprod hpart hcut hσ (e := .out γ u)
          (by intro q k j d h; cases h) (.out ha hstep hexp (.nil τ))
          ⟨by intro c' hc'; rcases hγ with rfl | rfl
              · cases hc'
              · simp at hc'; exact ⟨u, hc'⟩,
           hγ, by rw [← h1]; exact hu, hge⟩
      refine ⟨H', ext, hext, hwf', hprod', hpart', fun q hq' => hq q (fun h => hq' (h ▸ rfl)),
        by rw [hp]; simp, γ, u, hTQ _ _ hu, by rw [hp]; simp⟩
    · -- Input acceptance
      intro j hj
      obtain ⟨w, hw, hge⟩ := havail j hj
      have hRw : σ.R j w := (h2 _ _).2 ⟨Q.sub _ _ (hTQ _ _ hw), hj, hge⟩
      let τ : State sp :=
        { cur := j, R := inputTable σ j, sub := fun k x h => σ.sub k x h.1,
          hasCur := ⟨w, hRw, PO.refl j⟩, above := fun k x h => h.2 }
      have hstep : Step σ (.input j) τ := Step.input σ τ j ⟨w, hRw⟩ rfl rfl
      obtain ⟨H', ext, hext, hwf', hprod', hpart', hp, hq⟩ :=
        extend_single (respSystem T) hwf hprod hpart hcut hσ (e := .inp j)
          (by intro q k j d h; cases h) (.inp hstep (.nil τ)) trivial
      exact ⟨H', ext, hext, hwf', hprod', hpart', fun q hq' => hq q (fun h => hq' (h ▸ rfl)),
        by rw [hp]; simp⟩
  · intro N init H comp hwf hprod _ c _ j hj
    let L : List O := (List.finRange N).flatMap
      (fun p => emittedOf (((H p).take (c p)).map LEv.erase))
    obtain ⟨u, hu, hall⟩ := consistentOn_outs hcons (j := j) L (by
      intro o ho
      simp only [L, List.mem_flatMap] at ho
      obtain ⟨p, _, ho⟩ := ho
      obtain ⟨τp, hp⟩ := hwf.1 p
      obtain ⟨σ, hσ⟩ := lrun_take hp (c p)
      obtain ⟨_, _, h3, _⟩ := rinv_of_produced T (compliant_take (hprod p) (c p)) hσ
      obtain ⟨i, hi, hle⟩ := h3 o ho
      exact ⟨i, hi, PO.trans hle (hj p σ hσ)⟩)
    refine ⟨u, hu, fun p γ o hm => hall o ?_⟩
    simp only [L, List.mem_flatMap]
    exact ⟨p, List.mem_finRange p, mem_emittedOf hm⟩


/-! ### (1)⇒(2) of Theorem `thm:complete-cap-response` -/

/-- Transport a local event to a history with another number of participants
(only ever applied to receive-free lists; receives become sends, which, like
receives, leave the state unchanged). -/
def tr {m N : Nat} : LEv sp D m → LEv sp D N
  | .inp j => .inp j
  | .out γ o => .out γ o
  | .send j d => .send j d
  | .recv _ _ j d => .send j d

theorem lrun_tr {m N : Nat} {σ τ : State sp} {l : List (LEv sp D m)} (h : LRun σ l τ) :
    LRun σ (l.map (tr (N := N))) τ := by
  induction h with
  | nil => exact .nil _
  | inp hs _ ih => exact .inp hs ih
  | out ha hs hx _ ih => exact .out ha hs hx ih
  | send _ ih => exact .send ih
  | recv _ ih => exact .send ih

theorem lrun_tr_inv {m N : Nat} {l : List (LEv sp D m)} :
    ∀ {σ τ : State sp}, LRun σ (l.map (tr (N := N))) τ → LRun σ l τ := by
  induction l with
  | nil => intro σ τ h; cases h; exact .nil _
  | cons e l ih =>
    intro σ τ h
    cases e with
    | inp j => cases h with | inp hs hr => exact .inp hs (ih hr)
    | out γ o => cases h with | out ha hs hx hr => exact .out ha hs hx (ih hr)
    | send j d => cases h with | send hr => exact .send (ih hr)
    | recv q k j d => cases h with | send hr => exact .recv (ih hr)

theorem tr_norecv {m N : Nat} (l : List (LEv sp D m)) (q : Fin N) (k : Nat) (j : Option I)
    (d : D) : LEv.recv q k j d ∉ l.map (tr (N := N)) := by
  intro h
  obtain ⟨e, _, he⟩ := List.mem_map.1 h
  cases e <;> simp [tr] at he

theorem erase_tr {m N : Nat} {l : List (LEv sp D m)}
    (hnr : ∀ q k j d, LEv.recv q k j d ∉ l) :
    (l.map (tr (N := N))).map LEv.erase = l.map LEv.erase := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    have ih' := ih (fun q k j d h => hnr q k j d (List.mem_cons_of_mem _ h))
    cases e with
    | recv q k j d => exact absurd (List.mem_cons_self ..) (hnr q k j d)
    | _ => simp only [List.map_cons, ih']; rfl

theorem compliant_tr {Sys : System sp D} {F : I → List (LEvN sp D) → LEvN sp D → Prop}
    (hF : ∀ n init p pre e, Sys.strat n init p pre e ↔ F (init p) (pre.map LEv.erase) e.erase)
    {m N : Nat} {init : Fin m → I} {init' : Fin N → I} {p : Fin m} {p' : Fin N}
    (hi : init' p' = init p) {l : List (LEv sp D m)} (hc : Compliant (Allowed Sys m init p) l)
    (hnr : ∀ q k j d, LEv.recv q k j d ∉ l) :
    Compliant (Allowed Sys N init' p') (l.map tr) := by
  intro a' e' b' h
  obtain ⟨l1, l2, rfl, h1, h2⟩ := List.map_eq_append_iff.1 h
  obtain ⟨e, l3, rfl, he, _⟩ := List.map_eq_cons_iff.1 h2
  subst h1 he
  have hA := hc l1 e l3 rfl
  have hnr1 : ∀ q k j d, LEv.recv q k j d ∉ l1 :=
    fun q k j d hm => hnr q k j d (List.mem_append_left _ hm)
  have hpre : (l1.map (tr (N := N))).map LEv.erase = l1.map LEv.erase := erase_tr hnr1
  cases e with
  | inp j => trivial
  | out γ o =>
    refine ⟨hA.1, (hF _ _ _ _ _).2 ?_⟩
    rw [hi, hpre]; exact (hF _ _ _ _ _).1 hA.2
  | send j d =>
    show Sys.strat _ _ _ _ _
    rw [hF, hi, hpre]; exact (hF _ _ _ _ _).1 hA
  | recv q k j d => exact absurd (by simp) (hnr q k j d)

theorem compliant_prefix {E : Type} {A : List E → E → Prop} {x y : List E}
    (h : Compliant A (x ++ y)) : Compliant A x := by
  have := compliant_take h x.length
  simpa using this

/-- In a partitioned history whose components are singletons, nobody receives. -/
theorem norecv_singletons {N : Nat} {init : Fin N → I} {H : History sp D N}
    (hwf : WF init H) (hpart : Partitioned H (fun p => p.val)) :
    ∀ p q k j d, LEv.recv q k j d ∉ H p := by
  intro p q k j d hm
  obtain ⟨a, b, hab⟩ := List.append_of_mem hm
  exact (hwf.2 p a q k j d b hab).1 (Fin.ext (hpart.2 p a q k j d b hab))

/-- Gluing receive-free, compliant local runs into a produced partitioned
history with singleton components. -/
theorem glue {Sys : System sp D} {N : Nat} (hN : 2 ≤ N) {init : Fin N → I}
    (L : History sp D N) (hnr : ∀ p q k j d, LEv.recv q k j d ∉ L p)
    (hc : ∀ p, Compliant (Allowed Sys N init p) (L p))
    (hr : ∀ p, ∃ τ, LRun (canon sp (init p)) (L p) τ) :
    WF init L ∧ Produced Sys N init L ∧ Partitioned L (fun p => p.val) ∧
    IsCut L (fun p => (L p).length) := by
  have hno : ∀ p a (q : Fin N) k j d b, L p ≠ a ++ LEv.recv q k j d :: b := by
    intro p a q k j d b h
    exact hnr p q k j d (by rw [h]; simp)
  refine ⟨⟨hr, fun p a q k j d b h => absurd h (hno p a q k j d b)⟩, hc,
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩, fun p a q k j d b h => absurd h (hno p a q k j d b)⟩,
    ⟨fun _ => Nat.le_refl _, fun p a q k j d b h => ?_⟩⟩
  rw [List.take_length] at h; exact absurd h (hno p a q k j d b)

/-- An isolated emission of `o` at current input `i` in some partitioned
history produced by the system. -/
def IsoEmit (Sys : System sp D) (i : I) (o : O) : Prop :=
  ∃ (n : Nat) (init : Fin n → I) (H : History sp D n) (comp : Fin n → Nat) (p : Fin n)
    (a b : List (LEv sp D n)) (γ : List (Commitment sp)) (σ : State sp),
    WF init H ∧ Produced Sys n init H ∧ Partitioned H comp ∧ H p = a ++ .out γ o :: b ∧
    (∀ q k j d, LEv.recv q k j d ∉ a) ∧ LRun (canon sp (init p)) a σ ∧ σ.cur = i

/-- Local data of an isolated emission. -/
structure LocW (Sys : System sp D) (i : I) (o : O) where
  n : Nat
  init : Fin n → I
  p : Fin n
  a : List (LEv sp D n)
  γ : List (Commitment sp)
  comp : Compliant (Allowed Sys n init p) (a ++ [LEv.out γ o])
  norecv : ∀ q k j d, LEv.recv q k j d ∉ a
  run : ∃ τ, LRun (canon sp (init p)) (a ++ [LEv.out γ o]) τ
  cur : ∀ σ, LRun (canon sp (init p)) a σ → σ.cur = i

theorem IsoEmit.loc {Sys : System sp D} {i : I} {o : O} (h : IsoEmit Sys i o) :
    Nonempty (LocW Sys i o) := by
  obtain ⟨n, init, H, _, p, a, b, γ, σ, hwf, hprod, _, hH, hnr, hσ, hcur⟩ := h
  have hH' : H p = (a ++ [LEv.out γ o]) ++ b := by simp [hH]
  obtain ⟨τ, hτ⟩ := hwf.1 p
  rw [hH'] at hτ
  obtain ⟨τ1, h1, _⟩ := lrun_append.1 hτ
  have hc := hprod p; rw [hH'] at hc
  exact ⟨⟨n, init, p, a, γ, compliant_prefix hc, hnr, ⟨τ1, h1⟩,
    fun σ' h => by rw [lrun_det h hσ]; exact hcur⟩⟩

/-- Replaying an isolated emission at a participant with the same initial input. -/
theorem LocW.replay {Sys : System sp D} {F : I → List (LEvN sp D) → LEvN sp D → Prop}
    (hF : ∀ n init p pre e, Sys.strat n init p pre e ↔ F (init p) (pre.map LEv.erase) e.erase)
    {i : I} {o : O} (w : LocW Sys i o) {N : Nat} {init' : Fin N → I} {p' : Fin N}
    (hi : init' p' = w.init w.p) :
    Compliant (Allowed Sys N init' p') ((w.a ++ [LEv.out w.γ o]).map tr) ∧
    (∀ q k j d, LEv.recv q k j d ∉ (w.a ++ [LEv.out w.γ o]).map (tr (N := N))) ∧
    (∃ τ, LRun (canon sp (init' p')) ((w.a ++ [LEv.out w.γ o]).map (tr (N := N))) τ) ∧
    (∀ σ, LRun (canon sp (init' p')) (w.a.map (tr (N := N))) σ → σ.cur = i) := by
  refine ⟨compliant_tr hF hi w.comp ?_, fun q k j d => tr_norecv _ q k j d, ?_, ?_⟩
  · intro q k j d hm
    rcases List.mem_append.1 hm with hm | hm
    · exact w.norecv q k j d hm
    · simp at hm
  · obtain ⟨τ, hτ⟩ := w.run; rw [hi]; exact ⟨τ, lrun_tr hτ⟩
  · intro σ h; rw [hi] at h; exact w.cur σ (lrun_tr_inv h)

theorem cut_of_norecv {N : Nat} {H : History sp D N} (hnr : ∀ p q k j d, LEv.recv q k j d ∉ H p)
    {c : Fin N → Nat} (hc : ∀ p, c p ≤ (H p).length) : IsCut H c := by
  refine ⟨hc, fun p a q k j d b h => absurd ?_ (hnr p q k j d)⟩
  have := take_split h; rw [this]; simp

/-- Answering, applied at a participant of a singleton-component history,
yields an isolated emission that expands every output the participant has
already emitted. -/
theorem answer_iso {Sys : System sp D} {Q : Obligation sp}
    (hRA : ResponseAvailability Sys (fun _ _ => Q.Q)) {N : Nat} {init : Fin N → I}
    {H : History sp D N} (hwf : WF init H) (hprod : Produced Sys N init H)
    (hpart : Partitioned H (fun p => p.val)) {c : Fin N → Nat} (hcut : IsCut H c)
    {p : Fin N} {σ : State sp} (hσ : LRun (canon sp (init p)) ((H p).take (c p)) σ) :
    ∃ u, Q.Q σ.cur u ∧ IsoEmit Sys σ.cur u ∧
      ∀ γ0 o, LEv.out γ0 o ∈ (H p).take (c p) → o ≼ u := by
  obtain ⟨⟨H', ext, hext, hwf', hprod', hpart', _, hnoinp, γ, u, hQ, hm⟩, _⟩ :=
    hRA N init H _ hwf hprod hpart c hcut p σ hσ
  obtain ⟨a, b, hab⟩ := List.append_of_mem hm
  have hH' : H' p = ((H p).take (c p) ++ a) ++ LEv.out γ u :: b := by rw [hext p, hab]; simp
  have hnr := norecv_singletons hwf' hpart'
  obtain ⟨τ, hτ⟩ := hwf'.1 p
  have hτ' := hτ; rw [hH'] at hτ'
  obtain ⟨σa, hσa, _⟩ := lrun_append.1 hτ'
  obtain ⟨σ1, h1, h2⟩ := lrun_append.1 hσa
  have hcur : σa.cur = σ.cur := by
    rw [lrun_noinp h2 (fun j hj => hnoinp j (by rw [hab]; simp [hj])), lrun_det h1 hσ]
  refine ⟨u, hQ, ⟨N, init, H', _, p, _, b, γ, σa, hwf', hprod', hpart', hH', ?_, hσa, hcur⟩, ?_⟩
  · intro q k j d hm'
    exact hnr p q k j d (by rw [hH']; exact List.mem_append_left _ hm')
  · intro γ0 o ho
    obtain ⟨l1, l2, hl⟩ := List.append_of_mem ho
    have : LRun (canon sp (init p)) (l1 ++ LEv.out γ0 o :: (l2 ++ ext p)) τ := by
      rw [hext p, hl] at hτ; simpa using hτ
    exact lrun_later_le this (List.mem_append_right _ hm)

/-- (1)⇒(2) of Theorem `thm:complete-cap-response`: `T` is the set of rows
of `Q` emitted in isolated emissions. -/
theorem response_necessary (Q : Obligation sp) (Sys : System sp D) (hrep : Sys.Replicated)
    (hRA : ResponseAvailability Sys (fun _ _ => Q.Q)) (hRPC : ResponsePC Sys) :
    ∃ T, ResponseInterface Q T ∧ ConsistentOn sp T := by
  classical
  obtain ⟨F, hF⟩ := hrep
  let T : Table I O := fun i o => Q.Q i o ∧ IsoEmit Sys i o
  -- replaying one isolated emission at participant `0` of two
  have replay2 : ∀ {i o} (w : LocW Sys i o),
      let L : History sp D 2 := fun q => if q.val = 0 then (w.a ++ [LEv.out w.γ o]).map tr else []
      let init : Fin 2 → I := fun _ => w.init w.p
      WF init L ∧ Produced Sys 2 init L ∧ Partitioned L (fun p => p.val) ∧
      IsCut L (fun p => (L p).length) ∧
      ∀ σ, LRun (canon sp (init 0)) ((L 0).take (L 0).length) σ → σ.cur = i := by
    intro i o w L init
    have hr := w.replay hF (N := 2) (init' := init) (p' := 0) rfl
    have hL0 : L 0 = (w.a ++ [LEv.out w.γ o]).map tr := rfl
    obtain ⟨h1, h2, h3, h4⟩ := glue (Sys := Sys) (by omega) (init := init) L
      (fun p => by
        by_cases hp : p.val = 0
        · simp only [L, hp, ↓reduceIte]; exact hr.2.1
        · simp only [L, hp, ↓reduceIte]; simp)
      (fun p => by
        by_cases hp : p.val = 0
        · have : p = 0 := Fin.ext hp
          subst this; exact hr.1
        · simp only [L, hp]; intro a e b h; simp at h)
      (fun p => by
        by_cases hp : p.val = 0
        · have : p = 0 := Fin.ext hp
          subst this; exact hr.2.2.1
        · simp only [L, hp]; exact ⟨_, .nil _⟩)
    refine ⟨h1, h2, h3, h4, fun σ hσ => ?_⟩
    rw [List.take_length, hL0, List.map_append] at hσ
    obtain ⟨σa, ha, hb⟩ := lrun_append.1 hσ
    rw [lrun_noinp hb (by simp [tr])]
    exact hr.2.2.2 σa ha
  refine ⟨T, ⟨fun _ _ h => h.1, ?_, ?_⟩, ?_⟩
  · -- totality
    intro i
    let L : History sp D 2 := fun _ => []
    obtain ⟨h1, h2, h3, h4⟩ := glue (Sys := Sys) (by omega) (init := fun _ => i) L
      (fun _ _ _ _ _ => by simp [L]) (fun _ a e b h => by simp [L] at h)
      (fun _ => ⟨_, .nil _⟩)
    obtain ⟨u, hQ, hiso, _⟩ := answer_iso hRA h1 h2 h3 h4 (p := 0) (σ := canon sp i) (.nil _)
    exact ⟨u, hQ, hiso⟩
  · -- self-continuation
    intro i o j hT hij
    let w := Classical.choice hT.2.loc
    obtain ⟨h1, h2, h3, h4, hcur⟩ := replay2 w
    let L : History sp D 2 := fun q => if q.val = 0 then (w.a ++ [LEv.out w.γ o]).map tr else []
    let init : Fin 2 → I := fun _ => w.init w.p
    obtain ⟨τ1, hτ1⟩ := h1.1 0
    have hτ1' : LRun (canon sp (init 0)) ((L 0).take (L 0).length) τ1 := by
      rw [List.take_length]; exact hτ1
    have hτc := hcur τ1 hτ1'
    obtain ⟨_, hacc⟩ := hRA 2 init L _ h1 h2 h3 _ h4 0 τ1 hτ1'
    obtain ⟨H2, ext2, hext2, hwf2, hprod2, hpart2, _, hinj⟩ := hacc j (hτc ▸ hij)
    obtain ⟨a2, b2, hab2⟩ := List.append_of_mem hinj
    have hnr2 := norecv_singletons hwf2 hpart2
    have hH20 : H2 0 = (L 0 ++ a2 ++ [LEv.inp j]) ++ b2 := by
      rw [hext2 0, List.take_length, hab2]; simp only [List.append_assoc, List.singleton_append]
      rfl
    let c2 : Fin 2 → Nat := fun q => if q.val = 0 then (L 0 ++ a2 ++ [LEv.inp j]).length
      else (H2 q).length
    have hc2 : IsCut H2 c2 := cut_of_norecv hnr2 (fun q => by
      by_cases hq : q.val = 0
      · have : q = 0 := Fin.ext hq
        subst this; simp only [c2, hq, ↓reduceIte]; rw [hH20]; simp
      · simp only [c2, hq, ↓reduceIte]; exact Nat.le_refl _)
    have htake : (H2 0).take (c2 0) = L 0 ++ a2 ++ [LEv.inp j] := by
      show List.take (if (0 : Fin 2).val = 0 then _ else _) _ = _
      simp only [Fin.val_zero, ↓reduceIte]; rw [hH20]; exact List.take_left' rfl
    obtain ⟨τ2, hτ2⟩ := hwf2.1 0
    obtain ⟨σ2, hσ2⟩ := lrun_take hτ2 (c2 0)
    have hσ2' := hσ2; rw [htake] at hσ2'
    obtain ⟨_, _, hlast⟩ := lrun_append.1 hσ2'
    have hj2 : σ2.cur = j := by
      cases hlast with
      | inp hs hr => cases hr; exact (step_input_inv hs).2.1
    obtain ⟨u, hQ, hiso, hge⟩ := answer_iso hRA hwf2 hprod2 hpart2 hc2 hσ2
    rw [hj2] at hQ hiso
    refine ⟨u, ⟨hQ, hiso⟩, hge w.γ o ?_⟩
    rw [htake]
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.2 ⟨LEv.out w.γ o, by simp, rfl⟩))
  · -- consistency on `T`
    intro rows hrows j hj
    by_cases hne : rows = []
    · subst hne; obtain ⟨u, hu⟩ := sp.total j; exact ⟨u, hu, by simp⟩
    have hlen : 0 < rows.length := by
      cases rows with
      | nil => exact absurd rfl hne
      | cons => simp
    let N := rows.length + 1
    have hT : ∀ r : Fin rows.length, T rows[r].1 rows[r].2 :=
      fun r => hrows _ (List.getElem_mem ..)
    let W : ∀ r : Fin rows.length, LocW Sys rows[r].1 rows[r].2 :=
      fun r => Classical.choice (hT r).2.loc
    let init : Fin N → I := fun p =>
      if h : p.val < rows.length then (W ⟨p.val, h⟩).init (W ⟨p.val, h⟩).p else j
    let L : History sp D N := fun p =>
      if h : p.val < rows.length then
        ((W ⟨p.val, h⟩).a ++ [LEv.out (W ⟨p.val, h⟩).γ rows[p.val].2]).map tr
      else []
    have hrep : ∀ (p : Fin N) (h : p.val < rows.length), _ := fun p h =>
      (W ⟨p.val, h⟩).replay hF (N := N) (init' := init) (p' := p)
        (by simp only [init, h, ↓reduceDIte])
    have hLp : ∀ (p : Fin N) (h : p.val < rows.length), L p =
        ((W ⟨p.val, h⟩).a ++ [LEv.out (W ⟨p.val, h⟩).γ rows[p.val].2]).map tr :=
      fun p h => by simp only [L, h, ↓reduceDIte]
    have hLn : ∀ (p : Fin N), ¬ p.val < rows.length → L p = [] :=
      fun p h => by simp only [L, h, ↓reduceDIte]
    obtain ⟨h1, h2, h3, h4⟩ := glue (Sys := Sys) (by omega) (init := init) L
      (fun p => by
        by_cases h : p.val < rows.length
        · rw [hLp p h]; exact (hrep p h).2.1
        · rw [hLn p h]; simp)
      (fun p => by
        by_cases h : p.val < rows.length
        · rw [hLp p h]; exact (hrep p h).1
        · rw [hLn p h]; intro a e b h; simp at h)
      (fun p => by
        by_cases h : p.val < rows.length
        · rw [hLp p h]; exact (hrep p h).2.2.1
        · rw [hLn p h]; exact ⟨_, .nil _⟩)
    have hcurs : ∀ p σ, LRun (canon sp (init p)) ((L p).take (L p).length) σ → σ.cur ≼ j := by
      intro p σ hσ
      rw [List.take_length] at hσ
      by_cases h : p.val < rows.length
      · rw [hLp p h, List.map_append] at hσ
        obtain ⟨σa, ha, hb⟩ := lrun_append.1 hσ
        rw [lrun_noinp hb (by simp [tr]), (hrep p h).2.2.2 σa ha]
        exact hj _ (List.getElem_mem ..)
      · rw [hLn p h] at hσ; cases hσ
        show init p ≼ j
        simp only [init, h, ↓reduceDIte]; exact PO.refl j
    obtain ⟨u, hu, hall⟩ := hRPC N init L _ h1 h2 h3 _ h4 j hcurs
    refine ⟨u, hu, fun r hr => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
    let p : Fin N := ⟨i, by omega⟩
    apply hall p (W ⟨i, hi⟩).γ
    rw [List.take_length, hLp p hi]
    exact List.mem_map.2 ⟨LEv.out _ _, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

/-- **Theorem `thm:complete-cap-response`** (response form of Complete CAP),
for a uniform obligation `Q`. -/
theorem complete_cap_response (sp : Spec I O) (D : Type) (Q : Obligation sp) :
    (∃ Sys : System sp D, Sys.Replicated ∧ ResponseAvailability Sys (fun _ _ => Q.Q) ∧
      ResponsePC Sys) ↔
    ∃ T, ResponseInterface Q T ∧ ConsistentOn sp T :=
  ⟨fun ⟨Sys, hrep, hRA, hRPC⟩ => response_necessary Q Sys hrep hRA hRPC,
   fun ⟨T, hT, hc⟩ => ⟨respSystem T, response_sufficient Q T hT hc⟩⟩

end CAP
end CC
