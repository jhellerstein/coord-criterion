import CoordCriterion.Instances.HATTaxonomyRules

/-!
# The HAT taxonomy: guarantees that are not highly available

Witness histories for the negative half of Bailis et al.'s classification, in
the model of `Instances/HATTaxonomy.lean`.  (Lost Update and Write Skew, which
make Cursor Stability, Snapshot Isolation, Repeatable Read and one-copy
serializability unavailable, are `HATSpec.lostUpdate_unavailable` and
`HATSpec.WS.writeSkew_unavailable`.)

* `ryw_not_ha`: read your writes, PRAM and causal consistency are not highly
  available.  Bailis §5.1.3: a client commits `T₁ : w x(1)` at one replica and
  then runs `T₂ : r x(a)` at "a different replica that is partitioned from the
  replica that executed `T₁`" (`w1`).  That replica holds only `x₀`, and
  `T₂` reading `x₀` is the anomaly MYR, so no answer the specification permits
  answers `T₂`'s read: no explicit relation inside the specification answers
  every read, which Complete CAP for an explicit relation requires.  (The read
  is not sticky: the replica has not received the client's write; by
  `sticky_of_rule` these guarantees are sticky available.)
* `recency_not_ha`, `recency_not_sticky`: recency is neither highly nor sticky
  available (Bailis §5.2.2: "an indefinitely long partition can force an
  available system to violate any recency bound").  Another client's write
  commits before the read in real time (recorded as happens-before) but never
  reaches the reading replica (`w2`); the read is sticky.
* `myrLit_not_sticky`: **a finding.**  MYR as Def. 34 of the extended paper
  writes it (a cycle of a transitive session-dependency, at least one
  anti-dependency, and anti- or write-dependencies otherwise) is not sticky
  available, contrary to the paper's classification of read your writes.  In
  `w3`, client 1 commits `T₁ : w x` (delivered to its replica 0), then runs
  `T₂ : r x, r y` at replica 0; client 2 runs `T₃ : r x, w y` at replica 1,
  partitioned from replica 0.  Every read is sticky and each one's only
  permitted answer at its own side is forced (`T₂` reads `y₀`, `T₃` reads
  `x₀`), but together they form the cycle `T₁ →s T₂ →rw_y T₃ →rw_x T₁`, so no
  explicit relation answering every sticky read is consistent, and by Complete
  CAP for an explicit relation (`CAP.complete_cap_for`) no system has
  Availability for it and Partition Consistency.  The single-item form `MYR`,
  which is what Def. 34's example (Fig. 17/18) exhibits, is sticky available
  (`sticky_of_rule`).
-/

namespace CC
namespace HATTax
open HATRC (Ts tsLt tsInit)
open IConf (Hist St)
open HATSpec (Ev Inp WF Lamport Ver Inst Next CTs wwI)

variable {reps : Nat → List Nat} {lam : Bool}

/-! ## Finite histories -/

/-- A finite history from its list of events and its (transitively closed) list
of happens-before pairs. -/
def mkHist (L : List Ev) (R : List (Nat × Nat))
    (hR : ∀ p ∈ R, p.1 < p.2 ∧ p.2 < L.length)
    (hT : ∀ p ∈ R, ∀ q ∈ R, p.2 = q.1 → (p.1, q.2) ∈ R) : Hist Ev where
  lab e := L[e]?
  lt a b := (a, b) ∈ R
  lt_ev h := by
    have := hR _ h
    simp only at this
    exact ⟨by simp; omega, by simp; omega⟩
  lt_num h := (hR _ h).1
  lt_trans h₁ h₂ := hT _ h₁ _ h₂ rfl
  fin := ⟨L.length, fun _ he => List.getElem?_eq_none he⟩

/-! ## `w1`: read your writes needs stickiness -/

def w1L : List Ev := [.cm 1 1 (1, 1) [0], .rd 1 2 0 0, .cm 1 2 (1, 2) []]
def w1R : List (Nat × Nat) := [(0, 1), (1, 2), (0, 2)]

def w1H : Hist Ev := mkHist w1L w1R (by decide) (by decide)

theorem w1_cases {e : Nat} {x : Ev} (h : w1H.lab e = some x) :
    (e = 0 ∧ x = .cm 1 1 (1, 1) [0]) ∨ (e = 1 ∧ x = .rd 1 2 0 0) ∨ (e = 2 ∧ x = .cm 1 2 (1, 2) []) := by
  have h' : w1L[e]? = some x := h
  match e, h' with
  | 0, h => cases h; simp
  | 1, h => cases h; simp
  | 2, h => cases h; simp

theorem w1_lt {a b : Nat} (h : w1H.lt a b) : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 0 ∧ b = 2) := by
  have h' : (a, b) ∈ w1R := h
  simp [w1R] at h'; omega

theorem w1_wf : WF w1H where
  cm_unique h h' := by
    rcases w1_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w1_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_unique h h' := by
    rcases w1_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w1_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_ne h := by
    rcases w1_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> decide
  dl_after h := by
    rcases w1_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  rd_before h h' := by
    rcases w1_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w1_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
    show (1, 2) ∈ w1R; decide
  replica {e e' r} h h' hne := by
    cases he : w1H.lab e with
    | none => rw [he] at h; exact h.elim
    | some x =>
      cases he' : w1H.lab e' with
      | none => rw [he'] at h'; exact h'.elim
      | some x' =>
        rw [he] at h; rw [he'] at h'
        rcases w1_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases w1_cases he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp_all [HATSpec.AtReplica]

theorem w1_lam : Lamport w1H := by
  intro e d f g c n k r c' n' t t' ks ks' _ hd
  rcases w1_cases hd with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx

theorem w1_sess (h0 : 0 ∈ reps 0) : Sess reps w1H where
  rd_rep h := by
    rcases w1_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx; exact h0
  prd_rep h := by
    rcases w1_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  prd_before h := by
    rcases w1_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  txn_order {e e' c n} h h' hne := by
    rcases h with ⟨k, r, h⟩ | ⟨ks, r, h⟩ <;> rcases h' with ⟨k', r', h'⟩ | ⟨ks', r', h'⟩ <;>
      rcases w1_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w1_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> exact absurd rfl hne
  seq {f f' e c n n' t t' ks ks'} hf hf' hl he := by
    rcases w1_lt hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases w1_cases hf with ⟨h, hx⟩ | ⟨h, hx⟩ | ⟨h, hx⟩ <;> cases h <;> cases hx <;>
      rcases w1_cases hf' with ⟨h, hx⟩ | ⟨h, hx⟩ | ⟨h, hx⟩ <;> cases h <;> cases hx
    rcases he with ⟨k, r, h⟩ | ⟨ks, r, h⟩ <;>
      rcases w1_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
    show (0, 1) ∈ w1R; decide
  sess_ts {f f' c n n' t t' ks ks'} hf hf' hl := by
    rcases w1_lt hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases w1_cases hf with ⟨h, hx⟩ | ⟨h, hx⟩ | ⟨h, hx⟩ <;> cases h <;> cases hx <;>
      rcases w1_cases hf' with ⟨h, hx⟩ | ⟨h, hx⟩ | ⟨h, hx⟩ <;> cases h <;> cases hx <;> decide

def w1 (h0 : 0 ∈ reps 0) : SInp reps lam := ⟨w1H, ⟨w1_wf, fun _ => w1_lam⟩, w1_sess h0⟩

theorem w1_inst {h0 : 0 ∈ reps 0} (t : Ts) : Inst (w1 (lam := lam) h0).inp 0 t ↔ t = tsInit ∨ t = (1, 1) := by
  constructor
  · rintro (h | ⟨f, c, n, ks, hf, hk⟩)
    · exact Or.inl h
    · rcases w1_cases hf with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;> cases hx
      · exact Or.inr rfl
      · simp at hk
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨0, 1, 1, [0], rfl, by simp⟩

/-- In `w1`, `T₂` reading `x₀` is MYR. -/
theorem w1_myr {h0 : 0 ∈ reps 0} (H : CH2 (w1 (lam := lam) h0)) (h : H.val 1 0 = tsInit) : MYR H := by
  have hn : Next (w1 (lam := lam) h0).inp 0 tsInit (1, 1) := by
    refine ⟨(w1_inst _).2 (Or.inl rfl), (w1_inst _).2 (Or.inr rfl), by decide, fun c hc => ?_⟩
    rcases (w1_inst c).1 hc with rfl | rfl <;> decide
  refine ⟨(1, 1), (1, 2), 0, 1, 1, 2, 0, .single ⟨0, 2, 1, 1, 2, [0], [], rfl, rfl, ?_⟩, rfl,
    ⟨2, [], rfl⟩, by decide, (1, 1), h ▸ hn, Or.inl rfl⟩
  show (0, 2) ∈ w1R; decide

/-- In `w1`, no visible version answers `T₂`'s read except `x₀`. -/
theorem w1_vis {h0 : 0 ∈ reps 0} {r : Nat} {v : Ts} (h : Vis (w1 (lam := lam) h0).1 1 0 r v) : v = tsInit := by
  rcases h with h | ⟨d, c', n', f, ks, hd, -⟩
  · exact h
  · rcases w1_cases hd with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;> cases hx

/-- **Read your writes, PRAM and causal consistency are not highly available.** -/
theorem ryw_not_ha (h0 : 0 ∈ reps 0) {g : Guar} (hg : g = .RYW ∨ g = .PRAM ∨ g = .Causal)
    (D : Type) : ¬ HighlyAvailable (reps := reps) (lam := lam) (tax g) D := by
  rintro ⟨E, hS, ht, ha, -⟩
  obtain ⟨o, ho⟩ := ht (w1 h0)
  obtain ⟨v, hv⟩ := ha _ o ho 1 1 2 0 0 (Or.inl rfl)
  obtain ⟨hvis, H, hF, hc⟩ := hS _ _ ho
  obtain ⟨c, n, r, ha', hvis'⟩ := hvis 1 0 v hv
  have hv0 := w1_vis hvis'
  have hH : H.val 1 0 = tsInit := by rw [← hv0]; exact (hF _ hv).2
  have hm := w1_myr H hH
  rcases hg with rfl | rfl | rfl
  · exact hc hm
  · exact hc (Or.inr (Or.inr hm))
  · exact hc (Or.inr (Or.inr (Or.inl hm)))

/-! ## `w2`: recency is not available, even with stickiness -/

def w2L : List Ev := [.cm 2 1 (1, 1) [0], .rd 1 1 0 0]
def w2R : List (Nat × Nat) := [(0, 1)]

def w2H : Hist Ev := mkHist w2L w2R (by decide) (by decide)

theorem w2_cases {e : Nat} {x : Ev} (h : w2H.lab e = some x) :
    (e = 0 ∧ x = .cm 2 1 (1, 1) [0]) ∨ (e = 1 ∧ x = .rd 1 1 0 0) := by
  have h' : w2L[e]? = some x := h
  match e, h' with
  | 0, h => cases h; simp
  | 1, h => cases h; simp

theorem w2_lt {a b : Nat} (h : w2H.lt a b) : a = 0 ∧ b = 1 := by
  have h' : (a, b) ∈ w2R := h
  simp [w2R] at h'; omega

theorem w2_wf : WF w2H where
  cm_unique h h' := by
    rcases w2_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w2_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_unique h h' := by
    rcases w2_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w2_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_ne h := by
    rcases w2_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> decide
  dl_after h := by
    rcases w2_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  rd_before h h' := by
    rcases w2_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w2_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  replica {e e' r} h h' hne := by
    cases he : w2H.lab e with
    | none => rw [he] at h; exact h.elim
    | some x =>
      cases he' : w2H.lab e' with
      | none => rw [he'] at h'; exact h'.elim
      | some x' =>
        rw [he] at h; rw [he'] at h'
        rcases w2_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases w2_cases he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp_all [HATSpec.AtReplica]

theorem w2_lam : Lamport w2H := by
  intro e d f g c n k r c' n' t t' ks ks' _ hd
  rcases w2_cases hd with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx

theorem w2_sess (h0 : 0 ∈ reps 0) : Sess reps w2H where
  rd_rep h := by
    rcases w2_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx; exact h0
  prd_rep h := by
    rcases w2_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  prd_before h := by
    rcases w2_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  txn_order {e e' c n} h h' hne := by
    rcases h with ⟨k, r, h⟩ | ⟨ks, r, h⟩ <;> rcases h' with ⟨k', r', h'⟩ | ⟨ks', r', h'⟩ <;>
      rcases w2_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w2_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> exact absurd rfl hne
  seq hf hf' hl := by
    obtain ⟨rfl, rfl⟩ := w2_lt hl
    rcases w2_cases hf' with ⟨h, -⟩ | ⟨-, hx⟩
    · cases h
    · cases hx
  sess_ts hf hf' hl := by
    obtain ⟨rfl, rfl⟩ := w2_lt hl
    rcases w2_cases hf' with ⟨h, -⟩ | ⟨-, hx⟩
    · cases h
    · cases hx

def w2 (h0 : 0 ∈ reps 0) : SInp reps lam := ⟨w2H, ⟨w2_wf, fun _ => w2_lam⟩, w2_sess h0⟩

theorem w2_rec {h0 : 0 ∈ reps 0} (H : CH2 (w2 (lam := lam) h0)) (h : H.val 1 0 = tsInit) : Recency H :=
  ⟨1, 1, 1, 0, 0, 0, 2, 1, (1, 1), [0], rfl, rfl, by simp, by decide,
    show (0, 1) ∈ w2R by decide, by rw [h]; decide⟩

theorem w2_vis {h0 : 0 ∈ reps 0} {r : Nat} {v : Ts} (h : Vis (w2 (lam := lam) h0).1 1 0 r v) : v = tsInit := by
  rcases h with h | ⟨d, c', n', f, ks, hd, -⟩
  · exact h
  · rcases w2_cases hd with ⟨_, hx⟩ | ⟨_, hx⟩ <;> cases hx

theorem w2_reflects {h0 : 0 ∈ reps 0} : Reflects (reps := reps) (w2 (lam := lam) h0).1 1 1 0 := by
  intro f n' t ks k hf hl
  obtain ⟨rfl, -⟩ := w2_lt hl
  rcases w2_cases hf with ⟨-, hx⟩ | ⟨h, -⟩
  · cases hx
  · cases h

theorem w2_absurd (h0 : 0 ∈ reps 0) (E : Table (SInp reps lam) (St Fact2))
    (hS : ∀ i o, E i o → (tax (reps := reps) (lam := lam) .Rec).P i o) {o : St Fact2}
    (ho : E (w2 h0) o) {v : Ts} (hv : o (.rv 1 0 v)) : False := by
  obtain ⟨hvis, H, hF, hc⟩ := hS _ _ ho
  obtain ⟨c, n, r, -, hvis'⟩ := hvis 1 0 v hv
  have hv0 := w2_vis hvis'
  have hH : H.val 1 0 = tsInit := by rw [← hv0]; exact (hF _ hv).2
  exact hc (w2_rec H hH)

/-- **Recency is not highly available.** -/
theorem recency_not_ha (h0 : 0 ∈ reps 0) (D : Type) :
    ¬ HighlyAvailable (reps := reps) (lam := lam) (tax .Rec) D := by
  rintro ⟨E, hS, ht, ha, -⟩
  obtain ⟨o, ho⟩ := ht (w2 h0)
  obtain ⟨v, hv⟩ := ha _ o ho 1 1 1 0 0 (Or.inl rfl)
  exact w2_absurd h0 E hS ho hv

/-- **Recency is not sticky available either**: the read in `w2` is sticky. -/
theorem recency_not_sticky (h0 : 0 ∈ reps 0) (D : Type) :
    ¬ StickyAvailable (reps := reps) (lam := lam) (tax .Rec) D := by
  rintro ⟨E, hS, ht, ha, -⟩
  obtain ⟨o, ho⟩ := ht (w2 h0)
  obtain ⟨v, hv⟩ := ha _ o ho 1 1 1 0 0 (Or.inl rfl) w2_reflects
  exact w2_absurd h0 E hS ho hv

/-! ## `w3`: MYR as written is not sticky available (a finding) -/

def w3L : List Ev :=
  [.cm 1 1 (1, 1) [0], .dl 1 1 0 0, .rd 1 2 0 0, .rd 1 2 1 0, .cm 1 2 (1, 2) [], .rd 2 1 0 1,
   .cm 2 1 (1, 3) [1]]
def w3R : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4), (5, 6)]

def w3H : Hist Ev := mkHist w3L w3R (by decide) (by decide)

theorem w3_cases {e : Nat} {x : Ev} (h : w3H.lab e = some x) :
    (e = 0 ∧ x = .cm 1 1 (1, 1) [0]) ∨ (e = 1 ∧ x = .dl 1 1 0 0) ∨ (e = 2 ∧ x = .rd 1 2 0 0) ∨
    (e = 3 ∧ x = .rd 1 2 1 0) ∨ (e = 4 ∧ x = .cm 1 2 (1, 2) []) ∨ (e = 5 ∧ x = .rd 2 1 0 1) ∨
    (e = 6 ∧ x = .cm 2 1 (1, 3) [1]) := by
  have h' : w3L[e]? = some x := h
  match e, h' with
  | 0, h => cases h; simp
  | 1, h => cases h; simp
  | 2, h => cases h; simp
  | 3, h => cases h; simp
  | 4, h => cases h; simp
  | 5, h => cases h; simp
  | 6, h => cases h; simp

theorem w3_lt_iff {a b : Nat} : w3H.lt a b ↔ (a, b) ∈ w3R := Iff.rfl

theorem w3_lt {a b : Nat} (h : w3H.lt a b) : (a < b ∧ b ≤ 4) ∨ (a = 5 ∧ b = 6) := by
  have h' : (a, b) ∈ w3R := h
  simp [w3R] at h'; omega

theorem w3_wf : WF w3H where
  cm_unique h h' := by
    rcases w3_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w3_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_unique h h' := by
    rcases w3_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w3_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_ne h := by
    rcases w3_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;> decide
  dl_after h := by
    rcases w3_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx
    exact ⟨0, (1, 1), [0], rfl, by simp, show (0, 1) ∈ w3R by decide⟩
  rd_before h h' := by
    rcases w3_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w3_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;> (rw [w3_lt_iff]; decide)
  replica {e e' r} h h' hne := by
    cases he : w3H.lab e with
    | none => rw [he] at h; exact h.elim
    | some x =>
      cases he' : w3H.lab e' with
      | none => rw [he'] at h'; exact h'.elim
      | some x' =>
        rw [he] at h; rw [he'] at h'
        rcases w3_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases w3_cases he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [HATSpec.AtReplica] at h h' <;>
          first
            | exact absurd rfl hne
            | (left; rw [w3_lt_iff]; decide)
            | (right; rw [w3_lt_iff]; decide)
            | omega

theorem w3_lam : Lamport w3H := by
  intro e d f g c n k r c' n' t t' ks ks' he hd hl hf hg
  rcases w3_cases hd with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
    ⟨rfl, hx⟩ <;> cases hx
  rcases w3_cases he with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
    ⟨rfl, hx⟩ <;> cases hx <;>
    rcases w3_cases hf with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
    ⟨rfl, hx⟩ <;> cases hx <;>
    rcases w3_cases hg with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
    ⟨rfl, hx⟩ <;> cases hx <;> first | decide | (exfalso; revert hl; rw [w3_lt_iff]; decide)

theorem w3_sess (h00 : 0 ∈ reps 0) (h01 : 0 ∈ reps 1) (h10 : 1 ∈ reps 0) : Sess reps w3H where
  rd_rep h := by
    rcases w3_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;> assumption
  prd_rep h := by
    rcases w3_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx
  prd_before h := by
    rcases w3_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx
  txn_order {e e' c n} h h' hne := by
    rcases h with ⟨k, r, h⟩ | ⟨ks, r, h⟩ <;> rcases h' with ⟨k', r', h'⟩ | ⟨ks', r', h'⟩ <;>
      rcases w3_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w3_cases h' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;>
      first
        | exact absurd rfl hne
        | (left; rw [w3_lt_iff]; decide)
        | (right; rw [w3_lt_iff]; decide)
  seq {f f' e c n n' t t' ks ks'} hf hf' hl he := by
    rcases w3_cases hf with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w3_cases hf' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;>
      (try (exfalso; revert hl; rw [w3_lt_iff]; decide)) <;>
      rcases he with ⟨k, r, h⟩ | ⟨ks, r, h⟩ <;>
      rcases w3_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;> (rw [w3_lt_iff]; decide)
  sess_ts {f f' c n n' t t' ks ks'} hf hf' hl := by
    rcases w3_cases hf with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;>
      rcases w3_cases hf' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx <;> first | decide | (exfalso; revert hl; rw [w3_lt_iff]; decide)

section W3
variable (h00 : 0 ∈ reps 0) (h01 : 0 ∈ reps 1) (h10 : 1 ∈ reps 0)

def w3 : SInp reps lam := ⟨w3H, ⟨w3_wf, fun _ => w3_lam⟩, w3_sess h00 h01 h10⟩

theorem w3_down1 : ∀ x y, w3H.lt x y → y ≤ 4 → x ≤ 4 := fun x y h hy => by
  rcases w3_lt h with ⟨h1, -⟩ | ⟨-, rfl⟩ <;> omega

theorem w3_down2 : ∀ x y, w3H.lt x y → 5 ≤ y → 5 ≤ x := fun x y h hy => by
  rcases w3_lt h with ⟨-, h2⟩ | ⟨rfl, -⟩ <;> omega

/-- Client 1's side: `T₁` and `T₂`. -/
noncomputable def w3a : SInp reps lam :=
  (w3 (lam := lam) h00 h01 h10).down (w3H.restrict (· ≤ 4) w3_down1) (IConf.Hist.restrict_le _ _ _)

/-- Client 2's side: `T₃`. -/
noncomputable def w3b : SInp reps lam :=
  (w3 (lam := lam) h00 h01 h10).down (w3H.restrict (5 ≤ ·) w3_down2) (IConf.Hist.restrict_le _ _ _)

theorem restrict_lab {P : Nat → Prop} {hP} {e : Nat} {x : Ev}
    (h : (w3H.restrict P hP).lab e = some x) : P e ∧ w3H.lab e = some x := by
  simp only [IConf.Hist.restrict] at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem restrict_lab' {P : Nat → Prop} {hP} {e : Nat} (he : P e) :
    (w3H.restrict P hP).lab e = w3H.lab e := by
  simp only [IConf.Hist.restrict, if_pos he]

end W3

variable {h00 : 0 ∈ reps 0} {h01 : 0 ∈ reps 1} {h10 : 1 ∈ reps 0}

theorem w3_inst0 (t : Ts) : Inst (w3 (lam := lam) h00 h01 h10).inp 0 t ↔ t = tsInit ∨ t = (1, 1) := by
  constructor
  · rintro (h | ⟨f, c, n, ks, hf, hk⟩)
    · exact Or.inl h
    · rcases w3_cases hf with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;>
        cases hx <;> simp_all
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨0, 1, 1, [0], rfl, by simp⟩

theorem w3_inst1 (t : Ts) : Inst (w3 (lam := lam) h00 h01 h10).inp 1 t ↔ t = tsInit ∨ t = (1, 3) := by
  constructor
  · rintro (h | ⟨f, c, n, ks, hf, hk⟩)
    · exact Or.inl h
    · rcases w3_cases hf with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;>
        cases hx <;> simp_all
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨6, 2, 1, [1], rfl, by simp⟩

/-- In `w3`, `T₂` reading `y₀` and `T₃` reading `x₀` is MYR as Def. 34 writes it:
`T₁ →s T₂ →rw_y T₃ →rw_x T₁`. -/
theorem w3_myrLit (H : CH2 (w3 (lam := lam) h00 h01 h10)) (hy : H.val 3 1 = tsInit)
    (hx : H.val 5 0 = tsInit) : MYRlit H := by
  have hn0 : Next (w3 (lam := lam) h00 h01 h10).inp 0 tsInit (1, 1) := by
    refine ⟨(w3_inst0 _).2 (Or.inl rfl), (w3_inst0 _).2 (Or.inr rfl), by decide, fun c hc => ?_⟩
    rcases (w3_inst0 c).1 hc with rfl | rfl <;> decide
  have hn1 : Next (w3 (lam := lam) h00 h01 h10).inp 1 tsInit (1, 3) := by
    refine ⟨(w3_inst1 _).2 (Or.inl rfl), (w3_inst1 _).2 (Or.inr rfl), by decide, fun c hc => ?_⟩
    rcases (w3_inst1 c).1 hc with rfl | rfl <;> decide
  refine ⟨(1, 1), (1, 2), (1, 2), (1, 3),
    .single ⟨0, 4, 1, 1, 2, [0], [], rfl, rfl, show (0, 4) ∈ w3R by decide⟩, Or.inl rfl,
    ⟨1, by decide, 3, 1, 2, 0, rfl, ⟨4, [], rfl⟩, hy ▸ hn1⟩,
    Or.inr (.single (Or.inl ⟨0, by decide, 5, 2, 1, 1, rfl, ⟨6, [1], rfl⟩, hx ▸ hn0⟩))⟩

/-- **Finding: MYR as Def. 34 writes it is not sticky available.** -/
theorem myrLit_not_sticky (h00 : 0 ∈ reps 0) (h01 : 0 ∈ reps 1) (h10 : 1 ∈ reps 0) (D : Type) :
    ¬ StickyAvailable (reps := reps) (lam := lam) (tax .RYWlit) D := by
  rw [stickyAvailable_iff]
  rintro ⟨E, hS, ht, ha, hc⟩
  let ja := w3a (lam := lam) h00 h01 h10
  let jb := w3b (lam := lam) h00 h01 h10
  obtain ⟨o₁, ho₁⟩ := ht ja
  obtain ⟨o₂, ho₂⟩ := ht jb
  -- `T₂`'s read of `y` (event 3) and `T₃`'s read of `x` (event 5) are sticky
  have hacc₁ : Acc ja.1 3 1 2 1 0 := Or.inl (by
    show (w3H.restrict (· ≤ 4) w3_down1).lab 3 = _
    rw [restrict_lab' (by decide)]; rfl)
  have hacc₂ : Acc jb.1 5 2 1 0 1 := Or.inl (by
    show (w3H.restrict (5 ≤ ·) w3_down2).lab 5 = _
    rw [restrict_lab' (by decide)]; rfl)
  have hst₁ : Reflects (reps := reps) ja.1 3 1 0 := by
    intro f n' t ks k hf hl hk hr
    obtain ⟨-, hf'⟩ := restrict_lab (hP := w3_down1) hf
    rcases w3_cases hf' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx
    · simp at hk; subst hk
      refine ⟨1, ?_, ?_⟩
      · show (w3H.restrict (· ≤ 4) w3_down1).lab 1 = _
        rw [restrict_lab' (by decide)]; rfl
      · exact ⟨show (1, 3) ∈ w3R by decide, by decide⟩
    · exact absurd hl.1 (by rw [w3_lt_iff]; decide)
  have hst₂ : Reflects (reps := reps) jb.1 5 2 1 := by
    intro f n' t ks k hf hl
    obtain ⟨-, hf'⟩ := restrict_lab (hP := w3_down2) hf
    rcases w3_cases hf' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ <;> cases hx
    exact absurd hl.1 (by rw [w3_lt_iff]; decide)
  obtain ⟨v₁, hv₁⟩ := ha ja o₁ ho₁ 3 1 2 1 0 hacc₁ hst₁
  obtain ⟨v₂, hv₂⟩ := ha jb o₂ ho₂ 5 2 1 0 1 hacc₂ hst₂
  -- each side's only visible answer is the initial version
  have e₁ : v₁ = tsInit := by
    obtain ⟨c, n, r, ha', hvis⟩ := (hS _ _ ho₁).1 3 1 v₁ hv₁
    obtain ⟨-, -, rfl⟩ := acc_unique hacc₁ ha'
    rcases hvis with h | ⟨d, c', n', f, ks, hd, -⟩
    · exact h
    · obtain ⟨-, hd'⟩ := restrict_lab (hP := w3_down1) hd
      rcases w3_cases hd' with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;>
        cases hx
  have e₂ : v₂ = tsInit := by
    obtain ⟨c, n, r, ha', hvis⟩ := (hS _ _ ho₂).1 5 0 v₂ hv₂
    obtain ⟨-, -, rfl⟩ := acc_unique hacc₂ ha'
    rcases hvis with h | ⟨d, c', n', f, ks, hd, -⟩
    · exact h
    · obtain ⟨hd5, hd'⟩ := restrict_lab (hP := w3_down2) hd
      rcases w3_cases hd' with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
        ⟨rfl, hx⟩ <;> cases hx
  -- together they force the cycle
  obtain ⟨u, ⟨-, H, hF, hcl⟩, hle⟩ := hc [(ja, o₁), (jb, o₂)]
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> assumption) (w3 h00 h01 h10)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact IConf.Hist.restrict_le _ _ w3_down1
        · exact IConf.Hist.restrict_le _ _ w3_down2)
  have a₁ : H.val 3 1 = tsInit := by
    rw [← e₁]; exact (hF _ (hle _ (List.mem_cons_self ..) _ hv₁)).2
  have a₂ : H.val 5 0 = tsInit := by
    rw [← e₂]; exact (hF _ (hle _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ hv₂)).2
  exact hcl (w3_myrLit H a₁ a₂)

end HATTax
end CC
