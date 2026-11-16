import CoordCriterion.Instances.HATSpec

/-!
# Write Skew is unavailable (HAT, Bailis et al. §5.2.1)

Bailis et al. (VLDB 2014, §5.2.1; extended version, Def. 39): "Write Skew is a
generalization of Lost Update to multiple keys.  It occurs when one transaction
`T₁` reads a given data item `x`, a second transaction `T₂` reads a different
data item `y`, then `T₁` writes to `y` and commits and `T₂` writes to `x` and
commits", formally "a directed cycle having one or more item-antidependency
edges" (Adya's G2-item), which in the item-only model of `Instances/HATSpec.lean`
is `G2`.  Their example `T₁ : r y(0) w x(1)`, `T₂ : r x(0) w y(1)`, run at two
partitioned replicas, is the witness here (`wsLab`); the proof follows
`lostUpdate_unavailableP` and is carried by Complete CAP for an explicit
relation (`CAP.complete_cap_for`).
-/

namespace CC
namespace HATSpec
namespace WS
open HATRC (Ts tsLt tsInit)
open IConf (Hist St)

variable {lam : Bool}

def wsLab : Nat → Option Ev
  | 0 => some (.rd 1 1 1 0)
  | 1 => some (.cm 1 1 (1, 1) [0])
  | 2 => some (.rd 2 1 0 1)
  | 3 => some (.cm 2 1 (1, 2) [1])
  | _ => none

def wsHist (keep : Nat → Prop) [DecidablePred keep] : Hist Ev where
  lab e := if keep e then wsLab e else none
  lt a b := ((a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3)) ∧ keep a ∧ keep b
  lt_ev {a b} h := by
    obtain ⟨hab, ha, hb⟩ := h
    simp only [ha, hb, if_true]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [wsLab]
  lt_num {a b} h := by rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  lt_trans {a b c} h₁ h₂ := by
    rcases h₁.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h₂.1 with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
  fin := ⟨4, fun e he => by
    split
    · match e, he with
      | n + 4, _ => rfl
    · rfl⟩

theorem wsLab_cases {e : Nat} {x : Ev} (h : wsLab e = some x) :
    (e = 0 ∧ x = .rd 1 1 1 0) ∨ (e = 1 ∧ x = .cm 1 1 (1, 1) [0]) ∨
      (e = 2 ∧ x = .rd 2 1 0 1) ∨ (e = 3 ∧ x = .cm 2 1 (1, 2) [1]) := by
  match e, h with
  | 0, h => cases h; simp
  | 1, h => cases h; simp
  | 2, h => cases h; simp
  | 3, h => cases h; simp

def wkeepJ : Nat → Prop := fun _ => True
def wkeep1 : Nat → Prop := fun e => e = 0 ∨ e = 1
def wkeep2 : Nat → Prop := fun e => e = 2 ∨ e = 3

instance : DecidablePred wkeepJ := fun _ => isTrue trivial
instance : DecidablePred wkeep1 := fun e => by unfold wkeep1; infer_instance
instance : DecidablePred wkeep2 := fun e => by unfold wkeep2; infer_instance

def wJ : Hist Ev := wsHist wkeepJ
theorem wk1 : ∀ e, wkeep1 (e + 1) → wkeep1 e ∨ e % 2 = 1 := fun e h => by unfold wkeep1 at *; omega
theorem wk2 : ∀ e, wkeep2 (e + 1) → wkeep2 e ∨ e % 2 = 1 := fun e h => by unfold wkeep2 at *; omega
def wh1 : Hist Ev := wsHist wkeep1
def wh2 : Hist Ev := wsHist wkeep2

theorem wJ_lab {e : Nat} {x : Ev} (h : wJ.lab e = some x) : wsLab e = some x := h

theorem wf_wJ : WF wJ where
  cm_unique {e e' c n t t' ks ks'} h h' := by
    rcases wsLab_cases (wJ_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases wsLab_cases (wJ_lab h') with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_unique {e e' c n c' n' t ks ks'} h h' := by
    rcases wsLab_cases (wJ_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases wsLab_cases (wJ_lab h') with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> rfl
  ts_ne {e c n t ks} h := by
    rcases wsLab_cases (wJ_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;> decide
  dl_after {d c n k r} h := by
    rcases wsLab_cases (wJ_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx
  rd_before {e f c n k r t ks} h h' := by
    rcases wsLab_cases (wJ_lab h) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      rcases wsLab_cases (wJ_lab h') with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx <;>
      exact ⟨by simp, trivial, trivial⟩
  replica {e e' r} h h' hne := by
    have l1 : wJ.lab e = wsLab e := rfl
    have l2 : wJ.lab e' = wsLab e' := rfl
    rw [l1] at h; rw [l2] at h'
    match e, e', h, h' with
    | 0, 0, _, _ => exact absurd rfl hne
    | 2, 2, _, _ => exact absurd rfl hne
    | 0, 2, h, h' => simp only [wsLab, AtReplica] at h h'; omega
    | 2, 0, h, h' => simp only [wsLab, AtReplica] at h h'; omega
    | 1, _, h, _ => simp [wsLab, AtReplica] at h
    | 3, _, h, _ => simp [wsLab, AtReplica] at h
    | _, 1, _, h' => simp [wsLab, AtReplica] at h'
    | _, 3, _, h' => simp [wsLab, AtReplica] at h'
    | n + 4, _, h, _ => simp [wsLab, AtReplica] at h
    | _, n + 4, _, h' => simp [wsLab, AtReplica] at h'

theorem lam_wJ : Lamport wJ := by
  intro e d f g c n k r c' n' t t' ks ks' _ hd
  rcases wsLab_cases (wJ_lab hd) with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> cases hx

theorem le_wJ (keep : Nat → Prop) [DecidablePred keep]
    (hk : ∀ e, keep (e + 1) → keep e ∨ e % 2 = 1) : wsHist keep ≼ wJ := by
  refine ⟨fun e x h => ?_, fun a b => ?_⟩
  · show (if wkeepJ e then wsLab e else none) = some x
    have : (if keep e then wsLab e else none) = some x := h
    split at this
    · simpa [wkeepJ] using this
    · cases this
  · show (((a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3)) ∧ keep a ∧ keep b) ↔
      ((((a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3)) ∧ wkeepJ a ∧ wkeepJ b) ∧ (if keep b then wsLab b else none) ≠ none)
    constructor
    · rintro ⟨hab, ha, hb⟩
      refine ⟨⟨hab, trivial, trivial⟩, ?_⟩
      rw [if_pos hb]; rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [wsLab]
    · rintro ⟨⟨hab, -, -⟩, hb⟩
      have hkb : keep b := by
        apply Classical.byContradiction; intro hn; rw [if_neg hn] at hb; exact hb rfl
      refine ⟨hab, ?_, hkb⟩
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hk 0 hkb with h | h
        · exact h
        · simp at h
      · rcases hk 2 hkb with h | h
        · exact h
        · simp at h

def wiJ : Inp lam := ⟨wJ, wf_wJ, fun _ => lam_wJ⟩
def wi1 : Inp lam := ⟨wh1, wf_down (le_wJ wkeep1 wk1) wf_wJ, fun _ => lamport_down (le_wJ wkeep1 wk1) lam_wJ⟩
def wi2 : Inp lam := ⟨wh2, wf_down (le_wJ wkeep2 wk2) wf_wJ, fun _ => lamport_down (le_wJ wkeep2 wk2) lam_wJ⟩

/-- In `wi₁` the only version `T₁` may read of `y` is `y₀`. -/
theorem wi1_ver {v : Ts} (h : Ver (wi1 (lam := lam)) 1 1 1 v) : v = tsInit := by
  rcases h with h | ⟨f, c', n', ks, hf, hk, -⟩
  · exact h
  · have : (if wkeep1 f then wsLab f else none) = some (.cm c' n' v ks) := hf
    split at this
    · next hkf =>
        rcases wsLab_cases this with ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, hx⟩ <;> cases hx
        · simp at hk
        · subst he; simp [wkeep1] at hkf
    · cases this

/-- In `wi₂` the only version `T₂` may read of `x` is `x₀`. -/
theorem wi2_ver {v : Ts} (h : Ver (wi2 (lam := lam)) 2 1 0 v) : v = tsInit := by
  rcases h with h | ⟨f, c', n', ks, hf, hk, -⟩
  · exact h
  · have : (if wkeep2 f then wsLab f else none) = some (.cm c' n' v ks) := hf
    split at this
    · next hkf =>
        rcases wsLab_cases this with ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, hx⟩ <;> cases hx
        · subst he; simp [wkeep2] at hkf
        · simp at hk
    · cases this

theorem wJ_inst0 (t : Ts) : Inst (wiJ (lam := lam)) 0 t ↔ t = tsInit ∨ t = (1, 1) := by
  constructor
  · rintro (h | ⟨f, c, n, ks, hf, hk⟩)
    · exact Or.inl h
    · rcases wsLab_cases (wJ_lab hf) with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;> cases hx
      · exact Or.inr rfl
      · simp at hk
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨1, 1, 1, [0], rfl, by simp⟩

theorem wJ_inst1 (t : Ts) : Inst (wiJ (lam := lam)) 1 t ↔ t = tsInit ∨ t = (1, 2) := by
  constructor
  · rintro (h | ⟨f, c, n, ks, hf, hk⟩)
    · exact Or.inl h
    · rcases wsLab_cases (wJ_lab hf) with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ <;> cases hx
      · simp at hk
      · exact Or.inr rfl
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨3, 2, 1, [1], rfl, by simp⟩

/-- In every complete history of `wJ` in which both reads return the initial
versions, `T₁`'s read of `y₀` and `T₂`'s read of `x₀` give the anti-dependencies
`T₁ → T₂` (by `y`) and `T₂ → T₁` (by `x`): a cycle with item-anti-dependency
edges, Write Skew (Def. 39 of the extended HAT paper, Adya's G2-item, here `G2`). -/
theorem ws_cycle (H : CH (wiJ (lam := lam))) (h0 : H.ans 0 = tsInit) (h2' : H.ans 2 = tsInit) :
    G2 H := by
  have hn0 : Next (wiJ (lam := lam)) 0 tsInit (1, 1) := by
    refine ⟨(wJ_inst0 _).2 (Or.inl rfl), (wJ_inst0 _).2 (Or.inr rfl), by decide, fun c hc => ?_⟩
    rcases (wJ_inst0 c).1 hc with rfl | rfl <;> decide
  have hn1 : Next (wiJ (lam := lam)) 1 tsInit (1, 2) := by
    refine ⟨(wJ_inst1 _).2 (Or.inl rfl), (wJ_inst1 _).2 (Or.inr rfl), by decide, fun c hc => ?_⟩
    rcases (wJ_inst1 c).1 hc with rfl | rfl <;> decide
  have hrw1 : rwI H 1 (1, 1) (1, 2) := ⟨by decide, 0, 1, 1, 0, rfl, ⟨1, [0], rfl⟩, h0 ▸ hn1⟩
  have hrw0 : rwI H 0 (1, 2) (1, 1) := ⟨by decide, 2, 2, 1, 1, rfl, ⟨3, [1], rfl⟩, h2' ▸ hn0⟩
  exact ⟨(1, 1), (1, 2), ⟨1, hrw1⟩, Or.inr (.single (Or.inr ⟨0, hrw0⟩))⟩

/-- **Write Skew is unavailable** (Bailis et al. §5.2.1: "Write Skew is a
generalization of Lost Update to multiple keys … it is also unavailable to HAT
systems").  For any set of proscribed phenomena `P` that includes Write Skew
(Adya's G2-item, `G2`), no availability relation `A ⊆ S` that answers every
read is consistent (Lifted Monotonicity for `A`), so by Complete CAP for `A`
(`CAP.complete_cap_for`) no system has Availability for `A` and Partition
Consistency.  Witness: Bailis et al.'s `T₁ : r(y) w(x)`, `T₂ : r(x) w(y)` at two
replicas with no delivery; each read's only permitted answer is the initial
version, and together they form the cycle of `ws_cycle`. -/
theorem writeSkew_unavailableP (P : (j : Inp lam) → CH j → Prop) (hP : ∀ j, ¬ P j (serial j))
    (hWS : ∀ j (H : CH j), G2 H → P j H) (D : Type)
    (A : Table (Inp lam) (St Fact)) (hAS : ∀ i o, A i o → (specP P hP).P i o) (htot : ∀ i, ∃ o, A i o)
    (hans : ∀ i o e, A i o → IsRd i e → ∃ v, o (.read e v)) :
    ¬ CAP.ConsistentOn (specP P hP) A ∧
      ¬ ∃ Sys : CAP.System (specP P hP) D, CAP.AvailabilityFor A Sys ∧ CAP.PartitionConsistencyAtEnd Sys := by
  have hn : ¬ CAP.ConsistentOn (specP P hP) A := by
    intro hC
    obtain ⟨o1, ho1⟩ := htot wi1
    obtain ⟨o2, ho2⟩ := htot wi2
    obtain ⟨v1, hv1⟩ := hans wi1 o1 0 ho1 ⟨1, 1, 1, 0, rfl⟩
    obtain ⟨v2, hv2⟩ := hans wi2 o2 2 ho2 ⟨2, 1, 0, 1, rfl⟩
    have e1 : v1 = tsInit := by
      obtain ⟨H, hF, -⟩ := hAS _ _ ho1
      obtain ⟨-, hv⟩ := hF _ hv1
      rw [← hv]; exact wi1_ver (H.ok 0 1 1 1 0 rfl)
    have e2 : v2 = tsInit := by
      obtain ⟨H, hF, -⟩ := hAS _ _ ho2
      obtain ⟨-, hv⟩ := hF _ hv2
      rw [← hv]; exact wi2_ver (H.ok 2 2 1 0 1 rfl)
    obtain ⟨u, ⟨H, hF, hPH⟩, hle⟩ := hC [(wi1, o1), (wi2, o2)]
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> assumption) wiJ
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact le_wJ wkeep1 wk1
          · exact le_wJ wkeep2 wk2)
    have a0 : H.ans 0 = tsInit := by
      rw [← e1]; exact (hF _ (hle _ (List.mem_cons_self ..) _ hv1)).2
    have a2 : H.ans 2 = tsInit := by
      rw [← e2]; exact (hF _ (hle _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ hv2)).2
    exact hPH (hWS _ H (ws_cycle H a0 a2))
  exact ⟨hn, fun h => hn ((CAP.complete_cap_for (specP P hP) D A hAS).1 h)⟩

/-- Repeatable read and serializability (which proscribe `G2`, i.e. Write
Skew) are unavailable by the Write Skew witness, independently of Lost
Update. -/
theorem writeSkew_unavailable (L : Level) (hL : L = .RR ∨ L = .SER) (D : Type)
    (A : Table (Inp lam) (St Fact)) (hAS : ∀ i o, A i o → (spec L).P i o) (htot : ∀ i, ∃ o, A i o)
    (hans : ∀ i o e, A i o → IsRd i e → ∃ v, o (.read e v)) :
    ¬ CAP.ConsistentOn (spec L) A ∧
      ¬ ∃ Sys : CAP.System (spec L) D, CAP.AvailabilityFor A Sys ∧ CAP.PartitionConsistencyAtEnd Sys :=
  writeSkew_unavailableP (Proscribed L) _ (fun _ H h => by
    rcases hL with rfl | rfl <;> exact Or.inr (Or.inr h)) D A hAS htot hans

end WS
end HATSpec
end CC
