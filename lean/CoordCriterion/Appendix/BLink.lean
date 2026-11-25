import CoordCriterion.Appendix.ClassicalFrontiers

/-!
# B-link trees: forward reachability equals the remembered exact claims

Namespace `CC.BLink`.  Supports the subsection `app:search` of
`paper/app-classical-problems.tex` (Props. `prop:persistent-forwarding` and
`prop:remembered-claims`(4)).

* **Histories of states.**  `SRestr` generalizes `Front.Restructuring`:
  histories are sequences of states, each with a structure snapshot, and the
  steps satisfy `Front.Obligations` on snapshots.  It has persistent
  forwarding (`SRestr.persistent_forwarding`), state-determined continuations
  (`SRestr.stateDet`) and the equality criterion `SRestr.fwd_eq_iff`;
  `ofRestructuring` embeds snapshot histories.  States are needed because an
  exact claim uses child edges only, and a snapshot does not record which
  edges are child edges.
* **The model.**  A tree `St` records for each node its level and low key,
  the inserted keys, and the posted nodes (those with a pointer in the level
  above).  High keys, right links, leaf contents and child pointers are
  computed: a node covers `k` when its low key is below `k` and no node of its
  level has a low key strictly between (`covers`); the link edge goes to the
  right neighbor (`linkE`); the child edge goes to the entry with the largest
  low key below `k` (`childE`).  Steps (`BStep`): insert a key; half-split the
  node of a level that covers a separator, creating a fresh right sibling
  (on internal levels the separator must be a posted child's low key);
  post a node into the level above; grow a root above the top level with
  pointers to the old root and to one posted node split off it.  Invariants
  `WF` hold on reachable trees (`WF.step`), and each step satisfies the
  obligations (`oblig_step`): searches are deterministic and stop at leaves,
  and old search edges are simulated in the sense of the weakened obligation
  2.  Posting violates the strong form of obligation 2 (`post_breaks_strong`).
* **Hypothesis (H).**  A valid claim `(k, π)` has `π` a node with low key
  below `k`, and `k` inserted (`valid_facts`).  `cut` removes the levels above
  `π`, the nodes of `π`'s level with low key between `π`'s and `k`, and on
  lower levels the unposted nodes between the last entry below `k` and `k`; the
  result is a tree (`cut_wf`, `cut_sub`) where the claim is exact
  (`cut_exact`).  Every sub-tree of a reachable tree can be completed to it
  (`complete`: insert the keys, then level by level split off the missing
  nodes, grow, and post).  Hence every valid claim was exact earlier on a
  history to the same tree (`blink_H`), and forward reachability equals the
  remembered exact claims (`blink_fwd_eq`).

Simplifications relative to Lehman and Yao: steps are atomic (no locks or
interleaved reads and writes inside a step); node contents are derived from
levels, low keys, keys and posted flags rather than stored; split points are
arbitrary (no node capacity or half-full rule); keys are natural numbers with
`0` as `-∞`; there are no deletions.
-/

namespace CC
namespace BLink
open CC.Front CC.Apps
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Restructuring over states -/

section General
variable {S K P : Type}

/-- A restructuring algorithm whose histories are sequences of states `S`;
each state has a structure snapshot `snap`, and every step satisfies the
obligations on snapshots. -/
structure SRestr (S K P : Type) where
  init : S
  step : S → S → Prop
  snap : S → Snap K P
  oblig : ∀ s s', step s s' → Obligations (snap s) (snap s')

inductive SChain (st : S → S → Prop) : S → List S → Prop
  | nil (s : S) : SChain st s []
  | cons {s s' : S} {l : List S} : st s s' → SChain st s' l → SChain st s (s' :: l)

/-- The state after a list of states. -/
def lastS : S → List S → S
  | s, [] => s
  | _, s :: l => lastS s l

theorem lastS_append (s : S) (l t : List S) : lastS s (l ++ t) = lastS (lastS s l) t := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih => exact ih x

theorem schain_append {st : S → S → Prop} :
    ∀ {s : S} (l t : List S), SChain st s (l ++ t) → SChain st (lastS s l) t
  | _, [], _, h => h
  | _, _ :: l, t, h => by
    cases h with
    | cons _ h' => exact schain_append l t h'

theorem schain_concat {st : S → S → Prop} :
    ∀ {s : S} (l t : List S), SChain st s l → SChain st (lastS s l) t → SChain st s (l ++ t)
  | _, [], _, _, h2 => h2
  | _, _ :: l, t, h1, h2 => by
    cases h1 with
    | cons hs h1' => exact SChain.cons hs (schain_concat l t h1' h2)

/-- Inputs: finite legal histories of states. -/
def SRestr.Hist (Rs : SRestr S K P) : Type := {l : List S // SChain Rs.step Rs.init l}

instance (Rs : SRestr S K P) : PO Rs.Hist where
  le h h' := ∃ t, h.1 ++ t = h'.1
  refl h := ⟨[], List.append_nil _⟩
  trans := by
    rintro a b c ⟨t, h1⟩ ⟨t', h2⟩
    exact ⟨t ++ t', by rw [← List.append_assoc, h1, h2]⟩

instance (Rs : SRestr S K P) : PO.Antisymm Rs.Hist where
  antisymm := by
    rintro a b ⟨t, h⟩ ⟨t', h'⟩
    have hl := congrArg List.length h
    have hl' := congrArg List.length h'
    simp only [List.length_append] at hl hl'
    have : t = [] := by
      cases t with
      | nil => rfl
      | cons _ _ => simp at hl; omega
    subst this
    exact Subtype.ext (by simpa using h)

/-- The current state of a history. -/
def SRestr.cur (Rs : SRestr S K P) (h : Rs.Hist) : S := lastS Rs.init h.1

/-- Claims valid in the current structure. -/
def SRestr.R (Rs : SRestr S K P) (h : Rs.Hist) : K → P → Prop := claims (Rs.snap (Rs.cur h))

theorem schain_claims (Rs : SRestr S K P) {s : S} {t : List S} (h : SChain Rs.step s t)
    {k : K} {p : P} (hc : claims (Rs.snap s) k p) : claims (Rs.snap (lastS s t)) k p := by
  induction h with
  | nil => exact hc
  | cons hs _ ih => exact ih (claims_step (Rs.oblig _ _ hs) hc)

/-- **Persistent forwarding** for state histories. -/
theorem SRestr.persistent_forwarding (Rs : SRestr S K P) {h h' : Rs.Hist} (hle : h ≼ h') :
    ∀ k p, Rs.R h k p → Rs.R h' k p := by
  intro k p hc
  obtain ⟨t, ht⟩ := hle
  have hch : SChain Rs.step Rs.init (h.1 ++ t) := by rw [ht]; exact h'.2
  have := schain_claims Rs (schain_append h.1 t hch) hc
  show claims (Rs.snap (lastS Rs.init h'.1)) k p
  rw [← ht, lastS_append]; exact this

/-- Continuations depend only on the current state. -/
theorem SRestr.stateDet (Rs : SRestr S K P) : StateDet Rs.cur := by
  rintro h h' k hg ⟨t, ht⟩
  have hk : SChain Rs.step Rs.init (h.1 ++ t) := by rw [ht]; exact k.2
  have htail := schain_append h.1 t hk
  have htail' : SChain Rs.step (lastS Rs.init h'.1) t := by
    have : lastS Rs.init h.1 = lastS Rs.init h'.1 := hg
    rw [← this]; exact htail
  refine ⟨⟨h'.1 ++ t, schain_concat _ _ h'.2 htail'⟩, ⟨t, rfl⟩, ?_⟩
  show lastS Rs.init (h'.1 ++ t) = lastS Rs.init k.1
  rw [← ht, lastS_append, lastS_append]
  exact congrArg (fun g => lastS g t) hg.symm

/-- Forward-reachability claims as a validity map. -/
def SRestr.fwdV (Rs : SRestr S K P) : Rs.Hist → K × P → Prop := fun h c => Rs.R h c.1 c.2

theorem SRestr.fwdV_grows (Rs : SRestr S K P) : Grows Rs.fwdV :=
  fun _ _ hle c hc => Rs.persistent_forwarding hle c.1 c.2 hc

/-- Forward reachability contains the claims of `X` remembered across
histories with the same current state, as long as `X` contains only valid
claims. -/
theorem SRestr.fwd_contains (Rs : SRestr S K P) (X : Rs.Hist → K × P → Prop)
    (hX : ∀ h c, X h c → Rs.fwdV h c) (h : Rs.Hist) (c : K × P)
    (hc : stateRemembered Rs.cur X h c) : Rs.fwdV h c :=
  stateRemembered_least Rs.cur X (fun s c => claims (Rs.snap s) c.1 c.2) hX
    (fun i j hij c hc => Rs.persistent_forwarding hij c.1 c.2 hc) h c hc

/-- Forward reachability equals the state-remembered map of `X` exactly when
every valid claim is state-remembered. -/
theorem SRestr.fwd_eq_iff (Rs : SRestr S K P) (X : Rs.Hist → K × P → Prop)
    (hX : ∀ h c, X h c → Rs.fwdV h c) :
    (∀ h c, Rs.fwdV h c ↔ stateRemembered Rs.cur X h c) ↔
      (∀ h c, Rs.fwdV h c → stateRemembered Rs.cur X h c) :=
  ⟨fun H h c => (H h c).1, fun H h c => ⟨H h c, Rs.fwd_contains X hX h c⟩⟩

/-- A restructuring algorithm on snapshots is the special case whose states
are their own snapshots. -/
def ofRestructuring (Rs : Restructuring K P) : SRestr (Snap K P) K P :=
  ⟨Rs.init, Rs.step, id, Rs.oblig⟩

end General

/-! ## The B-link tree model -/

section Model

/-- A B-link tree state.  Nodes are natural numbers; `lev x = some j` when
node `x` exists at level `j` (leaves are level 0).  `low x` is the low key
of `x` (exclusive; `0` stands for `-∞`).  `keys` are the inserted keys and
`posted` the nodes whose separator has been posted into the level above.
High keys, right links, leaf contents and child pointers are computed from
these (`covers`, `linkE`, `childE`, `occ`). -/
structure St where
  lev : Nat → Option Nat
  low : Nat → Nat
  keys : Nat → Prop
  posted : Nat → Prop

theorem St.ext' {a b : St} (h1 : a.lev = b.lev) (h2 : a.low = b.low) (h3 : a.keys = b.keys)
    (h4 : a.posted = b.posted) : a = b := by
  cases a; cases b; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

/-- Create node `y` at level `j` with low key `l`. -/
def St.addNode (s : St) (y j l : Nat) : St :=
  { s with lev := fun i => if i = y then some j else s.lev i,
           low := fun i => if i = y then l else s.low i }

/-- Mark `x` as posted. -/
def St.addPost (s : St) (x : Nat) : St := { s with posted := fun i => i = x ∨ s.posted i }

/-- Insert key `k`. -/
def St.addKey (s : St) (k : Nat) : St := { s with keys := fun i => i = k ∨ s.keys i }

/-- The initial tree: one empty leaf `0`. -/
def St.init : St := ⟨fun i => if i = 0 then some 0 else none, fun _ => 0, fun _ => False,
  fun _ => False⟩

variable (s : St)

/-- `x` covers `k`: `low x < k ≤ high x`, where the high key is the next low
key on the level. -/
def St.covers (x k : Nat) : Prop :=
  ∃ j, s.lev x = some j ∧ s.low x < k ∧ ∀ w, s.lev w = some j → s.low x < s.low w → k ≤ s.low w

/-- `w` has a pointer in the level above: it is posted, or it is the leftmost
node of its level and the level above exists. -/
def St.entry (w : Nat) : Prop :=
  s.posted w ∨ (s.low w = 0 ∧ ∃ j, s.lev w = some j ∧ ∃ r, s.lev r = some (j + 1))

/-- The right-link edge for `k` from `x` to its right neighbor `z`, taken when
`k` exceeds the high key of `x`. -/
def St.linkE (k x z : Nat) : Prop :=
  ∃ j, s.lev x = some j ∧ s.lev z = some j ∧ s.low x < s.low z ∧ s.low z < k ∧
    ∀ w, s.lev w = some j → s.low x < s.low w → s.low z ≤ s.low w

/-- The child edge for `k` from `y` (covering `k`) to its child `w`: the
entry of `y` with the largest separator below `k`. -/
def St.childE (k y w : Nat) : Prop :=
  ∃ j, s.lev y = some (j + 1) ∧ s.covers y k ∧ s.lev w = some j ∧ s.entry w ∧
    s.low y ≤ s.low w ∧ s.low w < k ∧
    ∀ w', s.lev w' = some j → s.entry w' → s.low w < s.low w' → k ≤ s.low w'

/-- `x` holds `k`: a leaf covering an inserted key. -/
def St.occ (k x : Nat) : Prop := s.lev x = some 0 ∧ s.covers x k ∧ s.keys k

/-- The structure snapshot: search edges are link and child edges. -/
def St.snap : Snap Nat Nat := ⟨fun k p q => s.linkE k p q ∨ s.childE k p q, s.occ⟩

/-- Paths of child edges. -/
inductive CPath (k : Nat) : Nat → Nat → Prop
  | refl (p : Nat) : CPath k p p
  | step {p q r : Nat} : s.childE k p q → CPath k q r → CPath k p r

/-- The claim `(k, p)` is exact: a search from `p` reaches an occurrence by
child edges alone. -/
def St.exact (k p : Nat) : Prop := ∃ q, CPath s k p q ∧ s.occ k q

/-- Invariants of reachable trees. -/
structure WF : Prop where
  root : s.lev 0 = some 0 ∧ s.low 0 = 0
  uniq : ∀ x y j, s.lev x = some j → s.lev y = some j → s.low x = s.low y → x = y
  dead : ∀ x, s.lev x = none → s.low x = 0 ∧ ¬ s.posted x
  inner : ∀ y j, s.lev y = some (j + 1) → ∃ w, s.lev w = some j ∧ s.entry w ∧ s.low w = s.low y
  post : ∀ x, s.posted x → ∃ j, s.lev x = some j ∧ 0 < s.low x ∧ ∃ r, s.lev r = some (j + 1)
  grown : ∀ r j, s.lev r = some (j + 1) → ∃ z, s.lev z = some j ∧ s.posted z
  left : ∀ x j, s.lev x = some j → ∃ y, s.lev y = some j ∧ s.low y = 0
  keyp : ∀ k, s.keys k → 0 < k
  bnd : ∃ N, (∀ i, N ≤ i → s.lev i = none) ∧ (∀ k, s.keys k → k < N) ∧
    (∀ i j, s.lev i = some j → j < N)

end Model

/-- The Lehman–Yao steps. -/
inductive BStep : St → St → Prop
  /-- Insert key `k` (into the leaf covering it). -/
  | ins (s : St) (k : Nat) : 0 < k → BStep s (s.addKey k)
  /-- Half-split the node of level `j` covering `l`: the new right sibling `y`
  gets low key `l`, the keys or child pointers above `l`, and the old right
  link; on internal levels `l` must be a separator held by the node. -/
  | split (s : St) (j l y : Nat) : (∃ x, s.lev x = some j) → s.lev y = none → 0 < l →
      (∀ z, s.lev z = some j → s.low z ≠ l) →
      (∀ i, j = i + 1 → ∃ w, s.lev w = some i ∧ s.posted w ∧ s.low w = l) →
      BStep s (s.addNode y j l)
  /-- Post the separator of `x` (and a pointer to `x`) into the node of the
  level above that covers it. -/
  | post (s : St) (x j : Nat) : s.lev x = some j → 0 < s.low x → ¬ s.posted x →
      (∃ r, s.lev r = some (j + 1)) → BStep s (s.addPost x)
  /-- Grow a new root `r` above the top level `j`, holding pointers to the old
  root and to a node `z` split off it. -/
  | grow (s : St) (j r z : Nat) : (∀ b, s.lev b ≠ some (j + 1)) → s.lev r = none →
      s.lev z = some j → 0 < s.low z → BStep s ((s.addNode r (j + 1) 0).addPost z)

/-! ## Invariants are preserved -/

section Steps
variable {s : St} {x y z r j l k i : Nat}

@[simp] theorem addNode_lev (s : St) (y j l i : Nat) :
    (s.addNode y j l).lev i = if i = y then some j else s.lev i := rfl
@[simp] theorem addNode_low (s : St) (y j l i : Nat) :
    (s.addNode y j l).low i = if i = y then l else s.low i := rfl
@[simp] theorem addNode_keys (s : St) (y j l : Nat) : (s.addNode y j l).keys = s.keys := rfl
@[simp] theorem addNode_posted (s : St) (y j l : Nat) : (s.addNode y j l).posted = s.posted := rfl
@[simp] theorem addPost_lev (s : St) (x : Nat) : (s.addPost x).lev = s.lev := rfl
@[simp] theorem addPost_low (s : St) (x : Nat) : (s.addPost x).low = s.low := rfl
@[simp] theorem addPost_keys (s : St) (x : Nat) : (s.addPost x).keys = s.keys := rfl
@[simp] theorem addPost_posted (s : St) (x i : Nat) : (s.addPost x).posted i = (i = x ∨ s.posted i) := rfl
@[simp] theorem addKey_lev (s : St) (k : Nat) : (s.addKey k).lev = s.lev := rfl
@[simp] theorem addKey_low (s : St) (k : Nat) : (s.addKey k).low = s.low := rfl
@[simp] theorem addKey_posted (s : St) (k : Nat) : (s.addKey k).posted = s.posted := rfl
@[simp] theorem addKey_keys (s : St) (k i : Nat) : (s.addKey k).keys i = (i = k ∨ s.keys i) := rfl

theorem ne_of_lev {a : Nat} {j : Nat} (h : s.lev a = some j) (hy : s.lev y = none) : a ≠ y := by
  intro e; subst e; rw [h] at hy; cases hy

theorem entry_addNode (hy : s.lev y = none) {w : Nat} (hd : ¬ s.posted y) (h : s.entry w) :
    (s.addNode y j l).entry w := by
  rcases h with hp | ⟨h0, j', hw, r, hr⟩
  · exact Or.inl hp
  · have h1 := ne_of_lev hw hy
    have h2 := ne_of_lev hr hy
    exact Or.inr ⟨by simp [h1, h0], j', by simp [h1, hw], r, by simp [h2, hr]⟩

theorem entry_addPost {w : Nat} (h : s.entry w) : (s.addPost x).entry w := by
  rcases h with hp | h
  · exact Or.inl (Or.inr hp)
  · exact Or.inr h

theorem WF.ofIns (hs : WF s) (hk : 0 < k) : WF (s.addKey k) := by
  obtain ⟨N, h1, h2, h3⟩ := hs.bnd
  refine ⟨hs.root, hs.uniq, hs.dead, hs.inner, hs.post, hs.grown, hs.left, ?_, ?_⟩
  · intro k' hk'; rcases hk' with e | hk'
    · subst e; exact hk
    · exact hs.keyp k' hk'
  · refine ⟨N + k + 1, fun i hi => h1 i (by omega), ?_, fun i j hi => by have := h3 i j hi; omega⟩
    intro k' hk'; rcases hk' with e | hk'
    · omega
    · have := h2 k' hk'; omega

theorem WF.ofSplit (hs : WF s) (hx : ∃ x, s.lev x = some j) (hy : s.lev y = none) (hl : 0 < l)
    (hz : ∀ z, s.lev z = some j → s.low z ≠ l)
    (hw : ∀ i, j = i + 1 → ∃ w, s.lev w = some i ∧ s.posted w ∧ s.low w = l) :
    WF (s.addNode y j l) := by
  have hdy := (hs.dead y hy).2
  have y0 : (0 : Nat) ≠ y := ne_of_lev hs.root.1 hy
  obtain ⟨N, h1, h2, h3⟩ := hs.bnd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hs.keyp, ?_⟩
  · simp only [addNode_lev, addNode_low, if_neg y0]; exact hs.root
  · intro a b j' ha hb hab
    simp only [addNode_lev, addNode_low] at ha hb hab
    by_cases hay : a = y <;> by_cases hby : b = y
    · rw [hay, hby]
    · simp [hay, hby] at ha hb hab; subst ha; exact absurd hab.symm (hz b hb)
    · simp [hay, hby] at ha hb hab; subst hb; exact absurd hab (hz a ha)
    · simp [hay, hby] at ha hb hab; exact hs.uniq a b j' ha hb hab
  · intro a ha
    by_cases hay : a = y
    · simp [hay] at ha
    · simp [hay] at ha ⊢; exact hs.dead a ha
  · intro b j' hb
    by_cases hby : b = y
    · simp [hby] at hb; subst hb
      obtain ⟨w, hw1, hw2, hw3⟩ := hw j' rfl
      have hwy := ne_of_lev hw1 hy
      exact ⟨w, by simp [hwy, hw1], Or.inl hw2, by simp [hwy, hby, hw3]⟩
    · simp [hby] at hb
      obtain ⟨w, hw1, hw2, hw3⟩ := hs.inner b j' hb
      have hwy := ne_of_lev hw1 hy
      exact ⟨w, by simp [hwy, hw1], entry_addNode hy hdy hw2, by simp [hwy, hby, hw3]⟩
  · intro a ha
    obtain ⟨j', ha1, ha2, r, hr⟩ := hs.post a ha
    have h1 := ne_of_lev ha1 hy
    have h2 := ne_of_lev hr hy
    exact ⟨j', by simp [h1, ha1], by simp [h1, ha2], r, by simp [h2, hr]⟩
  · intro b j' hb
    by_cases hby : b = y
    · simp [hby] at hb; subst hb
      obtain ⟨w, hw1, hw2, _⟩ := hw j' rfl
      exact ⟨w, by simp [ne_of_lev hw1 hy, hw1], hw2⟩
    · simp [hby] at hb
      obtain ⟨w, hw1, hw2⟩ := hs.grown b j' hb
      exact ⟨w, by simp [ne_of_lev hw1 hy, hw1], hw2⟩
  · intro a j' ha
    by_cases hay : a = y
    · simp [hay] at ha; subst ha
      obtain ⟨x, hx⟩ := hx
      obtain ⟨b, hb1, hb2⟩ := hs.left x _ hx
      exact ⟨b, by simp [ne_of_lev hb1 hy, hb1], by simp [ne_of_lev hb1 hy, hb2]⟩
    · simp [hay] at ha
      obtain ⟨b, hb1, hb2⟩ := hs.left a _ ha
      exact ⟨b, by simp [ne_of_lev hb1 hy, hb1], by simp [ne_of_lev hb1 hy, hb2]⟩
  · refine ⟨N + y + j + 1, ?_, fun k hk => by have := h2 k hk; omega, ?_⟩
    · intro i hi
      have : i ≠ y := by omega
      simp [this]; exact h1 i (by omega)
    · intro i j' hi
      by_cases hiy : i = y
      · simp [hiy] at hi; omega
      · simp [hiy] at hi; have := h3 i j' hi; omega

theorem WF.ofPost (hs : WF s) (hx : s.lev x = some j) (hl : 0 < s.low x)
    (hr : ∃ r, s.lev r = some (j + 1)) : WF (s.addPost x) := by
  refine ⟨hs.root, hs.uniq, ?_, ?_, ?_, ?_, hs.left, hs.keyp, hs.bnd⟩
  · intro a ha
    refine ⟨(hs.dead a ha).1, ?_⟩
    rintro (e | h)
    · subst e; simp only [addPost_lev] at ha; rw [hx] at ha; cases ha
    · exact (hs.dead a ha).2 h
  · intro b j' hb
    obtain ⟨w, hw1, hw2, hw3⟩ := hs.inner b j' hb
    exact ⟨w, hw1, entry_addPost hw2, hw3⟩
  · rintro a (e | ha)
    · subst e; exact ⟨j, hx, hl, hr⟩
    · exact hs.post a ha
  · intro b j' hb
    obtain ⟨w, hw1, hw2⟩ := hs.grown b j' hb
    exact ⟨w, hw1, Or.inr hw2⟩

theorem WF.ofGrow (hs : WF s) (htop : ∀ b, s.lev b ≠ some (j + 1)) (hr : s.lev r = none)
    (hz : s.lev z = some j) (hl : 0 < s.low z) : WF ((s.addNode r (j + 1) 0).addPost z) := by
  have hzr := ne_of_lev hz hr
  have hdy := (hs.dead r hr).2
  have y0 : (0 : Nat) ≠ r := ne_of_lev hs.root.1 hr
  obtain ⟨N, b1, b2, b3⟩ := hs.bnd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hs.keyp, ?_⟩
  · simp only [addPost_lev, addPost_low, addNode_lev, addNode_low, if_neg y0]; exact hs.root
  · intro a b j' ha hb hab
    simp only [addPost_lev, addPost_low, addNode_lev, addNode_low] at ha hb hab
    by_cases hay : a = r <;> by_cases hby : b = r
    · rw [hay, hby]
    · simp [hay, hby] at ha hb; subst ha; exact absurd hb (htop b)
    · simp [hay, hby] at ha hb; subst hb; exact absurd ha (htop a)
    · simp [hay, hby] at ha hb hab; exact hs.uniq a b j' ha hb hab
  · intro a ha
    by_cases hay : a = r
    · simp [hay] at ha
    · simp [hay] at ha ⊢
      refine ⟨(hs.dead a ha).1, ?_, (hs.dead a ha).2⟩
      intro e; subst e; rw [hz] at ha; cases ha
  · intro b j' hb
    by_cases hby : b = r
    · simp [hby] at hb; subst hb
      obtain ⟨w, hw1, hw2⟩ := hs.left z _ hz
      have hwy := ne_of_lev hw1 hr
      exact ⟨w, by simp [hwy, hw1], Or.inr ⟨by simp [hwy, hw2], j, by simp [hwy, hw1], r,
        by simp⟩, by simp [hwy, hby, hw2]⟩
    · simp [hby] at hb
      obtain ⟨w, hw1, hw2, hw3⟩ := hs.inner b j' hb
      have hwy := ne_of_lev hw1 hr
      exact ⟨w, by simp [hwy, hw1], entry_addPost (entry_addNode hr hdy hw2),
        by simp [hwy, hby, hw3]⟩
  · rintro a (e | ha)
    · subst e; exact ⟨j, by simp [hzr, hz], by simp [hzr, hl], r, by simp⟩
    obtain ⟨j', ha1, ha2, r', hr'⟩ := hs.post a ha
    have h1 := ne_of_lev ha1 hr
    have h2 := ne_of_lev hr' hr
    exact ⟨j', by simp [h1, ha1], by simp [h1, ha2], r', by simp [h2, hr']⟩
  · intro b j' hb
    by_cases hby : b = r
    · simp [hby] at hb; subst hb
      exact ⟨z, by simp [hzr, hz], Or.inl rfl⟩
    · simp [hby] at hb
      obtain ⟨w, hw1, hw2⟩ := hs.grown b j' hb
      exact ⟨w, by simp [ne_of_lev hw1 hr, hw1], Or.inr hw2⟩
  · intro a j' ha
    by_cases hay : a = r
    · subst hay; exact ⟨a, ha, by simp⟩
    · simp [hay] at ha
      obtain ⟨b, hb1, hb2⟩ := hs.left a _ ha
      exact ⟨b, by simp [ne_of_lev hb1 hr, hb1], by simp [ne_of_lev hb1 hr, hb2]⟩
  · refine ⟨N + r + j + 2, ?_, fun k hk => by have := b2 k hk; omega, ?_⟩
    · intro i hi
      have : i ≠ r := by omega
      simp [this]; exact b1 i (by omega)
    · intro i j' hi
      by_cases hiy : i = r
      · simp [hiy] at hi; omega
      · simp [hiy] at hi; have := b3 i j' hi; omega

theorem WF.step {s s' : St} (hs : WF s) (h : BStep s s') : WF s' := by
  cases h with
  | ins k hk => exact hs.ofIns hk
  | split j l y h1 h2 h3 h4 h5 => exact hs.ofSplit h1 h2 h3 h4 h5
  | post x j h1 h2 _ h4 => exact hs.ofPost h1 h2 h4
  | grow j r z h1 h2 h3 h4 => exact hs.ofGrow h1 h2 h3 h4

theorem WF.init : WF St.init := by
  refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun _ h => h.elim, ⟨1, ?_, fun _ h => h.elim, ?_⟩⟩
  · intro a b j ha hb _
    simp only [St.init] at ha hb
    by_cases h1 : a = 0 <;> by_cases h2 : b = 0 <;> simp_all
  · intro a ha; exact ⟨rfl, id⟩
  · intro b j hb; simp only [St.init] at hb; by_cases h : b = 0 <;> simp_all
  · intro _ h; exact h.elim
  · intro b j hb; simp only [St.init] at hb; by_cases h : b = 0 <;> simp_all
  · intro a j ha; exact ⟨0, by simp only [St.init] at ha ⊢; by_cases h : a = 0 <;> simp_all, rfl⟩
  · intro i hi; simp only [St.init]; simp; omega
  · intro i j hi; simp only [St.init] at hi; by_cases h : i = 0 <;> simp_all

end Steps

/-! ## Search obligations -/

section Oblig
variable {s : St} {x y z r j l k i : Nat}

/-- Least value of `f` on a nonempty set. -/
theorem exists_min (f : Nat → Nat) (P : Nat → Prop) (h : ∃ w, P w) :
    ∃ w, P w ∧ ∀ w', P w' → f w ≤ f w' := by
  obtain ⟨w0, hw0⟩ := h
  suffices H : ∀ n w, f w = n → P w → ∃ w, P w ∧ ∀ w', P w' → f w ≤ f w' from H _ w0 rfl hw0
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro w hw hp
    by_cases hc : ∃ w', P w' ∧ f w' < f w
    · obtain ⟨w', hp', hlt⟩ := hc
      exact ih (f w') (by omega) w' rfl hp'
    · exact ⟨w, hp, fun w' hp' => Nat.le_of_not_lt fun hlt => hc ⟨w', hp', hlt⟩⟩

/-- Greatest value of `f` below `k` on a set with an element below `k`. -/
theorem exists_max_below (f : Nat → Nat) (P : Nat → Prop) (k : Nat) (h : ∃ w, P w ∧ f w < k) :
    ∃ w, P w ∧ f w < k ∧ ∀ w', P w' → f w' < k → f w' ≤ f w := by
  obtain ⟨w0, hw0, hk0⟩ := h
  suffices H : ∀ n w, k - f w = n → P w → f w < k →
      ∃ w, P w ∧ f w < k ∧ ∀ w', P w' → f w' < k → f w' ≤ f w from H _ w0 rfl hw0 hk0
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro w hw hp hk
    by_cases hc : ∃ w', P w' ∧ f w' < k ∧ f w < f w'
    · obtain ⟨w', hp', hk', hlt⟩ := hc
      exact ih (k - f w') (by omega) w' rfl hp' hk'
    · exact ⟨w, hp, hk, fun w' hp' hk' => Nat.le_of_not_lt fun hlt => hc ⟨w', hp', hk', hlt⟩⟩

theorem lev_inj {a : Nat} {j j' : Nat} (h : s.lev a = some j) (h' : s.lev a = some j') : j = j' := by
  rw [h] at h'; exact Option.some.inj h'

theorem linkE_det (hs : WF s) (h1 : s.linkE k x z) (h2 : s.linkE k x z') : z = z' := by
  obtain ⟨j, hx, hz, a1, a2, a3⟩ := h1
  obtain ⟨j', hx', hz', b1, b2, b3⟩ := h2
  have := lev_inj hx hx'; subst this
  have e1 := a3 z' hz' b1
  have e2 := b3 z hz a1
  exact hs.uniq z z' j hz hz' (by omega)

theorem childE_det (hs : WF s) (h1 : s.childE k y w) (h2 : s.childE k y w') : w = w' := by
  obtain ⟨j, hy, _, hw, he, a1, a2, a3⟩ := h1
  obtain ⟨j', hy', _, hw', he', b1, b2, b3⟩ := h2
  have : j + 1 = j' + 1 := lev_inj hy hy'
  have : j = j' := by omega
  subst this
  have : s.low w = s.low w' := by
    rcases Nat.lt_trichotomy (s.low w) (s.low w') with c | c | c
    · have := a3 w' hw' he' c; omega
    · exact c
    · have := b3 w hw he c; omega
  exact hs.uniq w w' j hw hw' this

theorem linkE_not_covers (h1 : s.linkE k x z) (h2 : s.covers x k) : False := by
  obtain ⟨j, hx, hz, a1, a2, _⟩ := h1
  obtain ⟨j', hx', _, b3⟩ := h2
  have := lev_inj hx hx'; subst this
  have := b3 z hz a1; omega

theorem snap_det (hs : WF s) : ∀ k p q q', (St.snap s).edge k p q → (St.snap s).edge k p q' → q = q' := by
  intro k p q q' h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact linkE_det hs h1 h2
  · obtain ⟨_, _, hc, _⟩ := h2; exact (linkE_not_covers h1 hc).elim
  · obtain ⟨_, _, hc, _⟩ := h1; exact (linkE_not_covers h2 hc).elim
  · exact childE_det hs h1 h2

theorem snap_stop : ∀ k p q, (St.snap s).occ k p → ¬ (St.snap s).edge k p q := by
  rintro k p q ⟨h0, hc, _⟩ (h | ⟨j, hj, _⟩)
  · exact linkE_not_covers h hc
  · rw [h0] at hj; cases hj

theorem edge_path {p q : Nat} (h : (St.snap s).edge k p q) : Path (St.snap s) k p q :=
  Path.step h (Path.refl q)

/-- Searching right along a level reaches every node whose low key is below
the search key. -/
theorem walk (hs : WF s) : ∀ n q x, s.low x - s.low q = n → s.lev q = some j → s.lev x = some j →
    s.low q < s.low x → s.low x < k → Path (St.snap s) k q x := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro q x hn hq hx h1 h2
    obtain ⟨z, ⟨hz, hz1⟩, hzm⟩ := exists_min s.low (fun w => s.lev w = some j ∧ s.low q < s.low w)
      ⟨x, hx, h1⟩
    have hzx := hzm x ⟨hx, h1⟩
    have he : s.linkE k q z := ⟨j, hq, hz, hz1, by omega, fun w hw hw' => hzm w ⟨hw, hw'⟩⟩
    by_cases e : z = x
    · subst e; exact edge_path (Or.inl he)
    · have hlt : s.low z < s.low x := by
        rcases Nat.lt_or_eq_of_le hzx with c | c
        · exact c
        · exact absurd (hs.uniq z x j hz hx c) e
      exact Path.step (Or.inl he) (ih _ (by omega) z x rfl hz hx hlt h2)

/-! ### Insert -/

theorem oblig_ins (hs : WF s) : Obligations (St.snap s) (St.snap (s.addKey k)) := by
  refine ⟨snap_det hs, snap_stop, fun k' p q h => ⟨q, edge_path h, Path.refl q⟩, ?_⟩
  rintro k' p ⟨h1, h2, h3⟩
  exact ⟨p, Path.refl p, h1, h2, Or.inr h3⟩

/-! ### Post -/

theorem oblig_post (hs : WF s) (hx : s.lev x = some j) : Obligations (St.snap s) (St.snap (s.addPost x)) := by
  refine ⟨snap_det hs, snap_stop, ?_, fun k' p h => ⟨p, Path.refl p, h⟩⟩
  intro k p q h
  rcases h with h | h
  · exact ⟨q, edge_path (Or.inl h), Path.refl q⟩
  · obtain ⟨i, hp, hcov, hq, he, a1, a2, a3⟩ := h
    by_cases hc : j = i ∧ s.low q < s.low x ∧ s.low x < k
    · obtain ⟨e, c1, c2⟩ := hc
      subst e
      refine ⟨x, edge_path (Or.inr ⟨j, hp, hcov, hx, Or.inl (Or.inl rfl), by simp only [addPost_low]; omega, c2, ?_⟩),
        walk hs _ q x rfl hq hx c1 c2⟩
      intro w' hw' he' hlt
      simp only [addPost_lev, addPost_low] at hw' hlt ⊢
      rcases he' with (e | hpw) | hl
      · subst e; omega
      · exact a3 w' hw' (Or.inl hpw) (by omega)
      · exact a3 w' hw' (Or.inr hl) (by omega)
    · refine ⟨q, edge_path (Or.inr ⟨i, hp, hcov, hq, entry_addPost he, a1, a2, ?_⟩), Path.refl q⟩
      intro w' hw' he' hlt
      simp only [addPost_lev, addPost_low] at hw' hlt ⊢
      rcases he' with (e | hpw) | hl
      · subst e
        have := lev_inj hx hw'; subst this
        exact Nat.le_of_not_lt fun c => hc ⟨rfl, hlt, c⟩
      · exact a3 w' hw' (Or.inl hpw) hlt
      · exact a3 w' hw' (Or.inr hl) hlt

/-! ### Split -/

section SplitObl
variable (hs : WF s) (hx : ∃ x, s.lev x = some j) (hy : s.lev y = none) (hl : 0 < l)
  (hz : ∀ z, s.lev z = some j → s.low z ≠ l)
  (hw : ∀ i, j = i + 1 → ∃ w, s.lev w = some i ∧ s.posted w ∧ s.low w = l)
include hs hx hy hl hz hw

theorem entry_split_rev {w : Nat} (h : (s.addNode y j l).entry w) (hwy : w ≠ y) : s.entry w := by
  rcases h with hp | ⟨h0, j', hw', r, hr⟩
  · exact Or.inl hp
  · simp only [addNode_lev, addNode_low, if_neg hwy] at h0 hw'
    by_cases hry : r = y
    · simp only [addNode_lev, hry, if_pos] at hr
      have : j = j' + 1 := Option.some.inj hr
      subst this
      obtain ⟨x, hx⟩ := hx
      exact Or.inr ⟨h0, j', hw', x, hx⟩
    · simp only [addNode_lev, if_neg hry] at hr
      exact Or.inr ⟨h0, j', hw', r, hr⟩

theorem y_not_entry : ¬ (s.addNode y j l).entry y := by
  rintro (hp | ⟨h0, _⟩)
  · exact (hs.dead y hy).2 hp
  · simp at h0; omega

theorem covers_split {p : Nat} (h : s.covers p k) (hn : ¬ (s.lev p = some j ∧ s.low p < l ∧ l < k))
    (hpy : p ≠ y) : (s.addNode y j l).covers p k := by
  obtain ⟨j', hp, a1, a2⟩ := h
  refine ⟨j', by simp [hpy, hp], by simp [hpy, a1], ?_⟩
  intro w hw hlt
  by_cases hwy : w = y
  · subst hwy
    simp only [addNode_lev, addNode_low, if_pos, if_neg hpy] at hw hlt ⊢
    have : j = j' := Option.some.inj hw
    subst this
    exact Nat.le_of_not_lt fun c => hn ⟨hp, hlt, c⟩
  · simp only [addNode_lev, addNode_low, if_neg hwy, if_neg hpy] at hw hlt ⊢
    exact a2 w hw hlt

theorem split_link {p : Nat} (h : s.covers p k) (hp : s.lev p = some j) (h1 : s.low p < l)
    (h2 : l < k) : (s.addNode y j l).linkE k p y ∧ (s.addNode y j l).covers y k := by
  have hpy := ne_of_lev hp hy
  obtain ⟨j', hp', a1, a2⟩ := h
  have := lev_inj hp hp'; subst this
  refine ⟨⟨j, by simp [hpy, hp], by simp, by simp [hpy, h1], by simp [h2], ?_⟩,
    ⟨j, by simp, by simp [h2], ?_⟩⟩
  · intro w hw hlt
    by_cases hwy : w = y
    · subst hwy; simp
    · simp only [addNode_lev, addNode_low, if_neg hwy, if_neg hpy, if_pos] at hw hlt ⊢
      have := a2 w hw hlt; omega
  · intro w hw hlt
    by_cases hwy : w = y
    · subst hwy; simp at hlt
    · simp only [addNode_lev, addNode_low, if_neg hwy, if_pos] at hw hlt ⊢
      exact a2 w hw (by omega)

theorem linkE_split {p q : Nat} (h : s.linkE k p q) :
    (s.addNode y j l).linkE k p q ∨
      ((s.addNode y j l).linkE k p y ∧ (s.addNode y j l).linkE k y q) := by
  obtain ⟨j', hp, hq, a1, a2, a3⟩ := h
  have hpy := ne_of_lev hp hy
  have hqy := ne_of_lev hq hy
  by_cases hc : j' = j ∧ s.low p < l ∧ l < s.low q
  · obtain ⟨e, c1, c2⟩ := hc
    subst e
    refine Or.inr ⟨⟨j', by simp [hpy, hp], by simp, by simp [hpy, c1], by simp; omega, ?_⟩,
      ⟨j', by simp, by simp [hqy, hq], by simp [hqy, c2], by simp [hqy, a2], ?_⟩⟩
    · intro w hw hlt
      by_cases hwy : w = y
      · subst hwy; simp
      · simp only [addNode_lev, addNode_low, if_neg hwy, if_neg hpy, if_pos] at hw hlt ⊢
        have := a3 w hw hlt; omega
    · intro w hw hlt
      by_cases hwy : w = y
      · subst hwy; simp at hlt
      · simp only [addNode_lev, addNode_low, if_neg hwy, if_neg hqy, if_pos] at hw hlt ⊢
        exact a3 w hw (by omega)
  · refine Or.inl ⟨j', by simp [hpy, hp], by simp [hqy, hq], by simp [hpy, hqy, a1],
      by simp [hqy, a2], ?_⟩
    intro w hw hlt
    by_cases hwy : w = y
    · subst hwy
      simp only [addNode_lev, addNode_low, if_pos, if_neg hpy, if_neg hqy] at hw hlt ⊢
      have : j = j' := Option.some.inj hw
      subst this
      exact Nat.le_of_not_lt fun c => hc ⟨rfl, hlt, c⟩
    · simp only [addNode_lev, addNode_low, if_neg hwy, if_neg hpy, if_neg hqy] at hw hlt ⊢
      exact a3 w hw hlt

theorem childE_split {p q : Nat} (h : s.childE k p q) :
    (s.addNode y j l).childE k p q ∨
      ((s.addNode y j l).linkE k p y ∧ (s.addNode y j l).childE k y q) := by
  obtain ⟨i, hp, hcov, hq, he, a1, a2, a3⟩ := h
  have hpy := ne_of_lev hp hy
  have hqy := ne_of_lev hq hy
  have hdy := (hs.dead y hy).2
  have hmax : ∀ w', (s.addNode y j l).lev w' = some i → (s.addNode y j l).entry w' →
      (s.addNode y j l).low q < (s.addNode y j l).low w' → k ≤ (s.addNode y j l).low w' := by
    intro w' hw' he' hlt
    by_cases hwy : w' = y
    · subst hwy; exact absurd he' (y_not_entry hs hx hy hl hz hw)
    · have he2 := entry_split_rev hs hx hy hl hz hw he' hwy
      simp only [addNode_lev, addNode_low, if_neg hwy, if_neg hqy] at hw' hlt ⊢
      exact a3 w' hw' he2 hlt
  by_cases hc : i + 1 = j ∧ s.low p < l ∧ l < k
  · obtain ⟨e, c1, c2⟩ := hc
    subst e
    obtain ⟨hl1, hl2⟩ := split_link hs hx hy hl hz hw hcov hp c1 c2
    refine Or.inr ⟨hl1, i, by simp, hl2, by simp [hqy, hq], entry_addNode hy hdy he, ?_,
      by simp [hqy, a2], hmax⟩
    obtain ⟨w0, hw1, hw2, hw3⟩ := hw i rfl
    simp only [addNode_low, if_pos, if_neg hqy]
    refine Nat.le_of_not_lt fun c => ?_
    have := a3 w0 hw1 (Or.inl hw2) (by omega); omega
  · refine Or.inl ⟨i, by simp [hpy, hp], covers_split hs hx hy hl hz hw hcov ?_ hpy,
      by simp [hqy, hq], entry_addNode hy hdy he, by simp [hpy, hqy, a1], by simp [hqy, a2], hmax⟩
    rintro ⟨h1, h2, h3⟩
    exact hc ⟨lev_inj hp h1, h2, h3⟩

theorem occ_split {p : Nat} (h : s.occ k p) :
    (s.addNode y j l).occ k p ∨ ((s.addNode y j l).linkE k p y ∧ (s.addNode y j l).occ k y) := by
  obtain ⟨h0, hcov, hk⟩ := h
  have hpy := ne_of_lev h0 hy
  by_cases hc : j = 0 ∧ s.low p < l ∧ l < k
  · obtain ⟨e, c1, c2⟩ := hc
    subst e
    obtain ⟨hl1, hl2⟩ := split_link hs hx hy hl hz hw hcov h0 c1 c2
    exact Or.inr ⟨hl1, by simp, hl2, hk⟩
  · refine Or.inl ⟨by simp [hpy, h0], covers_split hs hx hy hl hz hw hcov ?_ hpy, hk⟩
    rintro ⟨h1, h2, h3⟩
    exact hc ⟨(lev_inj h0 h1).symm, h2, h3⟩

theorem oblig_split : Obligations (St.snap s) (St.snap (s.addNode y j l)) := by
  refine ⟨snap_det hs, snap_stop, ?_, ?_⟩
  · intro k p q h
    rcases h with h | h
    · rcases linkE_split hs hx hy hl hz hw h with h' | ⟨h1, h2⟩
      · exact ⟨q, edge_path (Or.inl h'), Path.refl q⟩
      · exact ⟨q, Path.step (Or.inl h1) (edge_path (Or.inl h2)), Path.refl q⟩
    · rcases childE_split hs hx hy hl hz hw h with h' | ⟨h1, h2⟩
      · exact ⟨q, edge_path (Or.inr h'), Path.refl q⟩
      · exact ⟨q, Path.step (Or.inl h1) (edge_path (Or.inr h2)), Path.refl q⟩
  · intro k p h
    rcases occ_split hs hx hy hl hz hw h with h' | ⟨h1, h2⟩
    · exact ⟨p, Path.refl p, h'⟩
    · exact ⟨y, edge_path (Or.inl h1), h2⟩

end SplitObl

/-! ### Grow -/

theorem below_top (hs : WF s) (htop : ∀ b, s.lev b ≠ some (j + 1)) {p m : Nat}
    (hp : s.lev p = some m) : m ≤ j := by
  suffices H : ∀ d p, s.lev p = some (j + 1 + d) → False by
    refine Nat.le_of_not_lt fun c => H (m - (j + 1)) p ?_
    rw [hp]; congr 1; omega
  intro d
  induction d with
  | zero => intro p hp; exact htop p hp
  | succ d ih =>
    intro p hp
    obtain ⟨w, hw, _⟩ := hs.inner p (j + 1 + d) (by rw [hp]; rfl)
    exact ih w hw

theorem oblig_grow (hs : WF s) (htop : ∀ b, s.lev b ≠ some (j + 1)) (hr : s.lev r = none)
    (hz : s.lev z = some j) :
    Obligations (St.snap s) (St.snap ((s.addNode r (j + 1) 0).addPost z)) := by
  have hdr := (hs.dead r hr).2
  have hcov : ∀ p k, s.covers p k → ((s.addNode r (j + 1) 0).addPost z).covers p k := by
    rintro p k ⟨m, hp, a1, a2⟩
    have hpr := ne_of_lev hp hr
    have hm := below_top hs htop hp
    refine ⟨m, by simp [hpr, hp], by simp [hpr, a1], ?_⟩
    intro w hw hlt
    by_cases hwr : w = r
    · subst hwr; simp at hw; omega
    · simp only [addPost_lev, addPost_low, addNode_lev, addNode_low, if_neg hwr,
        if_neg hpr] at hw hlt ⊢
      exact a2 w hw hlt
  refine ⟨snap_det hs, snap_stop, ?_, ?_⟩
  · intro k p q h
    refine ⟨q, edge_path ?_, Path.refl q⟩
    rcases h with ⟨m, hp, hq, a1, a2, a3⟩ | ⟨i, hp, hc, hq, he, a1, a2, a3⟩
    · have hpr := ne_of_lev hp hr
      have hqr := ne_of_lev hq hr
      have hm := below_top hs htop hp
      refine Or.inl ⟨m, by simp [hpr, hp], by simp [hqr, hq], by simp [hpr, hqr, a1],
        by simp [hqr, a2], ?_⟩
      intro w hw hlt
      by_cases hwr : w = r
      · subst hwr; simp at hw; omega
      · simp only [addPost_lev, addPost_low, addNode_lev, addNode_low, if_neg hwr,
          if_neg hpr, if_neg hqr] at hw hlt ⊢
        exact a3 w hw hlt
    · have hpr := ne_of_lev hp hr
      have hqr := ne_of_lev hq hr
      have hm := below_top hs htop hp
      refine Or.inr ⟨i, by simp [hpr, hp], hcov p k hc, by simp [hqr, hq],
        entry_addPost (entry_addNode hr hdr he), by simp [hpr, hqr, a1], by simp [hqr, a2], ?_⟩
      intro w hw he' hlt
      by_cases hwr : w = r
      · subst hwr; simp at hw; omega
      · simp only [addPost_lev, addPost_low, addNode_lev, addNode_low, if_neg hwr,
          if_neg hqr] at hw hlt ⊢
        refine a3 w hw ?_ hlt
        rcases he' with (e | hpw) | ⟨h0, i', hw', r', hr'⟩
        · subst e; have := lev_inj hz hw; omega
        · exact Or.inl hpw
        · simp only [addPost_lev, addPost_low, addNode_lev, addNode_low, if_neg hwr] at h0 hw'
          have := lev_inj hw hw'; subst this
          by_cases hrr : r' = r
          · subst hrr; simp at hr'; omega
          · simp only [addPost_lev, addNode_lev, if_neg hrr] at hr'
            exact Or.inr ⟨h0, i, hw', r', hr'⟩
  · rintro k p ⟨h0, hc, hk⟩
    have hpr := ne_of_lev h0 hr
    exact ⟨p, Path.refl p, by simp [hpr, h0], hcov p k hc, hk⟩

theorem oblig_step (hs : WF s) {s' : St} (h : BStep s s') : Obligations (St.snap s) (St.snap s') := by
  cases h with
  | ins k _ => exact oblig_ins hs
  | split j l y h1 h2 h3 h4 h5 => exact oblig_split hs h1 h2 h3 h4 h5
  | post x j h1 _ _ _ => exact oblig_post hs h1
  | grow j r z h1 h2 h3 _ => exact oblig_grow hs h1 h2 h3

end Oblig

/-! ## Completing a sub-tree -/

section Complete

/-- `T` is a sub-tree of `G`: its nodes are nodes of `G` with the same level
and low key, and its posted nodes and keys are among those of `G`. -/
def Sub (T G : St) : Prop :=
  (∀ i j, T.lev i = some j → G.lev i = some j ∧ T.low i = G.low i) ∧
  (∀ i, T.posted i → G.posted i) ∧ (∀ k, T.keys k → G.keys k)

inductive Star (R : St → St → Prop) : St → St → Prop
  | refl (a : St) : Star R a a
  | tail {a b c : St} : Star R a b → R b c → Star R a c

theorem Star.trans {R : St → St → Prop} {a b c : St} (h1 : Star R a b) (h2 : Star R b c) :
    Star R a c := by
  induction h2 with
  | refl => exact h1
  | tail _ h ih => exact Star.tail ih h

theorem Star.wf {a b : St} (h : Star BStep a b) (ha : WF a) : WF b := by
  induction h with
  | refl => exact ha
  | tail _ h ih => exact ih.step h

variable {G : St} (hG : WF G)
include hG

theorem complete_keys {T : St} (hT : WF T) :
    ∀ n, ∃ T', Star BStep T T' ∧ T'.lev = T.lev ∧ T'.low = T.low ∧ T'.posted = T.posted ∧
      ∀ k, T'.keys k ↔ (T.keys k ∨ (G.keys k ∧ k < n)) := by
  intro n
  induction n with
  | zero => exact ⟨T, Star.refl T, rfl, rfl, rfl, fun k => by simp⟩
  | succ n ih =>
    obtain ⟨T', hs, h1, h2, h3, h4⟩ := ih
    by_cases hk : G.keys n
    · refine ⟨T'.addKey n, Star.tail hs (BStep.ins _ n (hG.keyp n hk)), h1, h2, h3, ?_⟩
      intro k
      simp only [addKey_keys, h4]
      constructor
      · rintro (e | h | h)
        · subst e; exact Or.inr ⟨hk, by omega⟩
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩
      · rintro (h | ⟨h, hl⟩)
        · exact Or.inr (Or.inl h)
        · by_cases e : k = n
          · exact Or.inl e
          · exact Or.inr (Or.inr ⟨h, by omega⟩)
    · refine ⟨T', hs, h1, h2, h3, ?_⟩
      intro k
      rw [h4]
      constructor
      · rintro (h | ⟨h, hl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h, by omega⟩
      · rintro (h | ⟨h, hl⟩)
        · exact Or.inl h
        · by_cases e : k = n
          · subst e; exact absurd h hk
          · exact Or.inr ⟨h, by omega⟩

/-- The stage invariant: levels below `j` are complete. -/
def Stage (G : St) (j : Nat) (T : St) : Prop :=
  WF T ∧ Sub T G ∧ (∀ k, T.keys k ↔ G.keys k) ∧
  (∀ x i, G.lev x = some i → i < j → T.lev x = some i) ∧
  (∀ x i, G.posted x → G.lev x = some i → i < j → T.posted x) ∧
  ((∃ x, G.lev x = some j) → ∃ x, T.lev x = some j)

theorem sub_lev {T : St} (h : Sub T G) {x i j : Nat} (hG' : G.lev x = some i)
    (hT : T.lev x = some j) : i = j := by
  have := (h.1 x j hT).1; rw [hG'] at this; exact Option.some.inj this

/-- Adding the missing nodes of level `j`. -/
theorem complete_nodes (j : Nat) {T : St} (hT : Stage G j T) :
    ∀ n, ∃ U, Star BStep T U ∧ Stage G j U ∧ ∀ x, x < n → G.lev x = some j → U.lev x = some j := by
  intro n
  induction n with
  | zero => exact ⟨T, Star.refl T, hT, fun x hx => absurd hx (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨U, hs, ⟨hW, hS, hK, hL, hP, hE⟩, hN⟩ := ih
    by_cases hc : G.lev n = some j ∧ U.lev n ≠ some j
    · obtain ⟨hn, hu⟩ := hc
      have hun : U.lev n = none := by
        cases e : U.lev n with
        | none => rfl
        | some m => exact absurd (by rw [e, ← sub_lev hG hS hn e]) hu
      obtain ⟨x0, hx0⟩ := hE ⟨n, hn⟩
      have hl : 0 < G.low n := by
        refine Nat.pos_of_ne_zero fun e => ?_
        obtain ⟨y0, hy1, hy2⟩ := hW.left x0 j hx0
        have h1 := hS.1 y0 j hy1
        have := hG.uniq y0 n j h1.1 hn (by rw [← h1.2, hy2, e])
        subst this; rw [hy1] at hun; cases hun
      have hz : ∀ z, U.lev z = some j → U.low z ≠ G.low n := by
        intro z hz e
        have h1 := hS.1 z j hz
        have := hG.uniq z n j h1.1 hn (by rw [← h1.2, e])
        subst this; rw [hz] at hun; cases hun
      have hw : ∀ i, j = i + 1 → ∃ w, U.lev w = some i ∧ U.posted w ∧ U.low w = G.low n := by
        intro i e
        subst e
        obtain ⟨w, hw1, hw2, hw3⟩ := hG.inner n i hn
        have hpw : G.posted w := by
          rcases hw2 with h | ⟨h0, _⟩
          · exact h
          · omega
        have hu := hL w i hw1 (by omega)
        exact ⟨w, hu, hP w i hpw hw1 (by omega), by rw [(hS.1 w i hu).2, hw3]⟩
      have hstep := BStep.split U j (G.low n) n ⟨x0, hx0⟩ hun hl hz hw
      refine ⟨_, Star.tail hs hstep, ⟨hW.step hstep, ?_, hK, ?_, hP, ?_⟩, ?_⟩
      · refine ⟨?_, hS.2.1, hS.2.2⟩
        intro i m hi
        by_cases e : i = n
        · subst e; simp at hi; subst hi; simp [hn]
        · simp only [addNode_lev, addNode_low, if_neg e] at hi ⊢; exact hS.1 i m hi
      · intro x i hx hi
        have : x ≠ n := by intro e; subst e; rw [hn] at hx; cases hx; omega
        simp [this]; exact hL x i hx hi
      · intro _; exact ⟨n, by simp⟩
      · intro x hx hxj
        by_cases e : x = n
        · subst e; simp
        · simp [e]; exact hN x (by omega) hxj
    · refine ⟨U, hs, ⟨hW, hS, hK, hL, hP, hE⟩, ?_⟩
      intro x hx hxj
      by_cases e : x = n
      · subst e
        exact Classical.byContradiction fun h => hc ⟨hxj, h⟩
      · exact hN x (by omega) hxj

/-- Stage `j` with level `j` complete and the level above grown if needed. -/
def Stage2 (G : St) (j : Nat) (T : St) : Prop :=
  WF T ∧ Sub T G ∧ (∀ k, T.keys k ↔ G.keys k) ∧
  (∀ x i, G.lev x = some i → i < j + 1 → T.lev x = some i) ∧
  (∀ x i, G.posted x → G.lev x = some i → i < j → T.posted x) ∧
  ((∃ x, G.lev x = some (j + 1)) → ∃ x, T.lev x = some (j + 1))

theorem complete_grow (j : Nat) {N : Nat} (hN : ∀ i, N ≤ i → G.lev i = none) {T : St}
    (hT : Stage G j T) : ∃ U, Star BStep T U ∧ Stage2 G j U := by
  obtain ⟨U, hs, ⟨hW, hS, hK, hL, hP, hE⟩, hA⟩ := complete_nodes hG j hT N
  have hL' : ∀ x i, G.lev x = some i → i < j + 1 → U.lev x = some i := by
    intro x i hx hi
    by_cases e : i = j
    · subst e
      refine hA x ?_ hx
      exact Nat.lt_of_not_le fun c => by rw [hN x c] at hx; cases hx
    · exact hL x i hx (by omega)
  by_cases hc : (∃ x, G.lev x = some (j + 1)) ∧ ¬ ∃ x, U.lev x = some (j + 1)
  · obtain ⟨⟨x1, hx1⟩, hnone⟩ := hc
    obtain ⟨r0, hr1, hr2⟩ := hG.left x1 _ hx1
    obtain ⟨z, hz1, hz2⟩ := hG.grown x1 j hx1
    obtain ⟨jz, hz3, hz4, _⟩ := hG.post z hz2
    have := lev_inj hz1 hz3; subst this
    have htop : ∀ b, U.lev b ≠ some (j + 1) := fun b h => hnone ⟨b, h⟩
    have hr0 : U.lev r0 = none := by
      cases e : U.lev r0 with
      | none => rfl
      | some m =>
        have := sub_lev hG hS hr1 e; subst this; exact absurd ⟨r0, e⟩ hnone
    have hzU := hL' z j hz1 (by omega)
    have hlz : 0 < U.low z := by rw [(hS.1 z j hzU).2]; exact hz4
    have hstep := BStep.grow U j r0 z htop hr0 hzU hlz
    refine ⟨_, Star.tail hs hstep, hW.step hstep, ?_, hK, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, hS.2.2⟩
      · intro i m hi
        by_cases e : i = r0
        · subst e; simp at hi; subst hi; simp [hr1, hr2]
        · simp only [addPost_lev, addPost_low, addNode_lev, addNode_low, if_neg e] at hi ⊢
          exact hS.1 i m hi
      · rintro i (e | h)
        · subst e; exact hz2
        · exact hS.2.1 i h
    · intro x i hx hi
      have : x ≠ r0 := by intro e; subst e; rw [hr1] at hx; cases hx; omega
      simp [this]; exact hL' x i hx hi
    · intro x i hx1 hx2 hi; exact Or.inr (hP x i hx1 hx2 hi)
    · intro _; exact ⟨r0, by simp⟩
  · refine ⟨U, hs, hW, hS, hK, hL', hP, ?_⟩
    intro h
    exact Classical.byContradiction fun h' => hc ⟨h, h'⟩

theorem complete_posts (j : Nat) {T : St} (hT : Stage2 G j T) :
    ∀ n, ∃ U, Star BStep T U ∧ Stage2 G j U ∧
      ∀ x, x < n → G.posted x → G.lev x = some j → U.posted x := by
  intro n
  induction n with
  | zero => exact ⟨T, Star.refl T, hT, fun x hx => absurd hx (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨U, hs, ⟨hW, hS, hK, hL, hP, hE⟩, hN⟩ := ih
    by_cases hc : G.posted n ∧ G.lev n = some j ∧ ¬ U.posted n
    · obtain ⟨h1, h2, h3⟩ := hc
      obtain ⟨jn, hn1, hn2, r, hr⟩ := hG.post n h1
      have := lev_inj h2 hn1; subst this
      have hu := hL n j h2 (by omega)
      have hl : 0 < U.low n := by rw [(hS.1 n j hu).2]; exact hn2
      have hstep := BStep.post U n j hu hl h3 (hE ⟨r, hr⟩)
      refine ⟨_, Star.tail hs hstep, ⟨hW.step hstep, ⟨hS.1, ?_, hS.2.2⟩, hK, hL, ?_, hE⟩, ?_⟩
      · rintro i (e | h)
        · subst e; exact h1
        · exact hS.2.1 i h
      · intro x i a b c; exact Or.inr (hP x i a b c)
      · intro x hx a b
        by_cases e : x = n
        · exact Or.inl e
        · exact Or.inr (hN x (by omega) a b)
    · refine ⟨U, hs, ⟨hW, hS, hK, hL, hP, hE⟩, ?_⟩
      intro x hx a b
      by_cases e : x = n
      · subst e; exact Classical.byContradiction fun h => hc ⟨a, b, h⟩
      · exact hN x (by omega) a b

theorem complete_stage (j : Nat) {N : Nat} (hN : ∀ i, N ≤ i → G.lev i = none) {T : St}
    (hT : Stage G j T) : ∃ U, Star BStep T U ∧ Stage G (j + 1) U := by
  obtain ⟨U, hs, hU⟩ := complete_grow hG j hN hT
  obtain ⟨V, hs', ⟨hW, hS, hK, hL, hP, hE⟩, hA⟩ := complete_posts hG j hU N
  refine ⟨V, hs.trans hs', hW, hS, hK, hL, ?_, hE⟩
  intro x i hx1 hx2 hi
  by_cases e : i = j
  · subst e
    refine hA x ?_ hx1 hx2
    exact Nat.lt_of_not_le fun c => by rw [hN x c] at hx2; cases hx2
  · exact hP x i hx1 hx2 (by omega)

/-- **Every sub-tree of a reachable tree can be completed to it.** -/
theorem complete {T : St} (hT : WF T) (hTG : Sub T G) : Star BStep T G := by
  obtain ⟨N, hN1, hN2, hN3⟩ := hG.bnd
  obtain ⟨T1, hs1, e1, e2, e3, e4⟩ := complete_keys hG hT N
  have hW1 := hs1.wf hT
  have h0 : Stage G 0 T1 := by
    refine ⟨hW1, ⟨?_, ?_, ?_⟩, ?_, fun _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ => ⟨0, hW1.root.1⟩⟩
    · intro i j h; rw [e1] at h; rw [e2]; exact hTG.1 i j h
    · intro i h; rw [e3] at h; exact hTG.2.1 i h
    · intro k h; rcases (e4 k).1 h with h | h
      · exact hTG.2.2 k h
      · exact h.1
    · intro k; rw [e4]
      exact ⟨fun h => h.elim (hTG.2.2 k) (fun h => h.1), fun h => Or.inr ⟨h, hN2 k h⟩⟩
  have hall : ∀ j, ∃ U, Star BStep T1 U ∧ Stage G j U := by
    intro j
    induction j with
    | zero => exact ⟨T1, Star.refl _, h0⟩
    | succ j ih =>
      obtain ⟨U, hs, hU⟩ := ih
      obtain ⟨V, hs', hV⟩ := complete_stage hG j hN1 hU
      exact ⟨V, hs.trans hs', hV⟩
  obtain ⟨U, hs, hW, hS, hK, hL, hP, _⟩ := hall N
  have : U = G := by
    apply St.ext'
    · funext i
      cases e : G.lev i with
      | none =>
        cases e' : U.lev i with
        | none => rfl
        | some m => have := (hS.1 i m e').1; rw [e] at this; cases this
      | some m => exact hL i m e (hN3 i m e)
    · funext i
      cases e' : U.lev i with
      | some m => exact (hS.1 i m e').2
      | none =>
        rw [(hW.dead i e').1]
        cases e : G.lev i with
        | none => exact ((hG.dead i e).1).symm
        | some m => have := hL i m e (hN3 i m e); rw [e'] at this; cases this
    · funext k; exact propext (hK k)
    · funext i
      apply propext
      constructor
      · exact hS.2.1 i
      · intro h
        obtain ⟨m, hm, _⟩ := hG.post i h
        exact hP i m h hm (hN3 i m hm)
  rw [← this]
  exact hs1.trans hs

end Complete

/-! ## A sub-tree where a valid claim is exact -/

section Cut
variable (G : St) (k ℓ p : Nat)

/-- Nodes removed by `cut`: all levels above `ℓ`; on level `ℓ` the nodes with
low key in `(p, k)`; below `ℓ` the nodes with low key below `k` that come after
every entry below `k`. -/
def remv (i j : Nat) : Prop :=
  ℓ < j ∨ (j = ℓ ∧ p < G.low i ∧ G.low i < k) ∨
  (j < ℓ ∧ G.low i < k ∧ ∀ e, G.lev e = some j → G.entry e → G.low e < k → G.low e < G.low i)

def keepAt (i j : Nat) : Prop := G.lev i = some j ∧ ¬ remv G k ℓ p i j

/-- The sub-tree in which the claim `(k, π)` (with `π` on level `ℓ` and low key
`p`) is exact. -/
noncomputable def cut : St where
  lev i := if ∃ j, keepAt G k ℓ p i j then G.lev i else none
  low i := if ∃ j, keepAt G k ℓ p i j then G.low i else 0
  keys := G.keys
  posted i := G.posted i ∧ ∃ j, keepAt G k ℓ p i j ∧ j < ℓ

variable {G k ℓ p}

theorem cut_lev {i j : Nat} : (cut G k ℓ p).lev i = some j ↔ keepAt G k ℓ p i j := by
  by_cases h : ∃ j, keepAt G k ℓ p i j
  · obtain ⟨j', hj'⟩ := h
    simp only [cut, show ∃ j, keepAt G k ℓ p i j from ⟨j', hj'⟩, if_true]
    constructor
    · intro e; exact ⟨e, by have := lev_inj hj'.1 e; subst this; exact hj'.2⟩
    · intro e; exact e.1
  · simp only [cut, h, if_false]
    constructor
    · intro e; cases e
    · intro e; exact absurd ⟨j, e⟩ h

theorem cut_low {i j : Nat} (h : keepAt G k ℓ p i j) : (cut G k ℓ p).low i = G.low i := by
  simp only [cut, show ∃ j, keepAt G k ℓ p i j from ⟨j, h⟩, if_true]

theorem cut_level_le {i j : Nat} (h : keepAt G k ℓ p i j) : j ≤ ℓ :=
  Nat.le_of_not_lt fun c => h.2 (Or.inl c)

variable (hG : WF G) {π : Nat} (hπ : G.lev π = some ℓ) (hp : G.low π = p) (hk : p < k)
include hG hπ hp hk

theorem levels_below : ∀ i, i ≤ ℓ → ∃ x, G.lev x = some i := by
  suffices H : ∀ d, d ≤ ℓ → ∃ x, G.lev x = some (ℓ - d) by
    intro i hi
    obtain ⟨x, hx⟩ := H (ℓ - i) (by omega)
    exact ⟨x, by rw [hx]; congr 1; omega⟩
  intro d
  induction d with
  | zero => intro _; exact ⟨π, by simpa using hπ⟩
  | succ d ih =>
    intro hd
    obtain ⟨x, hx⟩ := ih (by omega)
    obtain ⟨w, hw, _⟩ := hG.inner x (ℓ - (d + 1)) (by rw [hx]; congr 1; omega)
    exact ⟨w, hw⟩

theorem keep_entry {e i : Nat} (he : G.lev e = some i) (hi : i < ℓ) (hen : G.entry e) :
    keepAt G k ℓ p e i := by
  refine ⟨he, ?_⟩
  rintro (c | ⟨c, _⟩ | ⟨_, c1, c2⟩)
  · omega
  · omega
  · have := c2 e he hen c1; omega

theorem keep_left {y i : Nat} (hy : G.lev y = some i) (hi : i ≤ ℓ) (h0 : G.low y = 0) :
    keepAt G k ℓ p y i := by
  refine ⟨hy, ?_⟩
  rintro (c | ⟨_, c, _⟩ | ⟨_, c1, c2⟩)
  · omega
  · omega
  · have := c2 y hy (Or.inr ⟨h0, i, hy, ?_⟩) c1
    · omega
    · obtain ⟨x, hx⟩ := levels_below hG hπ hp hk (i + 1) (by omega)
      exact ⟨x, hx⟩

theorem cut_has_level {i : Nat} (hi : i ≤ ℓ) : ∃ y, keepAt G k ℓ p y i ∧ G.low y = 0 := by
  obtain ⟨x, hx⟩ := levels_below hG hπ hp hk i hi
  obtain ⟨y, hy1, hy2⟩ := hG.left x i hx
  exact ⟨y, keep_left hG hπ hp hk hy1 hi hy2, hy2⟩

theorem cut_entry {e i : Nat} (he : G.lev e = some i) (hi : i < ℓ) (hen : G.entry e) :
    (cut G k ℓ p).entry e := by
  have hke := keep_entry hG hπ hp hk he hi hen
  rcases hen with hpe | ⟨h0, j, hj, r, hr⟩
  · exact Or.inl ⟨hpe, i, hke, hi⟩
  · have := lev_inj he hj; subst this
    obtain ⟨y, hy, _⟩ := cut_has_level hG hπ hp hk (i := i + 1) (by omega)
    exact Or.inr ⟨by rw [cut_low hke, h0], i, cut_lev.2 hke, y, cut_lev.2 hy⟩

theorem cut_entry_rev {e : Nat} (h : (cut G k ℓ p).entry e) : G.entry e := by
  rcases h with ⟨hpe, _⟩ | ⟨h0, j, hj, r, hr⟩
  · exact Or.inl hpe
  · have k1 := cut_lev.1 hj
    have k2 := cut_lev.1 hr
    exact Or.inr ⟨by rw [← cut_low k1]; exact h0, j, k1.1, r, k2.1⟩

theorem cut_wf : WF (cut G k ℓ p) := by
  obtain ⟨N, hN1, hN2, hN3⟩ := hG.bnd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hG.keyp, ?_⟩
  · have h0 := keep_left hG hπ hp hk hG.root.1 (Nat.zero_le ℓ) hG.root.2
    exact ⟨cut_lev.2 h0, by rw [cut_low h0]; exact hG.root.2⟩
  · intro a b j ha hb e
    have ka := cut_lev.1 ha
    have kb := cut_lev.1 hb
    rw [cut_low ka, cut_low kb] at e
    exact hG.uniq a b j ka.1 kb.1 e
  · intro a ha
    have hn : ¬ ∃ j, keepAt G k ℓ p a j := fun ⟨j, hj⟩ => by rw [cut_lev.2 hj] at ha; cases ha
    refine ⟨by simp only [cut, hn, if_false], ?_⟩
    rintro ⟨_, j, hj, _⟩; exact hn ⟨j, hj⟩
  · intro y j hy
    have ky := cut_lev.1 hy
    have hj := cut_level_le ky
    obtain ⟨w, hw1, hw2, hw3⟩ := hG.inner y j ky.1
    have kw := keep_entry hG hπ hp hk hw1 (by omega) hw2
    exact ⟨w, cut_lev.2 kw, cut_entry hG hπ hp hk hw1 (by omega) hw2,
      by rw [cut_low kw, cut_low ky, hw3]⟩
  · rintro x ⟨hpx, j, kx, hj⟩
    obtain ⟨j', hx, hl, _⟩ := hG.post x hpx
    have := lev_inj kx.1 hx; subst this
    obtain ⟨y, hy, _⟩ := cut_has_level hG hπ hp hk (i := j + 1) (by omega)
    exact ⟨j, cut_lev.2 kx, by rw [cut_low kx]; exact hl, y, cut_lev.2 hy⟩
  · intro r j hr
    have kr := cut_lev.1 hr
    have hj := cut_level_le kr
    obtain ⟨z, hz1, hz2⟩ := hG.grown r j kr.1
    have kz := keep_entry hG hπ hp hk hz1 (by omega) (Or.inl hz2)
    exact ⟨z, cut_lev.2 kz, hz2, j, kz, by omega⟩
  · intro x j hx
    obtain ⟨y, hy, hy0⟩ := cut_has_level hG hπ hp hk (cut_level_le (cut_lev.1 hx))
    exact ⟨y, cut_lev.2 hy, by rw [cut_low hy]; exact hy0⟩
  · refine ⟨N, ?_, hN2, ?_⟩
    · intro i hi
      cases e : (cut G k ℓ p).lev i with
      | none => rfl
      | some j => have := (cut_lev.1 e).1; rw [hN1 i hi] at this; cases this
    · intro i j hi; exact hN3 i j (cut_lev.1 hi).1

theorem cut_sub : Sub (cut G k ℓ p) G := by
  refine ⟨fun i j h => ⟨(cut_lev.1 h).1, cut_low (cut_lev.1 h)⟩, fun i h => h.1, fun _ h => h⟩

theorem cut_exact (hkey : G.keys k) : (cut G k ℓ p).exact k π := by
  have hW := cut_wf hG hπ hp hk
  -- descent through the levels below `ℓ`
  have desc : ∀ i x, (cut G k ℓ p).lev x = some i → i ≤ ℓ → (cut G k ℓ p).covers x k →
      (cut G k ℓ p).exact k x := by
    intro i
    induction i with
    | zero => intro x hx _ hc; exact ⟨x, CPath.refl x, hx, hc, hkey⟩
    | succ i ih =>
      intro x hx hi hc
      obtain ⟨w0, hw01, hw02, hw03⟩ := hW.inner x i hx
      obtain ⟨_, hx', hxk, _⟩ := id hc
      obtain ⟨w, ⟨hw1, hw2⟩, hw3, hw4⟩ := exists_max_below (cut G k ℓ p).low
        (fun w => (cut G k ℓ p).lev w = some i ∧ (cut G k ℓ p).entry w) k
        ⟨w0, ⟨hw01, hw02⟩, by omega⟩
      have hlo : (cut G k ℓ p).low x ≤ (cut G k ℓ p).low w := by
        have := hw4 w0 ⟨hw01, hw02⟩ (by omega); omega
      have hce : (cut G k ℓ p).childE k x w := by
        refine ⟨i, hx, hc, hw1, hw2, hlo, hw3, ?_⟩
        intro w' h1 h2 h3
        exact Nat.le_of_not_lt fun c => by have := hw4 w' ⟨h1, h2⟩ c; omega
      have kw := cut_lev.1 hw1
      have hcw : (cut G k ℓ p).covers w k := by
        refine ⟨i, hw1, hw3, ?_⟩
        intro v hv hlt
        refine Nat.le_of_not_lt fun c => ?_
        have kv := cut_lev.1 hv
        apply kv.2
        refine Or.inr (Or.inr ⟨by omega, by rw [← cut_low kv]; exact c, ?_⟩)
        intro e he hen hek
        have ke := keep_entry hG hπ hp hk he (by omega) hen
        have := hw4 e ⟨cut_lev.2 ke, cut_entry hG hπ hp hk he (by omega) hen⟩
          (by rw [cut_low ke]; exact hek)
        rw [cut_low ke] at this
        rw [← cut_low kv]
        omega
      obtain ⟨q, hq, hocc⟩ := ih w hw1 (by omega) hcw
      exact ⟨q, CPath.step hce hq, hocc⟩
  have kπ : keepAt G k ℓ p π ℓ := by
    refine ⟨hπ, ?_⟩
    rintro (c | ⟨_, c, _⟩ | ⟨c, _⟩) <;> omega
  refine desc ℓ π (cut_lev.2 kπ) (Nat.le_refl ℓ) ⟨ℓ, cut_lev.2 kπ, by rw [cut_low kπ]; omega, ?_⟩
  intro v hv hlt
  have kv := cut_lev.1 hv
  rw [cut_low kπ] at hlt
  rw [cut_low kv] at hlt ⊢
  exact Nat.le_of_not_lt fun c => kv.2 (Or.inr (Or.inl ⟨rfl, by omega, c⟩))

end Cut

/-! ## The B-link restructuring algorithm and hypothesis (H) -/

section Main

/-- Lehman–Yao restructuring: states are B-link trees reachable from the
empty leaf, steps are `BStep`, and the snapshot gives link and child edges. -/
def blink : SRestr St Nat Nat where
  init := St.init
  step s s' := WF s ∧ BStep s s'
  snap := St.snap
  oblig _ _ h := oblig_step h.1 h.2

/-- Exact claims of the current tree. -/
def exactX (h : blink.Hist) (c : Nat × Nat) : Prop := (blink.cur h).exact c.1 c.2

theorem cpath_path {s : St} {k p q : Nat} (h : CPath s k p q) : Path (St.snap s) k p q := by
  induction h with
  | refl p => exact Path.refl p
  | step he _ ih => exact Path.step (Or.inr he) ih

theorem exactX_valid : ∀ h c, exactX h c → blink.fwdV h c := by
  rintro h ⟨k, p⟩ ⟨q, hq, hocc⟩
  exact ⟨q, cpath_path hq, hocc⟩

theorem schain_wf {s : St} {l : List St} (h : SChain blink.step s l) (hs : WF s) :
    WF (lastS s l) := by
  induction h with
  | nil => exact hs
  | cons hst _ ih => exact ih (hst.1.step hst.2)

theorem cur_wf (h : blink.Hist) : WF (blink.cur h) := schain_wf h.2 WF.init

theorem star_chain {a b : St} (h : Star BStep a b) (ha : WF a) :
    ∃ l, SChain blink.step a l ∧ lastS a l = b := by
  induction h with
  | refl => exact ⟨[], SChain.nil _, rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨l, hl, e⟩ := ih
    have hb : WF b := by rw [← e]; exact schain_wf hl ha
    refine ⟨l ++ [c], schain_concat l [c] hl (by rw [e]; exact SChain.cons ⟨hb, hbc⟩ (SChain.nil c)),
      by rw [lastS_append, e]; rfl⟩

/-- A valid claim `(k, π)` has `π` a node with low key below `k`, and `k` is
an inserted key. -/
theorem valid_facts {s : St} {k π : Nat} (h : claims (St.snap s) k π) :
    ∃ ℓ, s.lev π = some ℓ ∧ s.low π < k ∧ s.keys k := by
  obtain ⟨o, hpo, hocc⟩ := h
  have hkey := hocc.2.2
  cases hpo with
  | refl => obtain ⟨_, _, hl, _⟩ := hocc.2.1; exact ⟨0, hocc.1, hl, hkey⟩
  | step he _ =>
    rcases he with ⟨j, hj, _, h1, h2, _⟩ | ⟨j, hj, ⟨_, _, hl, _⟩, _⟩
    · exact ⟨j, hj, by omega, hkey⟩
    · exact ⟨j + 1, hj, hl, hkey⟩

/-- **Hypothesis (H) holds for B-link trees**: every claim valid at the
current tree of a history was exact at an earlier point of some history that
reaches the same tree. -/
theorem blink_H : ∀ h c, blink.fwdV h c → stateRemembered blink.cur exactX h c := by
  rintro h ⟨k, π⟩ hc
  have hG := cur_wf h
  obtain ⟨ℓ, hπ, hlt, hkey⟩ := valid_facts hc
  let G := blink.cur h
  have hW := cut_wf hG hπ rfl hlt
  have hS := cut_sub hG hπ rfl hlt
  have hex := cut_exact hG hπ rfl hlt hkey
  have hiW : Sub St.init (cut G k ℓ (G.low π)) := by
    refine ⟨?_, fun _ h => h.elim, fun _ h => h.elim⟩
    intro i j hi
    simp only [St.init] at hi
    by_cases e : i = 0
    · subst e
      simp at hi; subst hi
      exact ⟨hW.root.1, hW.root.2.symm⟩
    · simp [e] at hi
  obtain ⟨l1, hl1, e1⟩ := star_chain (complete hW WF.init hiW) WF.init
  obtain ⟨l2, hl2, e2⟩ := star_chain (complete hG hW hS) hW
  have hl2' : SChain blink.step (lastS St.init l1) l2 := by rw [e1]; exact hl2
  refine ⟨⟨l1, hl1⟩, ⟨l1 ++ l2, schain_concat l1 l2 hl1 hl2'⟩, ⟨l2, rfl⟩, ?_, ?_⟩
  · show lastS St.init (l1 ++ l2) = lastS St.init h.1
    rw [lastS_append, e1, e2]; rfl
  · show (lastS St.init l1).exact k π
    rw [e1]; exact hex

/-- **Forward reachability equals the remembered exact claims** for B-link
trees (Prop. `prop:remembered-claims`(4) with (H)). -/
theorem blink_fwd_eq : ∀ h c, blink.fwdV h c ↔ stateRemembered blink.cur exactX h c :=
  (blink.fwd_eq_iff exactX exactX_valid).2 blink_H

end Main

/-! ## Posting breaks the strong form of obligation 2 -/

section Strong

/-- Search paths never go left on a level or up a level. -/
theorem path_mono {s : St} {k p q : Nat} (h : Path (St.snap s) k p q) :
    ∀ a, s.lev p = some a → ∃ b, s.lev q = some b ∧ (b < a ∨ (b = a ∧ s.low p ≤ s.low q)) := by
  induction h with
  | refl p => intro a ha; exact ⟨a, ha, Or.inr ⟨rfl, Nat.le_refl _⟩⟩
  | step he _ ih =>
    intro a ha
    rcases he with ⟨j, hj, hz, h1, _, _⟩ | ⟨j, hj, _, hw, _⟩
    · have := lev_inj ha hj; subst this
      obtain ⟨b, hb, c⟩ := ih a hz
      exact ⟨b, hb, by omega⟩
    · have := lev_inj ha hj; subst this
      obtain ⟨b, hb, c⟩ := ih j hw
      exact ⟨b, hb, by omega⟩

/-- The tree with leaves `0` (low `-∞`), `3` (low 3, unposted) and `1`
(low 5), under the root `2` holding pointers to `0` and `1`. -/
def s3 : St := ((((St.init.addNode 1 0 5).addNode 2 1 0).addPost 1).addNode 3 0 3)

theorem s3_lev (w j : Nat) :
    s3.lev w = some j ↔ (w = 0 ∧ j = 0) ∨ (w = 1 ∧ j = 0) ∨ (w = 2 ∧ j = 1) ∨ (w = 3 ∧ j = 0) := by
  simp only [s3, St.init, addNode_lev, addPost_lev]
  by_cases h3 : w = 3 <;> by_cases h2 : w = 2 <;> by_cases h1 : w = 1 <;> by_cases h0 : w = 0 <;>
    simp [h0, h1, h2, h3] <;> omega

theorem s3_low (w : Nat) : s3.low w = if w = 3 then 3 else if w = 1 then 5 else 0 := by
  simp only [s3, St.init, addNode_low, addPost_low]
  by_cases h3 : w = 3 <;> by_cases h2 : w = 2 <;> by_cases h1 : w = 1 <;> simp [h1, h2, h3] <;> omega

theorem s3_reach : Star BStep St.init s3 := by
  have a1 : BStep St.init (St.init.addNode 1 0 5) := by
    refine BStep.split _ 0 5 1 ⟨0, rfl⟩ rfl (by omega) ?_ (fun i h => by omega)
    intro z hz; simp only [St.init] at hz ⊢; omega
  have a2 : BStep (St.init.addNode 1 0 5) (((St.init.addNode 1 0 5).addNode 2 1 0).addPost 1) := by
    refine BStep.grow _ 0 2 1 ?_ rfl rfl (by simp)
    intro b hb
    simp only [St.init, addNode_lev] at hb
    by_cases h1 : b = 1 <;> by_cases h0 : b = 0 <;> simp [h0, h1] at hb
  have a3 : BStep (((St.init.addNode 1 0 5).addNode 2 1 0).addPost 1) s3 := by
    refine BStep.split _ 0 3 3 ⟨0, rfl⟩ rfl (by omega) ?_ (fun i h => by omega)
    intro z hz
    simp only [St.init, addNode_lev, addPost_lev, addNode_low, addPost_low] at hz ⊢
    by_cases h2 : z = 2 <;> by_cases h1 : z = 1 <;> simp [h1, h2] at hz ⊢
  exact Star.tail (Star.tail (Star.tail (Star.refl _) a1) a2) a3

theorem s3_wf : WF s3 := s3_reach.wf WF.init

/-- **Posting a separator violates the strong form of obligation 2.**  In the
reachable tree `s3`, the search edge for key 4 at the root `2` leads to leaf
`0`; after posting leaf `3`, the search for 4 from the root no longer reaches
`0`. -/
theorem post_breaks_strong :
    Star BStep St.init s3 ∧ BStep s3 (s3.addPost 3) ∧ (St.snap s3).edge 4 2 0 ∧
      ¬ Path (St.snap (s3.addPost 3)) 4 2 0 := by
  have hpost : BStep s3 (s3.addPost 3) := by
    refine BStep.post s3 3 0 ((s3_lev 3 0).2 (by omega)) (by rw [s3_low]; simp) ?_
      ⟨2, (s3_lev 2 1).2 (by omega)⟩
    simp [s3, St.init]
  have hW4 : WF (s3.addPost 3) := s3_wf.step hpost
  have l2 : s3.lev 2 = some 1 := (s3_lev 2 1).2 (by omega)
  have cov : s3.covers 2 4 := by
    refine ⟨1, l2, by rw [s3_low]; simp, ?_⟩
    intro w hw hlt
    rcases (s3_lev w 1).1 hw with ⟨_, h⟩ | ⟨_, h⟩ | ⟨e, _⟩ | ⟨_, h⟩ <;> try omega
    subst e; omega
  refine ⟨s3_reach, hpost, Or.inr ⟨0, l2, cov, (s3_lev 0 0).2 (by omega), ?_, by simp [s3_low],
    by simp [s3_low], ?_⟩, ?_⟩
  · exact Or.inr ⟨by simp [s3_low], 0, (s3_lev 0 0).2 (by omega), 2, l2⟩
  · intro w hw he hlt
    rcases (s3_lev w 0).1 hw with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, h⟩ | ⟨e, _⟩
    · subst e; simp [s3_low] at hlt
    · subst e; simp [s3_low]
    · omega
    · subst e
      rcases he with hp | ⟨h0, _⟩
      · simp [s3, St.init] at hp
      · simp [s3_low] at h0
  · intro hpath
    have hce : (s3.addPost 3).childE 4 2 3 := by
      refine ⟨0, l2, ⟨1, l2, by simp [s3_low], ?_⟩, (s3_lev 3 0).2 (by omega), Or.inl (Or.inl rfl),
        by simp [s3_low], by simp [s3_low], ?_⟩
      · intro w hw hlt
        rcases (s3_lev w 1).1 hw with ⟨_, h⟩ | ⟨_, h⟩ | ⟨e, _⟩ | ⟨_, h⟩ <;> try omega
        subst e; simp at hlt
      · intro w hw he hlt
        rcases (s3_lev w 0).1 hw with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, h⟩ | ⟨e, _⟩
        · subst e; simp [s3_low] at hlt
        · subst e; simp [s3_low]
        · omega
        · subst e; simp at hlt
    cases hpath with
    | step he rest =>
      have := snap_det hW4 4 2 _ 3 he (Or.inr hce)
      subst this
      obtain ⟨b, hb, c⟩ := path_mono rest 0 ((s3_lev 3 0).2 (by omega))
      simp [s3_low] at c

end Strong

end BLink
end CC
