/-!
# Read Committed is not closed under history union without Lamport timestamps

Bailis's dissertation (UCB/EECS-2015-206, §4.2.1) treats HAT as invariant
confluence over read-write histories.  A history is a set of committed
transactions, each with a unique timestamp, the items it writes, and the
versions its reads returned; histories merge by set union; versions are
ordered by timestamp.  The dissertation argues that Read Committed is
invariant confluent: "Adya's G1c is prevented by the fact that G0 graphs are
acyclic for writes … and transactions can only read-depend on other
transactions that appear in their histories; thus, unioning two histories
that do not exhibit G1c cannot introduce new edges to incur G1c."

The union step fails.  In the counterexample the union introduces no new
edge: its dependency graph is the union of the two histories' graphs, each
acyclic.  But the union of two acyclic graphs can have a cycle.  Write-
dependencies follow timestamp order, while read-dependencies can run against
it (a transaction may read a version with a larger timestamp than its own),
and edges from the two histories close a G1c cycle (`counterexample`).  The step does hold when every read
returns a version with a timestamp below the reader's (`lamport_union`);
HAT's patched clients guarantee this (`Instances/HATRC.lean`).

Model (`Tx`): timestamp `ts` (`0` is `T_init`), written items, and reads as
pairs `(item, version timestamp)`.  On a history `h` (a list read as a set):

* `installs h k t`: `t = 0`, or a transaction of `h` with timestamp `t`
  writes `k`;
* `next h k a b`: `x_b` is the next version of `k` after `x_a` in timestamp
  order among the installers in `h`;
* `ww h a b`: `next h k a b` for some item written in `h`;
* `wr h a b`: a transaction of `h` with timestamp `b` read the version with
  timestamp `a` (`a ≠ b`);
* G0: a `ww` cycle; G1c: a cycle of `ww`/`wr` edges; G1a: a read whose
  version no transaction of `h` installs (the reader saw a transaction
  outside the committed history).  G1b cannot occur: each transaction has
  one version per item.
-/

namespace CC
namespace HATUnion

structure Tx where
  ts : Nat
  writes : List Nat
  reads : List (Nat × Nat)
  deriving DecidableEq

section
variable (h : List Tx)

def installs (k t : Nat) : Bool := t == 0 || h.any (fun x => x.ts == t && x.writes.contains k)

def next (k a b : Nat) : Bool :=
  installs h k a && installs h k b && decide (a < b) &&
    !(h.any fun x => x.writes.contains k && decide (a < x.ts) && decide (x.ts < b))

def keys : List Nat := h.flatMap (·.writes)

def ww (a b : Nat) : Bool := (keys h).any fun k => next h k a b

def wr (a b : Nat) : Bool := a != b && h.any fun t => t.ts == b && t.reads.any fun r => r.2 == a

def dep (a b : Nat) : Bool := ww h a b || wr h a b

def G0 : Prop := ∃ t, Relation.TransGen (fun a b => ww h a b = true) t t
def G1c : Prop := ∃ t, Relation.TransGen (fun a b => dep h a b = true) t t
def G1a : Prop := ∃ t ∈ h, ∃ r ∈ t.reads, installs h r.1 r.2 = false

/-- The Lamport condition: every read returns a version with a timestamp
below the reader's. -/
def Lamport : Prop := ∀ t ∈ h, ∀ r ∈ t.reads, r.2 < t.ts

/-- Union of histories (lists read as sets). -/
def union (h₁ h₂ : List Tx) : List Tx := h₁ ++ h₂

end

theorem tg_rank {R : Nat → Nat → Prop} (f : Nat → Nat) (hR : ∀ a b, R a b → f a < f b) {a b : Nat}
    (h : Relation.TransGen R a b) : f a < f b := by
  induction h with
  | single h => exact hR _ _ h
  | tail _ h ih => exact Nat.lt_trans ih (hR _ _ h)

theorem no_cycle_rank {R : Nat → Nat → Prop} (f : Nat → Nat) (hR : ∀ a b, R a b → f a < f b)
    {t : Nat} (h : Relation.TransGen R t t) : False :=
  Nat.lt_irrefl _ (tg_rank f hR h)

/-- Endpoints of edges: `T_init`, timestamps of `h`, or versions read in `h`. -/
def nodes (h : List Tx) : List Nat := 0 :: h.map (·.ts) ++ (h.flatMap (·.reads)).map (·.2)

theorem installs_nodes {h : List Tx} {k t : Nat} (hi : installs h k t = true) : t ∈ nodes h := by
  unfold installs at hi
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true] at hi
  rcases hi with rfl | ⟨x, hx, hxt, -⟩
  · exact List.mem_cons_self ..
  · apply List.mem_cons_of_mem; apply List.mem_append_left
    exact List.mem_map.2 ⟨x, hx, by simpa using hxt⟩

theorem dep_nodes {h : List Tx} {a b : Nat} (hd : dep h a b = true) : a ∈ nodes h ∧ b ∈ nodes h := by
  unfold dep at hd
  simp only [Bool.or_eq_true] at hd
  rcases hd with hw | hr
  · unfold ww at hw
    obtain ⟨k, -, hn⟩ := List.any_eq_true.1 hw
    unfold next at hn
    simp only [Bool.and_eq_true] at hn
    exact ⟨installs_nodes hn.1.1.1, installs_nodes hn.1.1.2⟩
  · unfold wr at hr
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hr
    obtain ⟨-, t, ht, htb, r, hr, hra⟩ := hr
    refine ⟨?_, ?_⟩
    · apply List.mem_cons_of_mem; apply List.mem_append_right
      exact List.mem_map.2 ⟨r, List.mem_flatMap.2 ⟨t, ht, hr⟩, by simpa using hra⟩
    · apply List.mem_cons_of_mem; apply List.mem_append_left
      exact List.mem_map.2 ⟨t, ht, by simpa using htb⟩

/-- No G0 and no G1c, from a rank that increases along every `dep` edge
between nodes (a finite, decidable check). -/
theorem acyclic_of_rank (h : List Tx) (f : Nat → Nat)
    (hf : ∀ a ∈ nodes h, ∀ b ∈ nodes h, dep h a b = true → f a < f b) : ¬ G0 h ∧ ¬ G1c h := by
  have hd : ∀ a b, dep h a b = true → f a < f b := fun a b e =>
    hf a (dep_nodes e).1 b (dep_nodes e).2 e
  refine ⟨fun ⟨t, ht⟩ => no_cycle_rank f (fun a b e => hd a b (by simp [dep, e])) ht,
    fun ⟨t, ht⟩ => no_cycle_rank f hd ht⟩

/-! ## The counterexample -/

-- items
def x : Nat := 0
def y : Nat := 1
def z : Nat := 2
def w : Nat := 3

/-- `D` (ts 1) reads `B`'s `z`, writes `w`. -/
def D : Tx := ⟨1, [w], [(z, 4)]⟩
/-- `A` (ts 2) writes `x` and `w`. -/
def A : Tx := ⟨2, [x, w], []⟩
/-- `C` (ts 3) reads `A`'s `x`, writes `y`. -/
def C : Tx := ⟨3, [y], [(x, 2)]⟩
/-- `B` (ts 4) writes `y` and `z`. -/
def B : Tx := ⟨4, [y, z], []⟩

def h1 : List Tx := [A, B, C]
def h2 : List Tx := [A, B, D]

def rank1 : Nat → Nat
  | 2 => 1 | 3 => 2 | 4 => 3 | _ => 0
def rank2 : Nat → Nat
  | 4 => 1 | 1 => 2 | 2 => 3 | _ => 0

/-- (i) Each history is read committed: no G1a, G0 or G1c (edges of `h₁`:
`A →wr C →ww B`; of `h₂`: `B →wr D →ww A`). -/
theorem h1_rc : ¬ G1a h1 ∧ ¬ G0 h1 ∧ ¬ G1c h1 := by
  refine ⟨by unfold G1a; decide, acyclic_of_rank h1 rank1 (by decide)⟩

theorem h2_rc : ¬ G1a h2 ∧ ¬ G0 h2 ∧ ¬ G1c h2 := by
  refine ⟨by unfold G1a; decide, acyclic_of_rank h2 rank2 (by decide)⟩

/-- (ii) Their union has the G1c cycle `A →wr C →ww B →wr D →ww A`
(timestamps `2 → 3 → 4 → 1 → 2`), and still no G1a or G0.  Every edge of the
cycle is already an edge of `h₁` (`A → C → B`) or `h₂` (`B → D → A`). -/
theorem union_g1c :
    wr (union h1 h2) 2 3 = true ∧ ww (union h1 h2) 3 4 = true ∧
      wr (union h1 h2) 4 1 = true ∧ ww (union h1 h2) 1 2 = true ∧
      G1c (union h1 h2) ∧ ¬ G1a (union h1 h2) ∧ ¬ G0 (union h1 h2) := by
  have e1 : wr (union h1 h2) 2 3 = true := by decide
  have e2 : ww (union h1 h2) 3 4 = true := by decide
  have e3 : wr (union h1 h2) 4 1 = true := by decide
  have e4 : ww (union h1 h2) 1 2 = true := by decide
  refine ⟨e1, e2, e3, e4, ⟨2, ?_⟩, by unfold G1a; decide, ?_⟩
  · have d : ∀ {a b}, (ww (union h1 h2) a b = true ∨ wr (union h1 h2) a b = true) →
        dep (union h1 h2) a b = true := fun h => by simpa [dep] using h
    exact .tail (.tail (.tail (.single (d (Or.inr e1))) (d (Or.inl e2))) (d (Or.inr e3))) (d (Or.inl e4))
  · -- write-dependencies alone follow timestamps
    rintro ⟨t, ht⟩
    exact no_cycle_rank id (fun a b e => by
      unfold ww at e; obtain ⟨k, -, hn⟩ := List.any_eq_true.1 e
      unfold next at hn; simp only [Bool.and_eq_true, decide_eq_true_eq] at hn; exact hn.1.2) ht

/-- The counterexample violates the Lamport condition only at `D`, which
reads `B`'s version (ts 4) with timestamp 1. -/
theorem counterexample_not_lamport : Lamport h1 ∧ ¬ Lamport h2 := by
  unfold Lamport; decide

/-- (iii) Under the Lamport condition, every `ww` and `wr` edge increases
timestamps, so no history has G0 or G1c, and the condition is preserved by
union.  Hence unions of Lamport histories never exhibit G1c. -/
theorem lamport_union (h₁ h₂ : List Tx) (l₁ : Lamport h₁) (l₂ : Lamport h₂) :
    Lamport (union h₁ h₂) ∧ ¬ G0 (union h₁ h₂) ∧ ¬ G1c (union h₁ h₂) := by
  have hl : Lamport (union h₁ h₂) := by
    intro t ht r hr
    rcases List.mem_append.1 ht with ht | ht
    · exact l₁ t ht r hr
    · exact l₂ t ht r hr
  have hww : ∀ a b, ww (union h₁ h₂) a b = true → a < b := fun a b e => by
    unfold ww at e; obtain ⟨k, -, hn⟩ := List.any_eq_true.1 e
    unfold next at hn; simp only [Bool.and_eq_true, decide_eq_true_eq] at hn; exact hn.1.2
  have hwr : ∀ a b, wr (union h₁ h₂) a b = true → a < b := fun a b e => by
    unfold wr at e
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at e
    obtain ⟨-, t, ht, rfl, r, hr, rfl⟩ := e
    exact hl t ht r hr
  refine ⟨hl, fun ⟨t, ht⟩ => no_cycle_rank id hww ht, fun ⟨t, ht⟩ => no_cycle_rank id (fun a b e => ?_) ht⟩
  unfold dep at e; simp only [Bool.or_eq_true] at e
  exact e.elim (hww a b) (hwr a b)

/-- The counterexample: two read-committed histories whose union exhibits
G1c, so Read Committed is not invariant confluent over this history model
without the Lamport condition; with it, unions stay free of G1c. -/
theorem counterexample :
    (¬ G1a h1 ∧ ¬ G0 h1 ∧ ¬ G1c h1) ∧ (¬ G1a h2 ∧ ¬ G0 h2 ∧ ¬ G1c h2) ∧ G1c (union h1 h2) ∧
      ∀ h₁ h₂, Lamport h₁ → Lamport h₂ → ¬ G1c (union h₁ h₂) :=
  ⟨h1_rc, h2_rc, union_g1c.2.2.2.2.1, fun h₁ h₂ l₁ l₂ => (lamport_union h₁ h₂ l₁ l₂).2.2⟩

end HATUnion
end CC
