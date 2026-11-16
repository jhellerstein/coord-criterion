import CoordCriterion.CAP.AsyncGilbertLynch

/-!
# From Gilbert and Lynch's fair executions to the finite forms (Appendix F)

Supports the paragraph after Prop. `prop:gl-async`: "Gilbert and Lynch require
availability and atomicity in all fair executions, including those in which
messages are lost, in Lynch's asynchronous network model.  Both imply the forms
in the proposition.  In their model any message may be lost and client requests
are inputs, so a finite execution extends to a fair execution with no new
request in which every message is lost; their own proofs extend executions
fairly in this way.  Availability answers the pending request at some finite
point of that extension, and the prefix up to that response is the extension
the proposition requires.  Atomicity of the fair extension gives atomicity of
the finite execution, since atomicity is a safety property and so holds of
every prefix of an atomic execution."

* `IExec`: an infinite execution, as a chain of finite executions `E t`, each
  extending the last by actions later than all of its own, together with the
  node states along the way (Lynch's executions alternate states and actions).
* `IExec.Fair`: each node's task (its locally controlled actions, responses and
  sends) gets its turn infinitely often: from every point there is a later step
  at which the node performs a locally controlled action, or has none enabled
  in its current state.  Lost messages need no fairness.
* `AvailableFair`, `AtomicFair`: Gilbert and Lynch's notions over fair
  executions with well-formed clients.
* `fair_extension`: every finite execution extends to a fair execution that
  adds no invocation and no receipt (every message is lost), round robin over
  the nodes.
* `available_of_fair`, `atomic_of_fair`: the fair forms imply the finite forms
  `Available`, `Atomic` of Prop. `prop:gl-async`; `gilbert_lynch_fair`: their
  Theorem 1 as they state it.

Modeling choice: atomicity of an infinite execution is atomicity of each of its
finite prefixes (`AtomicExec`).  That this agrees with Lynch's definition by
linearizations of the infinite execution is her result that atomicity is a
safety property (*Distributed Algorithms*, Chapter 13), which the paper cites.
-/

namespace CC
namespace AsyncGL

open Classical

variable {N : Nat} {M : Type}

/-- Locally controlled actions: responses and sends. -/
def Local : Act N M → Prop
  | .resp _ _ => True
  | .send _ _ => True
  | _ => False

/-- An infinite execution of `A`: finite executions `E t`, each extending the
last by later actions, and node states following each node's actions. -/
structure IExec (A : Alg N M) where
  E : Nat → GExec N M
  st : Nat → Fin N → A.St
  exec : ∀ t, IsGExec A (E t)
  run0 : ∀ i, NRun A i (A.start i) (acts ((E 0).tr i)) (st 0 i)
  step : ∀ t i, ∃ β, (E (t+1)).tr i = (E t).tr i ++ β ∧
    (∀ y ∈ β, ∀ j x, x ∈ (E t).tr j → x.1 < y.1) ∧ NRun A i (st t i) (acts β) (st (t+1) i)

/-- Fairness: from every point, each node later performs a locally controlled
action or has none enabled in its current state. -/
def IExec.Fair {A : Alg N M} (ρ : IExec A) : Prop :=
  ∀ i t, ∃ t', t ≤ t' ∧
    ((∃ y, y ∈ (ρ.E (t'+1)).tr i ∧ y ∉ (ρ.E t').tr i ∧ Local y.2) ∨
     ¬ ∃ x s', Local x ∧ A.step i (ρ.st t' i) x s')

/-- Gilbert–Lynch availability: in every fair execution with well-formed
clients, every invocation is answered at its node. -/
def AvailableFair (A : Alg N M) : Prop :=
  ∀ ρ : IExec A, ρ.Fair → (∀ t, ClientWF (ρ.E t)) →
    ∀ t i T a kd, (T, Act.inv a kd) ∈ (ρ.E t).tr i →
      ∃ t' T' r, (T', Act.resp a r) ∈ (ρ.E t').tr i

/-- Gilbert–Lynch atomicity: every fair execution with well-formed clients is
atomic (every finite prefix is). -/
def AtomicFair (A : Alg N M) : Prop :=
  ∀ ρ : IExec A, ρ.Fair → (∀ t, ClientWF (ρ.E t)) → ∀ t, AtomicExec (ρ.E t)

/-! ## The round-robin fair extension -/

section Construction

variable (A : Alg N M) (E : GExec N M)

theorem le_foldr_max : ∀ (l : List Nat), ∀ m ∈ l, m ≤ l.foldr max 0
  | [], _, h => by cases h
  | a :: l, m, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max l m h) (Nat.le_max_right _ _)

/-- A time above every action of `E`. -/
def bnd : Nat :=
  ((List.finRange N).flatMap (fun j => (E.tr j).map Prod.fst)).foldr max 0 + 1

theorem lt_bnd : ∀ j x, x ∈ E.tr j → x.1 < bnd E := by
  intro j x hx
  apply Nat.lt_succ_of_le
  apply le_foldr_max
  rw [List.mem_flatMap]
  exact ⟨j, List.mem_finRange j, List.mem_map_of_mem hx⟩

/-- The node whose turn is step `t`. -/
def turn (t : Nat) : Option (Fin N) :=
  if h : 0 < N then some ⟨t % N, Nat.mod_lt _ h⟩ else none

/-- One round-robin step at time `bnd E + t`. -/
noncomputable def next (c : GExec N M × (Fin N → A.St)) (t : Nat) :
    GExec N M × (Fin N → A.St) :=
  match turn (N := N) t with
  | none => c
  | some i =>
    if h : ∃ x s', Local x ∧ A.step i (c.2 i) x s' then
      (⟨fun j => if j = i then c.1.tr j ++ [(bnd E + t, Classical.choose h)] else c.1.tr j⟩,
        fun j => if j = i then Classical.choose (Classical.choose_spec h) else c.2 j)
    else c

/-- The configurations of the extension. -/
noncomputable def cfg (s0 : Fin N → A.St) : Nat → GExec N M × (Fin N → A.St)
  | 0 => (E, s0)
  | t + 1 => next A E (cfg s0 t) t

/-- The step from `t` to `t+1`: either nothing changes, or the node `i` whose
turn it is appends one enabled local action at time `bnd E + t`. -/
theorem cfg_succ (s0 : Fin N → A.St) (t : Nat) :
    cfg A E s0 (t+1) = cfg A E s0 t ∨
    ∃ i x s', turn (N := N) t = some i ∧ Local x ∧ A.step i ((cfg A E s0 t).2 i) x s' ∧
      (cfg A E s0 (t+1)).1.tr = (fun j => if j = i then (cfg A E s0 t).1.tr j ++ [(bnd E + t, x)]
        else (cfg A E s0 t).1.tr j) ∧
      (cfg A E s0 (t+1)).2 = (fun j => if j = i then s' else (cfg A E s0 t).2 j) := by
  rw [show cfg A E s0 (t+1) = next A E (cfg A E s0 t) t from rfl]
  unfold next
  cases ht : turn (N := N) t with
  | none => exact Or.inl rfl
  | some i =>
    simp only
    by_cases h : ∃ x s', Local x ∧ A.step i ((cfg A E s0 t).2 i) x s'
    · simp only [dif_pos h]
      have hs := Classical.choose_spec (Classical.choose_spec h)
      exact Or.inr ⟨i, _, _, rfl, hs.1, hs.2, rfl, rfl⟩
    · left
      rw [dif_neg h]

/-- When the step does nothing at node `i` whose turn it is, `i` has no
enabled local action. -/
theorem cfg_idle (s0 : Fin N → A.St) (t : Nat) (i : Fin N) (ht : turn (N := N) t = some i)
    (hn : ¬ ∃ x s', Local x ∧ A.step i ((cfg A E s0 t).2 i) x s') :
    cfg A E s0 (t+1) = cfg A E s0 t := by
  show next A E (cfg A E s0 t) t = cfg A E s0 t
  unfold next
  rw [ht]
  simp only [dif_neg hn]

theorem cfg_busy (s0 : Fin N → A.St) (t : Nat) (i : Fin N) (ht : turn (N := N) t = some i)
    (he : ∃ x s', Local x ∧ A.step i ((cfg A E s0 t).2 i) x s') :
    ∃ x, Local x ∧ (bnd E + t, x) ∈ (cfg A E s0 (t+1)).1.tr i := by
  refine ⟨Classical.choose he, (Classical.choose_spec (Classical.choose_spec he)).1, ?_⟩
  show (bnd E + t, _) ∈ (next A E (cfg A E s0 t) t).1.tr i
  unfold next
  rw [ht]
  simp only [dif_pos he]
  simp

/-- Invariant: every action of `cfg t` is earlier than `bnd E + t`; each node's
trace is `E`'s followed by local actions at times `≥ bnd E`; and the states
follow the traces. -/
theorem cfg_inv (s0 : Fin N → A.St) (hs0 : ∀ i, NRun A i (A.start i) (acts (E.tr i)) (s0 i)) :
    ∀ t, (∀ j x, x ∈ (cfg A E s0 t).1.tr j → x.1 < bnd E + t) ∧
      (∀ j, ∃ β, (cfg A E s0 t).1.tr j = E.tr j ++ β ∧ ∀ y ∈ β, bnd E ≤ y.1 ∧ Local y.2) ∧
      (∀ j, NRun A j (A.start j) (acts ((cfg A E s0 t).1.tr j)) ((cfg A E s0 t).2 j))
  | 0 => ⟨fun j x hx => Nat.lt_of_lt_of_le (lt_bnd E j x hx) (Nat.le_add_right _ _),
      fun j => ⟨[], by simp [cfg], by simp⟩, hs0⟩
  | t + 1 => by
    obtain ⟨h1, h2, h3⟩ := cfg_inv s0 hs0 t
    rcases cfg_succ A E s0 t with h | ⟨i, x, s', _, hx, hst, htr, hs⟩
    · rw [h]
      exact ⟨fun j y hy => Nat.lt_succ_of_lt (h1 j y hy), h2, h3⟩
    · refine ⟨fun j y hy => ?_, fun j => ?_, fun j => ?_⟩
      · rw [htr] at hy
        by_cases hj : j = i
        · subst hj
          simp only [if_true] at hy
          rcases List.mem_append.1 hy with hy | hy
          · exact Nat.lt_succ_of_lt (h1 _ y hy)
          · simp at hy; subst hy; exact Nat.lt_succ_self _
        · simp only [hj, if_false] at hy
          exact Nat.lt_succ_of_lt (h1 j y hy)
      · obtain ⟨β, hβ, hβy⟩ := h2 j
        rw [htr]
        by_cases hj : j = i
        · subst hj
          refine ⟨β ++ [(bnd E + t, x)], by simp [hβ], fun y hy => ?_⟩
          rcases List.mem_append.1 hy with hy | hy
          · exact hβy y hy
          · simp at hy; subst hy; exact ⟨Nat.le_add_right _ _, hx⟩
        · simp only [hj, if_false]; exact ⟨β, hβ, hβy⟩
      · rw [htr, hs]
        by_cases hj : j = i
        · subst hj
          simp only [if_true]
          have : acts ((cfg A E s0 t).1.tr j ++ [(bnd E + t, x)]) =
              acts ((cfg A E s0 t).1.tr j) ++ [x] := by simp [acts]
          rw [this]
          exact nrun_append.2 ⟨_, h3 j, .cons hst (.nil _)⟩
        · simp only [hj, if_false]; exact h3 j

theorem local_not_recv {x : Act N M} (h : Local x) : ∀ s m, x ≠ Act.recv s m := by
  intro s m e; subst e; exact h

theorem local_not_inv {x : Act N M} (h : Local x) : ∀ a k, x ≠ Act.inv a k := by
  intro a k e; subst e; exact h

/-- Each configuration is an execution. -/
theorem cfg_exec (s0 : Fin N → A.St) (hs0 : ∀ i, NRun A i (A.start i) (acts (E.tr i)) (s0 i))
    (hE : IsGExec A E) : ∀ t, IsGExec A (cfg A E s0 t).1
  | 0 => hE
  | t + 1 => by
    have hprev := cfg_exec s0 hs0 hE t
    obtain ⟨h1, _, _⟩ := cfg_inv A E s0 hs0 t
    obtain ⟨_, _, h3'⟩ := cfg_inv A E s0 hs0 (t+1)
    rcases cfg_succ A E s0 t with h | ⟨i, x, s', _, hx, _, htr, _⟩
    · rw [h]; exact hprev
    · obtain ⟨_, hpw, hdis, f, hf⟩ := hprev
      have hmem : ∀ j y, y ∈ (cfg A E s0 (t+1)).1.tr j →
          y ∈ (cfg A E s0 t).1.tr j ∨ (j = i ∧ y = (bnd E + t, x)) := by
        intro j y hy
        rw [htr] at hy
        by_cases hj : j = i
        · subst hj
          simp only [if_true] at hy
          rcases List.mem_append.1 hy with hy | hy
          · exact Or.inl hy
          · simp at hy; exact Or.inr ⟨rfl, hy⟩
        · simp only [hj, if_false] at hy; exact Or.inl hy
      have hold : ∀ j y, y ∈ (cfg A E s0 t).1.tr j → y ∈ (cfg A E s0 (t+1)).1.tr j := by
        intro j y hy
        rw [htr]
        by_cases hj : j = i
        · subst hj; simp only [if_true]; exact List.mem_append_left _ hy
        · simp only [hj, if_false]; exact hy
      refine ⟨fun j => ⟨_, h3' j⟩, fun j => ?_, ?_, f, ?_⟩
      · rw [htr]
        by_cases hj : j = i
        · subst hj
          simp only [if_true]
          rw [List.pairwise_append]
          refine ⟨hpw j, by simp, fun a ha b hb => ?_⟩
          simp at hb; subst hb
          exact h1 j a ha
        · simp only [hj, if_false]; exact hpw j
      · intro j j' y z hy hz he
        rcases hmem j y hy with hy | ⟨hj, rfl⟩ <;> rcases hmem j' z hz with hz | ⟨hj', rfl⟩
        · exact hdis j j' y z hy hz he
        · exact absurd he (Nat.ne_of_lt (h1 j y hy))
        · exact absurd he.symm (Nat.ne_of_lt (h1 j' z hz))
        · exact ⟨hj.trans hj'.symm, rfl⟩
      · intro j T src m hr
        rcases hmem j _ hr with hr | ⟨_, he⟩
        · obtain ⟨hlt, hs, hu⟩ := hf j T src m hr
          refine ⟨hlt, hold src _ hs, fun j' T' src' m' hr' hfe => ?_⟩
          rcases hmem j' _ hr' with hr' | ⟨_, he'⟩
          · exact hu j' T' src' m' hr' hfe
          · cases he'; exact absurd rfl (local_not_recv hx src' m')
        · cases he; exact absurd rfl (local_not_recv hx src m)

end Construction

/-- Well-formed clients are preserved by an extension that adds no
invocation. -/
theorem clientWF_ext {E E' : GExec N M} (hc : ClientWF E)
    (hext : ∀ j, ∃ β, E'.tr j = E.tr j ++ β ∧ ∀ y ∈ β, ∀ a k, y.2 ≠ Act.inv a k) :
    ClientWF E' := by
  have hinv : ∀ j y a k, y ∈ E'.tr j → y.2 = Act.inv a k → y ∈ E.tr j := by
    intro j y a k hy he
    obtain ⟨β, hβ, hβy⟩ := hext j
    rw [hβ] at hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hy
    · exact absurd he (hβy y hy a k)
  have hsub : ∀ j y, y ∈ E.tr j → y ∈ E'.tr j := by
    intro j y hy
    obtain ⟨β, hβ, _⟩ := hext j
    rw [hβ]; exact List.mem_append_left _ hy
  refine ⟨fun i j x y a k k' hx hy hxa hya => hc.1 i j x y a k k' (hinv i x a k hx hxa)
    (hinv j y a k' hy hya) hxa hya, fun i T a k T' b k' h1 h2 hlt => ?_⟩
  obtain ⟨T'', r, hlt', hr⟩ := hc.2 i T a k T' b k' (hinv i _ a k h1 rfl) (hinv i _ b k' h2 rfl) hlt
  exact ⟨T'', r, hlt', hsub i _ hr⟩

/-- **Every finite execution extends to a fair execution with no new request
in which every message is lost.**  The extension starts at `E`, and every
action it adds is a local action later than every action of `E`. -/
theorem fair_extension (A : Alg N M) (E : GExec N M) (hE : IsGExec A E) :
    ∃ ρ : IExec A, ρ.E 0 = E ∧ ρ.Fair ∧
      ∀ t j, ∃ β, (ρ.E t).tr j = E.tr j ++ β ∧
        ∀ y ∈ β, (∀ j' x, x ∈ E.tr j' → x.1 < y.1) ∧ Local y.2 := by
  have hs : ∀ i, ∃ s, NRun A i (A.start i) (acts (E.tr i)) s := hE.1
  let s0 : Fin N → A.St := fun i => Classical.choose (hs i)
  have hs0 : ∀ i, NRun A i (A.start i) (acts (E.tr i)) (s0 i) :=
    fun i => Classical.choose_spec (hs i)
  have inv := cfg_inv A E s0 hs0
  refine ⟨⟨fun t => (cfg A E s0 t).1, fun t => (cfg A E s0 t).2, cfg_exec A E s0 hs0 hE, hs0,
    fun t i => ?_⟩, rfl, fun i t => ?_, fun t j => ?_⟩
  · obtain ⟨h1, _, _⟩ := inv t
    rcases cfg_succ A E s0 t with h | ⟨i', x, s', _, _, hst, htr, hst'⟩
    · exact ⟨[], by rw [h]; simp, by simp, by rw [h]; exact .nil _⟩
    · by_cases hi : i = i'
      · subst hi
        refine ⟨[(bnd E + t, x)], by rw [htr]; simp, fun y hy j x' hx' => ?_, ?_⟩
        · simp at hy; subst hy; exact h1 j x' hx'
        · rw [hst']; simp only [if_true]; exact .cons hst (.nil _)
      · refine ⟨[], by rw [htr]; simp [hi], by simp, ?_⟩
        rw [hst']; simp only [hi, if_false]; exact .nil _
  · -- the turn of `i` comes at `N * (t+1) + i`
    have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    let t' := N * (t+1) + i.val
    have hle : t ≤ t' := by
      have : t + 1 ≤ N * (t+1) := Nat.le_mul_of_pos_left _ hN
      omega
    have hturn : turn (N := N) t' = some i := by
      unfold turn
      rw [dif_pos hN]
      congr 1
      apply Fin.ext
      show (N * (t+1) + i.val) % N = i.val
      rw [Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt i.isLt
    refine ⟨t', hle, ?_⟩
    by_cases he : ∃ x s', Local x ∧ A.step i ((cfg A E s0 t').2 i) x s'
    · obtain ⟨x, hx, hm⟩ := cfg_busy A E s0 t' i hturn he
      refine Or.inl ⟨_, hm, fun hold => ?_, hx⟩
      have := (inv t').1 i _ hold
      exact Nat.lt_irrefl _ this
    · exact Or.inr he
  · obtain ⟨_, h2, _⟩ := inv t
    obtain ⟨β, hβ, hβy⟩ := h2 j
    exact ⟨β, hβ, fun y hy => ⟨fun j' x hx => Nat.lt_of_lt_of_le (lt_bnd E j' x hx) (hβy y hy).1,
      (hβy y hy).2⟩⟩

/-! ## The fair forms imply the finite forms -/

/-- **Availability in fair executions gives the finite form.**  The fair
extension of the finite execution answers the pending request at some finite
point; the prefix up to that point is the extension `Available` requires. -/
theorem available_of_fair {A : Alg N M} (h : AvailableFair A) : Available A := by
  intro E hE hc i T a kd hinv _
  obtain ⟨ρ, h0, hfair, hext⟩ := fair_extension A E hE
  have hwf : ∀ t, ClientWF (ρ.E t) := fun t =>
    clientWF_ext hc fun j => by
      obtain ⟨β, hβ, hβy⟩ := hext t j
      exact ⟨β, hβ, fun y hy => local_not_inv (hβy y hy).2⟩
  obtain ⟨t', T', r, hr⟩ := h ρ hfair hwf 0 i T a kd (by rw [h0]; exact hinv)
  refine ⟨ρ.E t', ρ.exec t', fun j => ?_, T', r, hr⟩
  obtain ⟨β, hβ, hβy⟩ := hext t' j
  exact ⟨β, hβ, fun y hy => ⟨(hβy y hy).1, local_not_inv (hβy y hy).2,
    local_not_recv (hβy y hy).2⟩⟩

/-- **Atomicity in fair executions gives the finite form.**  The finite
execution is the first prefix of its fair extension. -/
theorem atomic_of_fair {A : Alg N M} (h : AtomicFair A) : Atomic A := by
  intro E hE hc
  obtain ⟨ρ, h0, hfair, hext⟩ := fair_extension A E hE
  have hwf : ∀ t, ClientWF (ρ.E t) := fun t =>
    clientWF_ext hc fun j => by
      obtain ⟨β, hβ, hβy⟩ := hext t j
      exact ⟨β, hβ, fun y hy => local_not_inv (hβy y hy).2⟩
  have := h ρ hfair hwf 0
  rw [h0] at this
  exact this

/-- **Gilbert and Lynch's Theorem 1, in their fair-execution form.**  With at
least two nodes, no algorithm for a read/write register is available and atomic
in all fair executions. -/
theorem gilbert_lynch_fair (hN : 2 ≤ N) (A : Alg N M) : ¬ (AvailableFair A ∧ AtomicFair A) :=
  fun ⟨hav, hat⟩ => gilbert_lynch_async hN A ⟨available_of_fair hav, atomic_of_fair hat⟩

end AsyncGL
end CC
