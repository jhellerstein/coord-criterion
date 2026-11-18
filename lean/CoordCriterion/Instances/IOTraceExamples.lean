import CoordCriterion.Instances.IOTrace

/-!
# Examples for §6.5 (namespace `CC.IOT`)

* `Poll` — a registrar that may close the polls early: after the first
  ballot `p` it may reply `x` at once and then ignore later ballots, or wait
  for a second ballot, reply `x`, and later `z`.  Its projected spec is
  consistent, but the automaton is not confluent, and the projected spec has a
  run (`p`, `x`, `p`, `z`) that no execution produces.
* `Hid`, `Vis` — after the first `p`, `Hid` takes an internal step to `sA`
  or `sB`; both reply `x`, but only `sB` can then reply `z`.  `Vis` has only
  `sB`.  The two have the same executions' receive and reply sequences (the
  same projected spec), yet `Hid`'s system narrows away `z` after `x`, a
  commitment event that `Vis`'s system never makes.
* `Race`, `Queue` — a counter that reports its current count whenever the
  report fires (inconsistent projected spec), and one that records the count
  at each arrival and reports from that record (consistent projected spec,
  confluent automaton).
* `realizability_alone`, `domination_alone` — neither obligation of
  Prop. `prop:declared-specification` suffices alone.
-/

namespace CC
namespace IOT

open Classical

/-! ## Closing the polls early -/

namespace Poll

inductive Act | p | x | z

inductive St | s0 | s1 | s2 | s3 | s4 | cl

def sig : IOA.Sig Act where
  inp a := a = .p
  out a := a = .x ∨ a = .z
  int _ := False
  inp_out a h h' := by subst h; rcases h' with h' | h' <;> cases h'
  inp_int _ _ h := h
  out_int _ _ h := h

/-- `s1 → cl` replies early and closes the polls; `cl` ignores later ballots. -/
inductive Tr : St → Act → St → Prop
  | a0 : Tr .s0 .p .s1
  | a1 : Tr .s1 .p .s2
  | a2 : Tr .s1 .x .cl
  | a3 : Tr .s2 .p .s2
  | a4 : Tr .s2 .x .s3
  | a5 : Tr .s3 .p .s3
  | a6 : Tr .s3 .z .s4
  | a7 : Tr .s4 .p .s4
  | a8 : Tr .cl .p .cl

def M : IOA.Automaton Act where
  St := St
  sig := sig
  start s := s = .s0
  start_nonempty := ⟨.s0, rfl⟩
  trans := Tr
  trans_acts s a t h := by
    cases h <;> simp [IOA.Sig.acts, sig]
  input_enabled s a h := by
    cases h
    cases s
    · exact ⟨_, .a0⟩
    · exact ⟨_, .a1⟩
    · exact ⟨_, .a3⟩
    · exact ⟨_, .a5⟩
    · exact ⟨_, .a7⟩
    · exact ⟨_, .a8⟩

/-- The reply sequence each state has sent. -/
def Inv : St → List Act → Prop
  | .s0, r => r = []
  | .s1, r => r = []
  | .s2, r => r = []
  | .s3, r => r = [.x]
  | .cl, r => r = [.x]
  | .s4, r => r = [.x, .z]

theorem inv_run {s t : M.St} {γ : List Act} (h : IOA.Run M s γ t) :
    ∀ pre, Inv s (replies M pre) → Inv t (replies M (pre ++ γ)) := by
  induction h with
  | nil => intro pre h; simpa using h
  | @cons s s' t a γ htr _ ih =>
    intro pre hI
    have : pre ++ a :: γ = (pre ++ [a]) ++ γ := by simp
    rw [this]
    apply ih
    have hr : replies M (pre ++ [a]) = replies M pre ++ replies M [a] := replies_append _ _
    cases htr <;> simp_all [Inv, replies, M, sig]

theorem replies_cases {β : List Act} {s : M.St} (h : IOA.Execution M β s) :
    replies M β = [] ∨ replies M β = [.x] ∨ replies M β = [.x, .z] := by
  obtain ⟨s0, rfl, hr⟩ := h
  have := inv_run hr [] rfl
  simp only [List.nil_append] at this
  cases s <;> simp_all [Inv]

theorem chain_comparable {t t' : List Act}
    (ht : t = [] ∨ t = [.x] ∨ t = [.x, .z]) (ht' : t' = [] ∨ t' = [.x] ∨ t' = [.x, .z]) :
    t <+: t' ∨ t' <+: t := by
  rcases ht with rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl <;>
    first
    | exact Or.inl (List.prefix_refl _)
    | exact Or.inl List.nil_prefix
    | exact Or.inr List.nil_prefix
    | exact Or.inl ⟨[.z], rfl⟩
    | exact Or.inr ⟨[.z], rfl⟩

/-- The projected spec is consistent: every reply sequence is `[]`, `[x]`, or
`[x, z]`. -/
theorem consistent : (spec M).Consistent := by
  rw [consistent_iff]
  rintro w t t' ⟨β, s, hx, _, rfl⟩ ⟨β', s', hx', _, rfl⟩
  exact chain_comparable (replies_cases hx) (replies_cases hx')

theorem run_quiet {s t : M.St} {γ : List Act} (h : IOA.Run M s γ t) (hs : s = St.cl ∨ s = St.s4) :
    replies M γ = [] ∧ t = s := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons s s' t a γ htr _ ih =>
    rcases hs with rfl | rfl <;> cases htr <;>
      · obtain ⟨h1, h2⟩ := ih (by first | exact Or.inl rfl | exact Or.inr rfl)
        exact ⟨by simpa [replies, M, sig] using h1, h2⟩

theorem live_quiet {β : List Act} {s : M.St} (hs : s = St.cl ∨ s = St.s4) {k : InS M} {u : OutS M}
    (h : Live M β s k u) : u.val = replies M β := by
  obtain ⟨γ, t, hr, _, rfl⟩ := h
  simp [outW_val, replies_append, (run_quiet hr hs).1]

theorem ex_early : IOA.Execution M [.p, .x] .cl := ⟨.s0, rfl, .cons .a0 (.cons .a2 (.nil _))⟩
theorem ex_late : IOA.Execution M [.p, .p, .x, .z] .s4 :=
  ⟨.s0, rfl, .cons .a0 (.cons .a1 (.cons .a4 (.cons .a6 (.nil _))))⟩

/-- The automaton is not confluent: once it has replied early, it cannot
reach the row at two ballots that the late execution has reached. -/
theorem not_confluent : ¬ Confluent M := by
  intro h
  let j : InS M := ⟨[.p, .p], by simp [M, sig]⟩
  obtain ⟨u, hu⟩ := h [([.p, .x], .cl), ([.p, .p, .x, .z], .s4)]
    (by simp only [List.mem_cons, List.mem_nil_iff, or_false]
        rintro e (rfl | rfl)
        · exact ex_early
        · exact ex_late) j
    (by simp only [List.mem_cons, List.mem_nil_iff, or_false]
        rintro e (rfl | rfl)
        · exact ⟨[.p], by simp [inW_val, recvs, M, sig, j]⟩
        · exact ⟨[], by simp [inW_val, recvs, M, sig, j]⟩)
  have h1 := live_quiet (Or.inl rfl) (hu ([.p, .x], .cl) (by simp))
  have h2 := live_quiet (Or.inr rfl) (hu ([.p, .p, .x, .z], .s4) (by simp))
  rw [h1] at h2
  simp [replies, M, sig] at h2

/-- Replying early removes the row at two ballots with reply sequence
`[x, z]`: it is in the canonical table of the execution `p`, `x`, and no
longer reachable. -/
theorem early_removes :
    Removed M [.p, .x] .cl ⟨[.p, .p], by simp [M, sig]⟩ ⟨[.x, .z], by simp [M, sig]⟩ := by
  refine ⟨⟨?_, ⟨[.p], by simp [inW_val, recvs, M, sig]⟩, ⟨[.z], by simp [outW_val, replies, M, sig]⟩⟩,
    fun h => ?_⟩
  · have := spec_row ex_late
    have e1 : inW M [.p, .p, .x, .z] = ⟨[.p, .p], by simp [M, sig]⟩ :=
      Wd.ext (by simp [inW_val, recvs, M, sig])
    have e2 : outW M [.p, .p, .x, .z] = ⟨[.x, .z], by simp [M, sig]⟩ :=
      Wd.ext (by simp [outW_val, replies, M, sig])
    rwa [e1, e2] at this
  · have := live_quiet (Or.inl rfl) h
    simp [replies, M, sig] at this

/-- The run `p`, `x`, `p`, `z` of the projected spec. -/
theorem spec_run : ∃ σ, Exec (canon (spec M) (inW M [])) (evs M [.p, .x, .p, .z]) σ := by
  have r1 : (spec M).P (inW M [.p]) (outW M [.p]) := spec_row ⟨.s0, rfl, .cons .a0 (.nil _)⟩
  have r2 : (spec M).P (inW M [.p, .x]) (outW M [.p, .x]) := spec_row ex_early
  have r3 : (spec M).P (inW M [.p, .p, .x, .z]) (outW M [.p, .p, .x, .z]) := spec_row ex_late
  have e1 : inW M ([] ++ [.p]) = inW M [.p] := rfl
  have e2 : inW M [.p, .x] = inW M [.p] := Wd.ext (by simp [inW_val, recvs, M, sig])
  have e3 : inW M [.p, .x, .p] = inW M [.p, .p, .x, .z] := Wd.ext (by simp [inW_val, recvs, M, sig])
  have e4 : outW M [.p, .x, .p, .z] = outW M [.p, .p, .x, .z] :=
    Wd.ext (by simp [outW_val, replies, M, sig])
  have e5 : outW M [.p, .x, .p] = outW M [.p, .x] := Wd.ext (by simp [outW_val, replies, M, sig])
  have hev : evs M [.p, .x, .p, .z] = [.input (inW M [.p]), .output (outW M [.p, .x]),
      .input (inW M [.p, .p, .x, .z]), .output (outW M [.p, .p, .x, .z])] := by
    have ip : M.sig.inp Act.p := rfl
    have nx : ¬ M.sig.inp Act.x := fun h => by cases h
    have nz : ¬ M.sig.inp Act.z := fun h => by cases h
    have ox : M.sig.out Act.x := Or.inl rfl
    have oz : M.sig.out Act.z := Or.inr rfl
    simp only [evs, evsFrom, ip, nx, nz, ox, oz, ↓reduceIte, List.nil_append, List.cons_append,
      List.append_nil]
    rw [e3, e4]
  rw [hev]
  let σ0 := canon (spec M) (inW M [])
  have h0 : σ0.R (inW M [.p]) (outW M [.p]) := ⟨r1, inW_nil_le _⟩
  let σ1 := Guard.inState σ0 (inW M [.p]) (outW M [.p]) h0
  have r2' : (spec M).P (inW M [.p]) (outW M [.p, .x]) := e2 ▸ r2
  have h1 : σ1.R σ1.cur (outW M [.p, .x]) := ⟨⟨r2', inW_nil_le _⟩, PO.refl (inW M [.p])⟩
  let σ2 := outState σ1 (outW M [.p, .x]) h1
  have h2 : σ2.R (inW M [.p, .p, .x, .z]) (outW M [.p, .p, .x, .z]) :=
    ⟨⟨⟨r3, inW_nil_le _⟩, ⟨[.p], by simp [inW_val, recvs, M, sig]⟩⟩,
      ⟨[.z], by simp [outW_val, replies, M, sig]⟩⟩
  let σ3 := Guard.inState σ2 _ _ h2
  have h3 : σ3.R σ3.cur (outW M [.p, .p, .x, .z]) := ⟨h2, PO.refl _⟩
  exact ⟨_, .cons (Step.input σ0 σ1 _ ⟨_, h0⟩ rfl rfl)
    (.cons (step_output_outState h1)
    (.cons (Step.input σ2 σ3 _ ⟨_, h2⟩ rfl rfl)
    (.cons (step_output_outState h3) (.nil _))))⟩

/-- No execution produces the run `p`, `x`, `p`, `z`. -/
theorem no_execution {β : List Act} {s : M.St} (h : IOA.Execution M β s) :
    evs M β ≠ evs M [.p, .x, .p, .z] := by
  intro he
  have ht := evs_inj he
  have htr : trace M [.p, .x, .p, .z] = [.p, .x, .p, .z] := by simp [trace, M, sig]
  rw [trace_eq_of_noint (fun _ h => h) h, htr] at ht
  subst ht
  obtain ⟨s0, hs0, hr⟩ := h
  have hs0' : s0 = St.s0 := hs0
  subst hs0'
  obtain ⟨_, h1, hr⟩ := run_cons_inv hr
  cases h1
  obtain ⟨_, h2, hr⟩ := run_cons_inv hr
  cases h2
  obtain ⟨_, h3, hr⟩ := run_cons_inv hr
  cases h3
  obtain ⟨_, h4, _⟩ := run_cons_inv hr
  cases h4

end Poll

/-! ## A hidden internal choice -/

namespace Hid

inductive Act | p | x | z | τ

inductive St | s0 | s1 | sA | sB | a1 | b1 | b2

def sig : IOA.Sig Act where
  inp a := a = .p
  out a := a = .x ∨ a = .z
  int a := a = .τ
  inp_out a h h' := by subst h; rcases h' with h' | h' <;> cases h'
  inp_int a h h' := by subst h; cases h'
  out_int a h h' := by subst h'; rcases h with h | h <;> cases h

/-- `Hid`: after the first ballot, an internal step chooses `sA` (reply `x`,
never `z`) or `sB` (reply `x`, then possibly `z`).  Later ballots are
ignored. -/
inductive TrH : St → Act → St → Prop
  | p0 : TrH .s0 .p .s1
  | ps (s : St) : s ≠ .s0 → TrH s .p s
  | tA : TrH .s1 .τ .sA
  | tB : TrH .s1 .τ .sB
  | xA : TrH .sA .x .a1
  | xB : TrH .sB .x .b1
  | zB : TrH .b1 .z .b2

/-- `Vis`: the same without the choice of `sA`. -/
inductive TrV : St → Act → St → Prop
  | p0 : TrV .s0 .p .s1
  | ps (s : St) : s ≠ .s0 → TrV s .p s
  | tB : TrV .s1 .τ .sB
  | xB : TrV .sB .x .b1
  | zB : TrV .b1 .z .b2

theorem enabled (s : St) : ∃ t, TrH s .p t ∧ TrV s .p t := by
  cases s
  · exact ⟨_, .p0, .p0⟩
  all_goals exact ⟨_, .ps _ (by intro h; cases h), .ps _ (by intro h; cases h)⟩

def H : IOA.Automaton Act where
  St := St
  sig := sig
  start s := s = .s0
  start_nonempty := ⟨.s0, rfl⟩
  trans := TrH
  trans_acts s a t h := by cases h <;> simp [IOA.Sig.acts, sig]
  input_enabled s a h := by
    cases h; obtain ⟨t, h1, _⟩ := enabled s; exact ⟨t, h1⟩

def V : IOA.Automaton Act where
  St := St
  sig := sig
  start s := s = .s0
  start_nonempty := ⟨.s0, rfl⟩
  trans := TrV
  trans_acts s a t h := by cases h <;> simp [IOA.Sig.acts, sig]
  input_enabled s a h := by
    cases h; obtain ⟨t, _, h2⟩ := enabled s; exact ⟨t, h2⟩

/-- `Hid` simulates into `Vis` by sending `sA` to `sB` and `a1` to `b1`. -/
def f : St → St
  | .sA => .sB
  | .a1 => .b1
  | s => s

theorem f_ne {s : St} (h : s ≠ .s0) : f s ≠ .s0 := by
  cases s <;> simp_all [f]

theorem sim_HV : ∀ s a t, H.trans s a t → V.trans (f s) a (f t) := by
  intro s a t h
  cases h with
  | p0 => exact .p0
  | ps s hs => exact .ps _ (f_ne hs)
  | tA => exact .tB
  | tB => exact .tB
  | xA => exact .xB
  | xB => exact .xB
  | zB => exact .zB

theorem sim_VH : ∀ s a t, V.trans s a t → H.trans s a t := by
  intro s a t h
  cases h with
  | p0 => exact .p0
  | ps s hs => exact .ps s hs
  | tB => exact .tB
  | xB => exact .xB
  | zB => exact .zB

/-- **The same executions**: `Hid` and `Vis` have the same schedules of
finite executions, hence the same traces. -/
theorem same_executions (β : List Act) :
    (∃ s, IOA.Execution H β s) ↔ (∃ s, IOA.Execution V β s) :=
  ⟨fun ⟨s, hx⟩ => ⟨f s, execution_sim (N := V) f (fun s h => by
      show f s = St.s0; rw [show s = St.s0 from h]; rfl) sim_HV hx⟩,
   fun ⟨s, hx⟩ => ⟨s, execution_sim (M := V) (N := H) id (fun s h => h) sim_VH hx⟩⟩

/-- **The same projected spec**: `Hid` and `Vis` have the same pairs of
receive and reply sequences. -/
theorem same_rows (w t : List Act) :
    (∃ β s, IOA.Execution H β s ∧ recvs H β = w ∧ replies H β = t) ↔
      (∃ β s, IOA.Execution V β s ∧ recvs V β = w ∧ replies V β = t) := by
  constructor
  · rintro ⟨β, s, hx, h1, h2⟩
    exact ⟨β, f s, execution_sim (N := V) f (fun s h => by
      show f s = St.s0; rw [show s = St.s0 from h]; rfl) sim_HV hx, h1, h2⟩
  · rintro ⟨β, s, hx, h1, h2⟩
    exact ⟨β, s, execution_sim (M := V) (N := H) id (fun s h => h) sim_VH hx, h1, h2⟩

/-- In `Vis`, the only state after the reply `x` alone is `b1`. -/
def InvV : St → List Act → Prop
  | .s0, r => r = []
  | .s1, r => r = []
  | .sB, r => r = []
  | .b1, r => r = [.x]
  | .b2, r => r = [.x, .z]
  | .sA, _ => False
  | .a1, _ => False

theorem invV_run {s t : V.St} {γ : List Act} (h : IOA.Run V s γ t) :
    ∀ pre, InvV s (replies V pre) → InvV t (replies V (pre ++ γ)) := by
  induction h with
  | nil => intro pre h; simpa using h
  | @cons s s' t a γ htr _ ih =>
    intro pre hI
    have : pre ++ a :: γ = (pre ++ [a]) ++ γ := by simp
    rw [this]
    apply ih
    have hr : replies V (pre ++ [a]) = replies V pre ++ replies V [a] := replies_append _ _
    cases htr <;> simp_all [InvV, replies, V, sig]

theorem vis_b1 {β : List Act} {s : V.St} (h : IOA.Execution V β s) (hr : replies V β = [.x]) :
    s = St.b1 := by
  obtain ⟨s0, hs0, hrun⟩ := h
  have hs0' : s0 = St.s0 := hs0
  subst hs0'
  have := invV_run hrun [] rfl
  simp only [List.nil_append, hr] at this
  cases s <;> first | rfl | (exfalso; simp_all [InvV])

def xH : OutS H := ⟨[.x], by simp [H, sig]⟩
def xzH : OutS H := ⟨[.x, .z], by simp [H, sig]⟩
def xV : OutS V := ⟨[.x], by simp [V, sig]⟩
def xzV : OutS V := ⟨[.x, .z], by simp [V, sig]⟩

theorem run_a1 {s t : H.St} {γ : List Act} (h : IOA.Run H s γ t) (hs : s = St.a1) :
    replies H γ = [] := by
  induction h with
  | nil => rfl
  | @cons s s' t a γ htr _ ih =>
    subst hs
    cases htr with
    | ps _ _ =>
      have := ih rfl
      simp [replies, H, sig] at this ⊢; exact this

/-- **The internal choice is a commitment event.**  `Hid`'s system has a
history that has emitted `[x]` and whose table no longer has the row with
`[x, z]` at its current input: the internal step to `sA` narrowed it away. -/
theorem hid_narrows : ∃ l σ, Guard.Produces (sys H) (inW H []) l σ ∧
    l.foldl outStep (outW H []) = xH ∧ ¬ σ.R σ.cur xzH := by
  have hx : IOA.Execution H [.p, .τ, .x] St.a1 :=
    ⟨.s0, rfl, .cons .p0 (.cons .tA (.cons .xA (.nil _)))⟩
  obtain ⟨l, σ, hp, hm, heq, _⟩ := complete _ _ hx
  refine ⟨l, σ, hp, ?_, fun hr => ?_⟩
  · rw [corr_out hm.2.1]; exact Wd.ext (by simp [outW_val, replies, H, sig, xH])
  · obtain ⟨γ, t, hrun, _, hu⟩ := (heq _ _).1 hr
    have hv := congrArg Wd.val hu
    rw [outW_val, replies_append, run_a1 hrun rfl] at hv
    simp [replies, H, sig, xzH] at hv

/-- **`Vis` never makes that commitment.**  Every history of `Vis`'s system
that has emitted `[x]` keeps the row with `[x, z]` at its current input. -/
theorem vis_keeps {l : List (SEvent (spec V))} {σ : State (spec V)}
    (hp : Guard.Produces (sys V) (inW V []) l σ) (ho : l.foldl outStep (outW V []) = xV) :
    σ.R σ.cur xzV := by
  obtain ⟨β, s, hm⟩ := sound l σ hp
  rw [corr_out hm.2.1] at ho
  have hr : replies V β = [.x] := congrArg Wd.val ho
  have hb := vis_b1 hm.1 hr
  subst hb
  rw [matches_cur hp hm]
  refine hm.2.2 _ _ ⟨[.z], St.b2, .cons .zB (.nil _), ?_, ?_⟩
  · exact Wd.ext (by simp [inW_val, recvs_append, recvs, V, sig])
  · exact Wd.ext (by rw [outW_val, replies_append, hr]; simp [replies, V, sig, xzV])

end Hid

/-! ## Counters -/

namespace Ctr

inductive Act | inc | rep (n : Nat)

def sig : IOA.Sig Act where
  inp a := a = .inc
  out a := ∃ n, a = .rep n
  int _ := False
  inp_out a h h' := by subst h; obtain ⟨n, h'⟩ := h'; cases h'
  inp_int _ _ h := h
  out_int _ _ h := h

/-- A counter whose report carries the count at the moment it fires. -/
inductive RTr : Nat → Act → Nat → Prop
  | inc (n : Nat) : RTr n .inc (n + 1)
  | rep (n : Nat) : RTr n (.rep n) n

def Race : IOA.Automaton Act where
  St := Nat
  sig := sig
  start n := n = 0
  start_nonempty := ⟨0, rfl⟩
  trans := RTr
  trans_acts s a t h := by cases h <;> simp [IOA.Sig.acts, sig]
  input_enabled s a h := by cases h; exact ⟨_, .inc s⟩

/-- **The racing counter's projected spec is inconsistent**: after two
arrivals, it may have reported `1` (before the second arrival) or `2`. -/
theorem race_inconsistent : ¬ (spec Race).Consistent := by
  rw [not_consistent_iff]
  refine ⟨[.inc, .rep 1, .inc], (2 : Nat), [.inc, .inc, .rep 2], (2 : Nat),
    ⟨(0 : Nat), rfl, .cons (.inc 0) (.cons (.rep 1) (.cons (.inc 1) (.nil _)))⟩,
    ⟨(0 : Nat), rfl, .cons (.inc 0) (.cons (.inc 1) (.cons (.rep 2) (.nil _)))⟩,
    Wd.ext (by simp [inW_val, recvs, Race, sig]), ?_⟩
  intro h
  rcases h with h | h <;>
  · have h' := h.eq_of_length (by simp [outW_val, replies, Race, sig])
    simp [outW_val, replies, Race, sig] at h'

/-- A counter that records the count at each arrival, in state `(n, m)`
after `n` arrivals and `m` reports, and reports `m + 1` next. -/
inductive QTr : Nat × Nat → Act → Nat × Nat → Prop
  | inc (n m : Nat) : QTr (n, m) .inc (n + 1, m)
  | rep (n m : Nat) : m < n → QTr (n, m) (.rep (m + 1)) (n, m + 1)

def Queue : IOA.Automaton Act where
  St := Nat × Nat
  sig := sig
  start s := s = (0, 0)
  start_nonempty := ⟨(0, 0), rfl⟩
  trans := QTr
  trans_acts s a t h := by cases h <;> simp [IOA.Sig.acts, sig]
  input_enabled s a h := by cases h; exact ⟨_, .inc s.1 s.2⟩

/-- The reports `1, …, m`. -/
def reps : Nat → List Act
  | 0 => []
  | m + 1 => reps m ++ [.rep (m + 1)]

/-- The reports `m + 1, …, m + k`. -/
def repsFrom (m : Nat) : Nat → List Act
  | 0 => []
  | k + 1 => .rep (m + 1) :: repsFrom (m + 1) k

theorem reps_add (m k : Nat) : reps (m + k) = reps m ++ repsFrom m k := by
  induction k generalizing m with
  | zero => simp [reps, repsFrom]
  | succ k ih =>
    rw [show m + (k + 1) = (m + 1) + k by omega, ih (m + 1)]
    simp [reps, repsFrom]

theorem reps_prefix {m m' : Nat} (h : m ≤ m') : reps m <+: reps m' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [reps_add]; exact List.prefix_append _ _

theorem replies_inc (n : Nat) : replies Queue (List.replicate n .inc) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, replies, Queue, sig] at ih ⊢ <;> exact ih

theorem recvs_inc (n : Nat) : recvs Queue (List.replicate n .inc) = List.replicate n .inc := by
  apply recvs_of_inputs; intro a ha; exact (List.eq_of_mem_replicate ha)

theorem replies_repsFrom (m k : Nat) : replies Queue (repsFrom m k) = repsFrom m k := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih => simp [repsFrom, replies, Queue, sig] at ih ⊢; exact ih (m + 1)

theorem recvs_repsFrom (m k : Nat) : recvs Queue (repsFrom m k) = [] := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih => simp [repsFrom, recvs, Queue, sig] at ih ⊢; exact ih (m + 1)

theorem replies_reps (m : Nat) : replies Queue (reps m) = reps m := by
  have h : reps m = repsFrom 0 m := by simpa [reps] using reps_add 0 m
  rw [h]; exact replies_repsFrom 0 m

/-- What a state of `Queue` has received and reported. -/
theorem queue_inv {s t : Queue.St} {γ : List Act} (h : IOA.Run Queue s γ t) :
    ∀ pre, recvs Queue pre = List.replicate s.1 .inc → replies Queue pre = reps s.2 → s.2 ≤ s.1 →
      recvs Queue (pre ++ γ) = List.replicate t.1 .inc ∧ replies Queue (pre ++ γ) = reps t.2 ∧
        t.2 ≤ t.1 := by
  induction h with
  | nil => intro pre h1 h2 h3; simpa using ⟨h1, h2, h3⟩
  | @cons s s' t a γ htr _ ih =>
    intro pre h1 h2 h3
    have : pre ++ a :: γ = (pre ++ [a]) ++ γ := by simp
    rw [this]
    cases htr with
    | inc n m =>
      apply ih
      · rw [recvs_append, h1]; simp [recvs, Queue, sig, List.replicate_succ']
      · rw [replies_append, h2]; simp [replies, Queue, sig]
      · simp at h3 ⊢; omega
    | rep n m hlt =>
      apply ih
      · rw [recvs_append, h1]; simp [recvs, Queue, sig]
      · rw [replies_append, h2]; simp [replies, Queue, sig, reps]
      · show m + 1 ≤ n; omega

theorem queue_exec {β : List Act} {s : Queue.St} (h : IOA.Execution Queue β s) :
    recvs Queue β = List.replicate s.1 .inc ∧ replies Queue β = reps s.2 ∧ s.2 ≤ s.1 := by
  obtain ⟨s0, hs0, hr⟩ := h
  have hs0' : s0 = (0, 0) := hs0
  subst hs0'
  simpa using queue_inv hr [] rfl rfl (Nat.le_refl 0)

/-- **The recording counter's projected spec is consistent**: its reply
sequences are `1, …, m`, so any two are one a prefix of the other. -/
theorem queue_consistent : (spec Queue).Consistent := by
  rw [consistent_iff]
  rintro w t t' ⟨β, s, hx, _, rfl⟩ ⟨β', s', hx', _, rfl⟩
  show replies Queue β <+: replies Queue β' ∨ replies Queue β' <+: replies Queue β
  rw [(queue_exec hx).2.1, (queue_exec hx').2.1]
  rcases Nat.le_total s.2 s'.2 with h | h
  · exact Or.inl (reps_prefix h)
  · exact Or.inr (reps_prefix h)

theorem run_incs (n m k : Nat) : IOA.Run Queue (n, m) (List.replicate k .inc) (n + k, m) := by
  induction k generalizing n with
  | zero => exact .nil _
  | succ k ih =>
    rw [List.replicate_succ, show n + (k + 1) = (n + 1) + k by omega]
    exact .cons (.inc n m) (ih (n + 1))

theorem run_reps (n m k : Nat) (h : m + k ≤ n) : IOA.Run Queue (n, m) (repsFrom m k) (n, m + k) := by
  induction k generalizing m with
  | zero => exact .nil _
  | succ k ih =>
    rw [show m + (k + 1) = (m + 1) + k by omega]
    exact .cons (.rep n m (by omega)) (ih (m + 1) (by omega))

/-- **The recording counter is confluent**: every execution can receive the
remaining arrivals of `j` and report up to their number. -/
theorem queue_confluent : Confluent Queue := by
  intro fam hx j hj
  have hj' : j.val = List.replicate j.val.length .inc :=
    List.eq_replicate_iff.2 ⟨rfl, fun b hb => j.prop b hb⟩
  let N := j.val.length
  refine ⟨⟨reps N, fun a ha => ?_⟩, fun e he => ?_⟩
  · have : a ∈ replies Queue (reps N) := by rw [replies_reps]; exact ha
    exact (mem_replies.1 this).2
  · rcases e with ⟨β, n, m⟩
    obtain ⟨h1, h2, h3⟩ := queue_exec (hx _ he)
    have hle := hj _ he
    change recvs Queue β <+: j.val at hle
    change recvs Queue β = List.replicate n .inc at h1
    change replies Queue β = reps m at h2
    change m ≤ n at h3
    rw [h1, hj'] at hle
    have hn : n ≤ N := by simpa using hle.length_le
    refine ⟨List.replicate (N - n) .inc ++ repsFrom m (N - m), ((N, N) : Nat × Nat),
      (IOA.run_append_iff _ _).2 ⟨((N, m) : Nat × Nat), ?_, ?_⟩, ?_, ?_⟩
    · have := run_incs n m (N - n); rwa [show n + (N - n) = N by omega] at this
    · have := run_reps N m (N - m) (by omega); rwa [show m + (N - m) = N by omega] at this
    · apply Wd.ext
      rw [inW_val, recvs_append, recvs_append, h1, recvs_inc, recvs_repsFrom, hj',
        List.append_nil, List.replicate_append_replicate]
      congr 1; omega
    · apply Wd.ext
      rw [outW_val, replies_append, replies_append, h2, replies_inc, replies_repsFrom,
        List.nil_append, ← reps_add]
      congr 1; omega

/-- The rule "after `n` arrivals, the reports `1, …, n`". -/
def allReported : Spec (InS Queue) (OutS Queue) where
  P w t := t.val = reps w.val.length
  total w := ⟨⟨reps w.val.length, fun a ha => by
      have : a ∈ replies Queue (reps w.val.length) := by rw [replies_reps]; exact ha
      exact (mem_replies.1 this).2⟩, rfl⟩

/-- **A declared spec for the recording counter**: the rule "after `n`
arrivals, the reports `1, …, n`" satisfies realizability and domination, so it
is consistent exactly when the projected spec is (and both are). -/
theorem queue_declared :
    CofinalAlong id allReported (spec Queue) ∧ allReported.Consistent := by
  have hc : CofinalAlong id allReported (spec Queue) := Cofinal.along
    { real := fun w t ht => by
        have hw : w.val = List.replicate w.val.length .inc :=
          List.eq_replicate_iff.2 ⟨rfl, fun b hb => w.prop b hb⟩
        let N := w.val.length
        have h1 := run_incs 0 0 N
        have h2 := run_reps N 0 N (by omega)
        rw [Nat.zero_add] at h1 h2
        refine ⟨List.replicate N .inc ++ repsFrom 0 N, ((N, N) : Nat × Nat),
          ⟨((0, 0) : Nat × Nat), rfl, (IOA.run_append_iff _ _).2 ⟨((N, 0) : Nat × Nat), h1, h2⟩⟩, ?_, ?_⟩
        · apply Wd.ext
          rw [inW_val, recvs_append, recvs_inc, recvs_repsFrom, List.append_nil]
          exact hw.symm
        · apply Wd.ext
          rw [outW_val, replies_append, replies_inc, replies_repsFrom, List.nil_append, ht]
          have := reps_add 0 N
          simp only [Nat.zero_add, reps, List.nil_append] at this
          exact this.symm
      dom := fun w t ⟨β, s, hx, hw, ht⟩ => by
        obtain ⟨h1, h2, h3⟩ := queue_exec hx
        refine ⟨⟨reps w.val.length, fun a ha => by
          have : a ∈ replies Queue (reps w.val.length) := by rw [replies_reps]; exact ha
          exact (mem_replies.1 this).2⟩, rfl, ?_⟩
        rw [← ht]
        show replies Queue β <+: reps w.val.length
        rw [h2, ← hw]
        show reps s.2 <+: reps (recvs Queue β).length
        rw [h1, List.length_replicate]
        exact reps_prefix h3 }
  exact ⟨hc, (declared id allReported hc).2 queue_consistent⟩

/-! ### Neither obligation of a declared spec suffices alone -/

/-- The declared spec that allows no replies at all. -/
def noReplies (M : IOA.Automaton Act) : Spec (InS M) (OutS M) where
  P _ t := t.val = []
  total _ := ⟨⟨[], fun _ h => by cases h⟩, rfl⟩

/-- The declared spec that allows every reply sequence. -/
def allReplies (M : IOA.Automaton Act) : Spec (InS M) (OutS M) where
  P _ _ := True
  total _ := ⟨⟨[], fun _ h => by cases h⟩, trivial⟩

/-- **Realizability alone does not suffice**: allowing no replies is
realizable for the racing counter and is consistent, but the racing counter's
projected spec is not. -/
theorem realizability_alone :
    (∀ w t, (noReplies Race).P w t → (spec Race).P w t) ∧ (noReplies Race).Consistent ∧
      ¬ (spec Race).Consistent := by
  refine ⟨fun w t ht => ?_, ?_, race_inconsistent⟩
  · have : t = outW Race [] := Wd.ext ht
    rw [this]; exact row_inputs w
  · rw [complete_calm]
    intro i j _ X _ hX
    exact ⟨⟨[], fun _ h => by cases h⟩, rfl, fun x hx => by
      show x.val <+: []; rw [hX x hx]; exact List.prefix_refl _⟩

/-- **Domination alone does not suffice**: allowing every reply sequence
dominates the recording counter, whose projected spec is consistent, but it
is not consistent itself. -/
theorem domination_alone :
    (∀ w t, (spec Queue).P w t → ∃ u, (allReplies Queue).P w u ∧ t ≼ u) ∧
      ¬ (allReplies Queue).Consistent ∧ (spec Queue).Consistent := by
  refine ⟨fun w t _ => ⟨t, trivial, PO.refl t⟩, fun h => ?_, queue_consistent⟩
  rw [complete_calm, liftedMono_iff_relMono_directed] at h
  let w0 : InS Queue := ⟨[], fun _ h => by cases h⟩
  let t1 : OutS Queue := ⟨[.rep 1], by simp [Queue, sig]⟩
  let t2 : OutS Queue := ⟨[.rep 2], by simp [Queue, sig]⟩
  obtain ⟨u, _, hall⟩ := h.2 w0 [t1, t2] (by simp) (fun _ _ => trivial)
  rcases prefix_comparable (hall t1 (by simp)) (hall t2 (by simp)) with h | h <;>
  · have h' := h.eq_of_length (by simp [t1, t2])
    simp [t1, t2] at h'

end Ctr

end IOT
end CC
