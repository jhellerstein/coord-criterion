import CoordCriterion.Instances.IOMachine

/-!
# Local proof obligations for Lifted Monotonicity of a machine automaton

The specification `spec k G` of `Instances/IOMachine.lean` is defined by all
finite executions of the composed system, so Lifted Monotonicity cannot be
established by enumerating them.  This file gives *local* proof obligations
on the transitions of the machine automaton `G` alone, in the style of a
simulation proof: each obligation quantifies over one state, or two related
states, and a bounded number of transitions (at most four, for the
commutation diamond).  They imply Lifted Monotonicity (and
hence consistency) of `spec k G` for both channel disciplines
(`liftedMono_of_obligations`).

The obligations (`Obligations G I le`) are stated relative to an inductive
invariant `I` and a preorder `le` on machine states (the prover's choice, as
in a simulation proof; for a state-based CRDT `le` is the lattice order).  An
*internal step* (`IStep`) is an output to some client or an internal action.
For states satisfying `I`:

* `obs_mono`: `q ≤ q'` implies `obs q ≼ obs q'`;
* `recv_up`, `int_up`: every step goes up in `le`;
* `recv_mono`: receiving the same payload at related states gives related
  states (for every pair of successors, so receives are deterministic up to
  `le`);
* `int_sim`: an internal step at `q ≤ q'` is matched by internal steps at
  `q'`;
* `recv_comm`: two receives commute up to `le`;
* `int_recv`: an internal step can be postponed past a receive, up to `le`.

The proof never re-orders the given execution `β`: it extends `β` by internal
and output steps only (which leave its input unchanged, `extend_int`), and
shows by a normal-form argument on machine runs (`Obligations.dominate`) that
some such extension ends above every state of a finite family of executions
whose inputs `β` expands.  Hence the channel discipline and the clients'
reactions to outputs play no role, which is also why the obligations are
conservative.

Coverage (honest scope):

* The obligations are sufficient, not necessary.  `dip` satisfies Lifted
  Monotonicity over either channel but no invariant and preorder satisfy the
  obligations: an internal step lowers the observation and a later one
  raises it above everything (`dip_liftedMono`, `dip_not_obligations`).
  `log` (append each payload to a list, prefix order) is consistent with a
  single client over FIFO, where arrival order is fixed, yet violates the
  commutation obligation for every choice (`log_fifo_liftedMono`,
  `log_not_obligations`); over a bag it is not consistent
  (`log_bag_not_liftedMono`).
* A positive instance whose outputs change state and whose fibers are
  infinite: `cnt` (sum of received numbers, and the count of outputs)
  satisfies the obligations (`cnt_obligations`, `cnt_liftedMono`).

Testing side: a violation of Lifted Monotonicity is witnessed by finitely
many executions and one execution `β` whose input expands theirs, such that
no execution with the input of `β` refines them all
(`not_liftedMono_iff_witness`).  The last clause quantifies over all
executions with that input.  It is implied by a check over the machine
automaton's own runs on arrival orders of that input
(`not_liftedMono_of_machine_cert`, by `fiber_sub_run`), or over any finite list
of values containing the fiber (`not_liftedMono_of_fiber_list`).
-/

namespace CC
namespace IOM
open IOA

variable {C P Q O : Type}

/-! ### Machine runs -/

/-- One internal step of the machine: an output to some client, or an
internal action. -/
def IStep (G : Machine C P Q O) (q q' : Q) : Prop := (∃ c o, G.out q c o q') ∨ G.tau q q'

/-- `MRun G q w q'`: the machine goes from `q` to `q'` receiving the payloads
`w` in order, interleaved with internal steps.  `MRun G q [] q'` is a run of
internal steps only. -/
inductive MRun (G : Machine C P Q O) : Q → List P → Q → Prop where
  | nil (q : Q) : MRun G q [] q
  | int {q q1 q2 : Q} {w : List P} : IStep G q q1 → MRun G q1 w q2 → MRun G q w q2
  | recv {q q1 q2 : Q} {p : P} {w : List P} : G.recv q p q1 → MRun G q1 w q2 →
      MRun G q (p :: w) q2

/-- Receives only. -/
inductive RRun (G : Machine C P Q O) : Q → List P → Q → Prop where
  | nil (q : Q) : RRun G q [] q
  | recv {q q1 q2 : Q} {p : P} {w : List P} : G.recv q p q1 → RRun G q1 w q2 →
      RRun G q (p :: w) q2

section runs
variable {G : Machine C P Q O}

theorem MRun.append {a b c : Q} {u v : List P} (h1 : MRun G a u b) (h2 : MRun G b v c) :
    MRun G a (u ++ v) c := by
  induction h1 with
  | nil => exact h2
  | int hs _ ih => exact .int hs (ih h2)
  | recv hs _ ih => exact .recv hs (ih h2)

theorem RRun.toM {a b : Q} {w : List P} (h : RRun G a w b) : MRun G a w b := by
  induction h with
  | nil => exact .nil _
  | recv hs _ ih => exact .recv hs ih

theorem rrun_exists (G : Machine C P Q O) : ∀ (q : Q) (w : List P), ∃ q', RRun G q w q'
  | q, [] => ⟨q, .nil q⟩
  | q, p :: w => by
    obtain ⟨q1, h1⟩ := G.recv_enabled q p
    obtain ⟨q2, h2⟩ := rrun_exists G q1 w
    exact ⟨q2, .recv h1 h2⟩

end runs

/-! ### The obligations -/

/-- **Local proof obligations** for a machine automaton `G`, relative to an
invariant `I` and a preorder `le` on states.  Each field quantifies over one
or two states and at most four transitions; the fields other than the
preorder laws need hold only at states satisfying `I`.  Since `recv_mono`
applies to every pair of successors, receives are deterministic up to `le`
in both directions. -/
structure Obligations [PO O] (G : Machine C P Q O) (I : Q → Prop) (le : Q → Q → Prop) :
    Prop where
  le_refl : ∀ q, le q q
  le_trans : ∀ {q1 q2 q3}, le q1 q2 → le q2 q3 → le q1 q3
  inv_start : I G.q0
  inv_recv : ∀ {q p q'}, I q → G.recv q p q' → I q'
  inv_int : ∀ {q q'}, I q → IStep G q q' → I q'
  /-- Observations are monotone in `le`. -/
  obs_mono : ∀ {q q'}, I q → I q' → le q q' → G.obs q ≼ G.obs q'
  /-- Receives go up. -/
  recv_up : ∀ {q p q'}, I q → G.recv q p q' → le q q'
  /-- Internal steps go up. -/
  int_up : ∀ {q q'}, I q → IStep G q q' → le q q'
  /-- Receiving the same payload at related states gives related states. -/
  recv_mono : ∀ {q q' p q1 q1'}, I q → I q' → le q q' → G.recv q p q1 → G.recv q' p q1' →
    le q1 q1'
  /-- An internal step below is matched by internal steps above. -/
  int_sim : ∀ {q q' q1}, I q → I q' → le q q' → IStep G q q1 →
    ∃ q1', MRun G q' [] q1' ∧ le q1 q1'
  /-- Receives commute up to `le`. -/
  recv_comm : ∀ {q p p' q1 q2 q1' q2'}, I q → G.recv q p q1 → G.recv q1 p' q2 →
    G.recv q p' q1' → G.recv q1' p q2' → le q2 q2'
  /-- An internal step can be postponed past a receive, up to `le`. -/
  int_recv : ∀ {q q1 p q2 q1'}, I q → IStep G q q1 → G.recv q1 p q2 → G.recv q p q1' →
    ∃ q2', MRun G q1' [] q2' ∧ le q2 q2'

namespace Obligations
variable [PO O] {G : Machine C P Q O} {I : Q → Prop} {le : Q → Q → Prop}
  (H : Obligations G I le)
include H

theorem inv_mrun {a b : Q} {w : List P} (h : MRun G a w b) (ha : I a) : I b := by
  induction h with
  | nil => exact ha
  | int hs _ ih => exact ih (H.inv_int ha hs)
  | recv hs _ ih => exact ih (H.inv_recv ha hs)

theorem inv_rrun {a b : Q} {w : List P} (h : RRun G a w b) (ha : I a) : I b :=
  H.inv_mrun h.toM ha

theorem up_mrun {a b : Q} {w : List P} (h : MRun G a w b) (ha : I a) : le a b := by
  induction h with
  | nil => exact H.le_refl _
  | int hs _ ih => exact H.le_trans (H.int_up ha hs) (ih (H.inv_int ha hs))
  | recv hs _ ih => exact H.le_trans (H.recv_up ha hs) (ih (H.inv_recv ha hs))

/-- Receives simulate receives. -/
theorem sim_rrun {s s' : Q} {w : List P} (h : RRun G s w s') :
    ∀ {t}, I s → I t → le s t → ∃ t', RRun G t w t' ∧ le s' t' := by
  induction h with
  | nil => intro t _ _ hle; exact ⟨t, .nil t, hle⟩
  | @recv s s1 _ p _ hs _ ih =>
    intro t hs0 ht hle
    obtain ⟨t1, ht1⟩ := G.recv_enabled t p
    obtain ⟨t', h', hl⟩ := ih (H.inv_recv hs0 hs) (H.inv_recv ht ht1) (H.recv_mono hs0 ht hle hs ht1)
    exact ⟨t', .recv ht1 h', hl⟩

/-- Internal steps simulate internal steps. -/
theorem sim_int {s s' : Q} (h : MRun G s [] s') :
    ∀ {t}, I s → I t → le s t → ∃ t', MRun G t [] t' ∧ le s' t' := by
  generalize hw : ([] : List P) = w at h
  induction h with
  | nil => intro t _ _ hle; exact ⟨t, .nil t, hle⟩
  | int hs _ ih =>
    intro t hs0 ht hle
    obtain ⟨t1, ht1, hl1⟩ := H.int_sim hs0 ht hle hs
    obtain ⟨t', h', hl⟩ := ih hw (H.inv_int hs0 hs) (H.inv_mrun ht1 ht) hl1
    exact ⟨t', ht1.append h', hl⟩
  | recv _ _ _ => cases hw

/-- Internal steps can be pushed past a sequence of receives. -/
theorem push : ∀ (w : List P) {s s1 a : Q}, I s → MRun G s [] s1 → RRun G s1 w a →
    ∃ a' b', RRun G s w a' ∧ MRun G a' [] b' ∧ le a b'
  | [], s, s1, a, _, h1, h2 => by
    cases h2
    exact ⟨s, s1, .nil s, h1, H.le_refl _⟩
  | p :: w, s, s1, a, hs, h1, h2 => by
    have one : ∀ {s s1 a : Q}, I s → IStep G s s1 → RRun G s1 (p :: w) a →
        ∃ a' b', RRun G s (p :: w) a' ∧ MRun G a' [] b' ∧ le a b' := by
      intro s s1 a hs hst hr
      cases hr with
      | recv h1 hr' =>
        obtain ⟨d, hd⟩ := G.recv_enabled s p
        obtain ⟨e, he, hce⟩ := H.int_recv hs hst h1 hd
        have hc := H.inv_recv (H.inv_int hs hst) h1
        have hd' := H.inv_recv hs hd
        obtain ⟨a2, ha2, haa2⟩ := H.sim_rrun hr' hc (H.inv_mrun he hd') hce
        obtain ⟨a', b', h1', h2', h3'⟩ := push w hd' he ha2
        exact ⟨a', b', .recv hd h1', h2', H.le_trans haa2 h3'⟩
    generalize hv : ([] : List P) = v at h1
    induction h1 generalizing a with
    | nil => exact ⟨a, a, h2, .nil a, H.le_refl _⟩
    | @int s s2 _ _ hst _ ih =>
      subst hv
      obtain ⟨a'', b'', h1'', h2'', h3''⟩ := ih a (H.inv_int hs hst) h2 rfl
      obtain ⟨a', b', h1', h2', h3'⟩ := one hs hst h1''
      have ha'' := H.inv_rrun h1'' (H.inv_int hs hst)
      have ha' := H.inv_rrun h1' hs
      obtain ⟨b3, hb3, hl3⟩ := H.sim_int h2'' ha'' (H.inv_mrun h2' ha') h3'
      exact ⟨a', b3, h1', h2'.append hb3, H.le_trans h3'' hl3⟩
    | recv _ _ _ => cases hv

/-- **Normal form.**  Every run is dominated by a run that receives the same
payloads first, in the same order, and then takes internal steps. -/
theorem normalize {s s' : Q} {w : List P} (h : MRun G s w s') (hs : I s) :
    ∃ a b, RRun G s w a ∧ MRun G a [] b ∧ le s' b := by
  induction h with
  | nil q => exact ⟨q, q, .nil q, .nil q, H.le_refl q⟩
  | @int s s1 _ w hst _ ih =>
    obtain ⟨a, b, hr, hm, hle⟩ := ih (H.inv_int hs hst)
    obtain ⟨a', b', hr', hm', hle'⟩ := H.push w hs (.int hst (.nil _)) hr
    have ha := H.inv_rrun hr (H.inv_int hs hst)
    obtain ⟨b'', hm'', hle''⟩ := H.sim_int hm ha (H.inv_mrun hm' (H.inv_rrun hr' hs)) hle'
    exact ⟨a', b'', hr', hm'.append hm'', H.le_trans hle hle''⟩
  | recv hst _ ih =>
    obtain ⟨a, b, hr, hm, hle⟩ := ih (H.inv_recv hs hst)
    exact ⟨a, b, .recv hst hr, hm, hle⟩

/-- Receives may be permuted, up to `le`. -/
theorem perm_rrun {w w' : List P} (hp : w.Perm w') :
    ∀ {s a : Q}, I s → RRun G s w a → ∃ a', RRun G s w' a' ∧ le a a' := by
  induction hp with
  | nil => intro s a _ h; exact ⟨a, h, H.le_refl a⟩
  | cons x _ ih =>
    intro s a hs h
    cases h with
    | recv h1 h2 =>
      obtain ⟨a', h', hl⟩ := ih (H.inv_recv hs h1) h2
      exact ⟨a', .recv h1 h', hl⟩
  | swap x y l =>
    intro s a hs h
    cases h with
    | recv h1 h2 =>
      cases h2 with
      | recv h3 h4 =>
        obtain ⟨t1, ht1⟩ := G.recv_enabled s x
        obtain ⟨t2, ht2⟩ := G.recv_enabled t1 y
        have hle := H.recv_comm hs h1 h3 ht1 ht2
        obtain ⟨a', h', hl⟩ := H.sim_rrun h4 (H.inv_recv (H.inv_recv hs h1) h3)
          (H.inv_recv (H.inv_recv hs ht1) ht2) hle
        exact ⟨a', .recv ht1 (.recv ht2 h'), hl⟩
  | trans _ _ ih1 ih2 =>
    intro s a hs h
    obtain ⟨a1, h1, l1⟩ := ih1 hs h
    obtain ⟨a2, h2, l2⟩ := ih2 hs h1
    exact ⟨a2, h2, H.le_trans l1 l2⟩

/-- Receiving `w` first ends below any run receiving `w` from above. -/
theorem rrun_le_mrun {t q : Q} {w : List P} (h : MRun G t w q) :
    ∀ {s a : Q}, I s → I t → le s t → RRun G s w a → le a q := by
  induction h with
  | nil => intro s a _ _ hst hr; cases hr; exact hst
  | int hst' _ ih =>
    intro s a hs ht hle hr
    exact ih hs (H.inv_int ht hst') (H.le_trans hle (H.int_up ht hst')) hr
  | recv h1 _ ih =>
    intro s a hs ht hle hr
    cases hr with
    | recv h2 hr' =>
      exact ih (H.inv_recv hs h2) (H.inv_recv ht h1) (H.recv_mono hs ht hle h2 h1) hr'

/-- **Domination.**  If a run from the start receives `w`, and another
receives a sub-multiset `wr` of `w`, then internal steps extend the first to
a state above the end of the second. -/
theorem dominate {w wr rest : List P} {q qr : Q} (h : MRun G G.q0 w q)
    (hr : MRun G G.q0 wr qr) (hp : (wr ++ rest).Perm w) :
    ∃ q', MRun G q [] q' ∧ le qr q' := by
  have h0 := H.inv_start
  obtain ⟨a, b, ha, hb, hle⟩ := H.normalize hr h0
  have hb' := H.inv_mrun hb (H.inv_rrun ha h0)
  obtain ⟨c, hc⟩ := rrun_exists G b rest
  have hbc := H.up_mrun hc.toM hb'
  have hm : MRun G G.q0 (wr ++ rest) c := ha.toM.append (hb.append hc.toM)
  obtain ⟨a2, b2, ha2, hb2, hle2⟩ := H.normalize hm h0
  obtain ⟨a3, ha3, hle3⟩ := H.perm_rrun hp h0 ha2
  have ha3' := H.inv_rrun ha3 h0
  obtain ⟨b3, hb3, hle4⟩ := H.sim_int hb2 (H.inv_rrun ha2 h0) ha3' hle3
  have hq := H.rrun_le_mrun h h0 h0 (H.le_refl _) ha3
  obtain ⟨q', hq', hle5⟩ := H.sim_int hb3 ha3' (H.inv_mrun h h0) hq
  exact ⟨q', hq', H.le_trans hle (H.le_trans hbc (H.le_trans hle2 (H.le_trans hle4 hle5)))⟩

/-- Domination of a finite family at once. -/
theorem dominate_all {w : List P} {q : Q} (h : MRun G G.q0 w q) :
    ∀ fam : List (List P × Q), (∀ r ∈ fam, MRun G G.q0 r.1 r.2 ∧ ∃ rest, (r.1 ++ rest).Perm w) →
      ∃ q', MRun G q [] q' ∧ ∀ r ∈ fam, le r.2 q'
  | [], _ => ⟨q, .nil q, fun _ h => nomatch h⟩
  | r :: fam, hf => by
    obtain ⟨q1, hq1, hall⟩ := dominate_all h fam fun r hr => hf r (List.mem_cons_of_mem _ hr)
    have h1 : MRun G G.q0 w q1 := by simpa using h.append hq1
    obtain ⟨hr, rest, hp⟩ := hf r (List.mem_cons_self ..)
    obtain ⟨q', hq', hle⟩ := H.dominate h1 hr hp
    have hup := H.up_mrun hq' (H.inv_mrun h1 H.inv_start)
    refine ⟨q', hq1.append hq', fun r' hr' => ?_⟩
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact hle
    · exact H.le_trans (hall r' hr') hup

end Obligations

/-! ### From the machine to the system -/

section system
variable [DecidableEq C] {k : ChanKind} {G : Machine C P Q O}

omit [DecidableEq C] in
/-- A run of the machine automaton is a machine run on the payloads it
receives. -/
theorem mrun_of_run :
    ∀ {q q' : Q} {γ : List (Act C P O)}, Run (machA G) q γ q' →
      MRun G q ((recvs γ).map Ev.payload) q'
  | _, _, [], .nil _ => .nil _
  | _, _, a :: γ, .cons ht hr => by
    cases a with
    | send => exact ht.elim
    | recv e => exact .recv ht (mrun_of_run hr)
    | out c o => simpa using MRun.int (Or.inl ⟨c, o, ht⟩) (mrun_of_run hr)
    | tau => simpa using MRun.int (Or.inr ht) (mrun_of_run hr)

theorem mrun_of_reach {β : List (Act C P O)} {f : Flat C P Q} (h : Reach k G β f) :
    MRun G G.q0 ((recvs β).map Ev.payload) f.q := by
  have := mrun_of_run (reach_inv β f h).runs
  rwa [recvs_macts] at this

omit [DecidableEq C] in
/-- Appending an internal step does not change the input. -/
theorem input_snoc_tau (β : List (Act C P O)) : input (β ++ [.tau]) = input β := by
  have hs : ∀ i e, SendAt (β ++ [.tau]) i e ↔ SendAt β i e := fun _ _ => sendAt_snoc nofun
  have hr : ∀ e, Act.recv e ∈ β ++ [.tau] ↔ Act.recv e ∈ β := by simp
  refine Inp.ext' (funext fun e => propext (hr e)) (funext fun a => funext fun b => propext ?_)
  constructor
  · rintro ⟨⟨ha, hb⟩, i, j, hi, hj, hij⟩
    have hj' := (hs j b).1 hj
    exact ⟨⟨(hr a).1 ha, (hr b).1 hb⟩, i, j, (hs i a).1 hi, hj',
      (hb_append (sendAt_lt hj')).1 hij⟩
  · rintro ⟨⟨ha, hb⟩, i, j, hi, hj, hij⟩
    exact ⟨⟨(hr a).2 ha, (hr b).2 hb⟩, i, j, (hs i a).2 hi, (hs j b).2 hj,
      (hb_append (sendAt_lt hj)).2 hij⟩

/-- **Extension by internal steps.**  Internal steps of the machine extend
an execution without changing its input. -/
theorem extend_int {q q' : Q} (hm : MRun G q [] q') :
    ∀ {β : List (Act C P O)} {f : Flat C P Q}, Reach k G β f → f.q = q →
      ∃ γ f', Reach k G (β ++ γ) f' ∧ input (β ++ γ) = input β ∧ f'.q = q' := by
  generalize hw : ([] : List P) = w at hm
  induction hm with
  | nil => intro β f hr hq; exact ⟨[], f, by simpa using hr, by simp, hq⟩
  | @int q q1 _ _ hs _ ih =>
    intro β f hr hq
    rcases hs with ⟨c, o, ho⟩ | ht
    · have hr1 : Reach k G (β ++ [.out c o]) ⟨q1, f.cnt, f.ch⟩ :=
        reach_snoc.2 ⟨f, hr, FStep.out f c o q1 (hq ▸ ho)⟩
      obtain ⟨γ, f', hf', hi, hq'⟩ := ih hw hr1 rfl
      refine ⟨.out c o :: γ, f', by simpa using hf', ?_, hq'⟩
      have : β ++ Act.out c o :: γ = (β ++ [.out c o]) ++ γ := by simp
      rw [this, hi, input_snoc_out]
    · have hr1 : Reach k G (β ++ [.tau]) ⟨q1, f.cnt, f.ch⟩ :=
        reach_snoc.2 ⟨f, hr, FStep.tau f q1 (hq ▸ ht)⟩
      obtain ⟨γ, f', hf', hi, hq'⟩ := ih hw hr1 rfl
      refine ⟨.tau :: γ, f', by simpa using hf', ?_, hq'⟩
      have : β ++ Act.tau :: γ = (β ++ [.tau]) ++ γ := by simp
      rw [this, hi, input_snoc_tau]
  | recv _ _ _ => cases hw

/-- If one input expands another, the payloads received in the first
execution are a sub-multiset of those received in the second. -/
theorem perm_of_input_le {β β' : List (Act C P O)} {f f' : Flat C P Q}
    (hr : Reach k G β f) (hr' : Reach k G β' f') (hle : input β ≼ input β') :
    ∃ rest, ((recvs β).map Ev.payload ++ rest).Perm ((recvs β').map Ev.payload) := by
  classical
  have n1 := recvs_nodup hr
  have n2 := recvs_nodup hr'
  have hsub : ∀ x ∈ recvs β, x ∈ recvs β' := fun x hx =>
    mem_recvs.2 (hle.1 x (mem_recvs.1 hx))
  let restE := (recvs β').filter fun x => decide (x ∉ recvs β)
  have hp : (recvs β ++ restE).Perm (recvs β') := by
    refine (List.perm_ext_iff_of_nodup ?_ n2).2 fun a => ?_
    · refine List.nodup_append.2 ⟨n1, n2.sublist List.filter_sublist, fun a ha b hb => ?_⟩
      have := (List.mem_filter.1 hb).2
      simp only [decide_eq_true_eq] at this
      exact fun h => this (h ▸ ha)
    · simp only [List.mem_append, restE, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro (h | h)
        · exact hsub a h
        · exact h.1
      · intro h
        by_cases ha : a ∈ recvs β
        · exact Or.inl ha
        · exact Or.inr ⟨h, ha⟩
  exact ⟨restE.map Ev.payload, by simpa using hp.map Ev.payload⟩

/-- **Local obligations imply confluence across executions** (either
channel). -/
theorem obsConfluent_of_obligations [PO O] (k : ChanKind) {I : Q → Prop} {le : Q → Q → Prop}
    (H : Obligations G I le) : ObsConfluent (C := C) k G := by
  intro fam hfam β s hx hle
  have hr : Reach k G β (toFlat s) := ⟨s, hx, rfl⟩
  obtain ⟨q', hq', hall⟩ := H.dominate_all (mrun_of_reach hr)
    (fam.map fun r => ((recvs r.1).map Ev.payload, r.2 .mach)) (by
      intro r hr'
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr'
      have hR : Reach k G r0.1 (toFlat r0.2) := ⟨r0.2, hfam r0 hr0, rfl⟩
      exact ⟨mrun_of_reach hR, perm_of_input_le hR hr (hle r0 hr0)⟩)
  obtain ⟨γ, f', ⟨s', hx', hs'⟩, hi, hq⟩ := extend_int hq' hr rfl
  refine ⟨β ++ γ, s', hx', hi, fun r hr' => ?_⟩
  have hl := hall _ (List.mem_map_of_mem hr')
  have hm : s' .mach = q' := by rw [← hq, ← hs']; rfl
  rw [hm]
  have hR : Reach k G r.1 (toFlat r.2) := ⟨r.2, hfam r hr', rfl⟩
  exact H.obs_mono (H.inv_mrun (mrun_of_reach hR) H.inv_start)
    (H.inv_mrun hq' (H.inv_mrun (mrun_of_reach hr) H.inv_start)) hl

/-- **Local obligations imply Lifted Monotonicity and consistency.**  If the
machine automaton `G` satisfies `Obligations G I le` for some invariant `I`
and preorder `le`, the induced specification over a bag or a FIFO channel
satisfies Lifted Monotonicity, and is therefore consistent. -/
theorem liftedMono_of_obligations [PO O] (k : ChanKind) {I : Q → Prop} {le : Q → Q → Prop}
    (H : Obligations G I le) :
    (spec (C := C) k G).LiftedMono ∧ (spec (C := C) k G).Consistent := by
  have hL := (confluent_iff_liftedMono k G).1.1 (obsConfluent_of_obligations k H)
  exact ⟨hL, (confluent_iff_liftedMono k G).2.2 hL⟩

end system

/-! ### Testing: finite witnesses of a violation -/

section testing
variable [PO O] (k : ChanKind) (G : Machine C P Q O)

/-- **A violation is witnessed by finitely many executions and one input.**
Lifted Monotonicity fails iff there are finitely many executions `βᵣ` and an
execution `β` whose input expands each of theirs, such that no execution
with the input of `β` ends with an observation refining every `βᵣ`'s.  The
last clause ranges over all executions with that input. -/
theorem not_liftedMono_iff_witness :
    ¬ (spec (C := C) k G).LiftedMono ↔
      ∃ fam : List (List (Act C P O) × (sys (C := C) k G).St),
        (∀ r ∈ fam, Execution (sys k G) r.1 r.2) ∧
        ∃ β s, Execution (sys k G) β s ∧ (∀ r ∈ fam, input r.1 ≼ input β) ∧
          ∀ β' s', Execution (sys k G) β' s' → input β' = input β →
            ∃ r ∈ fam, ¬ G.obs (r.2 .mach) ≼ G.obs (s' .mach) := by
  rw [← (confluent_iff_liftedMono k G).1]
  constructor
  · intro hn
    refine Classical.byContradiction fun hne => hn ?_
    intro fam hfam β s hx hle
    refine Classical.byContradiction fun hno => hne ⟨fam, hfam, β, s, hx, hle, ?_⟩
    intro β' s' hx' hi'
    refine Classical.byContradiction fun hall => hno ⟨β', s', hx', hi', fun r hr => ?_⟩
    exact Classical.byContradiction fun h => hall ⟨r, hr, h⟩
  · rintro ⟨fam, hfam, β, s, hx, hle, hno⟩ hO
    obtain ⟨β', s', hx', hi', hall⟩ := hO fam hfam β s hx hle
    obtain ⟨r, hr, hn⟩ := hno β' s' hx' hi'
    exact hn (hall r hr)

/-- **A finite list containing the fiber suffices.**  If every execution
with the input of `β` ends with an observation in the list `L`, and every
element of `L` fails to refine some `βᵣ`'s observation, Lifted Monotonicity
fails. -/
theorem not_liftedMono_of_fiber_list
    (fam : List (List (Act C P O) × (sys (C := C) k G).St))
    (hfam : ∀ r ∈ fam, Execution (sys k G) r.1 r.2) {β : List (Act C P O)}
    {s : (sys (C := C) k G).St} (hx : Execution (sys k G) β s)
    (hle : ∀ r ∈ fam, input r.1 ≼ input β) (L : List O)
    (hL : ∀ β' s', Execution (sys (C := C) k G) β' s' → input β' = input β → G.obs (s' .mach) ∈ L)
    (hcert : ∀ u ∈ L, ∃ r ∈ fam, ¬ G.obs (r.2 .mach) ≼ u) :
    ¬ (spec (C := C) k G).LiftedMono :=
  (not_liftedMono_iff_witness k G).2 ⟨fam, hfam, β, s, hx, hle, fun β' s' hx' hi' =>
    hcert _ (hL β' s' hx' hi')⟩

/-- **A check over the machine's own runs suffices.**  If every run of the
machine automaton that receives the events of `input β`, each once, in some
order (for FIFO, a linear extension of the input order), interleaved with
any internal and output steps, ends with an observation that fails to refine
some `βᵣ`'s, Lifted Monotonicity fails.  These runs over-approximate the
fiber (`fiber_sub_run`); for a finite-state machine they reach finitely many
states. -/
theorem not_liftedMono_of_machine_cert [DecidableEq C]
    (fam : List (List (Act C P O) × (sys (C := C) k G).St))
    (hfam : ∀ r ∈ fam, Execution (sys k G) r.1 r.2) {β : List (Act C P O)}
    {s : (sys (C := C) k G).St} (hx : Execution (sys k G) β s)
    (hle : ∀ r ∈ fam, input r.1 ≼ input β)
    (hcert : ∀ γ q, Execution (machA G) γ q → (recvs γ).Nodup →
      (∀ e, e ∈ recvs γ ↔ (input β).mem e) →
      (k = .fifo → (recvs γ).Pairwise fun a b => ¬ (input β).lt b a) →
      ∃ r ∈ fam, ¬ G.obs (r.2 .mach) ≼ G.obs q) :
    ¬ (spec (C := C) k G).LiftedMono := by
  refine (not_liftedMono_iff_witness k G).2 ⟨fam, hfam, β, s, hx, hle, fun β' s' hx' hi' => ?_⟩
  obtain ⟨γ, q, hγ, ho, hn, hm, hf⟩ :=
    fiber_sub_run (k := k) (G := G) ⟨input β, β, s, hx, rfl⟩ (G.obs (s' .mach))
      ⟨β', s', hx', hi', rfl⟩
  rw [← ho]
  exact hcert γ q hγ hn hm hf

end testing

/-! ### Examples -/

section examples

/-- `Nat` under `≤` (a local instance for the examples). -/
@[instance_reducible] def natPO : PO Nat where
  le := Nat.le
  refl := Nat.le_refl
  trans := Nat.le_trans
  antisymm := Nat.le_antisymm

/-- Pairs of naturals under the componentwise order (a local instance for
the examples). -/
@[instance_reducible] def pairPO : PO (Nat × Nat) where
  le a b := a.1 ≤ b.1 ∧ a.2 ≤ b.2
  refl _ := ⟨Nat.le_refl _, Nat.le_refl _⟩
  trans h1 h2 := ⟨Nat.le_trans h1.1 h2.1, Nat.le_trans h1.2 h2.2⟩
  antisymm h1 h2 := Prod.ext (Nat.le_antisymm h1.1 h2.1) (Nat.le_antisymm h1.2 h2.2)

attribute [local instance] natPO pairPO

/-! #### A transient dip: Lifted Monotonicity without the obligations -/

/-- States of `dip`. -/
inductive Dip where
  | a
  | b
  | c

/-- Observations of `dip`: `a ↦ 1`, `b ↦ 0`, `c ↦ 2`. -/
def Dip.obs : Dip → Nat
  | .a => 1
  | .b => 0
  | .c => 2

/-- Internal steps `a → b → c`; every receive goes to `c`; no outputs.  The
step `a → b` lowers the observation. -/
def dip (C P : Type) : Machine C P Dip Nat where
  q0 := .a
  recv _ _ q' := q' = .c
  recv_enabled _ _ := ⟨.c, rfl⟩
  out _ _ _ _ := False
  tau q q' := (q = .a ∧ q' = .b) ∨ (q = .b ∧ q' = .c)
  obs := Dip.obs

/-- `dip` satisfies Lifted Monotonicity over either channel: every fiber
contains `2`, which refines every observation. -/
theorem dip_liftedMono [DecidableEq C] (k : ChanKind) :
    (spec (C := C) k (dip C P)).LiftedMono := by
  refine (liftedMono_iff_commonExpansion _).2 fun rows hrows j _ => ?_
  obtain ⟨β, s, hx, hi⟩ := j.occ
  have hr : Reach k (dip C P) β (toFlat s) := ⟨s, hx, rfl⟩
  have hm : MRun (dip C P) (toFlat s).q [] .c := by
    cases (toFlat s).q with
    | a => exact .int (Or.inr (Or.inl ⟨rfl, rfl⟩)) (.int (Or.inr (Or.inr ⟨rfl, rfl⟩)) (.nil _))
    | b => exact .int (Or.inr (Or.inr ⟨rfl, rfl⟩)) (.nil _)
    | c => exact .nil _
  obtain ⟨γ, f', hf', hi', hq⟩ := extend_int hm hr rfl
  refine ⟨2, (spec_iff j 2).2 ⟨β ++ γ, f', hf', hi'.trans hi, by rw [hq]; rfl⟩, fun r hr' => ?_⟩
  obtain ⟨_, f, _, _, ho⟩ := (spec_iff _ _).1 (hrows r hr')
  rw [← ho]
  show Dip.obs f.q ≤ 2
  cases f.q <;> decide

/-- No invariant and preorder satisfy the obligations for `dip`: they force
the observation to grow along the step `a → b` from the start state. -/
theorem dip_not_obligations (I : Dip → Prop) (le : Dip → Dip → Prop) :
    ¬ Obligations (dip C P) I le := by
  intro H
  have hab : IStep (dip C P) .a .b := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have h := H.obs_mono H.inv_start (H.inv_int H.inv_start hab) (H.int_up H.inv_start hab)
  exact (by decide : ¬ (1 : Nat) ≤ 0) h

/-! #### An append log: order-sensitive, consistent over FIFO only -/

/-- The append log as a state machine: the state is the list of received
payloads, observed under the prefix order. -/
def logSM : SM.Machine (List Bool) Bool (SM.Seq Bool) where
  q0 := []
  step q p q' := q' = q ++ [p]
  enabled _ _ := ⟨_, rfl⟩
  obs := SM.Seq.mk

/-- The append log as a machine automaton (outputs report the observation). -/
abbrev log : Machine Unit Bool (List Bool) (SM.Seq Bool) := ofSM logSM

/-- With a single client over a FIFO channel the append log is consistent. -/
theorem log_fifo_liftedMono :
    (spec (C := Unit) .fifo log).LiftedMono ∧ (spec (C := Unit) .fifo log).Consistent := by
  have hd : SM.Deterministic logSM := fun _ _ _ _ h1 h2 => h1.trans h2.symm
  have ht : SM.TransMono logSM := fun _ _ e _ h => ⟨[e], h⟩
  have hc := ((fifo_single logSM).2.2.2.2.2 hd).2 ht
  exact ⟨(complete_calm _).1 hc, hc⟩

/-- No invariant and preorder satisfy the obligations for the append log:
the two receive orders of `true` and `false` from the start give
incomparable observations. -/
theorem log_not_obligations (I : List Bool → Prop) (le : List Bool → List Bool → Prop) :
    ¬ Obligations log I le := by
  intro H
  have h0 : I [] := H.inv_start
  have r1 : log.recv [] true [true] := rfl
  have r2 : log.recv [true] false [true, false] := rfl
  have r3 : log.recv [] false [false] := rfl
  have r4 : log.recv [false] true [false, true] := rfl
  have hle := H.recv_comm h0 r1 r2 r3 r4
  obtain ⟨v, hv⟩ := H.obs_mono (H.inv_recv (H.inv_recv h0 r1) r2)
    (H.inv_recv (H.inv_recv h0 r3) r4) hle
  simp [log, ofSM, logSM] at hv

/-- Over a bag the append log is not consistent: one client sends `true`
then `false`, the bag delivers them in either order, and the two
observations have no common refinement. -/
theorem log_bag_not_liftedMono : ¬ (spec (C := Unit) .bag log).LiftedMono := by
  intro hL
  let e1 : Ev Unit Bool := ⟨(), 0, true⟩
  let e2 : Ev Unit Bool := ⟨(), 1, false⟩
  have h1 : Reach .bag log [Act.send e1] ⟨[], bump (fun _ => 0) (), [e1]⟩ :=
    reach_snoc (β := []).2 ⟨_, reach_nil.2 rfl, FStep.send (init log) e1 rfl⟩
  have h2 : Reach .bag log [Act.send e1, .send e2]
      ⟨[], bump (bump (fun _ => 0) ()) (), [e1, e2]⟩ :=
    reach_snoc (β := [Act.send e1]).2 ⟨_, h1, FStep.send _ e2 (by simp [bump, e2])⟩
  have h3 : Reach .bag log [Act.send e1, .send e2, .recv e1]
      ⟨[true], bump (bump (fun _ => 0) ()) (), [e2]⟩ :=
    reach_snoc (β := [Act.send e1, .send e2]).2
      ⟨_, h2, FStep.recv _ e1 [true] [e2] rfl ⟨[], [e2], rfl, rfl⟩⟩
  have h4 : Reach .bag log [Act.send e1, .send e2, .recv e1, .recv e2]
      ⟨[true, false], bump (bump (fun _ => 0) ()) (), []⟩ :=
    reach_snoc (β := [Act.send e1, .send e2, .recv e1]).2
      ⟨_, h3, FStep.recv _ e2 [true, false] [] rfl ⟨[], [], rfl, rfl⟩⟩
  obtain ⟨s, hx, _⟩ := h4
  have hout : OutFree (O := SM.Seq Bool) [Act.send e1, .send e2, .recv e1, .recv e2] := by
    intro c o h; simp at h
  let h := occOf (⟨s, hx, rfl⟩ : Reach .bag log _ (toFlat s))
  have hmem : ∀ w : List (Ev Unit Bool), (∀ e, e ∈ w ↔ e = e1 ∨ e = e2) →
      ∀ e, e ∈ w ↔ h.val.mem e := by
    intro w hw e
    rw [hw e]
    show _ ↔ Act.recv e ∈ [Act.send e1, .send e2, .recv e1, .recv e2]
    simp
  have hne : e1 ≠ e2 := by simp [e1, e2]
  have f1 : (spec .bag log).S h ⟨[true, false]⟩ :=
    bag_fiber_of_outFree (M := logSM) hx hout h rfl (w := [e1, e2]) (by simp [hne])
      (hmem _ (by simp)) (.cons rfl (.cons rfl (.nil _)))
  have f2 : (spec .bag log).S h ⟨[false, true]⟩ :=
    bag_fiber_of_outFree (M := logSM) hx hout h rfl (w := [e2, e1]) (by simp [hne.symm])
      (hmem _ (by simp; exact fun _ => Or.comm)) (.cons rfl (.cons rfl (.nil _)))
  obtain ⟨u, _, hall⟩ := hL h h (PO.refl h) [⟨[true, false]⟩, ⟨[false, true]⟩] (by simp)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact f1
      · exact f2)
  obtain ⟨v, hv⟩ := hall _ (List.mem_cons_self ..)
  obtain ⟨v', hv'⟩ := hall ⟨[false, true]⟩ (by simp)
  have := hv.symm.trans hv'
  simp at this

/-! #### A counter whose outputs change state -/

/-- Sums the received numbers; each output reports the state and increments a
count of outputs.  The observation is the pair (sum, count) under the
componentwise order, so every fiber is infinite. -/
def cnt : Machine Unit Nat (Nat × Nat) (Nat × Nat) where
  q0 := (0, 0)
  recv q p q' := q' = (q.1 + p, q.2)
  recv_enabled _ _ := ⟨_, rfl⟩
  out q _ o q' := o = q ∧ q' = (q.1, q.2 + 1)
  tau _ _ := False
  obs q := q

theorem cnt_istep {q q' : Nat × Nat} (h : IStep cnt q q') : q' = (q.1, q.2 + 1) := by
  rcases h with ⟨_, _, _, h⟩ | h
  · exact h
  · exact h.elim

theorem cnt_out (q : Nat × Nat) : MRun cnt q [] (q.1, q.2 + 1) :=
  .int (Or.inl ⟨(), q, rfl, rfl⟩) (.nil _)

/-- `cnt` satisfies the obligations with the trivial invariant and the
componentwise order. -/
theorem cnt_obligations :
    Obligations cnt (fun _ => True) (fun a b => a.1 ≤ b.1 ∧ a.2 ≤ b.2) where
  le_refl _ := ⟨Nat.le_refl _, Nat.le_refl _⟩
  le_trans h1 h2 := ⟨Nat.le_trans h1.1 h2.1, Nat.le_trans h1.2 h2.2⟩
  inv_start := trivial
  inv_recv _ _ := trivial
  inv_int _ _ := trivial
  obs_mono _ _ h := h
  recv_up := by
    intro q p q' _ h; subst h; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  int_up := by
    intro q q' _ h; rw [cnt_istep h]; exact ⟨Nat.le_refl _, Nat.le_succ _⟩
  recv_mono := by
    intro q q' p q1 q1' _ _ hle h1 h2; subst h1 h2; exact ⟨Nat.add_le_add_right hle.1 _, hle.2⟩
  int_sim := by
    intro q q' q1 _ _ hle h; rw [cnt_istep h]
    exact ⟨_, cnt_out q', hle.1, Nat.succ_le_succ hle.2⟩
  recv_comm := by
    intro q p p' q1 q2 q1' q2' _ h1 h2 h3 h4; subst h1 h2 h3 h4
    exact ⟨by simp only; omega, Nat.le_refl _⟩
  int_recv := by
    intro q q1 p q2 q1' _ h h2 h3; rw [cnt_istep h] at h2; subst h2 h3
    exact ⟨_, cnt_out _, Nat.le_refl _, Nat.le_refl _⟩

/-- Hence `cnt` is consistent over either channel. -/
theorem cnt_liftedMono (k : ChanKind) :
    (spec (C := Unit) k cnt).LiftedMono ∧ (spec (C := Unit) k cnt).Consistent :=
  liftedMono_of_obligations k cnt_obligations

end examples

end IOM
end CC
