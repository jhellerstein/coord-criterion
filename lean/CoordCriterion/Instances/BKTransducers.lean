import CoordCriterion.Instances.BaccaertKetsman
import CoordCriterion.CAP.ResponseAvailability

/-!
# Baccaert and Ketsman's transducer networks, translated into anonymous clusters

Namespace `CC.BK`.  This file formalizes the operational model of Baccaert
and Ketsman (BK; "A Generalized CALM Theorem for Non-Deterministic Computation
in Asynchronous Distributed Systems", Information Systems 138, 2026),
abstracted over their relational mappings, and translates every node program
into an anonymous cluster of `CAP/Model.lean` (`sysOf`).  Their Prop. 11
((Id+Ord)-characterized behaviors are node monotone) is then obtained through
`nodeMono_of_placedConsistent_cover`, the list form of
`nodeMono_of_placedConsistent` (`Instances/BaccaertKetsman.lean`).

## Modeling choices (precise readings)

1. *Node program* (`Prog`; their transducer with configuration constraint
   Id+Ord).  A node sees its own facts `H(x)`, its state and the list `R` of
   messages it reads; it chooses a new state and a list `W` of messages to
   broadcast.  Id and Ord are visible because every fact carries its location
   and node numbers are `Nat`.  The mappings are total (`Prog.total`) and the
   output is inflationary (`Prog.mono`).  Genericity and domain preservation
   of their relational mappings are *not* modeled: our class of programs is
   larger, which only strengthens the results below.
2. *Network* (`Net`): the nodes of an instance `H` are `Fin N`, `node` a
   bijection onto `netw(H)`; node `x`'s own facts are the facts of `H` at
   `node x` (`Net.own`).  BK instances are finite: `FinNet` says the network
   is finite.  Networks are nonempty wherever a run is needed.
3. *Messages.*  A configuration is the nodes' states and the broadcast log
   `List (Fin N × Msg)`.  A transition at `x` reads a list `R` of logged
   messages from other nodes (any of them, any number of times: duplication
   and reordering), steps, and appends `W` tagged with `x` (`Enabled`,
   `Cfg.apply`).  In the translation each broadcast is received at most once
   by each participant (`WFB`): a read of a message already received is a
   re-read of the local history (the strategy's tick only asks that read
   messages were received), not a second receive (`recv_list`).  A fair run (`FairRun`) is an `ℕ`-indexed sequence of
   enabled transitions from the start configuration in which every node is
   active infinitely often and every logged message from `y` is eventually
   read by every `x ≠ y`.
4. *Output* (`dout`): the located output `{(node x, a) | a ∈ out(S x)}`.
   Quiescence at `T`: the output is constant from `T` on.  `Computes Pg B`:
   every fair run on every network has a quiescence time whose output is a
   row of `B`.  `Characterizes Pg B`: `Pg` computes `B`, and every row of `B` at
   a nonempty finite network is the quiescent output of some fair run.
   Behaviors are `Spec (LInp loc) (PSet (Nat × Out))`; their Def. 7 is
   `QRef.NodeMono loc B` restricted to nonempty finite networks
   (`NodeMonoFin`).  On an empty network no run exists (a run needs a node
   to act), so `Computes` says nothing there, and neither does it on an
   infinite network.
5. *Translation* (`sysOf Pg`).  The cluster's specification is the downward
   closure `downB B` of `B` on finite networks (any output is allowed at an
   input with an infinite network, where `B` says nothing about `Pg`).  Its
   basis is all canonical commitments.  The shared strategy (`stratF`) replays
   `Pg` against a trace it may choose (`IRun`): a BK transition is a *tick*
   (a send carrying no message) after receives of the messages it reads,
   followed by one send per message of `W`; an output event emits the
   participant's current located output and may occur at any time (it is not
   tied to a transition); every send carries the sender's current input, so
   held facts travel with messages.  Message data are `Option Msg` (`none` is
   the tick).  The current state of a node is never shown in the history:
   the strategy allows an event when *some* trace explains the local history
   up to and including it.  Under placement the environment may turn held
   facts into input events.

## Results

* `placedConsistent_of_computes` (T1): if `Pg` computes `B`, then `sysOf Pg`
  is consistent on placed histories for `downB B`.  A placed causal history
  linearizes into a valid finite BK sequence (`linearize`), which extends to a
  fair run on any finite common input extension (`fair_extension`); outputs
  only grow, so all emitted outputs lie below the quiescent output.
* `covers_of_characterizes` (T2): if `Pg` characterizes `B`, every row `(H, K)`
  of `B` at a nonempty finite network is covered by a placed history of
  `sysOf Pg` (`Covers`: every element of `K` is in some emitted output).
* `nodeMono_of_characterizes` (T3, BK Prop. 11): if `Pg` characterizes `B`,
  then `B` is node monotone on nonempty finite networks (`NodeMonoFin`).
-/

namespace CC
namespace BK

open CAP
open QRef (ExtInp netAdm Netw union)
open CALM (PSet)

/-! ## BK's operational model -/

/-- A node program (BK's transducer under Id+Ord, abstracted over its
relational mappings). -/
structure Prog (F Msg St Out : Type) where
  start : St
  step : PSet F → St → List Msg → St → List Msg → Prop
  total : ∀ h s R, ∃ s' W, step h s R s' W
  out : St → PSet Out
  mono : ∀ h s R s' W, step h s R s' W → out s ≼ out s'

variable {F Msg St Out : Type} {loc : F → Nat}

/-- A network for the instance `H`: nodes `Fin N`, numbered bijectively onto
`netw(H)`. -/
structure Net (loc : F → Nat) (H : PSet F) where
  N : Nat
  node : Fin N → Nat
  inj : ∀ x y, node x = node y → x = y
  net : ∀ x, Netw loc H (node x)
  cover : ∀ f, H.mem f → ∃ x, node x = loc f

/-- The facts of node `x`. -/
def Net.own {H : PSet F} (net : Net loc H) (x : Fin net.N) : PSet F :=
  ⟨fun f => H.mem f ∧ loc f = net.node x⟩

/-- The network of `H` is finite. -/
def FinNet (loc : F → Nat) (H : PSet F) : Prop :=
  ∃ l : List Nat, l.Nodup ∧ ∀ x, x ∈ l ↔ Netw loc H x

/-- A transition: node `x` reads `R`, moves to state `s`, broadcasts `W`. -/
structure Tr (N : Nat) (Msg St : Type) where
  x : Fin N
  R : List Msg
  s : St
  W : List Msg

/-- A configuration: states and the broadcast log. -/
structure Cfg (N : Nat) (Msg St : Type) where
  S : Fin N → St
  log : List (Fin N × Msg)

def upd {N : Nat} {α : Type} (S : Fin N → α) (x : Fin N) (a : α) : Fin N → α :=
  fun y => if y = x then a else S y

theorem upd_same {N : Nat} {α : Type} (S : Fin N → α) (x : Fin N) (a : α) : upd S x a x = a := by
  simp [upd]

theorem upd_other {N : Nat} {α : Type} (S : Fin N → α) {x y : Fin N} (a : α) (h : y ≠ x) :
    upd S x a y = S y := by
  simp [upd, h]

def Cfg.start {N : Nat} (Pg : Prog F Msg St Out) : Cfg N Msg St := ⟨fun _ => Pg.start, []⟩

def Cfg.apply {N : Nat} (c : Cfg N Msg St) (τ : Tr N Msg St) : Cfg N Msg St :=
  ⟨upd c.S τ.x τ.s, c.log ++ τ.W.map (fun m => (τ.x, m))⟩

/-- Transition `τ` is enabled at `c`: a step of the program from `x`'s state on
its own facts, reading only messages logged by other nodes. -/
def Enabled {N : Nat} (Pg : Prog F Msg St Out) (own : Fin N → PSet F) (c : Cfg N Msg St)
    (τ : Tr N Msg St) : Prop :=
  Pg.step (own τ.x) (c.S τ.x) τ.R τ.s τ.W ∧ ∀ m ∈ τ.R, ∃ y, y ≠ τ.x ∧ (y, m) ∈ c.log

/-- The configuration after a finite sequence. -/
def seqCfg {N : Nat} : Cfg N Msg St → List (Tr N Msg St) → Cfg N Msg St
  | c, [] => c
  | c, τ :: l => seqCfg (c.apply τ) l

/-- A finite sequence of enabled transitions. -/
def SeqOK {N : Nat} (Pg : Prog F Msg St Out) (own : Fin N → PSet F) :
    Cfg N Msg St → List (Tr N Msg St) → Prop
  | _, [] => True
  | c, τ :: l => Enabled Pg own c τ ∧ SeqOK Pg own (c.apply τ) l

/-- The configuration at time `t` of an infinite sequence. -/
def cfgAt {N : Nat} (Pg : Prog F Msg St Out) (ρ : Nat → Tr N Msg St) : Nat → Cfg N Msg St
  | 0 => Cfg.start Pg
  | t + 1 => (cfgAt Pg ρ t).apply (ρ t)

/-- A fair run (BK §3.3, with the message reading of item 3). -/
structure FairRun {N : Nat} (Pg : Prog F Msg St Out) (own : Fin N → PSet F)
    (ρ : Nat → Tr N Msg St) : Prop where
  valid : ∀ t, Enabled Pg own (cfgAt Pg ρ t) (ρ t)
  active : ∀ x T, ∃ t, T ≤ t ∧ (ρ t).x = x
  reads : ∀ t y m x, (y, m) ∈ (cfgAt Pg ρ t).log → y ≠ x →
    ∃ t', t ≤ t' ∧ (ρ t').x = x ∧ m ∈ (ρ t').R

/-- The located output of node number `nd` in state `s`. -/
def locOut (Pg : Prog F Msg St Out) (nd : Nat) (s : St) : PSet (Nat × Out) :=
  ⟨fun z => z.1 = nd ∧ (Pg.out s).mem z.2⟩

/-- The distributed output of a configuration (BK §3.4). -/
def dout (Pg : Prog F Msg St Out) {N : Nat} (node : Fin N → Nat) (c : Cfg N Msg St) :
    PSet (Nat × Out) :=
  ⟨fun z => ∃ x, z.1 = node x ∧ (Pg.out (c.S x)).mem z.2⟩

/-- Quiescence at `T`: the output no longer changes. -/
def Quiescent (Pg : Prog F Msg St Out) {N : Nat} (node : Fin N → Nat) (ρ : Nat → Tr N Msg St)
    (T : Nat) : Prop :=
  ∀ t, T ≤ t → dout Pg node (cfgAt Pg ρ t) = dout Pg node (cfgAt Pg ρ T)

/-- BK Def. 4: `Pg` computes `B`. -/
def Computes (Pg : Prog F Msg St Out) (B : Spec (LInp loc) (PSet (Nat × Out))) : Prop :=
  ∀ (H : PSet F) (net : Net loc H) (ρ : Nat → Tr net.N Msg St), FairRun Pg net.own ρ →
    ∃ T, Quiescent Pg net.node ρ T ∧ B.P ⟨H⟩ (dout Pg net.node (cfgAt Pg ρ T))

/-- BK Def. 4: `Pg` characterizes `B`. -/
def Characterizes (Pg : Prog F Msg St Out) (B : Spec (LInp loc) (PSet (Nat × Out))) : Prop :=
  Computes Pg B ∧
  ∀ (H : PSet F) (K : PSet (Nat × Out)), FinNet loc H → (∃ f, H.mem f) → B.P ⟨H⟩ K →
    ∃ (net : Net loc H) (ρ : Nat → Tr net.N Msg St), FairRun Pg net.own ρ ∧
      ∃ T, Quiescent Pg net.node ρ T ∧ dout Pg net.node (cfgAt Pg ρ T) = K

/-- BK Def. 7 on nonempty finite networks. -/
def NodeMonoFin (loc : F → Nat) {G' : Type} (B : Spec (LInp loc) (PSet G')) : Prop :=
  ∀ H₁ H₂ : PSet F, FinNet loc H₁ → FinNet loc H₂ → (∃ f, H₁.mem f) → (∃ f, H₂.mem f) →
    (∀ x, Netw loc H₁ x → ¬ Netw loc H₂ x) →
    ∀ K₁ K₂, B.P ⟨H₁⟩ K₁ → B.P ⟨H₂⟩ K₂ → ∃ K, B.P ⟨union H₁ H₂⟩ K ∧ K₁ ≼ K ∧ K₂ ≼ K

/-! ### Finite sequences and runs -/

section Runs

variable {Pg : Prog F Msg St Out} {N : Nat}

theorem seqCfg_append (c : Cfg N Msg St) (a b : List (Tr N Msg St)) :
    seqCfg c (a ++ b) = seqCfg (seqCfg c a) b := by
  induction a generalizing c with
  | nil => rfl
  | cons τ a ih => exact ih _

theorem seqOK_append {own : Fin N → PSet F} (c : Cfg N Msg St) (a b : List (Tr N Msg St)) :
    SeqOK Pg own c (a ++ b) ↔ SeqOK Pg own c a ∧ SeqOK Pg own (seqCfg c a) b := by
  induction a generalizing c with
  | nil => simp [SeqOK, seqCfg]
  | cons τ a ih =>
    simp only [List.cons_append, SeqOK, seqCfg, ih]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

theorem seqOK_get {own : Fin N → PSet F} :
    ∀ (l : List (Tr N Msg St)) (c : Cfg N Msg St), SeqOK Pg own c l →
      ∀ t (ht : t < l.length), Enabled Pg own (seqCfg c (l.take t)) l[t]
  | [], _, _, t, ht => absurd ht (by simp)
  | τ :: l, c, h, 0, _ => by simpa [seqCfg] using h.1
  | τ :: l, c, h, t + 1, ht => by
    have := seqOK_get l (c.apply τ) h.2 t (by simpa using ht)
    simpa [seqCfg] using this

theorem log_apply_mono (c : Cfg N Msg St) (τ : Tr N Msg St) {e : Fin N × Msg}
    (h : e ∈ c.log) : e ∈ (c.apply τ).log :=
  List.mem_append_left _ h

theorem cfgAt_log_mono (ρ : Nat → Tr N Msg St) {t t' : Nat} (h : t ≤ t') {e : Fin N × Msg}
    (he : e ∈ (cfgAt Pg ρ t).log) : e ∈ (cfgAt Pg ρ t').log := by
  induction h with
  | refl => exact he
  | step _ ih => exact log_apply_mono _ _ ih

/-- Along a valid run each node's output only grows. -/
theorem cfgAt_out_mono {own : Fin N → PSet F} {ρ : Nat → Tr N Msg St}
    (hv : ∀ t, Enabled Pg own (cfgAt Pg ρ t) (ρ t)) {t t' : Nat} (h : t ≤ t') (x : Fin N) :
    Pg.out ((cfgAt Pg ρ t).S x) ≼ Pg.out ((cfgAt Pg ρ t').S x) := by
  induction h with
  | refl => exact PO.refl _
  | @step t' _ ih =>
    refine PO.trans ih ?_
    show Pg.out ((cfgAt Pg ρ t').S x) ≼ Pg.out (upd (cfgAt Pg ρ t').S (ρ t').x (ρ t').s x)
    by_cases hx : x = (ρ t').x
    · subst hx; rw [upd_same]
      exact Pg.mono _ _ _ _ _ (hv t').1
    · rw [upd_other _ _ hx]; exact PO.refl _

theorem dout_mono {own : Fin N → PSet F} {ρ : Nat → Tr N Msg St} (node : Fin N → Nat)
    (hv : ∀ t, Enabled Pg own (cfgAt Pg ρ t) (ρ t)) {t t' : Nat} (h : t ≤ t') :
    dout Pg node (cfgAt Pg ρ t) ≼ dout Pg node (cfgAt Pg ρ t') := by
  rintro z ⟨x, hx, hz⟩
  exact ⟨x, hx, cfgAt_out_mono hv h x _ hz⟩

/-! ### Fair extension of a finite valid sequence -/

/-- The round-robin transition at `x`: read every message logged by another
node, and step by the program's totality. -/
noncomputable def nextTr (Pg : Prog F Msg St Out) (own : Fin N → PSet F) (c : Cfg N Msg St)
    (x : Fin N) : Tr N Msg St :=
  let R := (c.log.filter (fun e => decide (e.1 ≠ x))).map Prod.snd
  ⟨x, R, Classical.choose (Pg.total (own x) (c.S x) R),
    Classical.choose (Classical.choose_spec (Pg.total (own x) (c.S x) R))⟩

theorem nextTr_enabled (own : Fin N → PSet F) (c : Cfg N Msg St) (x : Fin N) :
    Enabled Pg own c (nextTr Pg own c x) := by
  refine ⟨Classical.choose_spec (Classical.choose_spec (Pg.total (own x) (c.S x) _)), ?_⟩
  intro m hm
  simp only [nextTr, List.mem_map, List.mem_filter] at hm
  obtain ⟨⟨y, m'⟩, ⟨hin, hne⟩, rfl⟩ := hm
  have hne' : y ≠ x := by simpa using hne
  exact ⟨y, hne', hin⟩

theorem mem_nextTr_R {own : Fin N → PSet F} {c : Cfg N Msg St} {x y : Fin N} {m : Msg}
    (h : (y, m) ∈ c.log) (hne : y ≠ x) : m ∈ (nextTr Pg own c x).R := by
  simp only [nextTr, List.mem_map, List.mem_filter]
  exact ⟨(y, m), ⟨h, by simpa using hne⟩, rfl⟩

/-- Configurations of the round-robin continuation. -/
noncomputable def rrCfg (Pg : Prog F Msg St Out) (own : Fin N → PSet F) (hN : 0 < N)
    (c0 : Cfg N Msg St) : Nat → Cfg N Msg St
  | 0 => c0
  | k + 1 => (rrCfg Pg own hN c0 k).apply (nextTr Pg own (rrCfg Pg own hN c0 k) ⟨k % N, Nat.mod_lt _ hN⟩)

/-- The prefix followed by the round-robin continuation. -/
noncomputable def extRun (Pg : Prog F Msg St Out) (own : Fin N → PSet F) (hN : 0 < N)
    (pre : List (Tr N Msg St)) (t : Nat) : Tr N Msg St :=
  if h : t < pre.length then pre[t]
  else nextTr Pg own (rrCfg Pg own hN (seqCfg (Cfg.start Pg) pre) (t - pre.length))
    ⟨(t - pre.length) % N, Nat.mod_lt _ hN⟩

theorem extRun_cfg_pre (own : Fin N → PSet F) (hN : 0 < N) (pre : List (Tr N Msg St)) :
    ∀ t, t ≤ pre.length → cfgAt Pg (extRun Pg own hN pre) t = seqCfg (Cfg.start Pg) (pre.take t)
  | 0, _ => rfl
  | t + 1, ht => by
    have ih := extRun_cfg_pre own hN pre t (by omega)
    show (cfgAt Pg (extRun Pg own hN pre) t).apply (extRun Pg own hN pre t) = _
    rw [ih]
    have hlt : t < pre.length := by omega
    have : extRun Pg own hN pre t = pre[t] := by simp [extRun, hlt]
    rw [this, List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, seqCfg_append]
    rfl

theorem extRun_cfg_post (own : Fin N → PSet F) (hN : 0 < N) (pre : List (Tr N Msg St)) :
    ∀ k, cfgAt Pg (extRun Pg own hN pre) (pre.length + k) =
      rrCfg Pg own hN (seqCfg (Cfg.start Pg) pre) k
  | 0 => by
    rw [Nat.add_zero, extRun_cfg_pre own hN pre _ (Nat.le_refl _), List.take_length]; rfl
  | k + 1 => by
    show (cfgAt Pg (extRun Pg own hN pre) (pre.length + k)).apply
      (extRun Pg own hN pre (pre.length + k)) = _
    rw [extRun_cfg_post own hN pre k]
    have : extRun Pg own hN pre (pre.length + k) =
        nextTr Pg own (rrCfg Pg own hN (seqCfg (Cfg.start Pg) pre) k) ⟨k % N, Nat.mod_lt _ hN⟩ := by
      unfold extRun; simp only [show ¬ (pre.length + k < pre.length) by omega, ↓reduceDIte, Nat.add_sub_cancel_left]
    rw [this]; rfl

theorem extRun_post (own : Fin N → PSet F) (hN : 0 < N) (pre : List (Tr N Msg St)) (k : Nat) :
    extRun Pg own hN pre (pre.length + k) =
      nextTr Pg own (cfgAt Pg (extRun Pg own hN pre) (pre.length + k)) ⟨k % N, Nat.mod_lt _ hN⟩ := by
  rw [extRun_cfg_post]; unfold extRun; simp only [show ¬ (pre.length + k < pre.length) by omega, ↓reduceDIte, Nat.add_sub_cancel_left]

/-- **Fair extension.**  On a nonempty network, every finite valid sequence
from the start configuration is the prefix of a fair run. -/
theorem fair_extension (own : Fin N → PSet F) (hN : 0 < N) (pre : List (Tr N Msg St))
    (hok : SeqOK Pg own (Cfg.start Pg) pre) :
    ∃ ρ : Nat → Tr N Msg St, FairRun Pg own ρ ∧
      cfgAt Pg ρ pre.length = seqCfg (Cfg.start Pg) pre := by
  refine ⟨extRun Pg own hN pre, ⟨fun t => ?_, fun x T => ?_, fun t y m x hm hne => ?_⟩, ?_⟩
  · by_cases ht : t < pre.length
    · rw [extRun_cfg_pre own hN pre t (Nat.le_of_lt ht)]
      have : extRun Pg own hN pre t = pre[t] := by simp [extRun, ht]
      rw [this]; exact seqOK_get pre _ hok t ht
    · obtain ⟨k, rfl⟩ : ∃ k, t = pre.length + k := ⟨t - pre.length, by omega⟩
      rw [extRun_post]; exact nextTr_enabled _ _ _
  · refine ⟨pre.length + (T * N + x.val), by
      have : T ≤ T * N := Nat.le_mul_of_pos_right T hN
      omega, ?_⟩
    rw [extRun_post]
    simp only [nextTr]
    ext; simp [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt x.isLt]
  · let k := t * N + x.val
    have hk : t ≤ pre.length + k := by
      have : t ≤ t * N := Nat.le_mul_of_pos_right t hN
      omega
    refine ⟨pre.length + k, hk, ?_, ?_⟩
    · rw [extRun_post]; simp only [nextTr]
      ext; simp [k, Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt x.isLt]
    · rw [extRun_post]
      have hx : (⟨k % N, Nat.mod_lt _ hN⟩ : Fin N) = x := by
        ext; simp [k, Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt x.isLt]
      rw [hx]
      exact mem_nextTr_R (cfgAt_log_mono _ hk hm) hne
  · rw [extRun_cfg_pre own hN pre _ (Nat.le_refl _), List.take_length]

end Runs

/-! ## The translation into an anonymous cluster -/

/-- A step of a trace: messages read, new state, messages broadcast. -/
structure LStep (Msg St : Type) where
  R : List Msg
  s : St
  W : List Msg

/-- The replay state of a participant: BK state, messages received, messages
of the current transition still to send, steps of the trace still to take. -/
structure ICfg (Msg St : Type) where
  s : St
  rcv : List Msg
  pend : List Msg
  rest : List (LStep Msg St)

def ICfg.init (Pg : Prog F Msg St Out) (tr : List (LStep Msg St)) : ICfg Msg St :=
  ⟨Pg.start, [], [], tr⟩

section Translation

variable {sp : Spec (LInp loc) (PSet (Nat × Out))}

/-- One anonymized event replayed against the trace.  A tick (`send j none`)
takes the next step of the trace: all messages of the previous step are sent,
the step is a step of the program on the node's own facts `h`, and it reads
only received messages.  A message send must be the next pending message.  An
output event emits the current located output. -/
inductive IStep (Pg : Prog F Msg St Out) (h : PSet F) (nd : Nat) :
    ICfg Msg St → LEvA sp (Option Msg) → ICfg Msg St → Prop
  | inp {c : ICfg Msg St} {j : LInp loc} : IStep Pg h nd c (.inp j) c
  | recvM {c : ICfg Msg St} {j : Option (LInp loc)} {m : Msg} :
      IStep Pg h nd c (.recv j (some m)) ⟨c.s, m :: c.rcv, c.pend, c.rest⟩
  | recvT {c : ICfg Msg St} {j : Option (LInp loc)} : IStep Pg h nd c (.recv j none) c
  | out {c : ICfg Msg St} {o : PSet (Nat × Out)} : o = locOut Pg nd c.s → IStep Pg h nd c (.out o) c
  | send {c : ICfg Msg St} {j : Option (LInp loc)} {m : Msg} {ps : List Msg} :
      c.pend = m :: ps → IStep Pg h nd c (.send j (some m)) ⟨c.s, c.rcv, ps, c.rest⟩
  | tick {c : ICfg Msg St} {j : Option (LInp loc)} {st : LStep Msg St} {rs : List (LStep Msg St)} :
      c.pend = [] → c.rest = st :: rs → Pg.step h c.s st.R st.s st.W → (∀ m ∈ st.R, m ∈ c.rcv) →
      IStep Pg h nd c (.send j none) ⟨st.s, c.rcv, st.W, rs⟩

inductive IRun (Pg : Prog F Msg St Out) (h : PSet F) (nd : Nat) :
    ICfg Msg St → List (LEvA sp (Option Msg)) → ICfg Msg St → Prop
  | nil (c : ICfg Msg St) : IRun Pg h nd c [] c
  | cons {c c' c'' : ICfg Msg St} {e : LEvA sp (Option Msg)} {l : List (LEvA sp (Option Msg))} :
      IStep Pg h nd c e c' → IRun Pg h nd c' l c'' → IRun Pg h nd c (e :: l) c''

/-- The current input after an anonymized local history. -/
def curA (i0 : LInp loc) : List (LEvA sp (Option Msg)) → LInp loc
  | [] => i0
  | .inp j :: l => curA j l
  | _ :: l => curA i0 l

/-- Which events the strategy performs: output events, and sends carrying the
current input. -/
def StratKind (x : LInp loc) (pre : List (LEvA sp (Option Msg))) : LEvA sp (Option Msg) → Prop
  | .out _ => True
  | .send j _ => j = some (curA x pre)
  | _ => False

/-- The shared strategy replaying `Pg`: some trace explains the local history
up to and including the event. -/
def stratF (Pg : Prog F Msg St Out) (x : LInp loc) (pre : List (LEvA sp (Option Msg)))
    (e : LEvA sp (Option Msg)) : Prop :=
  StratKind x pre e ∧ ∃ nd, (∀ f, x.set.mem f → loc f = nd) ∧
    ∃ tr c, IRun Pg x.set nd (ICfg.init Pg tr) (pre ++ [e]) c

/-- The anonymous cluster of `Pg`: all canonical commitments in the basis, and
the replaying strategy. -/
def sysOf (Pg : Prog F Msg St Out) : System sp (Option Msg) :=
  System.cluster (fun c => ∃ u, c = kcap u) (stratF Pg)

theorem sysOf_anonymous (Pg : Prog F Msg St Out) : (sysOf (sp := sp) Pg).Anonymous :=
  System.cluster_anonymous _ _

theorem sysOf_canonical (Pg : Prog F Msg St Out) : CanonicalSystem (sysOf (sp := sp) Pg) := by
  intro n init p pre γ h
  exact h.1

/-- Anonymized local history. -/
def anonL {n : Nat} (l : List (LEv sp (Option Msg) n)) : List (LEvA sp (Option Msg)) :=
  (l.map LEv.erase).map LEvN.anon

def anonE {n : Nat} (e : LEv sp (Option Msg) n) : LEvA sp (Option Msg) := (LEv.erase e).anon

@[simp] theorem anonL_nil {n : Nat} : anonL (sp := sp) (Msg := Msg) (n := n) [] = [] := rfl

@[simp] theorem anonL_append {n : Nat} (a b : List (LEv sp (Option Msg) n)) :
    anonL (a ++ b) = anonL a ++ anonL b := by simp [anonL]

@[simp] theorem anonL_cons {n : Nat} (e : LEv sp (Option Msg) n) (l : List (LEv sp (Option Msg) n)) :
    anonL (e :: l) = anonE e :: anonL l := rfl

theorem strat_sysOf {Pg : Prog F Msg St Out} {n : Nat} {init : Fin n → LInp loc} {p : Fin n}
    {pre : List (LEv sp (Option Msg) n)} {e : LEv sp (Option Msg) n} :
    (sysOf (sp := sp) Pg).strat n init p pre e ↔ stratF Pg (init p) (anonL pre) (anonE e) :=
  Iff.rfl

variable {Pg : Prog F Msg St Out} {h : PSet F} {nd : Nat}

theorem irun_append {c c'' : ICfg Msg St} :
    ∀ {a b : List (LEvA sp (Option Msg))},
      IRun Pg h nd c (a ++ b) c'' ↔ ∃ c', IRun Pg h nd c a c' ∧ IRun Pg h nd c' b c''
  | [], b => ⟨fun h => ⟨c, .nil _, h⟩, fun ⟨c', h1, h2⟩ => by cases h1; exact h2⟩
  | e :: a, b => by
    constructor
    · intro hr
      cases hr with
      | cons hs hr' =>
        obtain ⟨c', h1, h2⟩ := (irun_append (a := a) (b := b)).1 hr'
        exact ⟨c', .cons hs h1, h2⟩
    · rintro ⟨c', h1, h2⟩
      cases h1 with
      | cons hs h1' => exact .cons hs ((irun_append (a := a) (b := b)).2 ⟨c', h1', h2⟩)

theorem irun_nil_inv {c c' : ICfg Msg St} (hr : IRun Pg h nd c ([] : List (LEvA sp (Option Msg))) c') :
    c' = c := by
  cases hr; rfl

theorem irun_single {c c' : ICfg Msg St} {e : LEvA sp (Option Msg)} :
    IRun Pg h nd c [e] c' ↔ IStep Pg h nd c e c' :=
  ⟨fun hr => by cases hr with | cons hs hr' => cases hr'; exact hs,
   fun hs => .cons hs (.nil _)⟩

/-- Along a replay the program's output only grows, and every emitted output
lies below the final located output. -/
theorem irun_outs {c c' : ICfg Msg St} {l : List (LEvA sp (Option Msg))}
    (hr : IRun Pg h nd c l c') :
    Pg.out c.s ≼ Pg.out c'.s ∧ ∀ o, LEvA.out o ∈ l → o ≼ locOut Pg nd c'.s := by
  induction hr with
  | nil => exact ⟨PO.refl _, fun o ho => by cases ho⟩
  | @cons c c1 c2 e l hs _ ih =>
    have hsc : Pg.out c.s ≼ Pg.out c1.s := by
      cases hs with
      | tick _ _ hst _ => exact Pg.mono _ _ _ _ _ hst
      | _ => exact PO.refl _
    refine ⟨PO.trans hsc ih.1, fun o ho => ?_⟩
    rcases List.mem_cons.1 ho with rfl | ho'
    · cases hs with
      | out hoe =>
        subst hoe
        rintro z ⟨hz1, hz2⟩
        exact ⟨hz1, ih.1 _ hz2⟩
    · exact ih.2 o ho'

/-- Every received message was received by a receive event. -/
theorem irun_rcv {c c' : ICfg Msg St} {l : List (LEvA sp (Option Msg))}
    (hr : IRun Pg h nd c l c') :
    ∀ m ∈ c'.rcv, m ∈ c.rcv ∨ ∃ j, LEvA.recv j (some m) ∈ l := by
  induction hr with
  | nil => exact fun m hm => Or.inl hm
  | @cons c c1 c2 e l hs _ ih =>
    intro m hm
    rcases ih m hm with h1 | ⟨j, hj⟩
    · cases hs with
      | @recvM j' m' =>
        rcases List.mem_cons.1 h1 with rfl | h1'
        · exact Or.inr ⟨j', List.mem_cons_self ..⟩
        · exact Or.inl h1'
      | inp => exact Or.inl h1
      | recvT => exact Or.inl h1
      | out _ => exact Or.inl h1
      | send _ => exact Or.inl h1
      | tick _ _ _ _ => exact Or.inl h1
    · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj⟩

/-- Received messages stay received, and every received message is in the
final list. -/
theorem irun_rcv_grow {c c' : ICfg Msg St} {l : List (LEvA sp (Option Msg))}
    (hr : IRun Pg h nd c l c') :
    (∀ m ∈ c.rcv, m ∈ c'.rcv) ∧ ∀ j m, LEvA.recv j (some m) ∈ l → m ∈ c'.rcv := by
  induction hr with
  | nil => exact ⟨fun _ h => h, fun _ _ h => by cases h⟩
  | @cons c c1 c2 e l hs _ ih =>
    have hg : ∀ m ∈ c.rcv, m ∈ c1.rcv := by
      cases hs with
      | recvM => exact fun m hm => List.mem_cons_of_mem _ hm
      | inp => exact fun m hm => hm
      | recvT => exact fun m hm => hm
      | out _ => exact fun m hm => hm
      | send _ => exact fun m hm => hm
      | tick _ _ _ _ => exact fun m hm => hm
    refine ⟨fun m hm => ih.1 m (hg m hm), fun j m hm => ?_⟩
    rcases List.mem_cons.1 hm with he | hm'
    · subst he
      cases hs with
      | recvM => exact ih.1 m List.mem_cons_self
    · exact ih.2 j m hm'

theorem recv_mem_anonL {n : Nat} {l : List (LEv sp (Option Msg) n)} {q : Fin n} {k : Nat}
    {j : Option (LInp loc)} {d : Option Msg} (h : LEv.recv q k j d ∈ l) :
    LEvA.recv j d ∈ anonL l := by
  simp only [anonL, List.mem_map]
  exact ⟨_, ⟨_, h, rfl⟩, rfl⟩

theorem mem_anonL_recv {n : Nat} {l : List (LEv sp (Option Msg) n)} {j : Option (LInp loc)}
    {d : Option Msg} (h : LEvA.recv j d ∈ anonL l) : ∃ q k, LEv.recv q k j d ∈ l := by
  induction l with
  | nil => cases h
  | cons e l ih =>
    rcases List.mem_cons.1 h with he | h'
    · cases e with
      | recv q k j' d' =>
        simp only [LEv.erase, LEvN.anon, LEvA.recv.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨q, k, List.mem_cons_self ..⟩
      | _ => simp [LEv.erase, LEvN.anon] at he
    · obtain ⟨q, k, hm⟩ := ih h'
      exact ⟨q, k, List.mem_cons_of_mem _ hm⟩

theorem mem_anonL_out {n : Nat} {l : List (LEv sp (Option Msg) n)} {o : PSet (Nat × Out)}
    (h : LEv.out o ∈ l) : LEvA.out o ∈ anonL l := by
  induction l with
  | nil => cases h
  | cons e l ih =>
    rcases List.mem_cons.1 h with rfl | h'
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h')

theorem list_rev_ind {α : Type} {P : List α → Prop} (h0 : P []) (h1 : ∀ l e, P l → P (l ++ [e])) :
    ∀ l, P l := by
  suffices ∀ r : List α, P r.reverse from fun l => by simpa using this l.reverse
  intro r
  induction r with
  | nil => exact h0
  | cons e r ih => simpa using h1 _ e ih

/-- A history compliant with `sysOf Pg` is replayed by some trace. -/
theorem irun_of_compliant {n : Nat} {init : Fin n → LInp loc} {p : Fin n} {nd0 : Nat}
    (hf : ∃ f, (init p).set.mem f) (hnd : ∀ f, (init p).set.mem f → loc f = nd0) :
    ∀ l : List (LEv sp (Option Msg) n), Compliant (Allowed (sysOf (sp := sp) Pg) n init p) l →
      ∃ tr c, IRun Pg (init p).set nd0 (ICfg.init Pg tr) (anonL l) c := by
  intro l
  refine list_rev_ind (P := fun l => Compliant (Allowed (sysOf (sp := sp) Pg) n init p) l →
    ∃ tr c, IRun Pg (init p).set nd0 (ICfg.init Pg tr) (anonL l) c) (fun _ => ⟨[], _, .nil _⟩) ?_ l
  intro l e ih
  · intro hc
    have hcl : Compliant (Allowed (sysOf (sp := sp) Pg) n init p) l := by
      have := compliant_take hc l.length
      simpa using this
    have hA : Allowed (sysOf (sp := sp) Pg) n init p l e := hc l e [] rfl
    have hstrat : ∀ (hs : (sysOf (sp := sp) Pg).strat n init p l e),
        ∃ tr c, IRun Pg (init p).set nd0 (ICfg.init Pg tr) (anonL (l ++ [e])) c := by
      intro hs
      obtain ⟨_, nd, hnd', tr, c, hr⟩ := strat_sysOf.1 hs
      obtain ⟨f, hfm⟩ := hf
      have : nd = nd0 := (hnd' f hfm).symm.trans (hnd f hfm)
      subst this
      exact ⟨tr, c, by simpa using hr⟩
    cases e with
    | inp j =>
      obtain ⟨tr, c, hr⟩ := ih hcl
      exact ⟨tr, c, by rw [anonL_append]; exact irun_append.2 ⟨c, hr, irun_single.2 IStep.inp⟩⟩
    | recv q k j d =>
      obtain ⟨tr, c, hr⟩ := ih hcl
      cases d with
      | none => exact ⟨tr, c, by rw [anonL_append]; exact irun_append.2 ⟨c, hr, irun_single.2 IStep.recvT⟩⟩
      | some m => exact ⟨tr, _, by rw [anonL_append]; exact irun_append.2 ⟨c, hr, irun_single.2 IStep.recvM⟩⟩
    | out o => exact hstrat hA.2
    | send j d => exact hstrat hA
    | commitment γ => exact absurd hA.2 (fun h => h.1)

end Translation

/-! ## Linearizing a causal history into a BK sequence -/

section Linearize

variable {sp : Spec (LInp loc) (PSet (Nat × Out))} {Pg : Prog F Msg St Out}

theorem exists_bound {n : Nat} (f : Fin n → Nat) : ∃ B, ∀ p, f p < B := by
  induction n with
  | zero => exact ⟨0, fun p => p.elim0⟩
  | succ n ih =>
    obtain ⟨B, hB⟩ := ih (fun p => f p.succ)
    refine ⟨max B (f 0 + 1), fun p => ?_⟩
    refine Fin.cases ?_ (fun p => ?_) p
    · omega
    · have := hB p; omega

theorem prefix_recv {α : Type} {x y a b : List α} {e : α} (h : x = a ++ e :: b) :
    x ++ y = a ++ e :: (b ++ y) := by
  rw [h]; simp

theorem linearize_aux {n N : Nat} (g : Fin n → Fin N) (hg : ∀ p q, g p = g q → p = q)
    (own : Fin N → PSet F) (h : Fin n → PSet F) (hown : ∀ p, own (g p) = h p)
    (nd : Fin n → Nat) (tr : Fin n → List (LStep Msg St)) (t : Fin n → Nat → Nat)
    (hmono : ∀ p k k', k < k' → t p k < t p k') (hinj : ∀ p q k k', t p k = t q k' → p = q) :
    ∀ (T : Nat) (H : History sp (Option Msg) n) (c : Fin n → ICfg Msg St),
      (∀ p k, k < (H p).length → t p k < T) → RecvMatched H →
      (∀ p a q k j d b, H p = a ++ LEv.recv q k j d :: b → t q k < t p a.length) →
      (∀ p, IRun Pg (h p) (nd p) (ICfg.init Pg (tr p)) (anonL (H p)) (c p)) →
      ∃ seq : List (Tr N Msg St), SeqOK Pg own (Cfg.start Pg) seq ∧
        (∀ p, (seqCfg (Cfg.start Pg) seq).S (g p) = (c p).s) ∧
        (∀ p m, m ∈ (c p).pend → (g p, m) ∈ (seqCfg (Cfg.start Pg) seq).log) ∧
        (∀ q (k : Nat) (j : Option (LInp loc)) (m : Msg), (H q)[k]? = some (LEv.send j (some m)) →
          (g q, m) ∈ (seqCfg (Cfg.start Pg) seq).log) := by
  intro T
  induction T with
  | zero =>
    intro H c hT _ _ hrun
    have hH : ∀ p, H p = [] := fun p => by
      cases hp : H p with
      | nil => rfl
      | cons e l => exact absurd (hT p 0 (by simp [hp])) (Nat.not_lt_zero _)
    have hc : ∀ p, c p = ICfg.init Pg (tr p) := fun p => by
      have := hrun p; rw [hH p] at this; exact irun_nil_inv this
    refine ⟨[], trivial, fun p => by rw [hc p]; rfl, fun p m hm => (by rw [hc p] at hm; cases hm),
      fun q k j m hk => by rw [hH q] at hk; simp at hk⟩
  | succ T ih =>
    intro H c hT hm hcaus hrun
    by_cases hex : ∃ p k, k < (H p).length ∧ t p k = T
    · obtain ⟨p, k, hk, htk⟩ := hex
      have hlast : k + 1 = (H p).length := by
        apply Classical.byContradiction; intro hne
        have h1 := hmono p k ((H p).length - 1) (by omega)
        have h2 := hT p ((H p).length - 1) (by omega)
        omega
      obtain ⟨l, e, hle⟩ : ∃ l e, H p = l ++ [e] := by
        rcases List.eq_nil_or_concat (H p) with h0 | ⟨l, e, he⟩
        · rw [h0] at hk; simp at hk
        · exact ⟨l, e, by simpa using he⟩
      have hlen : l.length = k := by
        have := congrArg List.length hle; simp at this; omega
      classical
      let H' : History sp (Option Msg) n := fun q => if q = p then l else H q
      have hH'p : H' p = l := by simp [H']
      have hH'q : ∀ q, q ≠ p → H' q = H q := fun q hq => by simp [H', hq]
      have hsuf : ∀ q, ∃ s, H q = H' q ++ s := fun q => by
        by_cases hq : q = p
        · subst hq; exact ⟨[e], by rw [hH'p, hle]⟩
        · exact ⟨[], by rw [hH'q q hq]; simp⟩
      -- the replay of `p` before its last event
      have hrp := hrun p
      rw [hle, anonL_append] at hrp
      obtain ⟨cp', hrp', hlastStep⟩ := irun_append.1 hrp
      have hstep : IStep Pg (h p) (nd p) cp' (anonE e) (c p) := irun_single.1 hlastStep
      let c' : Fin n → ICfg Msg St := fun q => if q = p then cp' else c q
      have hc'p : c' p = cp' := by simp [c']
      have hc'q : ∀ q, q ≠ p → c' q = c q := fun q hq => by simp [c', hq]
      -- hypotheses for `H'`
      have hcaus' : ∀ r a q k j d b, H' r = a ++ LEv.recv q k j d :: b → t q k < t r a.length := by
        intro r a q k0 j d b hr
        obtain ⟨s, hs⟩ := hsuf r
        exact hcaus r a q k0 j d (b ++ s) (by rw [hs, hr]; simp)
      have hm' : RecvMatched H' := by
        intro r a q k0 j d b hr
        obtain ⟨s, hs⟩ := hsuf r
        have hr2 : H r = a ++ LEv.recv q k0 j d :: (b ++ s) := by rw [hs, hr]; simp
        obtain ⟨hne, hsend⟩ := hm r a q k0 j d (b ++ s) hr2
        refine ⟨hne, ?_⟩
        by_cases hqp : q = p
        · subst hqp
          have hk0 : k0 < (H q).length := (List.getElem?_eq_some_iff.1 hsend).1
          have hk0' : k0 < l.length := by
            apply Classical.byContradiction; intro hge
            have hk0e : k0 = k := by omega
            have h1 := hcaus r a q k0 j d (b ++ s) hr2
            have hrp : r ≠ q := fun h => hne h.symm
            have hal : a.length < (H r).length := by rw [hr2]; simp
            have h2 := hT r a.length hal
            rw [hk0e, htk] at h1
            omega
          rw [hH'p]; rw [hle] at hsend
          rwa [List.getElem?_append_left hk0'] at hsend
        · rw [hH'q q hqp]; exact hsend
      have hT' : ∀ q k0, k0 < (H' q).length → t q k0 < T := by
        intro q k0 hk0
        by_cases hqp : q = p
        · subst hqp; rw [hH'p] at hk0
          have := hmono q k0 k (by omega); omega
        · rw [hH'q q hqp] at hk0
          have h1 := hT q k0 hk0
          have h2 : t q k0 ≠ T := fun h2 => hqp (hinj q p k0 k (h2.trans htk.symm))
          omega
      have hrun' : ∀ q, IRun Pg (h q) (nd q) (ICfg.init Pg (tr q)) (anonL (H' q)) (c' q) := by
        intro q
        by_cases hqp : q = p
        · subst hqp; rw [hH'p, hc'p]; exact hrp'
        · rw [hH'q q hqp, hc'q q hqp]; exact hrun q
      obtain ⟨seq, hok, hS, hpend, hsend⟩ := ih H' c' hT' hm' hcaus' hrun'
      -- sends of `H` other than a final one are sends of `H'`
      have hsendH : ∀ L : List (Fin N × Msg), (∀ z ∈ (seqCfg (Cfg.start Pg) seq).log, z ∈ L) →
          (∀ j m, e = LEv.send j (some m) → (g p, m) ∈ L) →
          ∀ q (k0 : Nat) (j : Option (LInp loc)) (m : Msg), (H q)[k0]? = some (LEv.send j (some m)) → (g q, m) ∈ L := by
        intro L hL he q k0 j m hq
        by_cases hqp : q = p
        · subst hqp
          rw [hle] at hq
          by_cases hk0 : k0 < l.length
          · rw [List.getElem?_append_left hk0] at hq
            exact hL _ (hsend q k0 j m (by rw [hH'p]; exact hq))
          · have hk0' : k0 - l.length < 1 := by
              have := (List.getElem?_eq_some_iff.1 hq).1; simp at this; omega
            rw [List.getElem?_append_right (by omega)] at hq
            have : k0 - l.length = 0 := by omega
            rw [this] at hq; simp at hq
            exact he j m hq
        · exact hL _ (hsend q k0 j m (by rw [hH'q q hqp]; exact hq))
      -- the case of an event that changes no BK state
      generalize hcp : c p = cp at hstep
      have hquiet : (c p).s = cp'.s → (∀ m, m ∈ (c p).pend → m ∈ cp'.pend) →
          (∀ j m, e = LEv.send j (some m) → (g p, m) ∈ (seqCfg (Cfg.start Pg) seq).log) →
          ∃ seq : List (Tr N Msg St), SeqOK Pg own (Cfg.start Pg) seq ∧
            (∀ p, (seqCfg (Cfg.start Pg) seq).S (g p) = (c p).s) ∧
            (∀ p m, m ∈ (c p).pend → (g p, m) ∈ (seqCfg (Cfg.start Pg) seq).log) ∧
            (∀ q (k : Nat) (j : Option (LInp loc)) (m : Msg), (H q)[k]? = some (LEv.send j (some m)) →
              (g q, m) ∈ (seqCfg (Cfg.start Pg) seq).log) := by
        intro hs hpd hse
        refine ⟨seq, hok, fun q => ?_, fun q m hmq => ?_, hsendH _ (fun _ h => h) hse⟩
        · by_cases hqp : q = p
          · subst hqp; rw [hS q, hc'p, hs]
          · rw [hS q, hc'q q hqp]
        · by_cases hqp : q = p
          · subst hqp; exact hpend q m (by rw [hc'p]; exact hpd m hmq)
          · exact hpend q m (by rw [hc'q q hqp]; exact hmq)
      cases e with
      | inp j =>
        cases hstep
        exact hquiet (by rw [hcp]) (fun _ h => by rw [hcp] at h; exact h) (fun _ _ h => by cases h)
      | out o =>
        cases hstep
        exact hquiet (by rw [hcp]) (fun _ h => by rw [hcp] at h; exact h) (fun _ _ h => by cases h)
      | commitment γ => cases hstep
      | recv q k0 j d =>
        cases d with
        | none =>
          cases hstep
          exact hquiet (by rw [hcp]) (fun _ h => by rw [hcp] at h; exact h) (fun _ _ h => by cases h)
        | some m =>
          cases hstep
          exact hquiet (by rw [hcp]) (fun _ h => by rw [hcp] at h; exact h) (fun _ _ h => by cases h)
      | send j d =>
        cases d with
        | some m =>
          cases hstep with
          | send hpm =>
            refine hquiet (by rw [hcp]) (fun m' hm' => by
              rw [hcp] at hm'; rw [hpm]; exact List.mem_cons_of_mem _ hm') ?_
            intro j' m' he
            simp only [LEv.send.injEq, Option.some.injEq] at he
            obtain ⟨_, hmm⟩ := he
            subst hmm
            exact hpend p _ (by rw [hc'p, hpm]; exact List.mem_cons_self ..)
        | none =>
          cases hstep with
          | @tick _ st rs hpe hre hst hR =>
            let τ : Tr N Msg St := ⟨g p, st.R, st.s, st.W⟩
            have hcfg : seqCfg (Cfg.start Pg) (seq ++ [τ]) = (seqCfg (Cfg.start Pg) seq).apply τ := by
              rw [seqCfg_append]; rfl
            refine ⟨seq ++ [τ], ?_, fun q => ?_, fun q m hmq => ?_, ?_⟩
            · refine (seqOK_append _ _ _).2 ⟨hok, ⟨?_, ?_⟩, trivial⟩
              · show Pg.step (own (g p)) ((seqCfg (Cfg.start Pg) seq).S (g p)) st.R st.s st.W
                rw [hown, hS p, hc'p]; exact hst
              · intro m hmR
                rcases irun_rcv hrp' m (hR m hmR) with h0 | ⟨j', hj'⟩
                · cases h0
                · obtain ⟨q, k0, hq⟩ := mem_anonL_recv hj'
                  obtain ⟨a, b, hab⟩ := List.append_of_mem hq
                  obtain ⟨hne, hsq⟩ := hm' p a q k0 j' (some m) b (by rw [hH'p]; exact hab)
                  exact ⟨g q, fun h => hne (hg _ _ h), hsend q k0 j' m hsq⟩
            · rw [hcfg]
              show upd _ (g p) st.s (g q) = _
              by_cases hqp : q = p
              · subst hqp; rw [upd_same, hcp]
              · rw [upd_other _ _ (fun h => hqp (hg _ _ h)), hS q, hc'q q hqp]
            · rw [hcfg]
              show _ ∈ _ ++ _
              by_cases hqp : q = p
              · subst hqp
                rw [hcp] at hmq
                exact List.mem_append_right _ (List.mem_map.2 ⟨m, hmq, rfl⟩)
              · exact List.mem_append_left _ (hpend q m (by rw [hc'q q hqp]; exact hmq))
            · rw [hcfg]
              exact hsendH _ (fun z hz => List.mem_append_left _ hz) (fun _ _ h => by cases h)
    · apply ih H c _ hm hcaus hrun
      intro q k0 hk0
      have h1 := hT q k0 hk0
      have h2 : t q k0 ≠ T := fun h2 => hex ⟨q, k0, hk0, h2⟩
      omega

/-- **Linearization.**  A causal history whose local histories are replayed by
traces gives a valid finite BK sequence on any network into which the
participants embed, ending with every participant in its replayed state; the
messages of every send are logged. -/
theorem linearize {n N : Nat} (g : Fin n → Fin N) (hg : ∀ p q, g p = g q → p = q)
    (own : Fin N → PSet F) (h : Fin n → PSet F) (hown : ∀ p, own (g p) = h p)
    (nd : Fin n → Nat) (tr : Fin n → List (LStep Msg St))
    (H : History sp (Option Msg) n) (c : Fin n → ICfg Msg St) (hm : RecvMatched H) (hc : Causal H)
    (hrun : ∀ p, IRun Pg (h p) (nd p) (ICfg.init Pg (tr p)) (anonL (H p)) (c p)) :
    ∃ seq : List (Tr N Msg St), SeqOK Pg own (Cfg.start Pg) seq ∧
      ∀ p, (seqCfg (Cfg.start Pg) seq).S (g p) = (c p).s := by
  obtain ⟨t, hmono, hcaus⟩ := hc
  let t' : Fin n → Nat → Nat := fun p k => t p k * n + p.val
  have hn : ∀ p : Fin n, 0 < n := fun p => Nat.lt_of_le_of_lt (Nat.zero_le _) p.isLt
  have hmono' : ∀ p k k', k < k' → t' p k < t' p k' := by
    intro p k k' hkk
    have := Nat.mul_lt_mul_of_pos_right (hmono p k k' hkk) (hn p)
    show t p k * n + p.val < t p k' * n + p.val
    omega
  have hinj' : ∀ p q k k', t' p k = t' q k' → p = q := by
    intro p q k k' he
    have h1 : (p.val + t p k * n) % n = (q.val + t q k' * n) % n := by
      have : t p k * n + p.val = t q k' * n + q.val := he
      rw [Nat.add_comm p.val, Nat.add_comm q.val, this]
    rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.isLt,
      Nat.mod_eq_of_lt q.isLt] at h1
    exact Fin.ext h1
  have hcaus' : ∀ p a q k j d b, H p = a ++ LEv.recv q k j d :: b → t' q k < t' p a.length := by
    intro p a q k j d b hab
    have h1 := hcaus p a q k j d b hab
    have h2 : (t q k + 1) * n ≤ t p a.length * n := Nat.mul_le_mul_right n h1
    rw [Nat.succ_mul] at h2
    show t q k * n + q.val < t p a.length * n + p.val
    have := q.isLt
    omega
  obtain ⟨B, hB⟩ := exists_bound (fun p => t' p (H p).length)
  obtain ⟨seq, hok, hS, _, _⟩ := linearize_aux g hg own h hown nd tr t' hmono' hinj' B H c
    (fun p k hk => Nat.lt_trans (hmono' p k _ hk) (hB p)) hm hcaus' hrun
  exact ⟨seq, hok, hS⟩

end Linearize

/-! ## T1: computing implies consistency on placed histories -/

/-- The downward closure of `B` on finite networks; any output is allowed at
an input with an infinite network. -/
def downB (B : Spec (LInp loc) (PSet (Nat × Out))) : Spec (LInp loc) (PSet (Nat × Out)) where
  P i o := FinNet loc i.set → ∃ K, B.P i K ∧ o ≼ K
  total i := by
    obtain ⟨K, hK⟩ := B.total i
    exact ⟨K, fun _ => ⟨K, hK, PO.refl _⟩⟩

theorem downB_of_row {B : Spec (LInp loc) (PSet (Nat × Out))} {i : LInp loc} {K : PSet (Nat × Out)}
    (h : B.P i K) : (downB B).P i K := fun _ => ⟨K, h, PO.refl _⟩

theorem pset_ext {α : Type} {s t : PSet α} (h : ∀ x, s.mem x ↔ t.mem x) : s = t := by
  cases s; cases t
  simp only [PSet.mk.injEq]
  exact funext fun x => propext (h x)

section T1

variable {Pg : Prog F Msg St Out} {B : Spec (LInp loc) (PSet (Nat × Out))}

/-- A finite common input extension `j` of the current inputs of a placed
history over `G` has a network extending the participants: `G`'s nodes first,
then `j`'s new nodes. -/
theorem extend_net {n : Nat} {G : PSet F} {node : Fin n → Nat} (j : LInp loc)
    (hinj : ∀ p q, node p = node q → p = q) (hG : ∀ f, G.mem f → j.set.mem f)
    (hnet : ∀ p, Netw loc G (node p)) (hfin : FinNet loc j.set) :
    ∃ (net : Net loc j.set) (g : Fin n → Fin net.N), (∀ p q, g p = g q → p = q) ∧
      ∀ p, net.node (g p) = node p := by
  classical
  obtain ⟨l, hnd, hl⟩ := hfin
  let new := l.filter (fun x => decide (¬ ∃ p, node p = x))
  have hnew : ∀ i : Fin new.length, ¬ ∃ p, node p = new[i] := by
    intro i
    have hmem : new[i] ∈ new := List.getElem_mem ..
    simp only [new, List.mem_filter, decide_eq_true_eq] at hmem
    exact hmem.2
  have hnewl : ∀ i : Fin new.length, new[i] ∈ l := by
    intro i
    have hmem : new[i] ∈ new := List.getElem_mem ..
    exact (List.mem_filter.1 hmem).1
  have hnodup : new.Nodup := List.Pairwise.filter _ hnd
  let node' : Fin (n + new.length) → Nat := CAP.gF node (fun i : Fin new.length => new[i])
  refine ⟨⟨n + new.length, node', fun x y => ?_, fun x => ?_, fun f hf => ?_⟩, Fin.castAdd _,
    fun _ _ => CAP.castAdd_inj, fun p => by simp [node']⟩
  · refine Fin.addCases (motive := fun x => node' x = node' y → x = y) (fun p => ?_) (fun i => ?_) x <;>
    refine Fin.addCases (motive := fun y => _ = node' y → _ = y) (fun q => ?_) (fun i' => ?_) y <;>
    simp only [node', CAP.gF_left, CAP.gF_right] <;> intro h
    · rw [hinj p q h]
    · exact absurd ⟨p, h⟩ (hnew i')
    · exact absurd ⟨q, h.symm⟩ (hnew i)
    · have : i = i' := Fin.ext ((List.Nodup.getElem_inj hnodup).1 h)
      rw [this]
  · refine Fin.addCases (motive := fun x => Netw loc j.set (node' x)) (fun p => ?_) (fun i => ?_) x
    · simp only [node', CAP.gF_left]
      obtain ⟨f, hf, hfl⟩ := hnet p
      exact ⟨f, hG f hf, hfl⟩
    · simp only [node', CAP.gF_right]
      exact (hl _).1 (hnewl i)
  · have hlf : loc f ∈ l := (hl _).2 ⟨f, hf, rfl⟩
    by_cases hp : ∃ p, node p = loc f
    · obtain ⟨p, hp⟩ := hp
      exact ⟨Fin.castAdd _ p, by simp [node', hp]⟩
    · have hm : loc f ∈ new := List.mem_filter.2 ⟨hlf, by simpa using hp⟩
      obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 hm
      refine ⟨Fin.natAdd n ⟨i, hi⟩, ?_⟩
      show node' (Fin.natAdd n ⟨i, hi⟩) = loc f
      simp only [node', CAP.gF_right]; exact hie

/-- **T1.**  If `Pg` computes `B`, its cluster is consistent on placed
histories for the downward closure of `B`. -/
theorem placedConsistent_of_computes (hC : Computes Pg B) :
    PlacedConsistent (sysOf (sp := downB B) Pg) := by
  intro n G node init H hP hW hR j hj
  have hcut := isCut_of_matched hW.matched
  have hj' : ∀ p σ, LRun (canon (downB B) (init p)) ((H p).take (H p).length) σ →
      σ.cur ≼ j := by
    intro p σ hσ; rw [List.take_length] at hσ; exact hj p σ hσ
  suffices hrpc : RPCAt H (fun p => (H p).length) j by
    obtain ⟨ext, τ, hnr, hτ, hrun⟩ := confluent_ext_of_rpc_canonical hW.runs
      (fun p => canonOut_of_produced (sysOf_canonical Pg) hR p _) hj' hrpc
    have hext : Extends H (fun p => (H p).length) (fun q => H q ++ ext q) ext :=
      fun q => by rw [List.take_length]
    have hrun' : ∀ p, LRun (canon (downB B) (init p)) (H p ++ ext p) τ := fun p => by
      simpa [List.take_length] using hrun p
    exact ⟨τ, hτ, ext, wfb_extend hW hcut hext hnr (fun p => ⟨τ, hrun' p⟩), hrun'⟩
  simp only [RPCAt, List.take_length]
  by_cases hfin : FinNet loc j.set
  case neg => exact ⟨⟨fun _ => True⟩, fun hf => absurd hf hfin, fun _ _ _ _ _ => trivial⟩
  by_cases hn : n = 0
  · subst hn
    obtain ⟨K, hK⟩ := B.total j
    exact ⟨K, downB_of_row hK, fun p => p.elim0⟩
  -- current inputs
  have hcur : ∀ p, ∃ σ, LRun (canon (downB B) (init p)) (H p) σ := hW.1
  have hown_j : ∀ p f, j.set.mem f → loc f = node p → (init p).set.mem f := by
    intro p f hf hfl
    obtain ⟨σ, hσ⟩ := hcur p
    have hle : init p ≼ σ.cur := (lrun_mono hσ).1
    have hcl := placed_cur_closed hP p hσ
    by_cases hfc : σ.cur.set.mem f
    · exact (hP.init_own p f).2 ⟨(hcl f hfc).1, hfl⟩
    · have hok := (hj p σ hσ).2 f hf hfc
      obtain ⟨f0, hf0, hf0l⟩ := hP.node_net p
      have hf0i : (init p).set.mem f0 := (hP.init_own p f0).2 ⟨hf0, hf0l⟩
      exact absurd ⟨f0, hle.1 f0 hf0i, hf0l.trans hfl.symm⟩ hok
  have hinit_j : ∀ p f, (init p).set.mem f → j.set.mem f := by
    intro p f hf
    obtain ⟨σ, hσ⟩ := hcur p
    exact (hj p σ hσ).1 f ((lrun_mono hσ).1.1 f hf)
  have hG : ∀ f, G.mem f → j.set.mem f := by
    intro f hf
    obtain ⟨p, hp⟩ := hP.net_node f hf
    exact hinit_j p f ((hP.init_own p f).2 ⟨hf, hp.symm⟩)
  -- the network of `j`
  obtain ⟨net, g, hg, hnode⟩ := extend_net j hP.node_inj hG hP.node_net hfin
  have hown : ∀ p, net.own (g p) = (init p).set := by
    intro p
    apply pset_ext; intro f
    show j.set.mem f ∧ loc f = net.node (g p) ↔ _
    rw [hnode p]
    exact ⟨fun ⟨hf, hfl⟩ => hown_j p f hf hfl,
      fun hf => ⟨hinit_j p f hf, ((hP.init_own p f).1 hf).2⟩⟩
  -- replays
  have hrep : ∀ p, ∃ tr c, IRun Pg (init p).set (node p) (ICfg.init Pg tr) (anonL (H p)) c := by
    intro p
    obtain ⟨f0, hf0, hf0l⟩ := hP.node_net p
    exact irun_of_compliant ⟨f0, (hP.init_own p f0).2 ⟨hf0, hf0l⟩⟩
      (fun f hf => ((hP.init_own p f).1 hf).2) (H p) (hR p)
  let tr := fun p => Classical.choose (hrep p)
  have hrep' : ∀ p, ∃ c, IRun Pg (init p).set (node p) (ICfg.init Pg (tr p)) (anonL (H p)) c :=
    fun p => Classical.choose_spec (hrep p)
  let c := fun p => Classical.choose (hrep' p)
  have hrun : ∀ p, IRun Pg (init p).set (node p) (ICfg.init Pg (tr p)) (anonL (H p)) (c p) :=
    fun p => Classical.choose_spec (hrep' p)
  obtain ⟨seq, hok, hS⟩ := linearize g hg net.own (fun p => (init p).set) hown node tr H c hW.2
    hW.causal hrun
  have hN0 : 0 < net.N :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (g ⟨0, Nat.pos_of_ne_zero hn⟩).isLt
  obtain ⟨ρ, hfair, hcfg⟩ := fair_extension net.own hN0 seq hok
  obtain ⟨T, hq, hB⟩ := hC j.set net ρ hfair
  refine ⟨dout Pg net.node (cfgAt Pg ρ T), downB_of_row hB, fun p o ho => ?_⟩
  have h1 : o ≼ locOut Pg (node p) (c p).s := (irun_outs (hrun p)).2 o (mem_anonL_out ho)
  have h2 : locOut Pg (node p) (c p).s ≼ dout Pg net.node (cfgAt Pg ρ seq.length) := by
    rintro z ⟨hz1, hz2⟩
    refine ⟨g p, by rw [hz1, hnode p], ?_⟩
    rw [hcfg, hS p]; exact hz2
  have h3 := dout_mono net.node hfair.valid (Nat.le_max_right T seq.length)
  rw [hq _ (Nat.le_max_left T seq.length)] at h3
  exact PO.trans h1 (PO.trans h2 h3)

end T1

/-! ## Building causal histories event by event -/

section Build

variable {I' O' : Type} [PO I'] [PO O'] {sp' : Spec I' O'} {D : Type}

/-- Matched receives and a timing with a bound on the events present: what
appending matched events preserves. -/
def Good {n : Nat} (H : History sp' D n) : Prop :=
  RecvMatched H ∧ ∃ (tm : Fin n → Nat → Nat) (Bd : Nat), (∀ p k k', k < k' → tm p k < tm p k') ∧
    (∀ p (a : List (LEv sp' D n)) q k j d b, H p = a ++ LEv.recv q k j d :: b → tm q k < tm p a.length) ∧
    (∀ p k, k < (H p).length → tm p k < Bd)

theorem good_causal {n : Nat} {H : History sp' D n} (h : Good H) : Causal H := by
  obtain ⟨_, tm, _, h1, h2, _⟩ := h
  exact ⟨tm, h1, h2⟩

theorem good_empty {n : Nat} : Good (fun _ => [] : History sp' D n) :=
  ⟨fun p a q k j d b h => by simp at h, fun _ k => k, 0, fun _ _ _ h => h,
    fun p a q k j d b h => by simp at h, fun p k hk => by simp at hk⟩

/-- Append events at participant `p`. -/
def appendAt {n : Nat} (H : History sp' D n) (p : Fin n) (es : List (LEv sp' D n)) : History sp' D n :=
  fun r => if r = p then H p ++ es else H r

theorem appendAt_self {n : Nat} (H : History sp' D n) (p : Fin n) (es : List (LEv sp' D n)) :
    appendAt H p es p = H p ++ es := by simp [appendAt]

theorem appendAt_other {n : Nat} (H : History sp' D n) {p r : Fin n} (es : List (LEv sp' D n))
    (h : r ≠ p) : appendAt H p es r = H r := by simp [appendAt, h]

theorem appendAt_getElem? {n : Nat} (H : History sp' D n) (p : Fin n) (es : List (LEv sp' D n))
    {q : Fin n} {k : Nat} {x : LEv sp' D n} (h : (H q)[k]? = some x) : (appendAt H p es q)[k]? = some x := by
  by_cases hq : q = p
  · subst hq; rw [appendAt_self]
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]; exact h
  · rw [appendAt_other _ _ hq]; exact h

theorem appendAt_mem {n : Nat} (H : History sp' D n) (p : Fin n) (es : List (LEv sp' D n))
    {q : Fin n} {x : LEv sp' D n} (h : x ∈ H q) : x ∈ appendAt H p es q := by
  by_cases hq : q = p
  · subst hq; rw [appendAt_self]; exact List.mem_append_left _ h
  · rw [appendAt_other _ _ hq]; exact h

theorem snoc_split {α : Type} {l a b : List α} {e x : α} (h : l ++ [e] = a ++ x :: b) :
    (a = l ∧ x = e ∧ b = []) ∨ ∃ b', l = a ++ x :: b' := by
  rcases List.append_eq_append_iff.1 h with ⟨a', ha, he⟩ | ⟨c', hl, hc⟩
  · cases a' with
    | nil => simp at he; obtain ⟨rfl, rfl⟩ := he; simp at ha; exact Or.inl ⟨ha, rfl, rfl⟩
    | cons y ys => simp at he
  · cases c' with
    | nil => simp at hc hl; obtain ⟨rfl, rfl⟩ := hc; exact Or.inl ⟨hl.symm, rfl, rfl⟩
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact Or.inr ⟨ys, hl⟩

theorem good_snoc {n : Nat} {H : History sp' D n} (hG : Good H) (p : Fin n) (e : LEv sp' D n)
    (he : ∀ q k j d, e = LEv.recv q k j d → q ≠ p ∧ (H q)[k]? = some (LEv.send j d)) :
    Good (appendAt H p [e]) := by
  classical
  obtain ⟨hm, tm, Bd, hmono, hc, hb⟩ := hG
  -- receives of the new history
  have hcases : ∀ r (a : List (LEv sp' D n)) q k j d b,
      appendAt H p [e] r = a ++ LEv.recv q k j d :: b →
      (r = p ∧ a = H p ∧ e = LEv.recv q k j d) ∨ ∃ b', H r = a ++ LEv.recv q k j d :: b' := by
    intro r a q k j d b hr
    by_cases hrp : r = p
    · subst hrp; rw [appendAt_self] at hr
      rcases snoc_split hr with ⟨h1, h2, _⟩ | h
      · exact Or.inl ⟨rfl, h1, h2.symm⟩
      · exact Or.inr h
    · rw [appendAt_other _ _ hrp] at hr; exact Or.inr ⟨b, hr⟩
  refine ⟨fun r a q k j d b hr => ?_, ?_⟩
  · rcases hcases r a q k j d b hr with ⟨rfl, _, he'⟩ | ⟨b', hb'⟩
    · obtain ⟨hne, hs⟩ := he q k j d he'
      exact ⟨hne, appendAt_getElem? H _ _ hs⟩
    · obtain ⟨hne, hs⟩ := hm r a q k j d b' hb'
      exact ⟨hne, appendAt_getElem? H _ _ hs⟩
  · let tm' : Fin n → Nat → Nat := fun r k => if r = p ∧ (H p).length ≤ k then Bd + (k - (H p).length) else tm r k
    have hlt : ∀ r k, k < (H r).length → tm' r k = tm r k := by
      intro r k hk
      simp only [tm']
      split
      · rename_i hc; obtain ⟨rfl, hk'⟩ := hc; omega
      · rfl
    have hge : ∀ k, (H p).length ≤ k → tm' p k = Bd + (k - (H p).length) := by
      intro k hk; simp only [tm']; split
      · rfl
      · rename_i hc; simp at hc; omega
    refine ⟨tm', Bd + 1, fun r k k' hkk => ?_, fun r a q k j d b hr => ?_, fun r k hk => ?_⟩
    · by_cases hr : r = p
      · subst hr
        by_cases hk' : (H r).length ≤ k'
        · rw [hge k' hk']
          by_cases hk : (H r).length ≤ k
          · rw [hge k hk]; omega
          · have := hb r k (by omega)
            rw [hlt r k (by omega)]; omega
        · rw [hlt r k (by omega), hlt r k' (by omega)]; exact hmono r k k' hkk
      · have e0 : ∀ k0, tm' r k0 = tm r k0 := by
          intro k0
          simp only [tm']
          split
          · rename_i hc; exact absurd hc.1 hr
          · rfl
        rw [e0, e0]; exact hmono r k k' hkk
    · rcases hcases r a q k j d b hr with ⟨rfl, ha, he'⟩ | ⟨b', hb'⟩
      · obtain ⟨hne, hs⟩ := he q k j d he'
        have hk : k < (H q).length := (List.getElem?_eq_some_iff.1 hs).1
        rw [hlt q k hk]
        have := hb q k hk
        have hal : a.length = (H r).length := by rw [ha]
        rw [hal, hge _ (Nat.le_refl _)]; omega
      · obtain ⟨_, hs⟩ := hm r a q k j d b' hb'
        have hk : k < (H q).length := (List.getElem?_eq_some_iff.1 hs).1
        have hal : a.length < (H r).length := by rw [hb']; simp
        rw [hlt q k hk, hlt r a.length hal]
        exact hc r a q k j d b' hb'
    · by_cases hr : r = p
      · subst hr
        rw [appendAt_self] at hk; simp at hk
        by_cases hk' : (H r).length ≤ k
        · rw [hge k hk']; omega
        · rw [hlt r k (by omega)]; have := hb r k (by omega); omega
      · rw [appendAt_other _ _ hr] at hk
        rw [hlt r k hk]; have := hb r k hk; omega

theorem good_append {n : Nat} (p : Fin n) :
    ∀ (es : List (LEv sp' D n)) (H : History sp' D n), Good H →
      (∀ q k j d, LEv.recv q k j d ∈ es → q ≠ p ∧ (H q)[k]? = some (LEv.send j d)) →
      Good (appendAt H p es)
  | [], H, hG, _ => by
    have : appendAt H p [] = H := funext fun r => by
      by_cases hr : r = p
      · subst hr; simp [appendAt]
      · simp [appendAt, hr]
    rw [this]; exact hG
  | e :: es, H, hG, hes => by
    have heq : appendAt H p (e :: es) = appendAt (appendAt H p [e]) p es := funext fun r => by
      by_cases hr : r = p
      · subst hr; simp [appendAt]
      · simp [appendAt, hr]
    rw [heq]
    refine good_append p es _ (good_snoc hG p e (fun q k j d h => hes q k j d (by rw [h]; simp)))
      (fun q k j d h => ?_)
    obtain ⟨hne, hs⟩ := hes q k j d (List.mem_cons_of_mem _ h)
    exact ⟨hne, by rw [appendAt_other _ _ hne]; exact hs⟩

/-- No two receives in a local list name the same send. -/
def LRU {n : Nat} (l : List (LEv sp' D n)) : Prop :=
  ∀ (a : List (LEv sp' D n)) (q : Fin n) (k : Nat) (j : Option I') (d : D) b
    (a' : List (LEv sp' D n)) (j' : Option I') (d' : D) b',
    l = a ++ LEv.recv q k j d :: b → l = a' ++ LEv.recv q k j' d' :: b' → a.length = a'.length

theorem recvUniqueAt_of_LRU {n : Nat} {H : History sp' D n} (h : ∀ p, LRU (H p)) :
    RecvUniqueAt H :=
  fun p a q k j d b a' j' d' b' h1 h2 => h p a q k j d b a' j' d' b' h1 h2

theorem split_app {α : Type} {l1 l2 a b : List α} {e : α} (h : l1 ++ l2 = a ++ e :: b) :
    (∃ b', l1 = a ++ e :: b') ∨ (∃ a', a = l1 ++ a' ∧ l2 = a' ++ e :: b) := by
  rcases List.append_eq_append_iff.1 h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · exact Or.inr ⟨a', h1, h2⟩
  · cases c' with
    | nil => simp at h1 h2; exact Or.inr ⟨[], by simp [h1], by simp [h2]⟩
    | cons x c'' =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inl ⟨c'', h1⟩

theorem LRU_append {n : Nat} {l1 l2 : List (LEv sp' D n)} (h1 : LRU l1) (h2 : LRU l2)
    (hx : ∀ q k j d j' d', LEv.recv q k j d ∈ l1 → LEv.recv q k j' d' ∈ l2 → False) :
    LRU (l1 ++ l2) := by
  intro a q k j d b a' j' d' b' e1 e2
  rcases split_app e1 with ⟨c1, hc1⟩ | ⟨x1, ha1, hx1⟩ <;>
    rcases split_app e2 with ⟨c2, hc2⟩ | ⟨x2, ha2, hx2⟩
  · exact h1 a q k j d c1 a' j' d' c2 hc1 hc2
  · exact (hx q k j d j' d' (by rw [hc1]; simp) (by rw [hx2]; simp)).elim
  · exact (hx q k j' d' j d (by rw [hc2]; simp) (by rw [hx1]; simp)).elim
  · rw [ha1, ha2]; simp only [List.length_append]
    have := h2 x1 q k j d b x2 j' d' b' hx1 hx2; omega

theorem LRU_of_noRecv {n : Nat} {l : List (LEv sp' D n)} (h : ∀ q k j d, LEv.recv q k j d ∉ l) :
    LRU l := by
  intro a q k j d b _ _ _ _ e1 _
  exact absurd (by rw [e1]; simp) (h q k j d)

/-- Receives at different positions name different sends. -/
theorem LRU_of_pairwise {n : Nat} {l : List (LEv sp' D n)}
    (hp : l.Pairwise (fun e e' => ∀ q k j d q' k' j' d', e = LEv.recv q k j d →
      e' = LEv.recv q' k' j' d' → (q, k) ≠ (q', k'))) : LRU l := by
  intro a q k j d b a' j' d' b' e1 e2
  have g1 : l[a.length]? = some (LEv.recv q k j d) := by rw [e1]; simp
  have g2 : l[a'.length]? = some (LEv.recv q k j' d') := by rw [e2]; simp
  obtain ⟨i1, g1'⟩ := List.getElem?_eq_some_iff.1 g1
  obtain ⟨i2, g2'⟩ := List.getElem?_eq_some_iff.1 g2
  rcases Nat.lt_trichotomy a.length a'.length with hlt | heq | hgt
  · have := List.pairwise_iff_getElem.1 hp _ _ i1 i2 hlt
    rw [g1', g2'] at this
    exact (this q k j d q k j' d' rfl rfl rfl).elim
  · exact heq
  · have := List.pairwise_iff_getElem.1 hp _ _ i2 i1 hgt
    rw [g1', g2'] at this
    exact (this q k j' d' q k j d rfl rfl rfl).elim

/-- Appending matched events at every participant. -/
theorem good_family {n : Nat} (H0 : History sp' D n) (es : Fin n → List (LEv sp' D n)) (hG : Good H0)
    (hes : ∀ p q k j d, LEv.recv q k j d ∈ es p → q ≠ p ∧ (H0 q)[k]? = some (LEv.send j d)) :
    Good (fun p => H0 p ++ es p) := by
  classical
  have key : ∀ L : List (Fin n), Good (fun p => if p ∈ L then H0 p ++ es p else H0 p) := by
    intro L
    induction L with
    | nil => simpa using hG
    | cons a L ih =>
      by_cases ha : a ∈ L
      · have : (fun p => if p ∈ a :: L then H0 p ++ es p else H0 p) =
            (fun p => if p ∈ L then H0 p ++ es p else H0 p) := funext fun r => by
          by_cases hr : r = a
          · subst hr; simp [ha]
          · simp [hr]
        rw [this]; exact ih
      · have : (fun p => if p ∈ a :: L then H0 p ++ es p else H0 p) =
            appendAt (fun p => if p ∈ L then H0 p ++ es p else H0 p) a (es a) := funext fun r => by
          by_cases hr : r = a
          · subst hr; simp [appendAt, ha]
          · simp [appendAt, hr]
        rw [this]
        refine good_append a (es a) _ ih (fun q k j d h => ?_)
        obtain ⟨hne, hs⟩ := hes a q k j d h
        refine ⟨hne, ?_⟩
        show (if q ∈ L then H0 q ++ es q else H0 q)[k]? = _
        split
        · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hs).1]; exact hs
        · exact hs
  have := key (List.finRange n)
  simpa using this

end Build

/-! ## T2: characterized rows are covered by placed histories -/

section T2

variable {sp : Spec (LInp loc) (PSet (Nat × Out))} {Pg : Prog F Msg St Out}

/-- The events of a participant before the final phase: sends carrying its
own facts, and receives. -/
def OkEv {n : Nat} (i : LInp loc) : LEv sp (Option Msg) n → Prop
  | .send j _ => j = some i
  | .recv _ _ _ _ => True
  | _ => False

/-- Which events the strategy check needs: sends carry the current input. -/
def OkKind {n : Nat} (cur : LInp loc) : LEv sp (Option Msg) n → Prop
  | .send j _ => j = some cur
  | .commitment _ => False
  | _ => True

theorem irun_prefix {h : PSet F} {nd : Nat} {c c' : ICfg Msg St} {a b : List (LEvA sp (Option Msg))}
    (hr : IRun Pg h nd c (a ++ b) c') : ∃ c'', IRun Pg h nd c a c'' := by
  obtain ⟨c'', h1, _⟩ := irun_append.1 hr
  exact ⟨c'', h1⟩

/-- A replayed local history whose sends carry the current input is
compliant with `sysOf Pg`. -/
theorem compliant_of_irun {n : Nat} {init : Fin n → LInp loc} {p : Fin n} {nd : Nat}
    (hnd : ∀ f, (init p).set.mem f → loc f = nd) {tr : List (LStep Msg St)} {c : ICfg Msg St}
    {l : List (LEv sp (Option Msg) n)} (hr : IRun Pg (init p).set nd (ICfg.init Pg tr) (anonL l) c)
    (hk : ∀ a e b, l = a ++ e :: b → OkKind (curA (init p) (anonL a)) e) :
    Compliant (Allowed (sysOf (sp := sp) Pg) n init p) l := by
  intro a e b hl
  have hr' : IRun Pg (init p).set nd (ICfg.init Pg tr) (anonL a ++ [anonE e] ++ anonL b) c := by
    rw [hl] at hr; simpa using hr
  obtain ⟨c'', hc''⟩ := irun_prefix hr'
  have hke := hk a e b hl
  have hs : ∀ (hK : StratKind (init p) (anonL a) (anonE e)),
      (sysOf (sp := sp) Pg).strat n init p a e :=
    fun hK => strat_sysOf.2 ⟨hK, nd, hnd, tr, c'', hc''⟩
  cases e with
  | inp j => trivial
  | recv q k j d => trivial
  | out o => exact ⟨fun _ _ => Or.inr ⟨o, rfl⟩, hs trivial⟩
  | send j d => exact hs hke
  | commitment γ => exact absurd hke id

theorem curA_noinp {i : LInp loc} :
    ∀ {n : Nat} {a : List (LEv sp (Option Msg) n)}, (∀ e ∈ a, ∀ j, e ≠ LEv.inp j) →
      curA i (anonL a) = i
  | _, [], _ => rfl
  | _, e :: a, h => by
    have ih := curA_noinp (i := i) (a := a) (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    cases e with
    | inp j => exact absurd rfl (h _ (List.mem_cons_self ..) j)
    | out o => exact ih
    | commitment γ => exact ih
    | send j d => exact ih
    | recv q k j d => exact ih

theorem irun_sends {h : PSet F} {nd : Nat} {n : Nat} (j : Option (LInp loc)) :
    ∀ (W : List Msg) (c : ICfg Msg St), c.pend = W →
      IRun Pg h nd c (anonL (W.map (fun m => (LEv.send j (some m) : LEv sp (Option Msg) n))))
        ⟨c.s, c.rcv, [], c.rest⟩
  | [], c, hc => by
    cases c; simp only at hc; subst hc; exact .nil _
  | m :: W, c, hc => .cons (IStep.send hc) (irun_sends j W ⟨c.s, c.rcv, W, c.rest⟩ rfl)

theorem irun_recvsT {h : PSet F} {nd : Nat} {n : Nat} :
    ∀ (l : List (LEv sp (Option Msg) n)), (∀ e ∈ l, ∃ q k j, e = LEv.recv q k j none) →
      ∀ c : ICfg Msg St, IRun Pg h nd c (anonL l) c
  | [], _, c => .nil c
  | e :: l, hl, c => by
    obtain ⟨q, k, j, rfl⟩ := hl e (List.mem_cons_self ..)
    exact .cons IStep.recvT (irun_recvsT l (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) c)

/-- Receives for the messages a transition reads.  A message already
received (in `rcv0`) is not received again: the strategy re-reads it from the
local history, so each send is received at most once by each participant. -/
theorem recv_list {n : Nat} {h : PSet F} {nd : Nat} (H : History sp (Option Msg) n) (x : Fin n)
    (init : Fin n → LInp loc) :
    ∀ (R rcv0 : List Msg), (∀ m ∈ R, ∃ y, y ≠ x ∧ LEv.send (some (init y)) (some m) ∈ H y) →
      ∃ rl : List (LEv sp (Option Msg) n),
        (∀ q k j d, LEv.recv q k j d ∈ rl → q ≠ x ∧ (H q)[k]? = some (LEv.send j d)) ∧
        (∀ e ∈ rl, ∃ q k j m, e = LEv.recv q k j (some m) ∧ m ∉ rcv0) ∧
        rl.Pairwise (fun e e' => ∀ q k j d q' k' j' d', e = LEv.recv q k j d →
          e' = LEv.recv q' k' j' d' → d ≠ d') ∧
        ∀ c : ICfg Msg St, (∀ m ∈ rcv0, m ∈ c.rcv) →
          ∃ rcv', IRun Pg h nd c (anonL rl) ⟨c.s, rcv', c.pend, c.rest⟩ ∧
            (∀ m ∈ c.rcv, m ∈ rcv') ∧ ∀ m ∈ R, m ∈ rcv'
  | [], _, _ => ⟨[], by simp, by simp, .nil, fun c _ => ⟨c.rcv, .nil _, fun _ h => h, by simp⟩⟩
  | m :: R, rcv0, hR => by
    by_cases hm0 : m ∈ rcv0
    · obtain ⟨rl, h1, h2, h3, h4⟩ := recv_list H x init R rcv0
        (fun m' hm' => hR m' (List.mem_cons_of_mem _ hm'))
      refine ⟨rl, h1, h2, h3, fun c hc => ?_⟩
      obtain ⟨rcv', hr, hsub, hR'⟩ := h4 c hc
      refine ⟨rcv', hr, hsub, fun m' hm' => ?_⟩
      rcases List.mem_cons.1 hm' with rfl | hm''
      · exact hsub _ (hc _ hm0)
      · exact hR' m' hm''
    · obtain ⟨y, hy, hmem⟩ := hR m List.mem_cons_self
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hmem
      obtain ⟨rl, h1, h2, h3, h4⟩ := recv_list H x init R (m :: rcv0)
        (fun m' hm' => hR m' (List.mem_cons_of_mem _ hm'))
      refine ⟨LEv.recv y k (some (init y)) (some m) :: rl, fun q k' j d hm' => ?_,
        fun e he => ?_, ?_, fun c hc => ?_⟩
      · rcases List.mem_cons.1 hm' with he | hm''
        · simp only [LEv.recv.injEq] at he
          obtain ⟨rfl, rfl, rfl, rfl⟩ := he
          exact ⟨hy, hk⟩
        · exact h1 q k' j d hm''
      · rcases List.mem_cons.1 he with rfl | he'
        · exact ⟨_, _, _, _, rfl, hm0⟩
        · obtain ⟨q, k', j, m', rfl, hm'⟩ := h2 e he'
          exact ⟨q, k', j, m', rfl, fun h => hm' (List.mem_cons_of_mem _ h)⟩
      · refine List.Pairwise.cons (fun e' he' q k' j d q' k'' j' d' h1' h2' => ?_) h3
        simp only [LEv.recv.injEq] at h1'
        obtain ⟨_, _, _, rfl⟩ := h1'
        obtain ⟨_, _, _, m', he2, hm'⟩ := h2 e' he'
        rw [he2] at h2'
        simp only [LEv.recv.injEq] at h2'
        obtain ⟨_, _, _, rfl⟩ := h2'
        intro hd
        simp only [Option.some.injEq] at hd
        subst hd
        exact hm' List.mem_cons_self
      · obtain ⟨rcv', hr, hsub, hR'⟩ := h4 ⟨c.s, m :: c.rcv, c.pend, c.rest⟩ (fun m' hm' => by
          rcases List.mem_cons.1 hm' with rfl | h
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hc _ h))
        refine ⟨rcv', .cons IStep.recvM hr, fun m' hm' => hsub m' (List.mem_cons_of_mem _ hm'), ?_⟩
        intro m' hm'
        rcases List.mem_cons.1 hm' with rfl | hm''
        · exact hsub _ List.mem_cons_self
        · exact hR' m' hm''

/-- The steps of `x` in the transitions at times `t, …, T' - 1`. -/
def trL {N : Nat} (ρ : Nat → Tr N Msg St) (T' : Nat) (x : Fin N) (t : Nat) : List (LStep Msg St) :=
  ((List.range' t (T' - t)).filter (fun i => decide ((ρ i).x = x))).map
    (fun i => ⟨(ρ i).R, (ρ i).s, (ρ i).W⟩)

theorem trL_succ {N : Nat} (ρ : Nat → Tr N Msg St) {T' t : Nat} (x : Fin N) (ht : t < T') :
    trL ρ T' x t = (if (ρ t).x = x then [⟨(ρ t).R, (ρ t).s, (ρ t).W⟩] else []) ++ trL ρ T' x (t + 1) := by
  unfold trL
  rw [show T' - t = (T' - (t + 1)) + 1 by omega, List.range'_succ, List.filter_cons]
  by_cases hx : (ρ t).x = x <;> simp [hx]

/-- The invariant of the prefix construction at time `t`. -/
def PInv {H : PSet F} (net : Net loc H) (ρ : Nat → Tr net.N Msg St) (T' t : Nat)
    (Hh : History sp (Option Msg) net.N) : Prop :=
  Good Hh ∧ (∀ x e, e ∈ Hh x → OkEv ⟨net.own x⟩ e) ∧
  (∀ x, ∃ rcv, IRun Pg (net.own x) (net.node x) (ICfg.init Pg (trL ρ T' x 0)) (anonL (Hh x))
    ⟨(cfgAt Pg ρ t).S x, rcv, [], trL ρ T' x t⟩) ∧
  (∀ y m, (y, m) ∈ (cfgAt Pg ρ t).log → LEv.send (some ⟨net.own y⟩) (some m) ∈ Hh y) ∧
  (∀ x t0, t0 < t → (ρ t0).x = x → LEv.send (some ⟨net.own x⟩) none ∈ Hh x) ∧
  (∀ x, LRU (Hh x)) ∧ (∀ x q k j d, LEv.recv q k j d ∈ Hh x → ∃ m, d = some m)

/-- The prefix of a run up to `T'` as a history of `sysOf Pg`. -/
theorem build_prefix {H : PSet F} (net : Net loc H) (ρ : Nat → Tr net.N Msg St)
    (hv : ∀ t, Enabled Pg net.own (cfgAt Pg ρ t) (ρ t)) (T' : Nat) :
    ∀ t, t ≤ T' → ∃ Hh : History sp (Option Msg) net.N, PInv (Pg := Pg) net ρ T' t Hh := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun _ => [], good_empty, fun x e he => (by cases he), fun x => ⟨[], .nil _⟩,
      fun y m h => (by cases h), fun x t0 h => absurd h (Nat.not_lt_zero _),
      fun x => LRU_of_noRecv (by simp), fun x q k j d h => by cases h⟩
  | succ t ih =>
    intro ht
    obtain ⟨Hh, hG, hok, hrun, hlog, htick, huq, hsome⟩ := ih (by omega)
    let τ := ρ t
    let x := τ.x
    have hen := hv t
    obtain ⟨rcv0, hr0⟩ := hrun x
    have hR : ∀ m ∈ τ.R, ∃ y, y ≠ x ∧ LEv.send (some ⟨net.own y⟩) (some m) ∈ Hh y := by
      intro m hm
      obtain ⟨y, hy, hl⟩ := hen.2 m hm
      exact ⟨y, hy, hlog y m hl⟩
    obtain ⟨rl, hrlm, hrlk, hrlp, hrlrun⟩ := recv_list (Pg := Pg) (h := net.own x)
      (nd := net.node x) Hh x (fun y => ⟨net.own y⟩) τ.R rcv0 hR
    let tick : LEv sp (Option Msg) net.N := LEv.send (some ⟨net.own x⟩) none
    let sends : List (LEv sp (Option Msg) net.N) := τ.W.map (fun m => LEv.send (some ⟨net.own x⟩) (some m))
    let ev := rl ++ tick :: sends
    have hev_recv : ∀ q k j d, LEv.recv q k j d ∈ ev → LEv.recv q k j d ∈ rl := by
      intro q k j d h
      rcases List.mem_append.1 h with h | h
      · exact h
      · rcases List.mem_cons.1 h with h | h
        · simp [tick] at h
        · simp only [sends, List.mem_map] at h; obtain ⟨_, _, h⟩ := h; cases h
    have hSx : (cfgAt Pg ρ (t + 1)).S x = τ.s := upd_same _ _ _
    have hSy : ∀ y, y ≠ x → (cfgAt Pg ρ (t + 1)).S y = (cfgAt Pg ρ t).S y := fun y hy => upd_other _ _ hy
    have hLRUev : LRU ev := by
      refine LRU_append (LRU_of_pairwise ?_) (LRU_of_noRecv fun q k j d h => ?_)
        (fun q k j d j' d' _ h => ?_)
      · refine hrlp.imp_of_mem fun {e e'} he he' hd q k j d q' k' j' d' h1 h2 hqk => ?_
        subst h1; subst h2
        simp only [Prod.mk.injEq] at hqk
        obtain ⟨rfl, rfl⟩ := hqk
        have g1 := (hrlm q k j d he).2
        have g2 := (hrlm q k j' d' he').2
        rw [g1] at g2
        simp only [Option.some.injEq, LEv.send.injEq] at g2
        exact hd q k j d q k j' d' rfl rfl g2.2
      · rcases List.mem_cons.1 h with h | h
        · simp [tick] at h
        · simp only [sends, List.mem_map] at h; obtain ⟨_, _, h⟩ := h; cases h
      · rcases List.mem_cons.1 h with h | h
        · simp [tick] at h
        · simp only [sends, List.mem_map] at h; obtain ⟨_, _, h⟩ := h; cases h
    have hcross : ∀ q k j d j' d', LEv.recv q k j d ∈ Hh x → LEv.recv q k j' d' ∈ ev → False := by
      intro q k j d j' d' hold hnew
      have hn := hev_recv q k j' d' hnew
      obtain ⟨q1, k1, j1, m, he, hm⟩ := hrlk _ hn
      simp only [LEv.recv.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      have g2 := (hrlm q k j' (some m) hn).2
      obtain ⟨a, b, hab⟩ := List.append_of_mem hold
      have g1 := (hG.1 x a q k j d b hab).2
      rw [g1] at g2
      simp only [Option.some.injEq, LEv.send.injEq] at g2
      obtain ⟨rfl, rfl⟩ := g2
      exact hm ((irun_rcv_grow hr0).2 _ m (recv_mem_anonL hold))
    refine ⟨appendAt Hh x ev, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact good_append x ev Hh hG (fun q k j d h => hrlm q k j d (hev_recv q k j d h))
    · intro y e he
      by_cases hy : y = x
      · subst hy
        rw [appendAt_self] at he
        rcases List.mem_append.1 he with he | he
        · exact hok _ e he
        · rcases List.mem_append.1 he with he | he
          · obtain ⟨q, k, j, d, rfl, _⟩ := hrlk e he; trivial
          · rcases List.mem_cons.1 he with rfl | he
            · rfl
            · simp only [sends, List.mem_map] at he; obtain ⟨m, _, rfl⟩ := he; rfl
      · rw [appendAt_other _ _ hy] at he; exact hok y e he
    · intro y
      by_cases hy : y = x
      · subst hy
        have hr := hr0
        have htr : trL ρ T' τ.x t = ⟨τ.R, τ.s, τ.W⟩ :: trL ρ T' τ.x (t + 1) := by
          rw [trL_succ ρ _ (by omega)]; simp [τ]
        rw [htr] at hr
        obtain ⟨rcv', hr2, _, hRr⟩ := hrlrun ⟨(cfgAt Pg ρ t).S τ.x, rcv0, [], ⟨τ.R, τ.s, τ.W⟩ :: trL ρ T' τ.x (t + 1)⟩
          (fun _ h => h)
        have htk : IStep Pg (net.own τ.x) (net.node τ.x)
            ⟨(cfgAt Pg ρ t).S τ.x, rcv', [], ⟨τ.R, τ.s, τ.W⟩ :: trL ρ T' τ.x (t + 1)⟩
            (LEvA.send (some ⟨net.own τ.x⟩) none : LEvA sp (Option Msg))
            ⟨τ.s, rcv', τ.W, trL ρ T' τ.x (t + 1)⟩ :=
          IStep.tick (st := ⟨τ.R, τ.s, τ.W⟩) (rs := trL ρ T' τ.x (t + 1)) rfl rfl hen.1 hRr
        have hsn := irun_sends (sp := sp) (Pg := Pg) (h := net.own τ.x) (nd := net.node τ.x) (n := net.N)
          (some ⟨net.own τ.x⟩) τ.W ⟨τ.s, rcv', τ.W, trL ρ T' τ.x (t + 1)⟩ rfl
        refine ⟨rcv', ?_⟩
        rw [appendAt_self, hSx]
        rw [anonL_append]
        refine irun_append.2 ⟨_, hr, ?_⟩
        rw [anonL_append]
        exact irun_append.2 ⟨_, hr2, .cons htk hsn⟩
      · obtain ⟨rcv, hr⟩ := hrun y
        have htr : trL ρ T' y t = trL ρ T' y (t + 1) := by
          rw [trL_succ ρ _ (by omega)]
          have : ¬ (ρ t).x = y := fun h => hy h.symm
          simp [this]
        refine ⟨rcv, ?_⟩
        rw [appendAt_other _ _ hy, hSy y hy, ← htr]; exact hr
    · intro y m hm
      rcases List.mem_append.1 hm with hm | hm
      · exact appendAt_mem Hh x ev (hlog y m hm)
      · simp only [List.mem_map] at hm
        obtain ⟨m', hm', he⟩ := hm
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [appendAt_self]
        refine List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ ?_))
        exact List.mem_map.2 ⟨m', hm', rfl⟩
    · intro y t0 ht0 hy
      by_cases ht0' : t0 < t
      · exact appendAt_mem Hh x ev (htick y t0 ht0' hy)
      · have : t0 = t := by omega
        subst this
        have hyx : y = x := hy.symm
        subst hyx
        rw [appendAt_self]
        exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_self ..))
    · intro y
      by_cases hy : y = x
      · subst hy; rw [appendAt_self]; exact LRU_append (huq _) hLRUev hcross
      · rw [appendAt_other _ _ hy]; exact huq y
    · intro y q k j d hm
      by_cases hy : y = x
      · subst hy
        rw [appendAt_self] at hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hsome _ q k j d hm
        · obtain ⟨_, _, _, m, he, _⟩ := hrlk _ (hev_recv q k j d hm)
          simp only [LEv.recv.injEq] at he
          exact ⟨m, he.2.2.2⟩
      · rw [appendAt_other _ _ hy] at hm; exact hsome y q k j d hm

end T2

/-! ### Covered rows and the list form of Prop. 11 -/

section Cover

variable {G' : Type} {sp : Spec (LInp loc) (PSet G')} {D : Type}

/-- `K` is covered by a placed history over `G` that the system produces:
every element of `K` is in some emitted output. -/
def Covers (Sys : System sp D) (G : PSet F) (K : PSet G') : Prop :=
  ∃ (n : Nat) (node : Fin n → Nat) (init : Fin n → LInp loc) (H : History sp D n),
    Placed loc G node init H ∧ WFB init H ∧ Produced Sys n init H ∧
    ∀ z, K.mem z → ∃ p o, LEv.out o ∈ H p ∧ o.mem z

/-- **Necessity, list form.**  For an anonymous cluster consistent on placed
histories, two rows covered over instances with disjoint networks have a
common output extension in `P` at the union (as `nodeMono_of_placedConsistent`,
with all emitted outputs of each witness history). -/
theorem nodeMono_of_placedConsistent_cover {Sys : System sp D} (hA : Sys.Anonymous)
    (hc : PlacedConsistent Sys) (G₁ G₂ : PSet F) (hd : ∀ x, Netw loc G₁ x → ¬ Netw loc G₂ x)
    (K₁ K₂ : PSet G') (h₁ : Covers Sys G₁ K₁) (h₂ : Covers Sys G₂ K₂) :
    ∃ u, sp.P ⟨union G₁ G₂⟩ u ∧ K₁ ≼ u ∧ K₂ ≼ u := by
  obtain ⟨n₁, node₁, init₁, H₁, hP₁, hW₁, hR₁, hm₁⟩ := h₁
  obtain ⟨n₂, node₂, init₂, H₂, hP₂, hW₂, hR₂, hm₂⟩ := h₂
  have hP := placed_glue hd hP₁ hP₂
  have hW := wfb_glue hW₁ hW₂
  have hR := produced_glue hA hR₁ hR₂
  obtain ⟨τ, hτ, ext, _, hrun⟩ := hc _ _ _ _ _ hP hW hR ⟨union G₁ G₂⟩
    (fun p σ hσ => nodeClosed_le (placed_cur_closed hP p hσ))
  obtain ⟨u, hu⟩ := τ.hasCur
  rw [hτ] at hu
  refine ⟨u, τ.sub _ _ hu, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨p, o, ho, hzo⟩ := hm₁ z hz
    have hm : LEv.out o ∈ sideBySide H₁ H₂ (Fin.castAdd n₂ p) ++ ext (Fin.castAdd n₂ p) := by
      rw [sideBySide_left]; exact List.mem_append_left _ (List.mem_map.2 ⟨_, ho, rfl⟩)
    exact lrun_out_mem (hrun _) hm _ _ hu z hzo
  · obtain ⟨p, o, ho, hzo⟩ := hm₂ z hz
    have hm : LEv.out o ∈ sideBySide H₁ H₂ (Fin.natAdd n₁ p) ++ ext (Fin.natAdd n₁ p) := by
      rw [sideBySide_right]; exact List.mem_append_left _ (List.mem_map.2 ⟨_, ho, rfl⟩)
    exact lrun_out_mem (hrun _) hm _ _ hu z hzo

end Cover

section T2final

variable {Pg : Prog F Msg St Out} {B : Spec (LInp loc) (PSet (Nat × Out))}

theorem lrun_quiet {I' O' : Type} [PO I'] [PO O'] {sp' : Spec I' O'} {D : Type} {n : Nat}
    (σ : State sp') :
    ∀ l : List (LEv sp' D n), (∀ e ∈ l, (∃ j d, e = .send j d) ∨ ∃ q k j d, e = .recv q k j d) →
      LRun σ l σ
  | [], _ => .nil σ
  | e :: l, h => by
    have ih := lrun_quiet σ l (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    rcases h e (List.mem_cons_self ..) with ⟨j, d, rfl⟩ | ⟨q, k, j, d, rfl⟩
    · exact .send ih
    · exact .recv ih

theorem last_two {α : Type} (P : α → Prop) {L a b : List α} {e x y : α}
    (hL : ∀ z ∈ L, ¬ P z) (hy : ¬ P y) (h : L ++ [x, y] = a ++ e :: b) (he : P e) :
    a = L ∧ e = x := by
  rcases List.append_eq_append_iff.1 h with ⟨a', ha, hxy⟩ | ⟨c', hl, hc⟩
  · match a', hxy with
    | [], hxy => simp at hxy; exact ⟨by simpa using ha, hxy.1.symm⟩
    | [_], hxy => simp at hxy; obtain ⟨_, rfl, _⟩ := hxy; exact absurd he hy
    | _ :: _ :: _, hxy => simp at hxy
  · cases c' with
    | nil => simp at hc hl; exact ⟨hl.symm, hc.1⟩
    | cons c0 cs =>
      simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, _⟩ := hc
      exact absurd he (hL _ (by rw [hl]; simp))

/-- **T2.**  If `Pg` characterizes `B`, every row of `B` at a nonempty
finite network is covered by a placed history of `sysOf Pg`: run the fair run
up to a time after quiescence at which every node has stepped, let every
participant receive every other participant's first tick (which carries its
own facts), raise its input to the whole instance, and emit its located
output. -/
theorem covers_of_characterizes (hCh : Characterizes Pg B) {H : PSet F} {K : PSet (Nat × Out)}
    (hfin : FinNet loc H) (hne : ∃ f, H.mem f) (hK : B.P ⟨H⟩ K) :
    Covers (sysOf (sp := downB B) Pg) H K := by
  classical
  obtain ⟨net, ρ, hfair, T, hq, hout⟩ := hCh.2 H K hfin hne hK
  have hact : ∀ x, ∃ t, (ρ t).x = x := fun x => by
    obtain ⟨t, _, h⟩ := hfair.active x 0; exact ⟨t, h⟩
  let tx := fun x => Classical.choose (hact x)
  have htx : ∀ x, (ρ (tx x)).x = x := fun x => Classical.choose_spec (hact x)
  obtain ⟨Bd, hBd⟩ := exists_bound tx
  let T' := max Bd T
  obtain ⟨Hh, hG, hok, hrun, _, htick, huq, hsome⟩ :=
    build_prefix (sp := downB B) (Pg := Pg) net ρ hfair.valid T' T' (Nat.le_refl _)
  let init : Fin net.N → LInp loc := fun x => ⟨net.own x⟩
  have hticks : ∀ y, ∃ k, (Hh y)[k]? = some (LEv.send (some (init y)) none) := fun y =>
    List.mem_iff_getElem?.1 (htick y (tx y) (by have := hBd y; omega) (htx y))
  let ky := fun y => Classical.choose (hticks y)
  have hky : ∀ y, (Hh y)[ky y]? = some (LEv.send (some (init y)) none) :=
    fun y => Classical.choose_spec (hticks y)
  let fl : Fin net.N → List (LEv (downB B) (Option Msg) net.N) := fun x =>
    ((List.finRange net.N).filter (fun y => decide (y ≠ x))).map
      (fun y => LEv.recv y (ky y) (some (init y)) none)
  let Kx : Fin net.N → PSet (Nat × Out) := fun x => locOut Pg (net.node x) ((cfgAt Pg ρ T').S x)
  let tail : Fin net.N → List (LEv (downB B) (Option Msg) net.N) := fun x =>
    fl x ++ [LEv.inp (⟨H⟩ : LInp loc), LEv.out (Kx x)]
  let Hf : History (downB B) (Option Msg) net.N := fun x => Hh x ++ tail x
  have hKT : dout Pg net.node (cfgAt Pg ρ T') = K := by rw [hq T' (Nat.le_max_right _ _), hout]
  have hKx : ∀ x, Kx x ≼ K := fun x z hz => by
    rw [← hKT]; exact ⟨x, hz.1, hz.2⟩
  have hfl : ∀ x e, e ∈ fl x → ∃ y, y ≠ x ∧ e = LEv.recv y (ky y) (some (init y)) none := by
    intro x e he
    simp only [fl, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at he
    obtain ⟨y, hy, rfl⟩ := he
    exact ⟨y, hy, rfl⟩
  have hfl_mem : ∀ x y, y ≠ x → LEv.recv y (ky y) (some (init y)) none ∈ fl x := by
    intro x y hy
    simp only [fl, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    exact ⟨y, hy, rfl⟩
  have htail : ∀ x e, e ∈ tail x → (∃ y, y ≠ x ∧ e = LEv.recv y (ky y) (some (init y)) none) ∨
      e = LEv.inp ⟨H⟩ ∨ e = LEv.out (Kx x) := by
    intro x e he
    rcases List.mem_append.1 he with he | he
    · exact Or.inl (hfl x e he)
    · simp at he; exact Or.inr he
  have hHh : ∀ x e, e ∈ Hh x → (∃ j d, e = .send j d) ∨ ∃ q k j d, e = .recv q k j d := by
    intro x e he
    have := hok x e he
    cases e with
    | send j d => exact Or.inl ⟨j, d, rfl⟩
    | recv q k j d => exact Or.inr ⟨q, k, j, d, rfl⟩
    | _ => exact this.elim
  -- receives are matched and the history is causal
  have hGood : Good Hf := by
    refine good_family Hh tail hG (fun p q k j d h => ?_)
    rcases htail p _ h with ⟨y, hy, he⟩ | he | he
    · simp only [LEv.recv.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      exact ⟨hy, hky q⟩
    · cases he
    · cases he
  -- legality
  have hinitH : ∀ x, init x ≼ (⟨H⟩ : LInp loc) := fun x =>
    ⟨fun f hf => hf.1, fun f hfH hfn ⟨g, hg, hgl⟩ => hfn ⟨hfH, hgl.symm.trans hg.2⟩⟩
  have hR0 : ∀ x, (canon (downB B) (init x)).R ⟨H⟩ K := fun x => ⟨downB_of_row hK, hinitH x⟩
  let σ1 := fun x => CALM.inputState (canon (downB B) (init x)) ⟨H⟩ K (hR0 x)
  have hR1 : ∀ x, (σ1 x).R (σ1 x).cur (Kx x) := fun x =>
    ⟨⟨fun _ => ⟨K, hK, hKx x⟩, hinitH x⟩, PO.refl _⟩
  have hLRun : ∀ x, LRun (canon (downB B) (init x)) (Hf x) (outState (σ1 x) (Kx x) (hR1 x)) := by
    intro x
    refine lrun_append.2 ⟨_, lrun_quiet _ (Hh x) (hHh x), lrun_append.2 ⟨_, lrun_quiet _ (fl x) ?_,
      .inp (CALM.step_inputState _ _ _ _) (.out (step_output_outState _) (.nil _))⟩⟩
    intro e he
    obtain ⟨y, _, rfl⟩ := hfl x e he
    exact Or.inr ⟨_, _, _, _, rfl⟩
  have hLRUt : ∀ x, LRU (tail x) := by
    intro x
    refine LRU_append (LRU_of_pairwise ?_) (LRU_of_noRecv (by simp)) (fun _ _ _ _ _ _ _ h => by simp at h)
    have hnd : ((List.finRange net.N).filter (fun y => decide (y ≠ x))).Pairwise (· ≠ ·) :=
      (List.nodup_finRange net.N).filter _
    simp only [fl, List.pairwise_map]
    refine hnd.imp fun {y y'} hyy' q k j d q' k' j' d' h1 h2 hqk => ?_
    simp only [LEv.recv.injEq] at h1 h2
    obtain ⟨rfl, rfl, -, -⟩ := h1
    obtain ⟨rfl, rfl, -, -⟩ := h2
    simp only [Prod.mk.injEq] at hqk
    exact hyy' hqk.1
  have hW : WFB init Hf := by
    refine ⟨fun x => ⟨_, hLRun x⟩, hGood.1, recvUniqueAt_of_LRU fun x => ?_,
      acyclic_of_causal (good_causal hGood)⟩
    refine LRU_append (huq x) (hLRUt x) (fun q k j d j' d' hold hnew => ?_)
    rcases htail x _ hnew with ⟨y, _, he⟩ | he | he
    · simp only [LEv.recv.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨m, rfl⟩ := hsome x _ _ _ _ hold
      obtain ⟨a, b, hab⟩ := List.append_of_mem hold
      have g1 := (hG.1 x a q (ky q) j (some m) b hab).2
      rw [hky q] at g1
      simp at g1
    · cases he
    · cases he
  -- the strategy
  have hP : Produced (sysOf (sp := downB B) Pg) net.N init Hf := by
    intro x
    obtain ⟨rcv, hr⟩ := hrun x
    have hr' : IRun Pg (init x).set (net.node x) (ICfg.init Pg (trL ρ T' x 0)) (anonL (Hf x))
        ⟨(cfgAt Pg ρ T').S x, rcv, [], trL ρ T' x T'⟩ := by
      show IRun Pg (net.own x) _ _ (anonL (Hh x ++ (fl x ++ [LEv.inp ⟨H⟩, LEv.out (Kx x)]))) _
      rw [anonL_append, anonL_append]
      refine irun_append.2 ⟨_, hr, irun_append.2 ⟨_, irun_recvsT _ ?_ _,
        .cons IStep.inp (.cons (IStep.out rfl) (.nil _))⟩⟩
      intro e he
      obtain ⟨y, _, rfl⟩ := hfl x e he
      exact ⟨_, _, _, rfl⟩
    refine compliant_of_irun (init := init) (p := x) (fun f hf => hf.2) hr' (fun a e b hab => ?_)
    have hnot : ∀ (hS : ∀ z ∈ tail x, z ≠ e), ∃ b', Hh x = a ++ e :: b' :=
      fun hS => split_left hab (fun hm => hS e hm rfl)
    cases e with
    | send j d =>
      obtain ⟨b', hb'⟩ := hnot (fun z hz hze => by
        subst hze
        rcases htail x _ hz with ⟨_, _, h⟩ | h | h <;> cases h)
      have hj : j = some (init x) := hok x (LEv.send j d) (by rw [hb']; simp)
      show j = some (curA (init x) (anonL a))
      rw [curA_noinp (fun e' he' j' hej => by
        have := hok x e' (by rw [hb']; exact List.mem_append_left _ he')
        rw [hej] at this; exact this)]
      exact hj
    | commitment γ =>
      have hm : LEv.commitment γ ∈ Hf x := by rw [hab]; simp
      rcases List.mem_append.1 hm with hm | hm
      · exact hok x _ hm
      · rcases htail x _ hm with ⟨_, _, h⟩ | h | h <;> cases h
    | inp j => trivial
    | out o => trivial
    | recv q k j d => trivial
  -- placement
  have hlast : ∀ x a j b, Hf x = a ++ LEv.inp j :: b → a = Hh x ++ fl x ∧ j = ⟨H⟩ := by
    intro x a j b hab
    have h' : (Hh x ++ fl x) ++ [LEv.inp ⟨H⟩, LEv.out (Kx x)] = a ++ LEv.inp j :: b := by
      rw [← hab]; simp [Hf, tail]
    have := last_two (fun e : LEv (downB B) (Option Msg) net.N => ∃ j', e = LEv.inp j')
      (fun z hz ⟨j', hj'⟩ => by
        subst hj'
        rcases List.mem_append.1 hz with hz | hz
        · exact hok x _ hz
        · obtain ⟨_, _, h⟩ := hfl x _ hz; cases h)
      (fun ⟨j', h⟩ => by cases h) h' ⟨j, rfl⟩
    obtain ⟨ha, hj⟩ := this
    exact ⟨ha, by cases hj; rfl⟩
  have hPl : Placed loc H net.node init Hf := by
    refine ⟨net.inj, net.net, net.cover, fun p f => Iff.rfl, fun x a j b hab f hf => ?_,
      fun x a j b hab => ?_⟩
    · obtain ⟨ha, rfl⟩ := hlast x a j b hab
      obtain ⟨y, hy⟩ := net.cover f hf
      by_cases hyx : y = x
      · subst hyx; exact .own hf hy.symm
      · have hm : LEv.recv y (ky y) (some (init y)) none ∈ Hh x ++ fl x :=
          List.mem_append_right _ (hfl_mem x y hyx)
        obtain ⟨m, hmm⟩ := List.mem_iff_getElem?.1 hm
        have hml : m < (Hh x ++ fl x).length := (List.getElem?_eq_some_iff.1 hmm).1
        refine .recv (m := m) (q := y) (k' := ky y) (j := init y) (d := none) ?_ (by rw [ha]; exact hml) ⟨hf, hy.symm⟩
          (.own hf hy.symm)
        have : Hf x = (Hh x ++ fl x) ++ [LEv.inp ⟨H⟩, LEv.out (Kx x)] := by simp [Hf, tail]
        rw [this, List.getElem?_append_left hml]; exact hmm
    · obtain ⟨_, rfl⟩ := hlast x a j b hab
      exact fun f hf => ⟨hf, fun g hg _ => hg⟩
  refine ⟨net.N, net.node, init, Hf, hPl, hW, hP, fun z hz => ?_⟩
  rw [← hKT] at hz
  obtain ⟨x, hz1, hz2⟩ := hz
  exact ⟨x, Kx x, by simp [Hf, tail], hz1, hz2⟩

theorem finNet_union {H₁ H₂ : PSet F} (hd : ∀ x, Netw loc H₁ x → ¬ Netw loc H₂ x)
    (h₁ : FinNet loc H₁) (h₂ : FinNet loc H₂) : FinNet loc (union H₁ H₂) := by
  obtain ⟨l₁, nd₁, hl₁⟩ := h₁
  obtain ⟨l₂, nd₂, hl₂⟩ := h₂
  refine ⟨l₁ ++ l₂, List.nodup_append.2 ⟨nd₁, nd₂, fun a ha b hb hab => ?_⟩, fun x => ?_⟩
  · subst hab; exact hd a ((hl₁ a).1 ha) ((hl₂ a).1 hb)
  · rw [List.mem_append, hl₁, hl₂]
    constructor
    · rintro (⟨f, hf, hfl⟩ | ⟨f, hf, hfl⟩)
      · exact ⟨f, Or.inl hf, hfl⟩
      · exact ⟨f, Or.inr hf, hfl⟩
    · rintro ⟨f, hf | hf, hfl⟩
      · exact Or.inl ⟨f, hf, hfl⟩
      · exact Or.inr ⟨f, hf, hfl⟩

/-- **T3 (Baccaert–Ketsman, Prop. 11).**  A behavior characterized by a node
program under Id+Ord is node monotone on nonempty finite networks.  Through the
translation: `Pg` computes `B`, so `sysOf Pg` is consistent on placed
histories for `downB B` (T1); each row of `B` is covered by a placed history
(T2); the list form of our Prop. 11 gives a common output extension in
`downB B` at the union, hence below a row of `B`. -/
theorem nodeMono_of_characterizes (hCh : Characterizes Pg B) : NodeMonoFin loc B := by
  intro H₁ H₂ hf₁ hf₂ hn₁ hn₂ hd K₁ K₂ hK₁ hK₂
  obtain ⟨u, hu, h1, h2⟩ := nodeMono_of_placedConsistent_cover (sysOf_anonymous Pg)
    (placedConsistent_of_computes hCh.1) H₁ H₂ hd K₁ K₂
    (covers_of_characterizes hCh hf₁ hn₁ hK₁) (covers_of_characterizes hCh hf₂ hn₂ hK₂)
  obtain ⟨K, hK, huK⟩ := hu (finNet_union hd hf₁ hf₂)
  exact ⟨K, hK, PO.trans h1 huK, PO.trans h2 huK⟩

end T2final

end BK
end CC
