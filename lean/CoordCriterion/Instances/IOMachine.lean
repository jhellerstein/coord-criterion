import CoordCriterion.Foundations.IOAutomata
import CoordCriterion.Instances.StateMachine
import CoordCriterion.CompleteCALM.Theorem

/-!
# A state machine with clients and channels as I/O automata

A machine `G : Machine C P Q O`, its clients, and the channel between them
are I/O automata (`Foundations/IOAutomata.lean`) composed in the
Lynch–Tuttle sense.  Each execution is projected onto an *input* (the events
the machine received, ordered by happens-before) and an *output* (the
machine's observation); the pairs form a specification.

The machine (`Machine`) is a general machine automaton: states `Q`, a start
state `q0`, an input-enabled transition relation `recv q p q'` on payloads,
an output relation `out q c o q'` (the machine may emit `o` to client `c`
and move to `q'`), an internal relation `tau q q'`, and `obs : Q → O`.  A
state machine `M : SM.Machine Q P O` is the special case `ofSM M`: `recv` is `M.step`, an output reports `o = M.obs q` without
changing state, and there are no internal steps.

Components (actions `Act C P O`):

* events `Ev C P` carry an identity: the issuing client, a sequence number,
  and a payload;
* the machine `machA G` has inputs `recv e` (it consumes `e.payload` with
  `G.recv`), outputs `out c o` (by `G.out`), and the internal action `tau`
  (by `G.tau`);
* client `c` (`cliA c`) has outputs `send e` for every `e` with
  `e.client = c` and `e.seq` its next sequence number (any payload, at any
  time: clients are maximally nondeterministic) and inputs `out c o`;
* the channel `chanA k` has inputs `send e` and outputs `recv e`; it is a bag
  (`k = .bag`: any message in transit may be delivered next) or a FIFO
  queue (`k = .fifo`).  It neither loses nor duplicates messages; a message
  in transit may stay there forever.

`sys k G` is their composition.  The output `out c o` of the machine is the
same action as the input of client `c`, as in Lynch–Tuttle, so a client's
observation and the machine's report are one event.  Clients do not store
what they observe: since a client may send anything at any time, storing
the observation would not change its possible behaviours; the dependence of
later sends on an observation is recorded by happens-before.

Happens-before (`HB`) is Lamport's relation on the positions of a schedule:
the transitive closure of the local order at each process (the machine and
each client; the channel is not a process) and of the edges from `send e` to
`recv e`.  An `out c o` action is an event of both the machine and client
`c`, so it carries the edge from the machine to the client.

The input of a schedule `β` (`input β : Inp C P`) is the set of events
received by the machine, ordered by happens-before between their sends.
Inputs are ordered by `h ⊑ h'` iff `h`'s events are among `h'`'s and `h'`'s
order restricted to them is `h`'s (`Inp.instPO`).  The induced specification
`spec k G` has as inputs the inputs of executions (`OccInp`) and the row
`(input β, G.obs q)` for each execution `β` ending with machine state `q`.

Results for a general machine:

* `spec` is an ordered specification; inputs grow along executions
  (`input_mono`);
* the fiber at an input consists of observations of states the machine
  automaton reaches on its own executions whose receives are the input's
  events in some order (`fiber_sub_run`), in FIFO order a linear extension
  of the input order; when no client observes, every such machine execution
  over a bag is replayed by a system execution with the same input
  (`bag_arrival_run`, `bag_fiber_of_run`);
* single client, FIFO channel: inputs are chains, `word` is an order
  isomorphism onto payload sequences under prefix, and the fiber at `h` is
  the set of observations of machine executions receiving `word h`
  (`fifo_single_run`, the specification `runSpec G`);
* the machine's observations are confluent across executions iff the
  specification satisfies Lifted Monotonicity, iff it is consistent
  (`confluent_iff_liftedMono`); the same for emitted outputs when outputs
  report observations (`emitConfluent_iff_liftedMono_of`).

For a state machine (`ofSM M`) the results specialize to those of
`Instances/StateMachine.lean`: `fiber_sub`, `bag_arrival`,
`bag_fiber_of_outFree`, `fifo_single` (consistent iff `TransMono M` for
deterministic `M`), `emitConfluent_iff_liftedMono`.  More generally, for a
machine whose output and internal steps leave the state unchanged
(`Stationary`) with deterministic receives, the single-client FIFO
specification is functional and consistent iff `TransMono (recvSM G)`
(`fifo_single_stationary`).
-/

namespace CC
namespace IOM
open IOA

/-- An event: issuing client, sequence number, payload. -/
structure Ev (C P : Type) where
  client : C
  seq : Nat
  payload : P

/-- Actions of the system. -/
inductive Act (C P O : Type) where
  | send (e : Ev C P)
  | recv (e : Ev C P)
  | out (c : C) (o : O)
  | tau

/-- Components of the system. -/
inductive Node (C : Type) where
  | mach
  | cli (c : C)
  | chan

/-- Channel discipline. -/
inductive ChanKind where
  | bag
  | fifo

/-- A general machine automaton: states `Q`, start state `q0`, an
input-enabled relation `recv` on payloads, an output relation `out q c o q'`
(emit `o` to client `c`, moving to `q'`), an internal relation `tau`, and an
observation `obs`. -/
structure Machine (C P Q O : Type) where
  q0 : Q
  recv : Q → P → Q → Prop
  recv_enabled : ∀ q p, ∃ q', recv q p q'
  out : Q → C → O → Q → Prop
  tau : Q → Q → Prop
  obs : Q → O

variable {C P Q O : Type}

/-- A state machine as a machine automaton: outputs report the observation
without changing state, and there are no internal steps. -/
def ofSM (M : SM.Machine Q P O) : Machine C P Q O where
  q0 := M.q0
  recv := M.step
  recv_enabled := M.enabled
  out q _ o q' := o = M.obs q ∧ q' = q
  tau _ _ := False
  obs := M.obs

/-- Delivery of `e` from channel contents `l`, leaving `l'`. -/
def chanRecv : ChanKind → List (Ev C P) → Ev C P → List (Ev C P) → Prop
  | .bag, l, e, l' => ∃ a b, l = a ++ e :: b ∧ l' = a ++ b
  | .fifo, l, e, l' => l = e :: l'

/-! ### The component automata -/

/-- The machine as an I/O automaton. -/
def machA (G : Machine C P Q O) : Automaton (Act C P O) where
  St := Q
  sig := {
    inp := fun a => ∃ e, a = .recv e
    out := fun a => ∃ c o, a = .out c o
    int := fun a => a = .tau
    inp_out := by rintro _ ⟨e, rfl⟩ ⟨c, o, h⟩; cases h
    inp_int := by rintro _ ⟨e, rfl⟩ h; cases h
    out_int := by rintro _ ⟨c, o, rfl⟩ h; cases h }
  start q := q = G.q0
  start_nonempty := ⟨_, rfl⟩
  trans q a q' := match a with
    | .recv e => G.recv q e.payload q'
    | .out c o => G.out q c o q'
    | .tau => G.tau q q'
    | .send _ => False
  trans_acts q a q' h := by
    cases a with
    | send => exact h.elim
    | recv e => exact Or.inl ⟨e, rfl⟩
    | out c o => exact Or.inr (Or.inl ⟨c, o, rfl⟩)
    | tau => exact Or.inr (Or.inr rfl)
  input_enabled q a := by
    rintro ⟨e, rfl⟩
    exact G.recv_enabled q e.payload

/-- Client `c`: its state is its next sequence number. -/
def cliA (c : C) : Automaton (Act C P O) where
  St := Nat
  sig := {
    inp := fun a => ∃ o, a = .out c o
    out := fun a => ∃ e, a = .send e ∧ e.client = c
    int := fun _ => False
    inp_out := by rintro _ ⟨o, rfl⟩ ⟨e, h, _⟩; cases h
    inp_int := fun _ _ h => h
    out_int := fun _ _ h => h }
  start n := n = 0
  start_nonempty := ⟨_, rfl⟩
  trans n a n' := match a with
    | .send e => e.client = c ∧ e.seq = n ∧ n' = n + 1
    | .out c' _ => c' = c ∧ n' = n
    | .recv _ => False
    | .tau => False
  trans_acts n a n' h := by
    cases a with
    | send e => exact Or.inr (Or.inl ⟨e, rfl, h.1⟩)
    | recv => exact h.elim
    | out c' o => exact Or.inl ⟨o, by rw [h.1]⟩
    | tau => exact h.elim
  input_enabled n a := by
    rintro ⟨o, rfl⟩
    exact ⟨n, rfl, rfl⟩

/-- The channel: its state is the list of messages in transit. -/
def chanA (k : ChanKind) : Automaton (Act C P O) where
  St := List (Ev C P)
  sig := {
    inp := fun a => ∃ e, a = .send e
    out := fun a => ∃ e, a = .recv e
    int := fun _ => False
    inp_out := by rintro _ ⟨e, rfl⟩ ⟨e', h⟩; cases h
    inp_int := fun _ _ h => h
    out_int := fun _ _ h => h }
  start l := l = []
  start_nonempty := ⟨_, rfl⟩
  trans l a l' := match a with
    | .send e => l' = l ++ [e]
    | .recv e => chanRecv k l e l'
    | .out _ _ => False
    | .tau => False
  trans_acts l a l' h := by
    cases a with
    | send e => exact Or.inl ⟨e, rfl⟩
    | recv e => exact Or.inr (Or.inl ⟨e, rfl⟩)
    | out => exact h.elim
    | tau => exact h.elim
  input_enabled l a := by
    rintro ⟨e, rfl⟩
    exact ⟨_, rfl⟩

/-- The family of components. -/
def F (k : ChanKind) (G : Machine C P Q O) : Node C → Automaton (Act C P O)
  | .mach => machA G
  | .cli c => cliA c
  | .chan => chanA k

theorem compat (k : ChanKind) (G : Machine C P Q O) : Compatible (F k G) where
  out_disj i j a hi hj := by
    cases i <;> cases j <;> simp only [F, machA, cliA, chanA] at hi hj
    all_goals (try rfl)
    all_goals first
      | (obtain ⟨_, _, rfl⟩ := hi; simp_all)
      | (obtain ⟨_, rfl, _⟩ := hi; simp_all)
      | (obtain ⟨_, rfl⟩ := hi; simp_all)
  int_disj i j a hi hj := by
    cases i with
    | cli => exact hi.elim
    | chan => exact hi.elim
    | mach =>
      have ha : a = .tau := hi
      subst ha
      cases j with
      | mach => rfl
      | cli c => simp [F, cliA, Sig.acts] at hj
      | chan => simp [F, chanA, Sig.acts] at hj

/-- The system: the composition of the machine, the clients, and the
channel. -/
noncomputable def sys (k : ChanKind) (G : Machine C P Q O) : Automaton (Act C P O) :=
  compose (F k G) (compat k G)

/-! ### Flat view of the composite state -/

/-- The composite state, component by component. -/
structure Flat (C P Q : Type) where
  q : Q
  cnt : C → Nat
  ch : List (Ev C P)

section flat

variable [DecidableEq C] in
/-- Increment the sequence number of client `c`. -/
def bump (cnt : C → Nat) (c : C) : C → Nat := fun c' => if c' = c then cnt c' + 1 else cnt c'

variable [DecidableEq C] in
/-- One step of the system, on flat states. -/
inductive FStep (k : ChanKind) (G : Machine C P Q O) :
    Flat C P Q → Act C P O → Flat C P Q → Prop where
  | send (f : Flat C P Q) (e : Ev C P) : e.seq = f.cnt e.client →
      FStep k G f (.send e) ⟨f.q, bump f.cnt e.client, f.ch ++ [e]⟩
  | recv (f : Flat C P Q) (e : Ev C P) (q' : Q) (ch' : List (Ev C P)) :
      G.recv f.q e.payload q' → chanRecv k f.ch e ch' → FStep k G f (.recv e) ⟨q', f.cnt, ch'⟩
  | out (f : Flat C P Q) (c : C) (o : O) (q' : Q) :
      G.out f.q c o q' → FStep k G f (.out c o) ⟨q', f.cnt, f.ch⟩
  | tau (f : Flat C P Q) (q' : Q) : G.tau f.q q' → FStep k G f .tau ⟨q', f.cnt, f.ch⟩

variable {k : ChanKind} {G : Machine C P Q O}

/-- Read a composite state component by component. -/
def toFlat (s : (sys (C := C) k G).St) : Flat C P Q := ⟨s .mach, fun c => s (.cli c), s .chan⟩

/-- Assemble a composite state. -/
def ofFlat (k : ChanKind) (G : Machine C P Q O) (f : Flat C P Q) : (sys (C := C) k G).St :=
  fun n => match n with
    | .mach => f.q
    | .cli c => f.cnt c
    | .chan => f.ch

theorem toFlat_ofFlat (f : Flat C P Q) : toFlat (ofFlat k G f) = f := rfl

theorem acts_mach (a : Act C P O) :
    (F k G .mach).sig.acts a ↔ (match a with | .send _ => False | _ => True) := by
  cases a <;> simp [Sig.acts, F, machA]

theorem acts_cli (c : C) (a : Act C P O) :
    (F k G (.cli c)).sig.acts a ↔
      (match a with
        | .send e => e.client = c
        | .recv _ => False
        | .out c' _ => c' = c
        | .tau => False) := by
  cases a <;> simp [Sig.acts, F, cliA, eq_comm]

theorem acts_chan (a : Act C P O) :
    (F k G .chan).sig.acts a ↔
      (match a with | .send _ => True | .recv _ => True | .out _ _ => False | .tau => False) := by
  cases a <;> simp [Sig.acts, F, chanA]

theorem trans_iff [DecidableEq C] (s s' : (sys (C := C) k G).St) (a : Act C P O) :
    (sys k G).trans s a s' ↔ FStep k G (toFlat s) a (toFlat s') := by
  constructor
  · rintro ⟨_, h⟩
    have hm := h .mach
    have hc := fun c => h (.cli c)
    have hch := h .chan
    cases a with
    | send e =>
      have h2 : e.client = e.client ∧ e.seq = (toFlat s).cnt e.client ∧
          (toFlat s').cnt e.client = (toFlat s).cnt e.client + 1 :=
        (hc e.client).1 ((acts_cli _ _).2 rfl)
      have h3 : ∀ c, c ≠ e.client → (toFlat s').cnt c = (toFlat s).cnt c := fun c hne =>
        (hc c).2 ((not_congr (acts_cli _ _)).2 fun h => hne h.symm)
      have h4 : (toFlat s').ch = (toFlat s).ch ++ [e] := hch.1 ((acts_chan _).2 trivial)
      have h1 : s' .mach = s .mach := hm.2 ((not_congr (acts_mach _)).2 id)
      have : toFlat s' = ⟨(toFlat s).q, bump (toFlat s).cnt e.client, (toFlat s).ch ++ [e]⟩ := by
        show Flat.mk _ _ _ = _
        congr 1
        funext c
        by_cases hce : c = e.client
        · subst hce
          exact h2.2.2.trans (by simp [bump])
        · simp only [bump, hce, ↓reduceIte]; exact h3 c hce
      rw [this]
      exact .send _ _ h2.2.1
    | recv e =>
      have h1 : G.recv (toFlat s).q e.payload (toFlat s').q := hm.1 ((acts_mach _).2 trivial)
      have h3 : ∀ c, (toFlat s').cnt c = (toFlat s).cnt c := fun c =>
        (hc c).2 ((not_congr (acts_cli _ _)).2 id)
      have h4 : chanRecv k (toFlat s).ch e (toFlat s').ch := hch.1 ((acts_chan _).2 trivial)
      have : toFlat s' = ⟨(toFlat s').q, (toFlat s).cnt, (toFlat s').ch⟩ := by
        show Flat.mk _ _ _ = _
        congr 1
        funext c
        exact h3 c
      rw [this]
      exact .recv _ _ _ _ h1 h4
    | out c o =>
      have h1 : G.out (toFlat s).q c o (toFlat s').q := hm.1 ((acts_mach _).2 trivial)
      have h3 : ∀ c', (toFlat s').cnt c' = (toFlat s).cnt c' := by
        intro c'
        by_cases hcc : c = c'
        · subst hcc
          exact ((hc c).1 ((acts_cli _ _).2 rfl) : c = c ∧ _).2
        · exact (hc c').2 ((not_congr (acts_cli _ _)).2 hcc)
      have h4 : (toFlat s').ch = (toFlat s).ch := hch.2 ((not_congr (acts_chan _)).2 id)
      have : toFlat s' = ⟨(toFlat s').q, (toFlat s).cnt, (toFlat s).ch⟩ := by
        show Flat.mk _ _ _ = Flat.mk _ _ _
        congr 1
        · funext c'; exact h3 c'
      rw [this]
      exact .out _ _ _ _ h1
    | tau =>
      have h1 : G.tau (toFlat s).q (toFlat s').q := hm.1 ((acts_mach _).2 trivial)
      have h3 : ∀ c', (toFlat s').cnt c' = (toFlat s).cnt c' := fun c' =>
        (hc c').2 ((not_congr (acts_cli _ _)).2 id)
      have h4 : (toFlat s').ch = (toFlat s).ch := hch.2 ((not_congr (acts_chan _)).2 id)
      have : toFlat s' = ⟨(toFlat s').q, (toFlat s).cnt, (toFlat s).ch⟩ := by
        show Flat.mk _ _ _ = Flat.mk _ _ _
        congr 1
        · funext c'; exact h3 c'
      rw [this]
      exact .tau _ _ h1
  · intro h
    generalize hf : toFlat s = f at h
    generalize hf' : toFlat s' = f' at h
    have eq_q : ∀ (t : (sys (C := C) k G).St) g, toFlat t = g → t .mach = g.q := by
      rintro t g rfl; rfl
    have eq_c : ∀ (t : (sys (C := C) k G).St) g c, toFlat t = g → t (.cli c) = g.cnt c := by
      rintro t g c rfl; rfl
    have eq_ch : ∀ (t : (sys (C := C) k G).St) g, toFlat t = g → t .chan = g.ch := by
      rintro t g rfl; rfl
    cases h with
    | send e hs =>
      refine ⟨⟨.chan, Or.inl ⟨e, rfl⟩⟩, fun n => ?_⟩
      cases n with
      | mach =>
        refine ⟨fun h => ((acts_mach _).1 h).elim, fun _ => ?_⟩
        exact (eq_q s' _ hf').trans (eq_q s _ hf).symm
      | cli c =>
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have hc : e.client = c := (acts_cli _ _).1 h
          subst hc
          show e.client = e.client ∧ e.seq = (toFlat s).cnt e.client ∧
            (toFlat s').cnt e.client = (toFlat s).cnt e.client + 1
          rw [hf, hf']
          exact ⟨rfl, hs, by simp [bump]⟩
        · have hc : ¬ e.client = c := (not_congr (acts_cli _ _)).1 h
          show (toFlat s').cnt c = (toFlat s).cnt c
          rw [hf, hf']
          simp [bump, Ne.symm hc]
      | chan =>
        refine ⟨fun _ => ?_, fun h => ((h ((acts_chan _).2 trivial))).elim⟩
        show (toFlat s').ch = (toFlat s).ch ++ [e]
        rw [hf, hf']
    | recv e q' ch' hs hr =>
      refine ⟨⟨.chan, Or.inr (Or.inl ⟨e, rfl⟩)⟩, fun n => ?_⟩
      cases n with
      | mach =>
        refine ⟨fun _ => ?_, fun h => ((h ((acts_mach _).2 trivial))).elim⟩
        show G.recv (s .mach) e.payload (s' .mach)
        rw [eq_q s' _ hf', eq_q s _ hf]; exact hs
      | cli c =>
        refine ⟨fun h => ((acts_cli _ _).1 h).elim, fun _ => ?_⟩
        exact (eq_c s' _ _ hf').trans (eq_c s _ _ hf).symm
      | chan =>
        refine ⟨fun _ => ?_, fun h => ((h ((acts_chan _).2 trivial))).elim⟩
        show chanRecv k (s .chan) e (s' .chan)
        rw [eq_ch s' _ hf', eq_ch s _ hf]; exact hr
    | out c o q' ho =>
      refine ⟨⟨.mach, Or.inr (Or.inl ⟨c, o, rfl⟩)⟩, fun n => ?_⟩
      cases n with
      | mach =>
        refine ⟨fun _ => ?_, fun h => ((h ((acts_mach _).2 trivial))).elim⟩
        show G.out (s .mach) c o (s' .mach)
        rw [eq_q s' _ hf', eq_q s _ hf]; exact ho
      | cli c' =>
        refine ⟨fun h => ?_, fun _ => (eq_c s' _ _ hf').trans (eq_c s _ _ hf).symm⟩
        have hc : c = c' := (acts_cli _ _).1 h
        exact ⟨hc, (eq_c s' _ _ hf').trans (eq_c s _ _ hf).symm⟩
      | chan =>
        refine ⟨fun h => ((acts_chan _).1 h).elim, fun _ => ?_⟩
        exact (eq_ch s' _ hf').trans (eq_ch s _ hf).symm
    | tau q' ht =>
      refine ⟨⟨.mach, Or.inr (Or.inr rfl)⟩, fun n => ?_⟩
      cases n with
      | mach =>
        refine ⟨fun _ => ?_, fun h => ((h ((acts_mach _).2 trivial))).elim⟩
        show G.tau (s .mach) (s' .mach)
        rw [eq_q s' _ hf', eq_q s _ hf]; exact ht
      | cli c' =>
        refine ⟨fun h => ((acts_cli _ _).1 h).elim, fun _ => ?_⟩
        exact (eq_c s' _ _ hf').trans (eq_c s _ _ hf).symm
      | chan =>
        refine ⟨fun h => ((acts_chan _).1 h).elim, fun _ => ?_⟩
        exact (eq_ch s' _ hf').trans (eq_ch s _ hf).symm

end flat

/-! ### Executions as flat runs -/

section reach
variable {k : ChanKind} {G : Machine C P Q O}

/-- The initial flat state. -/
def init (G : Machine C P Q O) : Flat C P Q := ⟨G.q0, fun _ => 0, []⟩

/-- `β` is the schedule of an execution of the system ending in `f`. -/
def Reach (k : ChanKind) (G : Machine C P Q O) (β : List (Act C P O)) (f : Flat C P Q) : Prop :=
  ∃ s, Execution (sys k G) β s ∧ toFlat s = f

theorem reach_nil {f : Flat C P Q} : Reach k G [] f ↔ f = init G := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    have h := execution_nil_iff.1 hs
    have h1 : s .mach = G.q0 := h .mach
    have h2 : ∀ c, s (.cli c) = (0 : Nat) := fun c => h (.cli c)
    have h3 : s .chan = ([] : List (Ev C P)) := h .chan
    show Flat.mk _ _ _ = Flat.mk _ _ _
    congr 1
    funext c; exact h2 c
  · rintro rfl
    refine ⟨ofFlat k G (init G), execution_nil_iff.2 ?_, rfl⟩
    intro n; cases n <;> rfl

theorem reach_snoc [DecidableEq C] {β : List (Act C P O)} {a : Act C P O} {f' : Flat C P Q} :
    Reach k G (β ++ [a]) f' ↔ ∃ f, Reach k G β f ∧ FStep k G f a f' := by
  constructor
  · rintro ⟨s', hx, rfl⟩
    obtain ⟨m, hm, ht⟩ := execution_snoc_iff.1 hx
    exact ⟨toFlat m, ⟨m, hm, rfl⟩, (trans_iff m s' a).1 ht⟩
  · rintro ⟨f, ⟨s, hs, rfl⟩, hst⟩
    exact ⟨ofFlat k G f', execution_snoc_iff.2 ⟨s, hs, (trans_iff _ _ _).2 hst⟩, rfl⟩

theorem reach_prefix {β γ : List (Act C P O)} {f : Flat C P Q} (h : Reach k G (β ++ γ) f) :
    ∃ f0, Reach k G β f0 := by
  obtain ⟨s, hs, _⟩ := h
  obtain ⟨m, hm⟩ := execution_prefix hs
  exact ⟨_, m, hm, rfl⟩

theorem snoc_ind {α : Type} {p : List α → Prop} (h0 : p []) (h1 : ∀ l a, p l → p (l ++ [a])) :
    ∀ l, p l := by
  have : ∀ r : List α, p r.reverse := by
    intro r
    induction r with
    | nil => exact h0
    | cons a r ih => rw [List.reverse_cons]; exact h1 _ _ ih
  intro l
  simpa using this l.reverse

/-- Induction along executions. -/
theorem reach_induction [DecidableEq C] {p : List (Act C P O) → Flat C P Q → Prop}
    (h0 : p [] (init G))
    (h1 : ∀ β f a f', Reach k G β f → p β f → FStep k G f a f' → p (β ++ [a]) f') :
    ∀ β f, Reach k G β f → p β f := by
  refine snoc_ind (p := fun β => ∀ f, Reach k G β f → p β f) ?_ ?_
  · intro f h
    rw [reach_nil.1 h]; exact h0
  · intro β a ih f' h
    obtain ⟨f, hf, hs⟩ := reach_snoc.1 h
    exact h1 β f a f' hf (ih f hf) hs

end reach

/-! ### Sends, receives, and the execution invariant -/

/-- The event sent by an action, if any. -/
def sendOf : Act C P O → Option (Ev C P)
  | .send e => some e
  | _ => none

/-- The event received by an action, if any. -/
def recvOf : Act C P O → Option (Ev C P)
  | .recv e => some e
  | _ => none

/-- The events sent in `β`, in order. -/
def sends (β : List (Act C P O)) : List (Ev C P) := β.filterMap sendOf

/-- The events received in `β`, in arrival order. -/
def recvs (β : List (Act C P O)) : List (Ev C P) := β.filterMap recvOf

@[simp] theorem sends_append (β γ : List (Act C P O)) : sends (β ++ γ) = sends β ++ sends γ :=
  List.filterMap_append

@[simp] theorem recvs_append (β γ : List (Act C P O)) : recvs (β ++ γ) = recvs β ++ recvs γ :=
  List.filterMap_append

@[simp] theorem sends_nil : sends ([] : List (Act C P O)) = [] := rfl
@[simp] theorem recvs_nil : recvs ([] : List (Act C P O)) = [] := rfl
@[simp] theorem sends_cons_send (e : Ev C P) (β : List (Act C P O)) :
    sends (.send e :: β) = e :: sends β := rfl
@[simp] theorem sends_cons_recv (e : Ev C P) (β : List (Act C P O)) :
    sends (.recv e :: β) = sends β := rfl
@[simp] theorem sends_cons_out (c : C) (o : O) (β : List (Act C P O)) :
    sends (.out c o :: β) = sends β := rfl
@[simp] theorem recvs_cons_send (e : Ev C P) (β : List (Act C P O)) :
    recvs (.send e :: β) = recvs β := rfl
@[simp] theorem recvs_cons_recv (e : Ev C P) (β : List (Act C P O)) :
    recvs (.recv e :: β) = e :: recvs β := rfl
@[simp] theorem recvs_cons_out (c : C) (o : O) (β : List (Act C P O)) :
    recvs (.out c o :: β) = recvs β := rfl
@[simp] theorem sends_cons_tau (β : List (Act C P O)) : sends (.tau :: β) = sends β := rfl
@[simp] theorem recvs_cons_tau (β : List (Act C P O)) : recvs (.tau :: β) = recvs β := rfl

/-- The actions of the machine. -/
def isMach : Act C P O → Bool
  | .send _ => false
  | _ => true

/-- The machine's actions in `β`, in order: the projection of `β` onto the
machine automaton. -/
def macts (β : List (Act C P O)) : List (Act C P O) := β.filter isMach

@[simp] theorem macts_append (β γ : List (Act C P O)) : macts (β ++ γ) = macts β ++ macts γ :=
  List.filter_append ..

@[simp] theorem macts_nil : macts ([] : List (Act C P O)) = [] := rfl
@[simp] theorem macts_cons_send (e : Ev C P) (β : List (Act C P O)) :
    macts (.send e :: β) = macts β := rfl
@[simp] theorem macts_cons_recv (e : Ev C P) (β : List (Act C P O)) :
    macts (.recv e :: β) = .recv e :: macts β := rfl
@[simp] theorem macts_cons_out (c : C) (o : O) (β : List (Act C P O)) :
    macts (.out c o :: β) = .out c o :: macts β := rfl
@[simp] theorem macts_cons_tau (β : List (Act C P O)) : macts (.tau :: β) = .tau :: macts β := rfl

theorem recvs_macts : ∀ β : List (Act C P O), recvs (macts β) = recvs β
  | [] => rfl
  | a :: β => by cases a <;> simp [recvs_macts β]

/-- `macts` is the projection onto the machine component. -/
theorem macts_eq_proj (k : ChanKind) (G : Machine C P Q O) (β : List (Act C P O)) :
    macts β = proj (F k G) .mach β := by
  classical
  simp only [macts, proj]
  congr 1
  funext a
  cases a <;> simp [isMach, Sig.acts, F, machA]

theorem mem_sends {β : List (Act C P O)} {e : Ev C P} : e ∈ sends β ↔ .send e ∈ β := by
  simp only [sends, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    cases a <;> simp [sendOf] at h
    subst h; exact ha
  · intro h; exact ⟨_, h, rfl⟩

theorem mem_recvs {β : List (Act C P O)} {e : Ev C P} : e ∈ recvs β ↔ .recv e ∈ β := by
  simp only [recvs, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    cases a <;> simp [recvOf] at h
    subst h; exact ha
  · intro h; exact ⟨_, h, rfl⟩

theorem chanRecv_perm {k : ChanKind} {l l' : List (Ev C P)} {e : Ev C P}
    (h : chanRecv k l e l') : l.Perm (e :: l') ∧ (k = .fifo → l = e :: l') := by
  cases k with
  | bag =>
    obtain ⟨a, b, rfl, rfl⟩ := h
    exact ⟨List.perm_middle, fun h => nomatch h⟩
  | fifo =>
    cases h
    exact ⟨List.Perm.refl _, fun _ => rfl⟩

section inv
variable [DecidableEq C]

/-- Number of events client `c` sent in `β`. -/
def nSent (β : List (Act C P O)) (c : C) : Nat := ((sends β).filter fun e => e.client = c).length

/-- The invariant of executions. -/
structure Inv (k : ChanKind) (G : Machine C P Q O) (β : List (Act C P O)) (f : Flat C P Q) :
    Prop where
  cnt : ∀ c, f.cnt c = nSent β c
  nodup : (sends β).Nodup
  seq_lt : ∀ e ∈ sends β, e.seq < nSent β e.client
  perm : (sends β).Perm (recvs β ++ f.ch)
  fifo : k = .fifo → sends β = recvs β ++ f.ch
  runs : Run (machA G) G.q0 (macts β) f.q
  incr : (sends β).Pairwise fun a b => a.client = b.client → a.seq < b.seq

theorem nSent_snoc_send (β : List (Act C P O)) (e : Ev C P) (c : C) :
    nSent (β ++ [.send e]) c = nSent β c + (if e.client = c then 1 else 0) := by
  simp only [nSent, sends_append, List.filter_append, List.length_append]
  by_cases h : e.client = c <;> simp [sends, sendOf, h]

theorem nSent_snoc_recv (β : List (Act C P O)) (e : Ev C P) (c : C) :
    nSent (β ++ [.recv e]) c = nSent β c := by
  simp [nSent, sends, sendOf]

theorem nSent_snoc_out (β : List (Act C P O)) (c' : C) (o : O) (c : C) :
    nSent (β ++ [.out c' o]) c = nSent β c := by
  simp [nSent, sends, sendOf]

theorem nSent_snoc_tau (β : List (Act C P O)) (c : C) :
    nSent (β ++ [.tau]) c = nSent β c := by
  simp [nSent, sends, sendOf]

omit [DecidableEq C] in
/-- Extending a run by one step. -/
theorem run_snoc {M : Automaton (Act C P O)} {s m t : M.St} {β : List (Act C P O)} {a : Act C P O}
    (h : Run M s β m) (ht : M.trans m a t) : Run M s (β ++ [a]) t :=
  (run_append_iff β [a]).2 ⟨m, h, run_single_iff.2 ht⟩

theorem reach_inv {k : ChanKind} {G : Machine C P Q O} :
    ∀ (β : List (Act C P O)) (f : Flat C P Q), Reach k G β f → Inv k G β f := by
  refine reach_induction (C := C) (k := k) (G := G) ?_ ?_
  · exact ⟨fun _ => rfl, List.nodup_nil, fun _ h => (nomatch h), List.Perm.refl _,
      fun _ => rfl, Run.nil _, List.Pairwise.nil⟩
  · intro β f a f' _ I hs
    cases hs with
    | send e hseq =>
      have hseq' : e.seq = nSent β e.client := hseq.trans (I.cnt _)
      have hnot : e ∉ sends β := fun h => by
        have := I.seq_lt e h; omega
      refine ⟨fun c => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [nSent_snoc_send]
        by_cases h : e.client = c
        · subst h; simp [bump, I.cnt]
        · simp [bump, Ne.symm h, h, I.cnt]
      · simp only [sends_append, sends_cons_send, sends_nil]
        exact List.nodup_append.2 ⟨I.nodup, List.nodup_cons.2 ⟨fun h => (nomatch h), List.nodup_nil⟩,
          fun a ha b hb => by
            rw [List.mem_singleton] at hb; subst hb
            exact fun h => hnot (h ▸ ha)⟩
      · intro x hx
        rw [nSent_snoc_send]
        simp only [sends_append, sends_cons_send, sends_nil, List.mem_append,
          List.mem_singleton] at hx
        rcases hx with hx | rfl
        · have := I.seq_lt x hx; split <;> omega
        · simp [hseq']
      · simp only [sends_append, sends_cons_send, sends_nil, recvs_append, recvs_cons_send,
          recvs_nil, List.append_nil, ← List.append_assoc]
        exact I.perm.append_right _
      · intro hk
        simp only [sends_append, sends_cons_send, sends_nil, recvs_append, recvs_cons_send,
          recvs_nil, List.append_nil, ← List.append_assoc, I.fifo hk]
      · simpa using I.runs
      · simp only [sends_append, sends_cons_send, sends_nil]
        refine List.pairwise_append.2 ⟨I.incr, List.pairwise_singleton _ _, ?_⟩
        intro x hx y hy hc
        rw [List.mem_singleton] at hy; subst hy
        have := I.seq_lt x hx
        rw [hc] at this; omega
    | recv e q' ch' hstep hr =>
      obtain ⟨hp, hf⟩ := chanRecv_perm hr
      refine ⟨fun c => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [nSent_snoc_recv]; exact I.cnt c
      · simpa using I.nodup
      · intro x hx
        rw [nSent_snoc_recv]
        exact I.seq_lt x (by simpa using hx)
      · simp only [sends_append, sends_cons_recv, sends_nil, List.append_nil, recvs_append,
          recvs_cons_recv, recvs_nil, List.append_assoc, List.singleton_append]
        exact I.perm.trans (hp.append_left _)
      · intro hk
        simp only [sends_append, sends_cons_recv, sends_nil, List.append_nil, recvs_append,
          recvs_cons_recv, recvs_nil, List.append_assoc, List.singleton_append]
        rw [I.fifo hk, hf hk]
      · rw [macts_append]
        exact run_snoc I.runs hstep
      · simpa using I.incr
    | out c o q' ho =>
      refine ⟨fun c' => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [nSent_snoc_out]; exact I.cnt c'
      · simpa using I.nodup
      · intro x hx
        rw [nSent_snoc_out]
        exact I.seq_lt x (by simpa using hx)
      · simpa using I.perm
      · intro hk; simpa using I.fifo hk
      · rw [macts_append]
        exact run_snoc I.runs ho
      · simpa using I.incr
    | tau q' ht =>
      refine ⟨fun c' => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [nSent_snoc_tau]; exact I.cnt c'
      · simpa using I.nodup
      · intro x hx
        rw [nSent_snoc_tau]
        exact I.seq_lt x (by simpa using hx)
      · simpa using I.perm
      · intro hk; simpa using I.fifo hk
      · rw [macts_append]
        exact run_snoc I.runs ht
      · simpa using I.incr

end inv

/-! ### Happens-before -/

/-- Processes: the machine and the clients (the channel is not a process). -/
inductive Proc (C : Type) where
  | mach
  | cli (c : C)

/-- The processes at which an action occurs. -/
def onProc : Act C P O → Proc C → Prop
  | .send e, p => p = .cli e.client
  | .recv _, p => p = .mach
  | .out c _, p => p = .mach ∨ p = .cli c
  | .tau, p => p = .mach

/-- An edge of happens-before between positions `i < j` of `β`: both actions
occur at a common process, or `i` sends the event that `j` receives. -/
def Edge (β : List (Act C P O)) (i j : Nat) : Prop :=
  i < j ∧ ∃ a b, β[i]? = some a ∧ β[j]? = some b ∧
    ((∃ p, onProc a p ∧ onProc b p) ∨ ∃ e, a = .send e ∧ b = .recv e)

/-- Happens-before on the positions of `β` (Lamport). -/
def HB (β : List (Act C P O)) : Nat → Nat → Prop := Relation.TransGen (Edge β)

theorem edge_lt {β : List (Act C P O)} {i j : Nat} (h : Edge β i j) : i < j ∧ j < β.length := by
  obtain ⟨hij, a, b, _, hb, _⟩ := h
  exact ⟨hij, (List.getElem?_eq_some_iff.1 hb).1⟩

theorem hb_lt {β : List (Act C P O)} {i j : Nat} (h : HB β i j) : i < j ∧ j < β.length := by
  induction h with
  | single h => exact edge_lt h
  | tail _ h ih => have := edge_lt h; omega

theorem edge_append {β γ : List (Act C P O)} {i j : Nat} (hj : j < β.length) :
    Edge (β ++ γ) i j ↔ Edge β i j := by
  unfold Edge
  constructor
  · rintro ⟨hij, a, b, ha, hb, h⟩
    rw [List.getElem?_append_left (by omega)] at ha
    rw [List.getElem?_append_left hj] at hb
    exact ⟨hij, a, b, ha, hb, h⟩
  · rintro ⟨hij, a, b, ha, hb, h⟩
    refine ⟨hij, a, b, ?_, ?_, h⟩
    · rw [List.getElem?_append_left (by omega)]; exact ha
    · rw [List.getElem?_append_left hj]; exact hb

/-- Happens-before between positions of a prefix depends only on the
prefix. -/
theorem hb_append {β γ : List (Act C P O)} {i j : Nat} (hj : j < β.length) :
    HB (β ++ γ) i j ↔ HB β i j := by
  constructor
  · intro h
    revert hj
    induction h with
    | single h => intro hj; exact .single ((edge_append hj).1 h)
    | tail _ h2 ih =>
      intro hj
      have := edge_lt h2
      exact .tail (ih (by omega)) ((edge_append hj).1 h2)
  · intro h
    clear hj
    induction h with
    | single h => exact .single ((edge_append (edge_lt h).2).2 h)
    | tail _ h2 ih => exact .tail ih ((edge_append (edge_lt h2).2).2 h2)

/-- Position `i` of `β` sends `e`. -/
def SendAt (β : List (Act C P O)) (i : Nat) (e : Ev C P) : Prop := β[i]? = some (.send e)

theorem sends_sublist_cons (a : Act C P O) (β : List (Act C P O)) :
    (sends β).Sublist (sends (a :: β)) := by
  cases a <;> simp

/-- Sends are unique: an event is sent at most once. -/
theorem sendAt_unique : ∀ {β : List (Act C P O)} {i j : Nat} {e : Ev C P},
    (sends β).Nodup → SendAt β i e → SendAt β j e → i = j
  | [], _, _, _, _, h, _ => by simp [SendAt] at h
  | a :: β, i, j, e, hn, h1, h2 => by
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [SendAt, List.getElem?_cons_zero, Option.some.injEq,
          List.getElem?_cons_succ] at h1 h2
        subst h1
        rw [sends_cons_send, List.nodup_cons] at hn
        exact absurd (mem_sends.2 (List.mem_of_getElem? h2)) hn.1
    | succ i =>
      cases j with
      | zero =>
        simp only [SendAt, List.getElem?_cons_zero, Option.some.injEq,
          List.getElem?_cons_succ] at h1 h2
        subst h2
        rw [sends_cons_send, List.nodup_cons] at hn
        exact absurd (mem_sends.2 (List.mem_of_getElem? h1)) hn.1
      | succ j =>
        simp only [SendAt, List.getElem?_cons_succ] at h1 h2
        exact congrArg (· + 1) (sendAt_unique (hn.sublist (sends_sublist_cons a β)) h1 h2)

theorem sendAt_of_mem {β : List (Act C P O)} {e : Ev C P} (h : e ∈ sends β) :
    ∃ i, SendAt β i e :=
  List.mem_iff_getElem?.1 (mem_sends.1 h)

theorem sendAt_mem {β : List (Act C P O)} {i : Nat} {e : Ev C P} (h : SendAt β i e) :
    e ∈ sends β :=
  mem_sends.2 (List.mem_of_getElem? h)

theorem sendAt_lt {β : List (Act C P O)} {i : Nat} {e : Ev C P} (h : SendAt β i e) :
    i < β.length := (List.getElem?_eq_some_iff.1 h).1

theorem sendAt_append {β γ : List (Act C P O)} {i : Nat} {e : Ev C P} (h : i < β.length) :
    SendAt (β ++ γ) i e ↔ SendAt β i e := by
  unfold SendAt; rw [List.getElem?_append_left h]

theorem sendAt_snoc {β : List (Act C P O)} {a : Act C P O} {i : Nat} {e : Ev C P}
    (ha : a ≠ .send e) : SendAt (β ++ [a]) i e ↔ SendAt β i e := by
  unfold SendAt
  constructor
  · intro h
    rw [List.getElem?_append] at h
    split at h
    · exact h
    · simp [List.getElem?_singleton] at h
      exact absurd h.2 ha
  · intro h
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]; exact h

/-- In the order of sends, a relation that holds between earlier and later
sends holds pairwise. -/
theorem pairwise_sends_of_pos {R : Ev C P → Ev C P → Prop} :
    ∀ {β : List (Act C P O)},
      (∀ i j x y, i < j → SendAt β i x → SendAt β j y → R x y) → (sends β).Pairwise R
  | [], _ => List.Pairwise.nil
  | a :: β, h => by
    have ih := pairwise_sends_of_pos (β := β) fun i j x y hij hx hy =>
      h (i + 1) (j + 1) x y (by omega) hx hy
    cases a with
    | send x =>
      rw [sends_cons_send]
      refine List.pairwise_cons.2 ⟨fun y hy => ?_, ih⟩
      obtain ⟨j, hj⟩ := sendAt_of_mem hy
      exact h 0 (j + 1) x y (by omega) rfl hj
    | recv => exact ih
    | out => exact ih
    | tau => exact ih

/-- Conversely, a pairwise relation on sends holds between earlier and later
sends. -/
theorem pos_of_pairwise_sends {R : Ev C P → Ev C P → Prop} :
    ∀ {β : List (Act C P O)}, (sends β).Pairwise R →
      ∀ i j x y, i < j → SendAt β i x → SendAt β j y → R x y
  | [], _, _, _, _, _, _, h, _ => by simp [SendAt] at h
  | a :: β, hp, i, j, x, y, hij, hx, hy => by
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        simp only [SendAt, List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        rw [sends_cons_send, List.pairwise_cons] at hp
        exact hp.1 y (mem_sends.2 (List.mem_of_getElem? hy))
      | succ i =>
        exact pos_of_pairwise_sends (hp.sublist (sends_sublist_cons a β)) i j x y (by omega) hx hy

/-! ### Inputs -/

/-- An input: a set of events with a strict order on them. -/
structure Inp (C P : Type) where
  mem : Ev C P → Prop
  lt : Ev C P → Ev C P → Prop
  dom : ∀ a b, lt a b → mem a ∧ mem b

theorem Inp.ext' {h h' : Inp C P} (h1 : h.mem = h'.mem) (h2 : h.lt = h'.lt) : h = h' := by
  cases h; cases h'; cases h1; cases h2; rfl

/-- `h ⊑ h'`: `h`'s events are among `h'`'s, and `h'` orders them as `h`
does. -/
instance Inp.instPO : PO (Inp C P) where
  le h h' := (∀ e, h.mem e → h'.mem e) ∧ ∀ a b, h.mem a → h.mem b → (h.lt a b ↔ h'.lt a b)
  refl _ := ⟨fun _ h => h, fun _ _ _ _ => Iff.rfl⟩
  trans h1 h2 := ⟨fun e h => h2.1 e (h1.1 e h), fun a b ha hb =>
    (h1.2 a b ha hb).trans (h2.2 a b (h1.1 a ha) (h1.1 b hb))⟩
  antisymm {h h'} h1 h2 := by
    have hm : h.mem = h'.mem := funext fun e => propext ⟨h1.1 e, h2.1 e⟩
    refine Inp.ext' hm (funext fun a => funext fun b => propext ⟨fun hl => ?_, fun hl => ?_⟩)
    · exact (h1.2 a b (h.dom a b hl).1 (h.dom a b hl).2).1 hl
    · exact (h2.2 a b (h'.dom a b hl).1 (h'.dom a b hl).2).1 hl

/-- The input of a schedule: the events the machine received, ordered by
happens-before between their sends. -/
def input (β : List (Act C P O)) : Inp C P where
  mem e := .recv e ∈ β
  lt a b := (.recv a ∈ β ∧ .recv b ∈ β) ∧ ∃ i j, SendAt β i a ∧ SendAt β j b ∧ HB β i j
  dom _ _ h := h.1

section inputMono
variable [DecidableEq C] {k : ChanKind} {G : Machine C P Q O}

theorem recv_sent {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k G β f) {e : Ev C P}
    (h : .recv e ∈ β) : e ∈ sends β :=
  ((reach_inv β f hr).perm.mem_iff).2 (List.mem_append_left _ (mem_recvs.2 h))

/-- Inputs grow along executions. -/
theorem input_mono {β γ : List (Act C P O)} {f : Flat C P Q} (h : Reach k G (β ++ γ) f) :
    input β ≼ input (β ++ γ) := by
  obtain ⟨f0, h0⟩ := reach_prefix h
  have hn := (reach_inv _ _ h).nodup
  refine ⟨fun e he => List.mem_append_left _ he, fun a b ha hb => ⟨?_, ?_⟩⟩
  · rintro ⟨_, i, j, hi, hj, hij⟩
    exact ⟨⟨List.mem_append_left _ ha, List.mem_append_left _ hb⟩, i, j,
      (sendAt_append (sendAt_lt hi)).2 hi, (sendAt_append (sendAt_lt hj)).2 hj,
      (hb_append (sendAt_lt hj)).2 hij⟩
  · rintro ⟨_, i, j, hi, hj, hij⟩
    obtain ⟨i0, hi0⟩ := sendAt_of_mem (recv_sent h0 ha)
    obtain ⟨j0, hj0⟩ := sendAt_of_mem (recv_sent h0 hb)
    have e1 := sendAt_unique hn hi ((sendAt_append (sendAt_lt hi0)).2 hi0)
    have e2 := sendAt_unique hn hj ((sendAt_append (sendAt_lt hj0)).2 hj0)
    subst e1 e2
    exact ⟨⟨ha, hb⟩, i, j, hi0, hj0, (hb_append (sendAt_lt hj0)).1 hij⟩

/-- An event is sent before it is received. -/
theorem send_before_recv {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k G β f)
    {r : Nat} {e : Ev C P} (hrv : β[r]? = some (.recv e)) : ∃ i, SendAt β i e ∧ i < r := by
  have hlt : r < β.length := (List.getElem?_eq_some_iff.1 hrv).1
  have hsplit := List.take_append_drop (r + 1) β
  have hr' : Reach k G (β.take (r + 1) ++ β.drop (r + 1)) f := by rw [hsplit]; exact hr
  obtain ⟨f0, h0⟩ := reach_prefix hr'
  have hmem : Act.recv e ∈ β.take (r + 1) := by
    refine List.mem_of_getElem? (i := r) ?_
    rw [List.getElem?_take_of_lt (by omega)]; exact hrv
  obtain ⟨i, hi⟩ := sendAt_of_mem (recv_sent h0 hmem)
  have hil : i < r + 1 := by have := sendAt_lt hi; simp at this; omega
  have hi' : SendAt β i e := by
    have := (sendAt_append (γ := β.drop (r + 1)) (sendAt_lt hi)).2 hi
    rwa [hsplit] at this
  refine ⟨i, hi', ?_⟩
  rcases Nat.lt_or_ge i r with h | h
  · exact h
  · have : i = r := by omega
    subst this
    unfold SendAt at hi'
    rw [hrv] at hi'
    cases hi'

/-- **A client's later sends happen after what an output reflected.**  If
the machine received `e` (position `r`) before emitting `out c o`
(position `m`), and client `c` later sends `e'` (position `j`), then the
send of `e` happens before the send of `e'`, `e'` is delivered after `e`,
and if the machine received `e'` the input orders `e` before `e'`. -/
theorem send_after_out {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k G β f)
    {m r j : Nat} {c : C} {o : O} {e e' : Ev C P}
    (hm : β[m]? = some (.out c o)) (hrv : β[r]? = some (.recv e)) (hrm : r < m)
    (hj : SendAt β j e') (hmj : m < j) (hc : e'.client = c) :
    (∃ i, SendAt β i e ∧ HB β i j) ∧ (∀ t, β[t]? = some (.recv e') → r < t) ∧
      (.recv e' ∈ β → (input β).lt e e') := by
  obtain ⟨i, hi, hir⟩ := send_before_recv hr hrv
  have hij : HB β i j := by
    refine .tail (.tail (.single ⟨hir, _, _, hi, hrv, .inr ⟨e, rfl, rfl⟩⟩)
      ⟨hrm, _, _, hrv, hm, .inl ⟨.mach, rfl, .inl rfl⟩⟩) ⟨hmj, _, _, hm, hj, .inl ⟨.cli c, .inr rfl, ?_⟩⟩
    show Proc.cli c = Proc.cli e'.client
    rw [hc]
  refine ⟨⟨i, hi, hij⟩, fun t ht => ?_, fun he' => ⟨⟨List.mem_of_getElem? hrv, he'⟩, i, j, hi, hj, hij⟩⟩
  obtain ⟨j', hj', hjt⟩ := send_before_recv hr ht
  have := sendAt_unique (reach_inv β f hr).nodup hj' hj
  omega

end inputMono

/-- Appending a report does not change the input. -/
theorem input_snoc_out (β : List (Act C P O)) (c : C) (o : O) :
    input (β ++ [.out c o]) = input β := by
  have hs : ∀ i e, SendAt (β ++ [.out c o]) i e ↔ SendAt β i e := fun _ _ => sendAt_snoc nofun
  have hr : ∀ e, Act.recv e ∈ β ++ [.out c o] ↔ Act.recv e ∈ β := by simp
  refine Inp.ext' (funext fun e => propext (hr e)) (funext fun a => funext fun b => propext ?_)
  constructor
  · rintro ⟨⟨ha, hb⟩, i, j, hi, hj, hij⟩
    have hj' := (hs j b).1 hj
    exact ⟨⟨(hr a).1 ha, (hr b).1 hb⟩, i, j, (hs i a).1 hi, hj',
      (hb_append (sendAt_lt hj')).1 hij⟩
  · rintro ⟨⟨ha, hb⟩, i, j, hi, hj, hij⟩
    exact ⟨⟨(hr a).2 ha, (hr b).2 hb⟩, i, j, (hs i a).2 hi, (hs j b).2 hj,
      (hb_append (sendAt_lt hj)).2 hij⟩

/-! ### The induced specification (T1) -/

/-- `h` is the input of some execution. -/
def Occurs (k : ChanKind) (G : Machine C P Q O) (h : Inp C P) : Prop :=
  ∃ β s, Execution (sys k G) β s ∧ input β = h

/-- Inputs of executions. -/
structure OccInp (C P : Type) (k : ChanKind) (G : Machine C P Q O) where
  val : Inp C P
  occ : Occurs k G val

instance OccInp.instPO (k : ChanKind) (G : Machine C P Q O) : PO (OccInp C P k G) where
  le a b := a.val ≼ b.val
  refl a := PO.refl a.val
  trans h1 h2 := PO.trans h1 h2
  antisymm {a b} h1 h2 := by
    have := PO.antisymm h1 h2
    cases a; cases b; cases this; rfl

/-- **The induced specification (T1).**  Inputs are the inputs of
executions, ordered by `⊑`; the row `(input β, G.obs q)` is present for
each execution `β` that leaves the machine in state `q`.  It is total since
every input comes from an execution. -/
def spec [PO O] (k : ChanKind) (G : Machine C P Q O) : Spec (OccInp C P k G) O where
  S h o := ∃ β s, Execution (sys k G) β s ∧ input β = h.val ∧ G.obs (s .mach) = o
  total h := by
    obtain ⟨β, s, hx, hi⟩ := h.occ
    exact ⟨_, β, s, hx, hi, rfl⟩

section rows
variable [PO O] {k : ChanKind} {G : Machine C P Q O}

theorem spec_iff (h : OccInp C P k G) (o : O) :
    (spec k G).S h o ↔ ∃ β f, Reach k G β f ∧ input β = h.val ∧ G.obs f.q = o := by
  constructor
  · rintro ⟨β, s, hx, hi, ho⟩
    exact ⟨β, toFlat s, ⟨s, hx, rfl⟩, hi, ho⟩
  · rintro ⟨β, f, ⟨s, hx, rfl⟩, hi, ho⟩
    exact ⟨β, s, hx, hi, ho⟩

/-- The input of a reachable schedule, as an element of `OccInp`. -/
def occOf {β : List (Act C P O)} {f : Flat C P Q} (h : Reach k G β f) : OccInp C P k G :=
  ⟨input β, by obtain ⟨s, hx, _⟩ := h; exact ⟨β, s, hx, rfl⟩⟩

theorem spec_of_reach {β : List (Act C P O)} {f : Flat C P Q} (h : Reach k G β f) :
    (spec k G).S (occOf h) (G.obs f.q) :=
  (spec_iff _ _).2 ⟨β, f, h, rfl, rfl⟩

end rows

/-! ### Confluence across executions (T4) -/

theorem choose_list {R X : Type} {p : R → X → Prop} :
    ∀ rows : List R, (∀ r ∈ rows, ∃ x, p r x) →
      ∃ l : List (R × X), l.map Prod.fst = rows ∧ ∀ q ∈ l, p q.1 q.2
  | [], _ => ⟨[], rfl, fun _ h => nomatch h⟩
  | r :: rows, h => by
    obtain ⟨x, hx⟩ := h r (List.mem_cons_self ..)
    obtain ⟨l, hl, hp⟩ := choose_list rows fun r hr => h r (List.mem_cons_of_mem _ hr)
    refine ⟨(r, x) :: l, by simp [hl], fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hx
    · exact hp q hq

section confluence
variable [PO O] [DecidableEq C] (k : ChanKind) (G : Machine C P Q O)

/-- The machine's outputs are confluent across executions: for every finite
family of executions `βᵣ` ending in states `sᵣ`, and every execution `β`
whose input expands every input of the family, some execution with the same
input as `β` leaves the machine with an observation that refines the
observation at the end of every `βᵣ`. -/
def ObsConfluent : Prop :=
  ∀ fam : List (List (Act C P O) × (sys (C := C) k G).St),
    (∀ r ∈ fam, Execution (sys k G) r.1 r.2) →
    ∀ β s, Execution (sys k G) β s → (∀ r ∈ fam, input r.1 ≼ input β) →
      ∃ β' s', Execution (sys k G) β' s' ∧ input β' = input β ∧
        ∀ r ∈ fam, G.obs (r.2 .mach) ≼ G.obs (s' .mach)

/-- The same with outputs the machine emitted: `oᵣ` is reported by an
action `out c oᵣ` of `βᵣ`. -/
def EmitConfluent : Prop :=
  ∀ fam : List (List (Act C P O) × O),
    (∀ r ∈ fam, (∃ s, Execution (sys (C := C) k G) r.1 s) ∧ ∃ c, Act.out c r.2 ∈ r.1) →
    ∀ β s, Execution (sys k G) β s → (∀ r ∈ fam, input r.1 ≼ input β) →
      ∃ β' s', Execution (sys k G) β' s' ∧ input β' = input β ∧
        ∀ r ∈ fam, r.2 ≼ G.obs (s' .mach)

omit [DecidableEq C] in
theorem obsConfluent_iff_commonExpansion : ObsConfluent (C := C) k G ↔ (spec (C := C) k G).CommonExpansion := by
  constructor
  · intro hO rows hrows j hj
    obtain ⟨l, hl, hp⟩ := choose_list (X := List (Act C P O) × (sys (C := C) k G).St)
      (p := fun r x => Execution (sys k G) x.1 x.2 ∧ input x.1 = r.1.val ∧
        G.obs (x.2 .mach) = r.2) rows (fun r hr => by
          obtain ⟨β, s, h1, h2, h3⟩ := hrows r hr
          exact ⟨(β, s), h1, h2, h3⟩)
    obtain ⟨β, s, hx, hi⟩ := j.occ
    have hmem : ∀ q ∈ l, q.1 ∈ rows := fun q hq => hl ▸ List.mem_map_of_mem hq
    obtain ⟨β', s', hx', hi', ho⟩ := hO (l.map Prod.snd)
      (fun r hr => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
        exact (hp q hq).1) β s hx
      (fun r hr => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
        rw [(hp q hq).2.1, hi]
        exact hj q.1 (hmem q hq))
    refine ⟨G.obs (s' .mach), ⟨β', s', hx', hi'.trans hi, rfl⟩, fun r hr => ?_⟩
    rw [← hl] at hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
    rw [← (hp q hq).2.2]
    exact ho q.2 (List.mem_map_of_mem hq)
  · intro hC fam hfam β s hx hle
    let row : {r // r ∈ fam} → OccInp C P k G × O := fun r =>
      (⟨input r.1.1, r.1.1, r.1.2, hfam r.1 r.2, rfl⟩, G.obs (r.1.2 .mach))
    obtain ⟨u, hu, hall⟩ := hC (fam.attach.map row)
      (fun r hr => by
        obtain ⟨r, _, rfl⟩ := List.mem_map.1 hr
        exact ⟨r.1.1, r.1.2, hfam r.1 r.2, rfl, rfl⟩)
      ⟨input β, β, s, hx, rfl⟩
      (fun r hr => by
        obtain ⟨r, _, rfl⟩ := List.mem_map.1 hr
        exact hle r.1 r.2)
    obtain ⟨β', s', hx', hi', rfl⟩ := hu
    exact ⟨β', s', hx', hi', fun r hr =>
      hall (row ⟨r, hr⟩) (List.mem_map.2 ⟨⟨r, hr⟩, List.mem_attach _ _, rfl⟩)⟩

omit [PO O] [DecidableEq C] in
/-- Outputs report observations: every emitted value is the observation of
the state before or after the output step. -/
def OutReports : Prop := ∀ q c o q', G.out q c o q' → o = G.obs q ∨ o = G.obs q'

omit [PO O] [DecidableEq C] in
/-- Every state can report its observation to some client. -/
def OutEnabled : Prop := ∀ q, ∃ c q', G.out q c (G.obs q) q'

omit [PO O] in
theorem fstep_out {f f' : Flat C P Q} {c : C} {o : O} (h : FStep k G f (.out c o) f') :
    G.out f.q c o f'.q := by
  cases h; assumption

/-- If every state can report its observation, emitted-output confluence
implies the common-expansion condition. -/
theorem commonExpansion_of_emitConfluent (hE : OutEnabled G) :
    EmitConfluent (C := C) k G → (spec (C := C) k G).CommonExpansion := by
  intro hE' rows hrows j hj
  obtain ⟨l, hl, hp⟩ := choose_list (X := List (Act C P O))
    (p := fun r x => (∃ s, Execution (sys (C := C) k G) x s) ∧ (∃ c, Act.out c r.2 ∈ x) ∧
      input x = r.1.val) rows (fun r hr => by
        obtain ⟨β, f, hf, hi, ho⟩ := (spec_iff _ _).1 (hrows r hr)
        obtain ⟨c, q', hq'⟩ := hE f.q
        rw [ho] at hq'
        have hf' : Reach k G (β ++ [.out c r.2]) ⟨q', f.cnt, f.ch⟩ :=
          reach_snoc.2 ⟨f, hf, FStep.out f c _ q' hq'⟩
        obtain ⟨s, hs, _⟩ := hf'
        exact ⟨β ++ [.out c r.2], ⟨s, hs⟩, ⟨c, by simp⟩, by rw [input_snoc_out, hi]⟩)
  obtain ⟨β, s, hx, hi⟩ := j.occ
  have hmem : ∀ q ∈ l, q.1 ∈ rows := fun q hq => hl ▸ List.mem_map_of_mem hq
  obtain ⟨β', s', hx', hi', ho⟩ := hE' (l.map fun q => (q.2, q.1.2))
    (fun r hr => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      exact ⟨(hp q hq).1, (hp q hq).2.1⟩) β s hx
    (fun r hr => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      show input q.2 ≼ input β
      rw [(hp q hq).2.2, hi]
      exact hj q.1 (hmem q hq))
  refine ⟨G.obs (s' .mach), ⟨β', s', hx', hi'.trans hi, rfl⟩, fun r hr => ?_⟩
  rw [← hl] at hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
  exact ho (q.2, q.1.2) (List.mem_map_of_mem hq)

/-- If outputs report observations, the common-expansion condition implies
emitted-output confluence. -/
theorem emitConfluent_of_commonExpansion (hR : OutReports G) :
    (spec (C := C) k G).CommonExpansion → EmitConfluent (C := C) k G := by
  intro hC fam hfam β s hx hle
  obtain ⟨l, hl, hp⟩ := choose_list (X := OccInp C P k G)
    (p := fun r x => (spec k G).S x r.2 ∧ x.val ≼ input r.1) fam (fun r hr => by
      obtain ⟨⟨s0, hs0⟩, c, hc⟩ := hfam r hr
      obtain ⟨β0, γ, he⟩ := List.append_of_mem hc
      have hR' : Reach k G ((β0 ++ [.out c r.2]) ++ γ) (toFlat s0) :=
        ⟨s0, by rw [List.append_assoc, List.singleton_append, ← he]; exact hs0, rfl⟩
      obtain ⟨f1, h1⟩ := reach_prefix hR'
      obtain ⟨f0, h0, hst⟩ := reach_snoc.1 h1
      have hmono1 : input (β0 ++ [.out c r.2]) ≼ input r.1 := by
        have := input_mono (k := k) (G := G) hR'
        rwa [List.append_assoc, List.singleton_append, ← he] at this
      rcases hR _ _ _ _ (fstep_out k G hst) with ho | ho
      · refine ⟨occOf h0, (spec_iff _ _).2 ⟨_, f0, h0, rfl, ho.symm⟩, ?_⟩
        show input β0 ≼ input r.1
        rw [← input_snoc_out β0 c r.2]
        exact hmono1
      · exact ⟨occOf h1, (spec_iff _ _).2 ⟨_, f1, h1, rfl, ho.symm⟩, hmono1⟩)
  have hmem : ∀ q ∈ l, q.1 ∈ fam := fun q hq => hl ▸ List.mem_map_of_mem hq
  obtain ⟨u, hu, hall⟩ := hC (l.map fun q => (q.2, q.1.2))
    (fun r hr => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      exact (hp q hq).1)
    ⟨input β, β, s, hx, rfl⟩
    (fun r hr => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      exact (PO.trans (hp q hq).2 (hle q.1 (hmem q hq)) : q.2.val ≼ input β))
  obtain ⟨β', s', hx', hi', rfl⟩ := hu
  refine ⟨β', s', hx', hi', fun r hr => ?_⟩
  rw [← hl] at hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
  exact hall (q.2, q.1.2) (List.mem_map_of_mem hq)

theorem emitConfluent_iff_commonExpansion_of (hR : OutReports G) (hE : OutEnabled G) :
    EmitConfluent (C := C) k G ↔ (spec (C := C) k G).CommonExpansion :=
  ⟨commonExpansion_of_emitConfluent k G hE, emitConfluent_of_commonExpansion k G hR⟩

omit [DecidableEq C] in
/-- **T4.**  The machine's outputs are confluent across executions iff the
induced specification satisfies Lifted Monotonicity, iff it is consistent
(Complete CALM). -/
theorem confluent_iff_liftedMono :
    (ObsConfluent (C := C) k G ↔ (spec (C := C) k G).LiftedMono) ∧
      ((spec (C := C) k G).Consistent ↔ (spec (C := C) k G).LiftedMono) :=
  ⟨(obsConfluent_iff_commonExpansion k G).trans (liftedMono_iff_commonExpansion _).symm,
    complete_calm _⟩

/-- **T4, emitted outputs.**  If outputs report observations (`OutReports`)
and every state can report its observation (`OutEnabled`), confluence of the
emitted outputs is also equivalent to Lifted Monotonicity.  Without
`OutReports` the emitted values need not be observations at all. -/
theorem emitConfluent_iff_liftedMono_of (hR : OutReports G) (hE : OutEnabled G) :
    EmitConfluent (C := C) k G ↔ (spec (C := C) k G).LiftedMono :=
  (emitConfluent_iff_commonExpansion_of k G hR hE).trans (liftedMono_iff_commonExpansion _).symm

end confluence

/-! ### Arrival orders (T3) -/

section arrival
variable [DecidableEq C] {k : ChanKind} {G : Machine C P Q O}

theorem recvs_nodup {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k G β f) :
    (recvs β).Nodup :=
  (((reach_inv β f hr).perm.nodup_iff).1 (reach_inv β f hr).nodup).sublist
    (List.sublist_append_left _ _)

/-- Happens-before between sends of one client follows sequence numbers. -/
theorem seq_lt_of_lt {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k G β f)
    {a b : Ev C P} (h : (input β).lt a b) (hc : a.client = b.client) : a.seq < b.seq := by
  obtain ⟨_, i, j, hi, hj, hij⟩ := h
  exact pos_of_pairwise_sends (reach_inv β f hr).incr i j a b (hb_lt hij).1 hi hj hc

/-- Received events of one client are ordered by sequence number. -/
theorem lt_of_seq_lt {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k G β f)
    {a b : Ev C P} (ha : .recv a ∈ β) (hb : .recv b ∈ β) (hc : a.client = b.client)
    (hs : a.seq < b.seq) : (input β).lt a b := by
  obtain ⟨i, hi⟩ := sendAt_of_mem (recv_sent hr ha)
  obtain ⟨j, hj⟩ := sendAt_of_mem (recv_sent hr hb)
  refine ⟨⟨ha, hb⟩, i, j, hi, hj, ?_⟩
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exact .single ⟨hij, _, _, hi, hj, Or.inl ⟨.cli a.client, rfl, by simp [onProc, hc]⟩⟩
  · have : a = b := by
      have := hi.symm.trans hj
      simp only [Option.some.injEq, Act.send.injEq] at this
      exact this
    subst this; omega
  · have := pos_of_pairwise_sends (reach_inv β f hr).incr j i b a hij hj hi hc.symm
    omega

/-- Distinct received events of one client are comparable. -/
theorem lt_total_client {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k G β f)
    {a b : Ev C P} (ha : .recv a ∈ β) (hb : .recv b ∈ β) (hc : a.client = b.client)
    (hne : a ≠ b) : (input β).lt a b ∨ (input β).lt b a := by
  obtain ⟨i, hi⟩ := sendAt_of_mem (recv_sent hr ha)
  obtain ⟨j, hj⟩ := sendAt_of_mem (recv_sent hr hb)
  have I := reach_inv β f hr
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exact Or.inl (lt_of_seq_lt hr ha hb hc (pos_of_pairwise_sends I.incr i j a b hij hi hj hc))
  · exact absurd (by
      have := hi.symm.trans hj
      simp only [Option.some.injEq, Act.send.injEq] at this
      exact this) hne
  · exact Or.inr (lt_of_seq_lt hr hb ha hc.symm
      (pos_of_pairwise_sends I.incr j i b a hij hj hi hc.symm))

/-- No client observes: the machine reports nothing. -/
def OutFree (β : List (Act C P O)) : Prop := ∀ c o, Act.out c o ∉ β

/-- A position holding a send by `c`, a receive, or an internal step. -/
def Good (c : C) (x : Option (Act C P O)) : Prop :=
  (∃ e, x = some (.send e) ∧ e.client = c) ∨ (∃ e, x = some (.recv e)) ∨ x = some .tau

omit [DecidableEq C] in
theorem good_edge {β : List (Act C P O)} (hout : OutFree β) {c : C} {m j : Nat}
    (he : Edge β m j) (hg : Good c β[m]?) : Good c β[j]? := by
  obtain ⟨_, a, b, ha, hb, hE⟩ := he
  rw [ha] at hg
  rw [hb]
  cases b with
  | recv e => exact Or.inr (Or.inl ⟨e, rfl⟩)
  | tau => exact Or.inr (Or.inr rfl)
  | out c' o => exact absurd (List.mem_of_getElem? hb) (hout c' o)
  | send e' =>
    refine Or.inl ⟨e', rfl, ?_⟩
    rcases hE with ⟨p, hpa, hpb⟩ | ⟨e, _, hb'⟩
    · simp only [onProc] at hpb
      subst hpb
      rcases hg with ⟨e, he, rfl⟩ | ⟨e, he⟩ | he
      · simp only [Option.some.injEq] at he
        subst he
        simp only [onProc, Proc.cli.injEq] at hpa
        exact hpa
      · simp only [Option.some.injEq] at he
        subst he
        simp [onProc] at hpa
      · simp only [Option.some.injEq] at he
        subst he
        simp [onProc] at hpa
    · cases hb'

omit [DecidableEq C] in
theorem good_hb {β : List (Act C P O)} (hout : OutFree β) {c : C} {i j : Nat}
    (h : HB β i j) (hg : Good c β[i]?) : Good c β[j]? := by
  induction h with
  | single he => exact good_edge hout he hg
  | tail _ he ih => exact good_edge hout he ih

omit [DecidableEq C] in
/-- When no client observes, happens-before relates only sends of one
client. -/
theorem client_eq_of_lt {β : List (Act C P O)} (hout : OutFree β) {a b : Ev C P}
    (h : (input β).lt a b) : a.client = b.client := by
  obtain ⟨_, i, j, hi, hj, hij⟩ := h
  have := good_hb hout hij (Or.inl ⟨a, hi, rfl⟩)
  rw [show β[j]? = _ from hj] at this
  rcases this with ⟨e, he, hc⟩ | ⟨e, he⟩ | he
  · simp only [Option.some.injEq, Act.send.injEq] at he
    subst he; exact hc.symm
  · cases he
  · cases he

/-- When no client observes, the input order is the per-client order of
sequence numbers. -/
theorem lt_iff_outFree {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k G β f)
    (hout : OutFree β) (a b : Ev C P) :
    (input β).lt a b ↔ ((input β).mem a ∧ (input β).mem b) ∧ a.client = b.client ∧ a.seq < b.seq := by
  constructor
  · intro h
    have hc := client_eq_of_lt hout h
    exact ⟨h.1, hc, seq_lt_of_lt hr h hc⟩
  · rintro ⟨⟨ha, hb⟩, hc, hs⟩
    exact lt_of_seq_lt hr ha hb hc hs

/-- When no client observes, happens-before between two sends is the
per-client order of sequence numbers. -/
theorem hb_send_iff_outFree {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k G β f)
    (hout : OutFree β) {i j : Nat} {a b : Ev C P} (hi : SendAt β i a) (hj : SendAt β j b) :
    HB β i j ↔ a.client = b.client ∧ a.seq < b.seq := by
  have I := reach_inv β f hr
  constructor
  · intro hij
    have hg := good_hb hout hij (Or.inl ⟨a, hi, rfl⟩)
    rw [show β[j]? = _ from hj] at hg
    have hc : a.client = b.client := by
      rcases hg with ⟨e, he, hc⟩ | ⟨e, he⟩ | he
      · simp only [Option.some.injEq, Act.send.injEq] at he
        subst he; exact hc.symm
      · cases he
      · cases he
    exact ⟨hc, pos_of_pairwise_sends I.incr i j a b (hb_lt hij).1 hi hj hc⟩
  · rintro ⟨hc, hs⟩
    rcases Nat.lt_trichotomy i j with hij | rfl | hij
    · exact .single ⟨hij, _, _, hi, hj, Or.inl ⟨.cli a.client, rfl, by simp [onProc, hc]⟩⟩
    · have : a = b := by
        have := hi.symm.trans hj
        simp only [Option.some.injEq, Act.send.injEq] at this
        exact this
      subst this; omega
    · have := pos_of_pairwise_sends I.incr j i b a hij hj hi hc.symm
      omega

/-- Sends only, in order. -/
def sendActs (β : List (Act C P O)) : List (Act C P O) := (sends β).map .send

theorem reach_sendActs :
    ∀ (β : List (Act C P O)) (f : Flat C P Q), Reach k G β f →
      Reach k G (sendActs β) ⟨G.q0, f.cnt, sends β⟩ := by
  refine reach_induction (C := C) (k := k) (G := G) ?_ ?_
  · exact reach_nil.2 rfl
  · intro β f a f' _ ih hs
    cases hs with
    | send e hseq =>
      have : sendActs (β ++ [.send e]) = sendActs β ++ [.send e] := by simp [sendActs]
      rw [this, sends_append]
      exact reach_snoc.2 ⟨_, ih, FStep.send _ e hseq⟩
    | recv e q' ch' _ _ =>
      have : sendActs (β ++ [.recv e]) = sendActs β := by simp [sendActs]
      rw [this]; simpa using ih
    | out c o =>
      have : sendActs (β ++ [.out c o]) = sendActs β := by simp [sendActs]
      rw [this]; simpa using ih
    | tau =>
      have : sendActs (β ++ [.tau]) = sendActs β := by simp [sendActs]
      rw [this]; simpa using ih

omit [DecidableEq C] in
/-- A machine schedule contains no sends. -/
theorem run_mach_noSend {G : Machine C P Q O} :
    ∀ {q q' : Q} {γ : List (Act C P O)}, Run (machA G) q γ q' → ∀ e, Act.send e ∉ γ
  | _, _, [], _, _, h => nomatch h
  | _, _, a :: γ, .cons hs hr, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact hs.elim
    · exact run_mach_noSend hr e h

omit [DecidableEq C] in
theorem sendAt_lt_of_noSend {β γ : List (Act C P O)} (hγ : ∀ e, Act.send e ∉ γ) {i : Nat}
    {e : Ev C P} (h : SendAt (β ++ γ) i e) : i < β.length := by
  rcases Nat.lt_or_ge i β.length with hi | hi
  · exact hi
  · unfold SendAt at h
    rw [List.getElem?_append_right hi] at h
    exact absurd (List.mem_of_getElem? h) (hγ e)

/-- Replaying a machine schedule over a bag that holds every event it
receives. -/
theorem replay_bag {G : Machine C P Q O} :
    ∀ (γ : List (Act C P O)) (β : List (Act C P O)) (q q' : Q) (cnt : C → Nat)
      (ch : List (Ev C P)), Reach .bag G β ⟨q, cnt, ch⟩ → ch.Nodup → (recvs γ).Nodup →
      (∀ x ∈ recvs γ, x ∈ ch) → Run (machA G) q γ q' →
      ∃ ch', Reach .bag G (β ++ γ) ⟨q', cnt, ch'⟩
  | [], β, q, _, cnt, ch, hr, _, _, _, .nil _ => ⟨ch, by simpa using hr⟩
  | a :: γ, β, q, q', cnt, ch, hr, hch, hw, hsub, .cons (s' := q1) hs hq => by
    have hβ : β ++ a :: γ = (β ++ [a]) ++ γ := by simp
    rw [hβ]
    cases a with
    | send e => exact hs.elim
    | recv e =>
      have hw' := List.nodup_cons.1 (by simpa using hw : (e :: recvs γ).Nodup)
      have he : e ∈ ch := hsub e (by simp)
      obtain ⟨a, b, rfl⟩ := List.append_of_mem he
      have hr' : Reach .bag G (β ++ [.recv e]) ⟨q1, cnt, a ++ b⟩ :=
        reach_snoc.2 ⟨_, hr, FStep.recv ⟨q, cnt, a ++ e :: b⟩ e q1 (a ++ b) hs ⟨a, b, rfl, rfl⟩⟩
      exact replay_bag γ _ q1 q' cnt (a ++ b) hr'
        (hch.sublist (List.Sublist.append_left (List.sublist_cons_self e b) a)) hw'.2
        (fun x hx => by
          have h1 := hsub x (by simp [hx])
          have h2 : x ≠ e := fun h => hw'.1 (h ▸ hx)
          simp only [List.mem_append, List.mem_cons] at h1 ⊢
          rcases h1 with h1 | h1 | h1
          · exact Or.inl h1
          · exact absurd h1 h2
          · exact Or.inr h1) hq
    | out c o =>
      have hr' : Reach .bag G (β ++ [.out c o]) ⟨q1, cnt, ch⟩ :=
        reach_snoc.2 ⟨_, hr, FStep.out ⟨q, cnt, ch⟩ c o q1 hs⟩
      exact replay_bag γ _ q1 q' cnt ch hr' hch (by simpa using hw)
        (fun x hx => hsub x (by simpa using hx)) hq
    | tau =>
      have hr' : Reach .bag G (β ++ [.tau]) ⟨q1, cnt, ch⟩ :=
        reach_snoc.2 ⟨_, hr, FStep.tau ⟨q, cnt, ch⟩ q1 hs⟩
      exact replay_bag γ _ q1 q' cnt ch hr' hch (by simpa using hw)
        (fun x hx => hsub x (by simpa using hx)) hq

/-- **Arrival orders over a bag (general machine).**  If no client observes
in an execution `β` over a bag channel, then every execution `γ` of the
machine automaton whose receives are the events of `input β`, each once, in
any order, interleaved with any output and internal steps, is replayed by an
execution `β'` of the system with the same input that leaves the machine in
the state `γ` ends in; if `γ` has no outputs, neither has `β'`. -/
theorem bag_arrival_run {G : Machine C P Q O} {β : List (Act C P O)}
    {s : (sys (C := C) .bag G).St} (hx : Execution (sys .bag G) β s) (hout : OutFree β)
    {γ : List (Act C P O)} {q : Q} (hγ : Execution (machA G) γ q) (hw : (recvs γ).Nodup)
    (hmem : ∀ e, e ∈ recvs γ ↔ (input β).mem e) :
    ∃ β' s', Execution (sys .bag G) β' s' ∧ input β' = input β ∧ s' .mach = q ∧
      (OutFree γ → OutFree β') := by
  obtain ⟨q0, hq0, hγ⟩ := hγ
  have hq0' : q0 = G.q0 := hq0
  subst hq0'
  have hr : Reach .bag G β (toFlat s) := ⟨s, hx, rfl⟩
  have I := reach_inv β _ hr
  have hpre := reach_sendActs β _ hr
  obtain ⟨ch', hr'⟩ := replay_bag γ _ _ q _ _ hpre I.nodup hw
    (fun x hx => recv_sent hr ((hmem x).1 hx)) hγ
  have hns := run_mach_noSend hγ
  have houtS : OutFree (sendActs β) := by
    intro c o h; simp [sendActs] at h
  have hm : ∀ e, (input (sendActs β ++ γ)).mem e ↔ (input β).mem e := by
    intro e
    show Act.recv e ∈ _ ↔ _
    rw [← hmem, mem_recvs]; simp [sendActs]
  obtain ⟨s', hx', hs'⟩ := id hr'
  refine ⟨_, s', hx', Inp.ext' (funext fun e => propext (hm e))
    (funext fun a => funext fun b => propext ?_), congrArg Flat.q hs', fun hγo c o h => ?_⟩
  · rw [lt_iff_outFree hr hout]
    constructor
    · rintro ⟨⟨ha, hb⟩, i, j, hi, hj, hij⟩
      have hi' := (sendAt_append (sendAt_lt_of_noSend hns hi)).1 hi
      have hj' := (sendAt_append (sendAt_lt_of_noSend hns hj)).1 hj
      have hij' := (hb_append (sendAt_lt_of_noSend hns hj)).1 hij
      exact ⟨⟨(hm a).1 ha, (hm b).1 hb⟩, (hb_send_iff_outFree hpre houtS hi' hj').1 hij'⟩
    · rintro ⟨⟨ha, hb⟩, hc⟩
      obtain ⟨i, hi⟩ := sendAt_of_mem (recv_sent hr' ((hm a).2 ha))
      obtain ⟨j, hj⟩ := sendAt_of_mem (recv_sent hr' ((hm b).2 hb))
      have hi' := (sendAt_append (sendAt_lt_of_noSend hns hi)).1 hi
      have hj' := (sendAt_append (sendAt_lt_of_noSend hns hj)).1 hj
      exact ⟨⟨(hm a).2 ha, (hm b).2 hb⟩, i, j, hi, hj,
        (hb_append (sendAt_lt_of_noSend hns hj)).2 ((hb_send_iff_outFree hpre houtS hi' hj').2 hc)⟩
  · rcases List.mem_append.1 h with h | h
    · simp [sendActs] at h
    · exact hγo c o h

/-- **Arrival orders over a bag, as fibers (general machine).**  Under the
hypotheses of `bag_arrival_run`, the observation at the end of `γ` is in the
fiber at `h = input β`. -/
theorem bag_fiber_of_run [PO O] {G : Machine C P Q O} {β : List (Act C P O)}
    {s : (sys (C := C) .bag G).St} (hx : Execution (sys .bag G) β s) (hout : OutFree β)
    (h : OccInp C P .bag G) (hh : h.val = input β) {γ : List (Act C P O)} {q : Q}
    (hγ : Execution (machA G) γ q) (hw : (recvs γ).Nodup)
    (hmem : ∀ e, e ∈ recvs γ ↔ h.val.mem e) :
    (spec .bag G).S h (G.obs q) := by
  rw [hh] at hmem
  obtain ⟨β', s', hx', hi, hq', _⟩ := bag_arrival_run hx hout hγ hw hmem
  exact ⟨β', s', hx', hi.trans hh.symm, by rw [hq']⟩

/-- **The fiber is reached by the machine (general machine, any channel).**
Every observation in the fiber at `h` is the observation at the end of an
execution `γ` of the machine automaton whose receives are `h`'s events, each
once, in some order (interleaved with output and internal steps); with a
FIFO channel, that order is a linear extension of `h`'s order.  (`γ` is the
projection of a system execution onto the machine.) -/
theorem fiber_sub_run [PO O] {G : Machine C P Q O} (h : OccInp C P k G) (o : O)
    (hS : (spec k G).S h o) :
    ∃ γ : List (Act C P O), ∃ q, Execution (machA G) γ q ∧ G.obs q = o ∧
      (recvs γ).Nodup ∧ (∀ e, e ∈ recvs γ ↔ h.val.mem e) ∧
      (k = .fifo → (recvs γ).Pairwise fun a b => ¬ h.val.lt b a) := by
  obtain ⟨β, f, hr, hi, ho⟩ := (spec_iff _ _).1 hS
  obtain ⟨hv, hocc⟩ := h
  dsimp only at hi ⊢
  subst hi
  have I := reach_inv β f hr
  refine ⟨macts β, f.q, ⟨_, rfl, I.runs⟩, ho, ?_, fun e => ?_, fun hk => ?_⟩
  · rw [recvs_macts]; exact recvs_nodup hr
  · rw [recvs_macts]; exact mem_recvs
  rw [recvs_macts]
  have hp : (sends β).Pairwise fun a b => ¬ (input β).lt b a := by
    refine pairwise_sends_of_pos fun i j x y hij hx hy hl => ?_
    obtain ⟨_, j', i', hj', hi', hb⟩ := hl
    have e1 := sendAt_unique I.nodup hi' hx
    have e2 := sendAt_unique I.nodup hj' hy
    subst e1 e2
    have := (hb_lt hb).1
    omega
  rw [I.fifo hk] at hp
  exact hp.sublist (List.sublist_append_left _ _)

end arrival

/-! ### A single client over a FIFO channel (T2) -/

/-- Transfer of Lifted Monotonicity along an order isomorphism of inputs
that preserves fibers. -/
theorem liftedMono_transfer {I J : Type} [PO I] [PO J] [PO O] (sp : Spec I O) (sp' : Spec J O)
    (φ : I → J) (hle : ∀ a b, a ≼ b ↔ φ a ≼ φ b) (hsurj : ∀ j, ∃ i, φ i = j)
    (hS : ∀ i o, sp.S i o ↔ sp'.S (φ i) o) : sp.LiftedMono ↔ sp'.LiftedMono := by
  constructor
  · intro hL i' j' hij X hX hA
    obtain ⟨i, rfl⟩ := hsurj i'
    obtain ⟨j, rfl⟩ := hsurj j'
    obtain ⟨u, hu, hall⟩ := hL i j ((hle i j).2 hij) X hX fun x hx => (hS i x).2 (hA x hx)
    exact ⟨u, (hS j u).1 hu, hall⟩
  · intro hL i j hij X hX hA
    obtain ⟨u, hu, hall⟩ := hL (φ i) (φ j) ((hle i j).1 hij) X hX fun x hx => (hS i x).1 (hA x hx)
    exact ⟨u, (hS j u).2 hu, hall⟩

/-- The events `⟨(), n, p₀⟩, ⟨(), n+1, p₁⟩, …` of the single client. -/
def evs : Nat → List P → List (Ev Unit P)
  | _, [] => []
  | n, p :: w => ⟨(), n, p⟩ :: evs (n + 1) w

theorem evs_append : ∀ (n : Nat) (u v : List P), evs n (u ++ v) = evs n u ++ evs (n + u.length) v
  | n, [], v => by simp [evs]
  | n, p :: u, v => by
    simp only [List.cons_append, evs, evs_append (n + 1) u v, List.length_cons]
    rw [show n + 1 + u.length = n + (u.length + 1) by omega]

theorem evs_payload : ∀ (n : Nat) (w : List P), (evs n w).map Ev.payload = w
  | _, [] => rfl
  | n, p :: w => by simp [evs, evs_payload (n + 1) w]

theorem evs_length : ∀ (n : Nat) (w : List P), (evs n w).length = w.length
  | _, [] => rfl
  | n, p :: w => by simp [evs, evs_length (n + 1) w]

theorem le_seq_of_mem_evs : ∀ {n : Nat} {w : List P} {x : Ev Unit P}, x ∈ evs n w → n ≤ x.seq
  | _, [], _, h => nomatch h
  | n, p :: w, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_refl _
    · have := le_seq_of_mem_evs h; omega

theorem evs_sub_prefix : ∀ {n : Nat} {w w' : List P},
    (∀ x, x ∈ evs n w → x ∈ evs n w') → ∃ v, w' = w ++ v
  | _, [], w', _ => ⟨w', rfl⟩
  | n, p :: w, w', h => by
    have h0 := h _ (List.mem_cons_self ..)
    cases w' with
    | nil => exact nomatch h0
    | cons p' w' =>
      rcases List.mem_cons.1 h0 with h0 | h0
      · simp only [Ev.mk.injEq, true_and] at h0
        subst h0
        obtain ⟨v, hv⟩ := evs_sub_prefix (n := n + 1) (w := w) (w' := w') fun x hx => by
          rcases List.mem_cons.1 (h x (List.mem_cons_of_mem _ hx)) with rfl | hx'
          · exact absurd (le_seq_of_mem_evs hx) (Nat.not_succ_le_self n)
          · exact hx'
        exact ⟨v, by rw [hv]; rfl⟩
      · exact absurd (le_seq_of_mem_evs h0) (Nat.not_succ_le_self n)

theorem seq_eq_of_prefix {w w' : List P} {v u : List P} (h1 : w' = w ++ v) (h2 : w = w' ++ u) :
    w = w' := by
  have h := PO.antisymm (a := (⟨w⟩ : SM.Seq P)) (b := ⟨w'⟩) ⟨v, h1⟩ ⟨u, h2⟩
  exact congrArg SM.Seq.ev h

/-- The canonical replay of a machine schedule by the single client: each
receive of payload `p` becomes a send of `⟨(), n, p⟩` followed by its
receipt (with `n` counting up from the given start); outputs and internal
steps are kept. -/
def canon : Nat → List (Act Unit P O) → List (Act Unit P O)
  | _, [] => []
  | n, .recv e :: γ => .send ⟨(), n, e.payload⟩ :: .recv ⟨(), n, e.payload⟩ :: canon (n + 1) γ
  | n, .out c o :: γ => .out c o :: canon n γ
  | n, .tau :: γ => .tau :: canon n γ
  | n, .send _ :: γ => canon n γ

theorem recvs_canon_eq : ∀ (n : Nat) (γ : List (Act Unit P O)),
    recvs (canon n γ) = evs n ((recvs γ).map Ev.payload)
  | _, [] => rfl
  | n, .recv e :: γ => by simp [canon, evs, recvs_canon_eq (n + 1) γ]
  | n, .out c o :: γ => by simp [canon, recvs_canon_eq n γ]
  | n, .tau :: γ => by simp [canon, recvs_canon_eq n γ]
  | n, .send _ :: γ => by simp [canon, recvs_canon_eq n γ]

theorem recvs_map_recv : ∀ l : List (Ev C P), recvs (l.map .recv : List (Act C P O)) = l
  | [] => rfl
  | e :: l => by simp [recvs_map_recv l]

theorem chanRecv_single (k : ChanKind) (e : Ev C P) : chanRecv k [e] e [] := by
  cases k
  · exact ⟨[], [], rfl, rfl⟩
  · rfl

section single
variable {k : ChanKind} {G : Machine Unit P Q O}

/-- The single client's sends are `evs 0` of their payloads. -/
theorem reach_unit :
    ∀ (β : List (Act Unit P O)) (f : Flat Unit P Q), Reach k G β f →
      f.cnt () = (sends β).length ∧ sends β = evs 0 ((sends β).map Ev.payload) := by
  refine reach_induction (C := Unit) (k := k) (G := G) ⟨rfl, rfl⟩ ?_
  · intro β f a f' _ ih hs
    cases hs with
    | send e hseq =>
      obtain ⟨c, n, p⟩ := e
      cases c
      simp only at hseq
      subst hseq
      refine ⟨by simp [bump, ih.1], ?_⟩
      simp only [sends_append, sends_cons_send, sends_nil, List.map_append, List.map_cons,
        List.map_nil, evs_append, List.length_map]
      rw [← ih.2, ← ih.1]
      simp [evs]
    | recv => simpa using ih
    | out => simpa using ih
    | tau => simpa using ih

/-- With a FIFO channel, the single client's received events are `evs 0` of
their payloads. -/
theorem recvs_canon {β : List (Act Unit P O)} {f : Flat Unit P Q} (hr : Reach .fifo G β f) :
    recvs β = evs 0 ((recvs β).map Ev.payload) := by
  have h1 := (reach_unit β f hr).2
  rw [(reach_inv β f hr).fifo rfl] at h1
  rw [List.map_append, evs_append] at h1
  exact (List.append_inj h1 (by rw [evs_length, List.length_map])).1

/-- The canonical replay of a machine execution is an execution of the
system. -/
theorem replay_canon (k : ChanKind) (G : Machine Unit P Q O) :
    ∀ (γ β : List (Act Unit P O)) (q q' : Q) (n : Nat),
      Reach k G β ⟨q, fun _ => n, []⟩ → Run (machA G) q γ q' →
      Reach k G (β ++ canon n γ) ⟨q', fun _ => n + (recvs γ).length, []⟩
  | [], β, q, _, n, hr, .nil _ => by simpa [canon] using hr
  | a :: γ, β, q, q', n, hr, .cons (s' := q1) hs hq => by
    cases a with
    | send e => exact hs.elim
    | recv e =>
      let e' : Ev Unit P := ⟨(), n, e.payload⟩
      have r2 : Reach k G (β ++ [.send e']) ⟨q, bump (fun _ => n) (), [] ++ [e']⟩ :=
        reach_snoc.2 ⟨_, hr, FStep.send _ e' rfl⟩
      have hb : bump (fun _ => n) () = fun _ => n + 1 := by
        funext c; simp [bump]
      have r3 : Reach k G ((β ++ [.send e']) ++ [.recv e']) ⟨q1, fun _ => n + 1, []⟩ := by
        rw [← hb]
        exact reach_snoc.2 ⟨_, r2, FStep.recv _ e' q1 [] hs (chanRecv_single k e')⟩
      have := replay_canon k G γ _ q1 q' (n + 1) r3 hq
      have hl : n + 1 + (recvs γ).length = n + (recvs (.recv e :: γ)).length := by
        simp; omega
      rw [hl] at this
      simpa [canon, e'] using this
    | out c o =>
      have r2 : Reach k G (β ++ [.out c o]) ⟨q1, fun _ => n, []⟩ :=
        reach_snoc.2 ⟨_, hr, FStep.out _ c o q1 hs⟩
      simpa [canon] using replay_canon k G γ _ q1 q' n r2 hq
    | tau =>
      have r2 : Reach k G (β ++ [.tau]) ⟨q1, fun _ => n, []⟩ :=
        reach_snoc.2 ⟨_, hr, FStep.tau _ q1 hs⟩
      simpa [canon] using replay_canon k G γ _ q1 q' n r2 hq

/-- The machine can receive any list of events. -/
theorem run_recvs_exists (G : Machine C P Q O) :
    ∀ (q : Q) (l : List (Ev C P)), ∃ q', Run (machA G) q (l.map .recv) q'
  | q, [] => ⟨q, Run.nil (M := machA G) q⟩
  | q, e :: l => by
    obtain ⟨q1, h1⟩ := G.recv_enabled q e.payload
    obtain ⟨q2, h2⟩ := run_recvs_exists G q1 l
    exact ⟨q2, .cons h1 h2⟩

/-- The word of an input: the payloads of its events in sequence order. -/
noncomputable def word (h : OccInp Unit P .fifo G) : SM.Seq P :=
  ⟨(recvs (Classical.choose h.occ)).map Ev.payload⟩

theorem recvs_prefix {β β' : List (Act Unit P O)} {f f' : Flat Unit P Q}
    (hr : Reach .fifo G β f) (hr' : Reach .fifo G β' f')
    (h : ∀ e, Act.recv e ∈ β → Act.recv e ∈ β') :
    ∃ v, (recvs β').map Ev.payload = (recvs β).map Ev.payload ++ v := by
  apply evs_sub_prefix (n := 0)
  intro x hx
  rw [← recvs_canon hr] at hx
  rw [← recvs_canon hr']
  exact mem_recvs.2 (h x (mem_recvs.1 hx))

theorem word_spec (h : OccInp Unit P .fifo G) {β : List (Act Unit P O)} {f : Flat Unit P Q}
    (hr : Reach .fifo G β f) (hi : input β = h.val) :
    (word h).ev = (recvs β).map Ev.payload := by
  have hc := Classical.choose_spec h.occ
  obtain ⟨s0, hx0, hi0⟩ := hc
  have hr0 : Reach .fifo G (Classical.choose h.occ) (toFlat s0) := ⟨s0, hx0, rfl⟩
  have hm : ∀ e, Act.recv e ∈ β ↔ Act.recv e ∈ Classical.choose h.occ := fun e => by
    show (input β).mem e ↔ (input _).mem e
    rw [hi, hi0]
  obtain ⟨v, hv⟩ := recvs_prefix hr hr0 fun e => (hm e).1
  obtain ⟨u, hu⟩ := recvs_prefix hr0 hr fun e => (hm e).2
  exact seq_eq_of_prefix hu hv

theorem lt_iff_unit {β : List (Act Unit P O)} {f : Flat Unit P Q} (hr : Reach k G β f)
    (a b : Ev Unit P) :
    (input β).lt a b ↔ ((input β).mem a ∧ (input β).mem b) ∧ a.seq < b.seq :=
  ⟨fun h => ⟨h.1, seq_lt_of_lt hr h (Subsingleton.elim _ _)⟩,
    fun ⟨⟨ha, hb⟩, hs⟩ => lt_of_seq_lt hr ha hb (Subsingleton.elim _ _) hs⟩

theorem word_le_iff (h h' : OccInp Unit P .fifo G) : h ≼ h' ↔ word h ≼ word h' := by
  obtain ⟨β, s, hx, hi⟩ := h.occ
  obtain ⟨β', s', hx', hi'⟩ := h'.occ
  have hr : Reach .fifo G β (toFlat s) := ⟨s, hx, rfl⟩
  have hr' : Reach .fifo G β' (toFlat s') := ⟨s', hx', rfl⟩
  show h.val ≼ h'.val ↔ ∃ v, (word h').ev = (word h).ev ++ v
  rw [word_spec h hr hi, word_spec h' hr' hi', ← hi, ← hi']
  constructor
  · intro hle
    exact recvs_prefix hr hr' hle.1
  · rintro ⟨v, hv⟩
    have hmem : ∀ e, Act.recv e ∈ β → Act.recv e ∈ β' := by
      intro e he
      have h1 := mem_recvs.2 he
      rw [recvs_canon hr] at h1
      rw [← mem_recvs, recvs_canon hr', hv, evs_append]
      exact List.mem_append_left _ h1
    refine ⟨hmem, fun a b ha hb => ?_⟩
    rw [lt_iff_unit hr, lt_iff_unit hr']
    exact ⟨fun ⟨_, hs⟩ => ⟨⟨hmem a ha, hmem b hb⟩, hs⟩, fun ⟨_, hs⟩ => ⟨⟨ha, hb⟩, hs⟩⟩

theorem word_inj {h h' : OccInp Unit P .fifo G} (he : word h = word h') : h = h' :=
  PO.antisymm ((word_le_iff h h').2 (he ▸ PO.refl _)) ((word_le_iff h' h).2 (he ▸ PO.refl _))

/-- The canonical replay of a machine execution has the word of its
receives. -/
theorem word_replay {γ : List (Act Unit P O)} {q : Q} (hγ : Run (machA G) G.q0 γ q) :
    ∃ hr : Reach .fifo G (canon 0 γ) ⟨q, fun _ => (recvs γ).length, []⟩,
      word (occOf hr) = ⟨(recvs γ).map Ev.payload⟩ := by
  have hr := replay_canon .fifo G γ [] G.q0 q 0 (reach_nil.2 rfl) hγ
  simp only [List.nil_append, Nat.zero_add] at hr
  refine ⟨hr, ?_⟩
  have := word_spec (occOf hr) hr rfl
  rw [recvs_canon_eq, evs_payload] at this
  cases hw : word (occOf hr); rw [hw] at this; cases this; rfl

theorem word_surj (w : SM.Seq P) : ∃ h : OccInp Unit P .fifo G, word h = w := by
  obtain ⟨q, hq⟩ := run_recvs_exists G G.q0 (evs 0 w.ev)
  obtain ⟨hr, hw⟩ := word_replay hq
  refine ⟨occOf hr, ?_⟩
  rw [hw, recvs_map_recv, evs_payload]

/-- The specification of payload sequences under the prefix order whose
fiber at `w` holds the observations at the end of every execution of the
machine automaton whose receives carry the payloads `w` in order. -/
def runSpec [PO O] (G : Machine Unit P Q O) : Spec (SM.Seq P) O where
  S w o := ∃ γ q, Execution (machA G) γ q ∧ (recvs γ).map Ev.payload = w.ev ∧ G.obs q = o
  total w := by
    obtain ⟨q, hq⟩ := run_recvs_exists G G.q0 (evs 0 w.ev)
    exact ⟨_, _, q, ⟨_, rfl, hq⟩, by rw [recvs_map_recv, evs_payload], rfl⟩

variable [PO O] in
theorem word_fiber_run (h : OccInp Unit P .fifo G) (o : O) :
    (spec .fifo G).S h o ↔ (runSpec G).S (word h) o := by
  constructor
  · intro hS
    obtain ⟨β, f, hr, hi, ho⟩ := (spec_iff _ _).1 hS
    refine ⟨macts β, f.q, ⟨_, rfl, (reach_inv β f hr).runs⟩, ?_, ho⟩
    rw [recvs_macts, word_spec h hr hi]
  · rintro ⟨γ, q, ⟨q0, hq0, hγ⟩, hw, rfl⟩
    have hq0' : q0 = G.q0 := hq0
    subst hq0'
    obtain ⟨hr, he⟩ := word_replay hγ
    have he' : word (occOf hr) = word h := by rw [he, hw]
    rw [← word_inj he']
    exact spec_of_reach hr

/-- Every input is a chain (single client). -/
theorem inp_chain (h : OccInp Unit P k G) (a b : Ev Unit P) (ha : h.val.mem a) (hb : h.val.mem b)
    (hne : a ≠ b) : h.val.lt a b ∨ h.val.lt b a := by
  obtain ⟨β, s, hx, hi⟩ := h.occ
  rw [← hi] at ha hb ⊢
  exact lt_total_client ⟨s, hx, rfl⟩ ha hb (Subsingleton.elim _ _) hne

/-- **Single client, FIFO channel (general machine).**  Every input is a
chain; the map `word` (payloads in sequence order) is an order isomorphism
from the inputs onto payload sequences under the prefix order that carries
each fiber to the fiber of `runSpec G`: the observations at the end of the
machine automaton's executions that receive `word h` in order, interleaved
with output and internal steps.  Hence the induced specification is
consistent iff `runSpec G` is. -/
theorem fifo_single_run [PO O] (G : Machine Unit P Q O) :
    (∀ h : OccInp Unit P .fifo G, ∀ a b, h.val.mem a → h.val.mem b → a ≠ b →
      h.val.lt a b ∨ h.val.lt b a) ∧
    (∀ h h' : OccInp Unit P .fifo G, h ≼ h' ↔ word h ≼ word h') ∧
    (∀ w : SM.Seq P, ∃ h : OccInp Unit P .fifo G, word h = w) ∧
    (∀ h o, (spec .fifo G).S h o ↔ (runSpec G).S (word h) o) ∧
    ((spec (C := Unit) .fifo G).Consistent ↔ (runSpec G).Consistent) := by
  refine ⟨inp_chain, word_le_iff, word_surj, word_fiber_run, ?_⟩
  rw [complete_calm, complete_calm]
  exact liftedMono_transfer _ _ word word_le_iff word_surj word_fiber_run

end single

/-! ### State machines (`ofSM`): outputs do not change state -/

section stateMachine
variable {M : SM.Machine Q P O}

/-- A run of the machine automaton of a state machine is a run of the state
machine on the payloads it receives. -/
theorem runs_of_run_ofSM :
    ∀ {q q' : Q} {γ : List (Act C P O)}, Run (machA (ofSM (C := C) M)) q γ q' →
      SM.Runs M q ((recvs γ).map Ev.payload) q'
  | _, _, [], .nil _ => .nil _
  | _, _, a :: γ, .cons hs hr => by
    cases a with
    | send => exact hs.elim
    | recv e => exact .cons hs (runs_of_run_ofSM hr)
    | out c o =>
      obtain ⟨_, rfl⟩ := hs
      simpa using runs_of_run_ofSM hr
    | tau => exact hs.elim

/-- Conversely, a run of the state machine on the payloads of `w` is a run
of its machine automaton receiving `w`. -/
theorem run_ofSM_of_runs :
    ∀ {q q' : Q} (w : List (Ev C P)), SM.Runs M q (w.map Ev.payload) q' →
      Run (machA (ofSM (C := C) M)) q (w.map .recv) q'
  | _, _, [], h => by cases h; exact .nil _
  | _, _, e :: w, h => by
    cases h with
    | cons hs hr => exact .cons hs (run_ofSM_of_runs w hr)

/-- **Fibers of a state machine (any channel).**  Every observation in the
fiber at `h` comes from a run of `M` on an arrival order of `h`'s events;
with a FIFO channel, the arrival order is a linear extension of `h`'s
order. -/
theorem fiber_sub [PO O] [DecidableEq C] {k : ChanKind} (h : OccInp C P k (ofSM M)) (o : O)
    (hS : (spec k (ofSM M)).S h o) :
    ∃ w : List (Ev C P), w.Nodup ∧ (∀ e, e ∈ w ↔ h.val.mem e) ∧
      (∃ q, SM.Runs M M.q0 (w.map Ev.payload) q ∧ M.obs q = o) ∧
      (k = .fifo → w.Pairwise fun a b => ¬ h.val.lt b a) := by
  obtain ⟨γ, q, ⟨q0, hq0, hγ⟩, ho, hn, hm, hf⟩ := fiber_sub_run h o hS
  have hq0' : q0 = M.q0 := hq0
  subst hq0'
  exact ⟨recvs γ, hn, hm, ⟨q, runs_of_run_ofSM hγ, ho⟩, hf⟩

/-- **Bag, no observations (state machine).**  If no client observes in an
execution `β` over a bag channel, then for every arrival order `w` of the
events the machine received in `β` and every run of `M` on `w`, some
execution (again without observations) has the same input and leaves the
machine in the state of that run. -/
theorem bag_arrival [DecidableEq C] {β : List (Act C P O)}
    {s : (sys (C := C) .bag (ofSM M)).St} (hx : Execution (sys .bag (ofSM M)) β s)
    (hout : OutFree β) {w : List (Ev C P)} (hw : w.Nodup)
    (hmem : ∀ e, e ∈ w ↔ (input β).mem e) {q : Q} (hq : SM.Runs M M.q0 (w.map Ev.payload) q) :
    ∃ β' s', Execution (sys .bag (ofSM M)) β' s' ∧ OutFree β' ∧ input β' = input β ∧
      s' .mach = q := by
  have hγ : Execution (machA (ofSM (C := C) M)) (w.map .recv) q :=
    ⟨_, rfl, run_ofSM_of_runs w hq⟩
  rw [← recvs_map_recv (O := O) w] at hw hmem
  obtain ⟨β', s', hx', hi, hq', ho⟩ := bag_arrival_run hx hout hγ hw hmem
  exact ⟨β', s', hx', ho fun c o h => by simp at h, hi, hq'⟩

/-- **Bag, no observations, as fibers (state machine).**  Under the
hypotheses of `bag_arrival`, the observation after every run of `M` on every
arrival order of the received events is in the fiber. -/
theorem bag_fiber_of_outFree [PO O] [DecidableEq C] {β : List (Act C P O)}
    {s : (sys (C := C) .bag (ofSM M)).St} (hx : Execution (sys .bag (ofSM M)) β s)
    (hout : OutFree β) (h : OccInp C P .bag (ofSM M)) (hh : h.val = input β)
    {w : List (Ev C P)} (hw : w.Nodup) (hmem : ∀ e, e ∈ w ↔ h.val.mem e) {q : Q}
    (hq : SM.Runs M M.q0 (w.map Ev.payload) q) :
    (spec .bag (ofSM M)).S h (M.obs q) := by
  rw [hh] at hmem
  obtain ⟨β', s', hx', _, hi, hq'⟩ := bag_arrival hx hout hw hmem hq
  exact ⟨β', s', hx', hi.trans hh.symm, by rw [hq']; rfl⟩

/-- For a state machine, `runSpec` is the prefix encoding of
`Instances/StateMachine.lean`. -/
theorem runSpec_ofSM [PO O] (w : SM.Seq P) (o : O) :
    (runSpec (ofSM M)).S w o ↔ (SM.induced M (SM.prefixAbs P)).S w o := by
  constructor
  · rintro ⟨γ, q, ⟨q0, hq0, hγ⟩, hw, rfl⟩
    have hq0' : q0 = M.q0 := hq0
    subst hq0'
    refine ⟨_, q, ?_, runs_of_run_ofSM hγ, rfl⟩
    show SM.Seq.mk _ = w
    rw [hw]
  · rintro ⟨w', q, rfl, hq, rfl⟩
    rw [← evs_payload 0 w'] at hq
    refine ⟨(evs 0 w').map .recv, q, ⟨_, rfl, run_ofSM_of_runs _ hq⟩, ?_, rfl⟩
    rw [recvs_map_recv, evs_payload]
    rfl

/-- **Single client, FIFO channel (state machine).**  Every input is a
chain; the map `word` (payloads in sequence order) is an order isomorphism
from the inputs onto event sequences under the prefix order that carries
each fiber to the fiber of the prefix encoding `SM.induced M (SM.prefixAbs P)`.
Hence the induced specification is consistent iff the prefix encoding is,
and for deterministic `M` iff `M`'s observations grow along transitions. -/
theorem fifo_single [PO O] (M : SM.Machine Q P O) :
    (∀ h : OccInp Unit P .fifo (ofSM M), ∀ a b, h.val.mem a → h.val.mem b → a ≠ b →
      h.val.lt a b ∨ h.val.lt b a) ∧
    (∀ h h' : OccInp Unit P .fifo (ofSM M), h ≼ h' ↔ word h ≼ word h') ∧
    (∀ w : SM.Seq P, ∃ h : OccInp Unit P .fifo (ofSM M), word h = w) ∧
    (∀ h o, (spec .fifo (ofSM M)).S h o ↔ (SM.induced M (SM.prefixAbs P)).S (word h) o) ∧
    ((spec (C := Unit) .fifo (ofSM M)).Consistent ↔
      (SM.induced M (SM.prefixAbs P)).Consistent) ∧
    (SM.Deterministic M →
      ((spec (C := Unit) .fifo (ofSM M)).Consistent ↔ SM.TransMono M)) := by
  obtain ⟨h1, h2, h3, h4, _⟩ := fifo_single_run (ofSM (C := Unit) M)
  have hf : ∀ h o, (spec .fifo (ofSM M)).S h o ↔
      (SM.induced M (SM.prefixAbs P)).S (word h) o := fun h o =>
    (h4 h o).trans (runSpec_ofSM _ _)
  have hcons : (spec (C := Unit) .fifo (ofSM M)).Consistent ↔
      (SM.induced M (SM.prefixAbs P)).Consistent := by
    rw [complete_calm, complete_calm]
    exact liftedMono_transfer _ _ word h2 h3 hf
  exact ⟨h1, h2, h3, hf, hcons, fun hd => hcons.trans (SM.induced_prefix M hd).2⟩

/-- **Emitted outputs (state machine).**  With at least one client,
confluence of the emitted outputs is equivalent to Lifted Monotonicity. -/
theorem emitConfluent_iff_liftedMono [PO O] [DecidableEq C] [Nonempty C] (k : ChanKind)
    (M : SM.Machine Q P O) :
    EmitConfluent (C := C) k (ofSM M) ↔ (spec (C := C) k (ofSM M)).LiftedMono :=
  emitConfluent_iff_liftedMono_of k _ (fun _ _ _ _ h => Or.inl h.1)
    (fun q => ⟨Classical.choice ‹_›, q, rfl, rfl⟩)

end stateMachine

/-! ### Stationary machines: output and internal steps leave the state unchanged -/

section stationary

/-- The receive transitions of a machine automaton as a state machine. -/
def recvSM (G : Machine C P Q O) : SM.Machine Q P O := ⟨G.q0, G.recv, G.recv_enabled, G.obs⟩

/-- Output and internal steps leave the state unchanged. -/
def Stationary (G : Machine C P Q O) : Prop :=
  (∀ q c o q', G.out q c o q' → q' = q) ∧ ∀ q q', G.tau q q' → q' = q

/-- A state machine's machine automaton is stationary. -/
theorem stationary_ofSM (M : SM.Machine Q P O) : Stationary (ofSM (C := C) M) :=
  ⟨fun _ _ _ _ h => h.2, fun _ _ h => h.elim⟩

variable {G : Machine C P Q O}

/-- For a stationary machine, a run of the machine automaton is a run of its
receive transitions on the payloads it receives. -/
theorem runs_of_run_stationary (hs : Stationary G) :
    ∀ {q q' : Q} {γ : List (Act C P O)}, Run (machA G) q γ q' →
      SM.Runs (recvSM G) q ((recvs γ).map Ev.payload) q'
  | _, _, [], .nil _ => .nil _
  | _, _, a :: γ, .cons ht hr => by
    cases a with
    | send => exact ht.elim
    | recv e => exact .cons ht (runs_of_run_stationary hs hr)
    | out c o =>
      have e := hs.1 _ _ _ _ ht
      subst e
      simpa using runs_of_run_stationary hs hr
    | tau =>
      have e := hs.2 _ _ ht
      subst e
      simpa using runs_of_run_stationary hs hr

/-- Conversely, a run of the receive transitions on the payloads of `w` is a
run of the machine automaton receiving `w`. -/
theorem run_of_runs_recvSM :
    ∀ {q q' : Q} (w : List (Ev C P)), SM.Runs (recvSM G) q (w.map Ev.payload) q' →
      Run (machA G) q (w.map .recv) q'
  | _, _, [], h => by cases h; exact .nil _
  | _, _, e :: w, h => by
    cases h with
    | cons hs hr => exact .cons hs (run_of_runs_recvSM w hr)

/-- For a stationary machine, `runSpec` is the prefix encoding of its receive
transitions. -/
theorem runSpec_stationary [PO O] {G : Machine Unit P Q O} (hs : Stationary G)
    (w : SM.Seq P) (o : O) :
    (runSpec G).S w o ↔ (SM.induced (recvSM G) (SM.prefixAbs P)).S w o := by
  constructor
  · rintro ⟨γ, q, ⟨q0, hq0, hγ⟩, hw, rfl⟩
    have hq0' : q0 = G.q0 := hq0
    subst hq0'
    refine ⟨_, q, ?_, runs_of_run_stationary hs hγ, rfl⟩
    show SM.Seq.mk _ = w
    rw [hw]
  · rintro ⟨w', q, rfl, hq, rfl⟩
    rw [← evs_payload 0 w'] at hq
    refine ⟨(evs 0 w').map .recv, q, ⟨_, rfl, run_of_runs_recvSM _ hq⟩, ?_, rfl⟩
    rw [recvs_map_recv, evs_payload]
    rfl

/-- **Single client, FIFO channel, stationary deterministic machine.**  If
output and internal steps leave the state unchanged and receiving is
deterministic, the induced specification is functional, and it is consistent
iff observations grow along every receive transition from a reachable
state. -/
theorem fifo_single_stationary [PO O] {G : Machine Unit P Q O} (hs : Stationary G)
    (hd : SM.Deterministic (recvSM G)) :
    (spec (C := Unit) .fifo G).Functional ∧
      ((spec (C := Unit) .fifo G).Consistent ↔ SM.TransMono (recvSM G)) := by
  obtain ⟨_, h2, h3, h4, _⟩ := fifo_single_run G
  have hf : ∀ h o, (spec .fifo G).S h o ↔
      (SM.induced (recvSM G) (SM.prefixAbs P)).S (word h) o := fun h o =>
    (h4 h o).trans (runSpec_stationary hs _ _)
  have hcons : (spec (C := Unit) .fifo G).Consistent ↔
      (SM.induced (recvSM G) (SM.prefixAbs P)).Consistent := by
    rw [complete_calm, complete_calm]
    exact liftedMono_transfer _ _ word h2 h3 hf
  obtain ⟨hfun, hmono⟩ := SM.induced_prefix (recvSM G) hd
  exact ⟨fun h o o' ho ho' => hfun _ _ _ ((hf h o).1 ho) ((hf h o').1 ho'),
    hcons.trans hmono⟩

end stationary

end IOM
end CC
