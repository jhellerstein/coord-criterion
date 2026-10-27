import CoordCriterion.Foundations.IOAutomata
import CoordCriterion.Instances.StateMachine
import CoordCriterion.CompleteCALM.Theorem

/-!
# A state machine with clients and channels as I/O automata

The machine `M : SM.Machine Q P O`, its clients, and the channel between
them are I/O automata (`Foundations/IOAutomata.lean`) composed in the
Lynch–Tuttle sense.  Each execution is projected onto an *input* (the events
the machine received, ordered by happens-before) and an *output* (the
machine's observation); the pairs form a specification.

Components (actions `Act C P O`):

* events `Ev C P` carry an identity: the issuing client, a sequence number,
  and a payload;
* the machine `machA M` has inputs `recv e` (it consumes `e.payload` with
  `M.step`) and outputs `out c o` (it reports its current observation
  `o = M.obs q` to client `c`, without changing state);
* client `c` (`cliA c`) has outputs `send e` for every `e` with
  `e.client = c` and `e.seq` its next sequence number (any payload, at any
  time: clients are maximally nondeterministic) and inputs `out c o`;
* the channel `chanA k` has inputs `send e` and outputs `recv e`; it is a bag
  (`k = .bag`: any message in transit may be delivered next) or a FIFO
  queue (`k = .fifo`).  It neither loses nor duplicates messages; a message
  in transit may stay there forever.

`sys k M` is their composition.  The output `out c o` of the machine is the
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
`spec k M` has as inputs the inputs of executions (`OccInp`) and the row
`(input β, M.obs q)` for each execution `β` ending with machine state `q`.

Results:

* `spec` is an ordered specification (T1); inputs grow along executions
  (`input_mono`);
* single client, FIFO channel: every input is a chain, and the
  specification is order-isomorphic to the prefix encoding of
  `Instances/StateMachine.lean` with the same fibers; for deterministic `M`
  it is consistent iff `TransMono M` (T2, `fifo_single`);
* the fiber at an input consists of observations of `M` after consuming the
  received events in some arrival order (`fiber_sub`), in FIFO order a linear
  extension of the input order; when no client observes, every arrival order
  the bag allows occurs (T3, `bag_fiber_of_outFree`);
* the machine's outputs are confluent across executions iff the
  specification satisfies Lifted Monotonicity, iff it is consistent (T4,
  `confluent_iff_liftedMono`, `emitConfluent_iff_liftedMono`).
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

/-- Components of the system. -/
inductive Node (C : Type) where
  | mach
  | cli (c : C)
  | chan

/-- Channel discipline. -/
inductive ChanKind where
  | bag
  | fifo

variable {C P Q O : Type}

/-- Delivery of `e` from channel contents `l`, leaving `l'`. -/
def chanRecv : ChanKind → List (Ev C P) → Ev C P → List (Ev C P) → Prop
  | .bag, l, e, l' => ∃ a b, l = a ++ e :: b ∧ l' = a ++ b
  | .fifo, l, e, l' => l = e :: l'

/-! ### The component automata -/

/-- The machine as an I/O automaton. -/
def machA (M : SM.Machine Q P O) : Automaton (Act C P O) where
  St := Q
  sig := {
    inp := fun a => ∃ e, a = .recv e
    out := fun a => ∃ c o, a = .out c o
    int := fun _ => False
    inp_out := by rintro _ ⟨e, rfl⟩ ⟨c, o, h⟩; cases h
    inp_int := fun _ _ h => h
    out_int := fun _ _ h => h }
  start q := q = M.q0
  start_nonempty := ⟨_, rfl⟩
  trans q a q' := match a with
    | .recv e => M.step q e.payload q'
    | .out _ o => o = M.obs q ∧ q' = q
    | .send _ => False
  trans_acts q a q' h := by
    cases a with
    | send => exact h.elim
    | recv e => exact Or.inl ⟨e, rfl⟩
    | out c o => exact Or.inr (Or.inl ⟨c, o, rfl⟩)
  input_enabled q a := by
    rintro ⟨e, rfl⟩
    exact M.enabled q e.payload

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
  trans_acts n a n' h := by
    cases a with
    | send e => exact Or.inr (Or.inl ⟨e, rfl, h.1⟩)
    | recv => exact h.elim
    | out c' o => exact Or.inl ⟨o, by rw [h.1]⟩
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
  trans_acts l a l' h := by
    cases a with
    | send e => exact Or.inl ⟨e, rfl⟩
    | recv e => exact Or.inr (Or.inl ⟨e, rfl⟩)
    | out => exact h.elim
  input_enabled l a := by
    rintro ⟨e, rfl⟩
    exact ⟨_, rfl⟩

/-- The family of components. -/
def F (k : ChanKind) (M : SM.Machine Q P O) : Node C → Automaton (Act C P O)
  | .mach => machA M
  | .cli c => cliA c
  | .chan => chanA k

theorem compat (k : ChanKind) (M : SM.Machine Q P O) : Compatible (F (C := C) k M) where
  out_disj i j a hi hj := by
    cases i <;> cases j <;> simp only [F, machA, cliA, chanA] at hi hj
    all_goals (try rfl)
    all_goals first
      | (obtain ⟨_, _, rfl⟩ := hi; simp_all)
      | (obtain ⟨_, rfl, _⟩ := hi; simp_all)
      | (obtain ⟨_, rfl⟩ := hi; simp_all)
  int_disj i _ _ hi _ := by cases i <;> exact hi.elim

/-- The system: the composition of the machine, the clients, and the
channel. -/
noncomputable def sys (k : ChanKind) (M : SM.Machine Q P O) : Automaton (Act C P O) :=
  compose (F k M) (compat k M)

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
inductive FStep (k : ChanKind) (M : SM.Machine Q P O) :
    Flat C P Q → Act C P O → Flat C P Q → Prop where
  | send (f : Flat C P Q) (e : Ev C P) : e.seq = f.cnt e.client →
      FStep k M f (.send e) ⟨f.q, bump f.cnt e.client, f.ch ++ [e]⟩
  | recv (f : Flat C P Q) (e : Ev C P) (q' : Q) (ch' : List (Ev C P)) :
      M.step f.q e.payload q' → chanRecv k f.ch e ch' → FStep k M f (.recv e) ⟨q', f.cnt, ch'⟩
  | out (f : Flat C P Q) (c : C) : FStep k M f (.out c (M.obs f.q)) f

variable {k : ChanKind} {M : SM.Machine Q P O}

/-- Read a composite state component by component. -/
def toFlat (s : (sys (C := C) k M).St) : Flat C P Q := ⟨s .mach, fun c => s (.cli c), s .chan⟩

/-- Assemble a composite state. -/
def ofFlat (k : ChanKind) (M : SM.Machine Q P O) (f : Flat C P Q) : (sys (C := C) k M).St :=
  fun n => match n with
    | .mach => f.q
    | .cli c => f.cnt c
    | .chan => f.ch

theorem toFlat_ofFlat (f : Flat C P Q) : toFlat (ofFlat k M f) = f := rfl

theorem acts_mach (a : Act C P O) :
    (F k M .mach).sig.acts a ↔ (match a with | .send _ => False | _ => True) := by
  cases a <;> simp [Sig.acts, F, machA]

theorem acts_cli (c : C) (a : Act C P O) :
    (F k M (.cli c)).sig.acts a ↔
      (match a with | .send e => e.client = c | .recv _ => False | .out c' _ => c' = c) := by
  cases a <;> simp [Sig.acts, F, cliA, eq_comm]

theorem acts_chan (a : Act C P O) :
    (F k M .chan).sig.acts a ↔ (match a with | .out _ _ => False | _ => True) := by
  cases a <;> simp [Sig.acts, F, chanA]

theorem trans_iff [DecidableEq C] (s s' : (sys (C := C) k M).St) (a : Act C P O) :
    (sys k M).trans s a s' ↔ FStep k M (toFlat s) a (toFlat s') := by
  constructor
  · rintro ⟨_, h⟩
    have hm := h .mach
    have hc := fun c => h (.cli c)
    have hch := h .chan
    cases a with
    | send e =>
      have h1 : s' .mach = s .mach := hm.2 ((not_congr (acts_mach _)).2 id)
      have h2 : e.client = e.client ∧ e.seq = (toFlat s).cnt e.client ∧
          (toFlat s').cnt e.client = (toFlat s).cnt e.client + 1 :=
        (hc e.client).1 ((acts_cli _ _).2 rfl)
      have h3 : ∀ c, c ≠ e.client → (toFlat s').cnt c = (toFlat s).cnt c := fun c hne =>
        (hc c).2 ((not_congr (acts_cli _ _)).2 fun h => hne h.symm)
      have h4 : (toFlat s').ch = (toFlat s).ch ++ [e] := hch.1 ((acts_chan _).2 trivial)
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
      have h1 : M.step (toFlat s).q e.payload (toFlat s').q := hm.1 ((acts_mach _).2 trivial)
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
      have h1 : o = M.obs (toFlat s).q ∧ (toFlat s').q = (toFlat s).q :=
        hm.1 ((acts_mach _).2 trivial)
      have h3 : ∀ c', (toFlat s').cnt c' = (toFlat s).cnt c' := by
        intro c'
        by_cases hcc : c = c'
        · subst hcc
          exact ((hc c).1 ((acts_cli _ _).2 rfl) : c = c ∧ _).2
        · exact (hc c').2 ((not_congr (acts_cli _ _)).2 hcc)
      have h4 : (toFlat s').ch = (toFlat s).ch := hch.2 ((not_congr (acts_chan _)).2 id)
      have : toFlat s' = toFlat s := by
        show Flat.mk _ _ _ = Flat.mk _ _ _
        congr 1
        · exact h1.2
        · funext c'; exact h3 c'
      rw [this, h1.1]
      exact .out _ _
  · intro h
    generalize hf : toFlat s = f at h
    generalize hf' : toFlat s' = f' at h
    have eq_q : ∀ (t : (sys (C := C) k M).St) g, toFlat t = g → t .mach = g.q := by
      rintro t g rfl; rfl
    have eq_c : ∀ (t : (sys (C := C) k M).St) g c, toFlat t = g → t (.cli c) = g.cnt c := by
      rintro t g c rfl; rfl
    have eq_ch : ∀ (t : (sys (C := C) k M).St) g, toFlat t = g → t .chan = g.ch := by
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
        show M.step (s .mach) e.payload (s' .mach)
        rw [eq_q s' _ hf', eq_q s _ hf]; exact hs
      | cli c =>
        refine ⟨fun h => ((acts_cli _ _).1 h).elim, fun _ => ?_⟩
        exact (eq_c s' _ _ hf').trans (eq_c s _ _ hf).symm
      | chan =>
        refine ⟨fun _ => ?_, fun h => ((h ((acts_chan _).2 trivial))).elim⟩
        show chanRecv k (s .chan) e (s' .chan)
        rw [eq_ch s' _ hf', eq_ch s _ hf]; exact hr
    | out c =>
      subst hf
      refine ⟨⟨.mach, Or.inr (Or.inl ⟨c, _, rfl⟩)⟩, fun n => ?_⟩
      cases n with
      | mach =>
        refine ⟨fun _ => ?_, fun h => ((h ((acts_mach _).2 trivial))).elim⟩
        exact ⟨rfl, eq_q s' _ hf'⟩
      | cli c' =>
        refine ⟨fun h => ?_, fun _ => eq_c s' _ _ hf'⟩
        have hc : c = c' := (acts_cli _ _).1 h
        exact ⟨hc, eq_c s' _ _ hf'⟩
      | chan =>
        refine ⟨fun h => ((acts_chan _).1 h).elim, fun _ => eq_ch s' _ hf'⟩

end flat

/-! ### Executions as flat runs -/

section reach
variable {k : ChanKind} {M : SM.Machine Q P O}

/-- The initial flat state. -/
def init (M : SM.Machine Q P O) : Flat C P Q := ⟨M.q0, fun _ => 0, []⟩

/-- `β` is the schedule of an execution of the system ending in `f`. -/
def Reach (k : ChanKind) (M : SM.Machine Q P O) (β : List (Act C P O)) (f : Flat C P Q) : Prop :=
  ∃ s, Execution (sys k M) β s ∧ toFlat s = f

theorem reach_nil {f : Flat C P Q} : Reach k M [] f ↔ f = init M := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    have h := execution_nil_iff.1 hs
    have h1 : s .mach = M.q0 := h .mach
    have h2 : ∀ c, s (.cli c) = (0 : Nat) := fun c => h (.cli c)
    have h3 : s .chan = ([] : List (Ev C P)) := h .chan
    show Flat.mk _ _ _ = Flat.mk _ _ _
    congr 1
    funext c; exact h2 c
  · rintro rfl
    refine ⟨ofFlat k M (init M), execution_nil_iff.2 ?_, rfl⟩
    intro n; cases n <;> rfl

theorem reach_snoc [DecidableEq C] {β : List (Act C P O)} {a : Act C P O} {f' : Flat C P Q} :
    Reach k M (β ++ [a]) f' ↔ ∃ f, Reach k M β f ∧ FStep k M f a f' := by
  constructor
  · rintro ⟨s', hx, rfl⟩
    obtain ⟨m, hm, ht⟩ := execution_snoc_iff.1 hx
    exact ⟨toFlat m, ⟨m, hm, rfl⟩, (trans_iff m s' a).1 ht⟩
  · rintro ⟨f, ⟨s, hs, rfl⟩, hst⟩
    exact ⟨ofFlat k M f', execution_snoc_iff.2 ⟨s, hs, (trans_iff _ _ _).2 hst⟩, rfl⟩

theorem reach_prefix {β γ : List (Act C P O)} {f : Flat C P Q} (h : Reach k M (β ++ γ) f) :
    ∃ f0, Reach k M β f0 := by
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
    (h0 : p [] (init M))
    (h1 : ∀ β f a f', Reach k M β f → p β f → FStep k M f a f' → p (β ++ [a]) f') :
    ∀ β f, Reach k M β f → p β f := by
  refine snoc_ind (p := fun β => ∀ f, Reach k M β f → p β f) ?_ ?_
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
structure Inv (k : ChanKind) (M : SM.Machine Q P O) (β : List (Act C P O)) (f : Flat C P Q) :
    Prop where
  cnt : ∀ c, f.cnt c = nSent β c
  nodup : (sends β).Nodup
  seq_lt : ∀ e ∈ sends β, e.seq < nSent β e.client
  perm : (sends β).Perm (recvs β ++ f.ch)
  fifo : k = .fifo → sends β = recvs β ++ f.ch
  runs : SM.Runs M M.q0 ((recvs β).map Ev.payload) f.q
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

theorem reach_inv {k : ChanKind} {M : SM.Machine Q P O} :
    ∀ (β : List (Act C P O)) (f : Flat C P Q), Reach k M β f → Inv k M β f := by
  refine reach_induction (C := C) (k := k) (M := M) ?_ ?_
  · exact ⟨fun _ => rfl, List.nodup_nil, fun _ h => (nomatch h), List.Perm.refl _,
      fun _ => rfl, .nil _, List.Pairwise.nil⟩
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
      · simp only [recvs_append, recvs_cons_recv, recvs_nil, List.map_append, List.map_cons,
          List.map_nil]
        exact SM.runs_append I.runs (.cons hstep (.nil _))
      · simpa using I.incr
    | out c =>
      refine ⟨fun c' => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [nSent_snoc_out]; exact I.cnt c'
      · simpa using I.nodup
      · intro x hx
        rw [nSent_snoc_out]
        exact I.seq_lt x (by simpa using hx)
      · simpa using I.perm
      · intro hk; simpa using I.fifo hk
      · simpa using I.runs
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
variable [DecidableEq C] {k : ChanKind} {M : SM.Machine Q P O}

theorem recv_sent {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k M β f) {e : Ev C P}
    (h : .recv e ∈ β) : e ∈ sends β :=
  ((reach_inv β f hr).perm.mem_iff).2 (List.mem_append_left _ (mem_recvs.2 h))

/-- Inputs grow along executions. -/
theorem input_mono {β γ : List (Act C P O)} {f : Flat C P Q} (h : Reach k M (β ++ γ) f) :
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
theorem send_before_recv {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k M β f)
    {r : Nat} {e : Ev C P} (hrv : β[r]? = some (.recv e)) : ∃ i, SendAt β i e ∧ i < r := by
  have hlt : r < β.length := (List.getElem?_eq_some_iff.1 hrv).1
  have hsplit := List.take_append_drop (r + 1) β
  have hr' : Reach k M (β.take (r + 1) ++ β.drop (r + 1)) f := by rw [hsplit]; exact hr
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
theorem send_after_out {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k M β f)
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
def Occurs (k : ChanKind) (M : SM.Machine Q P O) (h : Inp C P) : Prop :=
  ∃ β s, Execution (sys k M) β s ∧ input β = h

/-- Inputs of executions. -/
structure OccInp (C P : Type) (k : ChanKind) (M : SM.Machine Q P O) where
  val : Inp C P
  occ : Occurs k M val

instance OccInp.instPO (k : ChanKind) (M : SM.Machine Q P O) : PO (OccInp C P k M) where
  le a b := a.val ≼ b.val
  refl a := PO.refl a.val
  trans h1 h2 := PO.trans h1 h2
  antisymm {a b} h1 h2 := by
    have := PO.antisymm h1 h2
    cases a; cases b; cases this; rfl

/-- **The induced specification (T1).**  Inputs are the inputs of
executions, ordered by `⊑`; the row `(input β, M.obs q)` is present for
each execution `β` that leaves the machine in state `q`.  It is total since
every input comes from an execution. -/
def spec [PO O] (k : ChanKind) (M : SM.Machine Q P O) : Spec (OccInp C P k M) O where
  S h o := ∃ β s, Execution (sys k M) β s ∧ input β = h.val ∧ M.obs (s .mach) = o
  total h := by
    obtain ⟨β, s, hx, hi⟩ := h.occ
    exact ⟨_, β, s, hx, hi, rfl⟩

section rows
variable [PO O] {k : ChanKind} {M : SM.Machine Q P O}

theorem spec_iff (h : OccInp C P k M) (o : O) :
    (spec k M).S h o ↔ ∃ β f, Reach k M β f ∧ input β = h.val ∧ M.obs f.q = o := by
  constructor
  · rintro ⟨β, s, hx, hi, ho⟩
    exact ⟨β, toFlat s, ⟨s, hx, rfl⟩, hi, ho⟩
  · rintro ⟨β, f, ⟨s, hx, rfl⟩, hi, ho⟩
    exact ⟨β, s, hx, hi, ho⟩

/-- The input of a reachable schedule, as an element of `OccInp`. -/
def occOf {β : List (Act C P O)} {f : Flat C P Q} (h : Reach k M β f) : OccInp C P k M :=
  ⟨input β, by obtain ⟨s, hx, _⟩ := h; exact ⟨β, s, hx, rfl⟩⟩

theorem spec_of_reach {β : List (Act C P O)} {f : Flat C P Q} (h : Reach k M β f) :
    (spec k M).S (occOf h) (M.obs f.q) :=
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
variable [PO O] [DecidableEq C] (k : ChanKind) (M : SM.Machine Q P O)

/-- The machine's outputs are confluent across executions: for every finite
family of executions `βᵣ` ending in states `sᵣ`, and every execution `β`
whose input expands every input of the family, some execution with the same
input as `β` leaves the machine with an observation that refines the
observation at the end of every `βᵣ`. -/
def ObsConfluent : Prop :=
  ∀ fam : List (List (Act C P O) × (sys (C := C) k M).St),
    (∀ r ∈ fam, Execution (sys k M) r.1 r.2) →
    ∀ β s, Execution (sys k M) β s → (∀ r ∈ fam, input r.1 ≼ input β) →
      ∃ β' s', Execution (sys k M) β' s' ∧ input β' = input β ∧
        ∀ r ∈ fam, M.obs (r.2 .mach) ≼ M.obs (s' .mach)

/-- The same with outputs the machine emitted: `oᵣ` is reported by an
action `out c oᵣ` of `βᵣ`. -/
def EmitConfluent : Prop :=
  ∀ fam : List (List (Act C P O) × O),
    (∀ r ∈ fam, (∃ s, Execution (sys (C := C) k M) r.1 s) ∧ ∃ c, Act.out c r.2 ∈ r.1) →
    ∀ β s, Execution (sys k M) β s → (∀ r ∈ fam, input r.1 ≼ input β) →
      ∃ β' s', Execution (sys k M) β' s' ∧ input β' = input β ∧
        ∀ r ∈ fam, r.2 ≼ M.obs (s' .mach)

omit [DecidableEq C] in
theorem obsConfluent_iff_commonExpansion : ObsConfluent (C := C) k M ↔ (spec (C := C) k M).CommonExpansion := by
  constructor
  · intro hO rows hrows j hj
    obtain ⟨l, hl, hp⟩ := choose_list (X := List (Act C P O) × (sys (C := C) k M).St)
      (p := fun r x => Execution (sys k M) x.1 x.2 ∧ input x.1 = r.1.val ∧
        M.obs (x.2 .mach) = r.2) rows (fun r hr => by
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
    refine ⟨M.obs (s' .mach), ⟨β', s', hx', hi'.trans hi, rfl⟩, fun r hr => ?_⟩
    rw [← hl] at hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
    rw [← (hp q hq).2.2]
    exact ho q.2 (List.mem_map_of_mem hq)
  · intro hC fam hfam β s hx hle
    let row : {r // r ∈ fam} → OccInp C P k M × O := fun r =>
      (⟨input r.1.1, r.1.1, r.1.2, hfam r.1 r.2, rfl⟩, M.obs (r.1.2 .mach))
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

omit [PO O] in
theorem fstep_out {f f' : Flat C P Q} {c : C} {o : O} (h : FStep k M f (.out c o) f') :
    o = M.obs f.q ∧ f' = f := by
  cases h; exact ⟨rfl, rfl⟩

theorem emitConfluent_iff_commonExpansion [Nonempty C] :
    EmitConfluent (C := C) k M ↔ (spec (C := C) k M).CommonExpansion := by
  constructor
  · intro hE rows hrows j hj
    obtain ⟨c⟩ := ‹Nonempty C›
    obtain ⟨l, hl, hp⟩ := choose_list (X := List (Act C P O))
      (p := fun r x => (∃ s, Execution (sys (C := C) k M) x s) ∧ Act.out c r.2 ∈ x ∧
        input x = r.1.val) rows (fun r hr => by
          obtain ⟨β, f, hf, hi, ho⟩ := (spec_iff _ _).1 (hrows r hr)
          have hf' : Reach k M (β ++ [.out c r.2]) f :=
            reach_snoc.2 ⟨f, hf, ho ▸ FStep.out f c⟩
          obtain ⟨s, hs, _⟩ := hf'
          exact ⟨β ++ [.out c r.2], ⟨s, hs⟩, by simp, by rw [input_snoc_out, hi]⟩)
    obtain ⟨β, s, hx, hi⟩ := j.occ
    have hmem : ∀ q ∈ l, q.1 ∈ rows := fun q hq => hl ▸ List.mem_map_of_mem hq
    obtain ⟨β', s', hx', hi', ho⟩ := hE (l.map fun q => (q.2, q.1.2))
      (fun r hr => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
        exact ⟨(hp q hq).1, c, (hp q hq).2.1⟩) β s hx
      (fun r hr => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
        show input q.2 ≼ input β
        rw [(hp q hq).2.2, hi]
        exact hj q.1 (hmem q hq))
    refine ⟨M.obs (s' .mach), ⟨β', s', hx', hi'.trans hi, rfl⟩, fun r hr => ?_⟩
    rw [← hl] at hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
    exact ho (q.2, q.1.2) (List.mem_map_of_mem hq)
  · intro hC fam hfam β s hx hle
    obtain ⟨l, hl, hp⟩ := choose_list (X := OccInp C P k M)
      (p := fun r x => (spec k M).S x r.2 ∧ x.val ≼ input r.1) fam (fun r hr => by
        obtain ⟨⟨s0, hs0⟩, c, hc⟩ := hfam r hr
        obtain ⟨β0, γ, he⟩ := List.append_of_mem hc
        have hR : Reach k M ((β0 ++ [.out c r.2]) ++ γ) (toFlat s0) :=
          ⟨s0, by rw [List.append_assoc, List.singleton_append, ← he]; exact hs0, rfl⟩
        obtain ⟨f1, h1⟩ := reach_prefix hR
        obtain ⟨f0, h0, hst⟩ := reach_snoc.1 h1
        obtain ⟨ho, _⟩ := fstep_out k M hst
        have hmono : input β0 ≼ input r.1 := by
          have := input_mono (k := k) (M := M) (γ := .out c r.2 :: γ)
            (by rw [← he]; exact ⟨s0, hs0, rfl⟩)
          rwa [← he] at this
        exact ⟨occOf h0, ho ▸ spec_of_reach h0, hmono⟩)
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

omit [DecidableEq C] in
/-- **T4.**  The machine's outputs are confluent across executions iff the
induced specification satisfies Lifted Monotonicity, iff it is consistent
(Complete CALM). -/
theorem confluent_iff_liftedMono :
    (ObsConfluent (C := C) k M ↔ (spec (C := C) k M).LiftedMono) ∧
      ((spec (C := C) k M).Consistent ↔ (spec (C := C) k M).LiftedMono) :=
  ⟨(obsConfluent_iff_commonExpansion k M).trans (liftedMono_iff_commonExpansion _).symm,
    complete_calm _⟩

/-- **T4, emitted outputs.**  With at least one client, confluence of the
emitted outputs is also equivalent to Lifted Monotonicity. -/
theorem emitConfluent_iff_liftedMono [Nonempty C] :
    EmitConfluent (C := C) k M ↔ (spec (C := C) k M).LiftedMono :=
  (emitConfluent_iff_commonExpansion k M).trans (liftedMono_iff_commonExpansion _).symm

end confluence

/-! ### Arrival orders (T3) -/

section arrival
variable [DecidableEq C] {k : ChanKind} {M : SM.Machine Q P O}

theorem recvs_nodup {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k M β f) :
    (recvs β).Nodup :=
  (((reach_inv β f hr).perm.nodup_iff).1 (reach_inv β f hr).nodup).sublist
    (List.sublist_append_left _ _)

/-- Happens-before between sends of one client follows sequence numbers. -/
theorem seq_lt_of_lt {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k M β f)
    {a b : Ev C P} (h : (input β).lt a b) (hc : a.client = b.client) : a.seq < b.seq := by
  obtain ⟨_, i, j, hi, hj, hij⟩ := h
  exact pos_of_pairwise_sends (reach_inv β f hr).incr i j a b (hb_lt hij).1 hi hj hc

/-- Received events of one client are ordered by sequence number. -/
theorem lt_of_seq_lt {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k M β f)
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
theorem lt_total_client {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k M β f)
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

/-- A position holding a send by `c` or a receive. -/
def Good (c : C) (x : Option (Act C P O)) : Prop :=
  (∃ e, x = some (.send e) ∧ e.client = c) ∨ ∃ e, x = some (.recv e)

omit [DecidableEq C] in
theorem good_edge {β : List (Act C P O)} (hout : OutFree β) {c : C} {m j : Nat}
    (he : Edge β m j) (hg : Good c β[m]?) : Good c β[j]? := by
  obtain ⟨_, a, b, ha, hb, hE⟩ := he
  rw [ha] at hg
  rw [hb]
  cases b with
  | recv e => exact Or.inr ⟨e, rfl⟩
  | out c' o => exact absurd (List.mem_of_getElem? hb) (hout c' o)
  | send e' =>
    refine Or.inl ⟨e', rfl, ?_⟩
    rcases hE with ⟨p, hpa, hpb⟩ | ⟨e, _, hb'⟩
    · simp only [onProc] at hpb
      subst hpb
      rcases hg with ⟨e, he, rfl⟩ | ⟨e, he⟩
      · simp only [Option.some.injEq] at he
        subst he
        simp only [onProc, Proc.cli.injEq] at hpa
        exact hpa
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
  rcases this with ⟨e, he, hc⟩ | ⟨e, he⟩
  · simp only [Option.some.injEq, Act.send.injEq] at he
    subst he; exact hc.symm
  · cases he

/-- When no client observes, the input order is the per-client order of
sequence numbers. -/
theorem lt_iff_outFree {β : List (Act C P O)} {f : Flat C P Q} (hr : Reach k M β f)
    (hout : OutFree β) (a b : Ev C P) :
    (input β).lt a b ↔ ((input β).mem a ∧ (input β).mem b) ∧ a.client = b.client ∧ a.seq < b.seq := by
  constructor
  · intro h
    have hc := client_eq_of_lt hout h
    exact ⟨h.1, hc, seq_lt_of_lt hr h hc⟩
  · rintro ⟨⟨ha, hb⟩, hc, hs⟩
    exact lt_of_seq_lt hr ha hb hc hs

/-- Sends only, in order. -/
def sendActs (β : List (Act C P O)) : List (Act C P O) := (sends β).map .send

theorem reach_sendActs :
    ∀ (β : List (Act C P O)) (f : Flat C P Q), Reach k M β f →
      Reach k M (sendActs β) ⟨M.q0, f.cnt, sends β⟩ := by
  refine reach_induction (C := C) (k := k) (M := M) ?_ ?_
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
    | out c =>
      have : sendActs (β ++ [.out c (M.obs f.q)]) = sendActs β := by simp [sendActs]
      rw [this]; simpa using ih

theorem deliver_bag {M : SM.Machine Q P O} :
    ∀ (w : List (Ev C P)) (β : List (Act C P O)) (q q' : Q) (cnt : C → Nat)
      (ch : List (Ev C P)), Reach .bag M β ⟨q, cnt, ch⟩ → ch.Nodup → w.Nodup →
      (∀ x ∈ w, x ∈ ch) → SM.Runs M q (w.map Ev.payload) q' →
      ∃ ch', Reach .bag M (β ++ w.map .recv) ⟨q', cnt, ch'⟩
  | [], β, q, q', cnt, ch, hr, _, _, _, hq => by
    cases hq
    exact ⟨ch, by simpa using hr⟩
  | e :: w, β, q, q', cnt, ch, hr, hch, hw, hsub, hq => by
    cases hq with
    | cons hs hq =>
      obtain ⟨a, b, rfl⟩ := List.append_of_mem (hsub e (List.mem_cons_self ..))
      have hr' : Reach .bag M (β ++ [.recv e]) ⟨_, cnt, a ++ b⟩ :=
        reach_snoc.2 ⟨_, hr, FStep.recv ⟨q, cnt, a ++ e :: b⟩ e _ (a ++ b) hs ⟨a, b, rfl, rfl⟩⟩
      have hw' := List.nodup_cons.1 hw
      obtain ⟨ch', h⟩ := deliver_bag w _ _ q' cnt (a ++ b) hr'
        (hch.sublist (List.Sublist.append_left (List.sublist_cons_self e b) a)) hw'.2
        (fun x hx => by
          have h1 := hsub x (List.mem_cons_of_mem _ hx)
          have h2 : x ≠ e := fun h => hw'.1 (h ▸ hx)
          simp only [List.mem_append, List.mem_cons] at h1 ⊢
          rcases h1 with h1 | h1 | h1
          · exact Or.inl h1
          · exact absurd h1 h2
          · exact Or.inr h1) hq
      exact ⟨ch', by simpa using h⟩

/-- **T3 (bag, no observations).**  If no client observes in an execution
`β` over a bag channel, then for every arrival order `w` of the events the
machine received in `β` and every run of `M` on `w`, some execution (again
without observations) has the same input and leaves the machine in the
state of that run. -/
theorem bag_arrival {M : SM.Machine Q P O} {β : List (Act C P O)} {s : (sys (C := C) .bag M).St}
    (hx : Execution (sys .bag M) β s) (hout : OutFree β) {w : List (Ev C P)} (hw : w.Nodup)
    (hmem : ∀ e, e ∈ w ↔ (input β).mem e) {q : Q} (hq : SM.Runs M M.q0 (w.map Ev.payload) q) :
    ∃ β' s', Execution (sys .bag M) β' s' ∧ OutFree β' ∧ input β' = input β ∧ s' .mach = q := by
  have hr : Reach .bag M β (toFlat s) := ⟨s, hx, rfl⟩
  have I := reach_inv β _ hr
  obtain ⟨ch', hr'⟩ := deliver_bag w _ _ q _ _ (reach_sendActs β _ hr) I.nodup hw
    (fun x hx => recv_sent hr ((hmem x).1 hx)) hq
  have hout' : OutFree (sendActs β ++ w.map .recv) := by
    intro c o h; simp [sendActs] at h
  have hm : ∀ e, (input (sendActs β ++ w.map .recv)).mem e ↔ (input β).mem e := by
    intro e
    show Act.recv e ∈ _ ↔ _
    rw [← hmem]; simp [sendActs]
  obtain ⟨s', hx', hs'⟩ := hr'
  refine ⟨_, s', hx', hout', Inp.ext' (funext fun e => propext (hm e))
    (funext fun a => funext fun b => propext ?_), congrArg Flat.q hs'⟩
  rw [lt_iff_outFree ⟨s', hx', hs'⟩ hout', lt_iff_outFree hr hout, hm, hm]

/-- **T3 (bag), as fibers.**  Under the hypotheses of `bag_arrival`, the
observation after every run of `M` on every arrival order of the received
events is in the fiber. -/
theorem bag_fiber_of_outFree [PO O] {M : SM.Machine Q P O} {β : List (Act C P O)}
    {s : (sys (C := C) .bag M).St} (hx : Execution (sys .bag M) β s) (hout : OutFree β)
    (h : OccInp C P .bag M) (hh : h.val = input β) {w : List (Ev C P)} (hw : w.Nodup)
    (hmem : ∀ e, e ∈ w ↔ h.val.mem e) {q : Q} (hq : SM.Runs M M.q0 (w.map Ev.payload) q) :
    (spec .bag M).S h (M.obs q) := by
  rw [hh] at hmem
  obtain ⟨β', s', hx', _, hi, hq'⟩ := bag_arrival hx hout hw hmem hq
  exact ⟨β', s', hx', hi.trans hh.symm, by rw [hq']⟩

/-- **T3, the converse inclusion (any channel, any execution).**  Every
observation in the fiber at `h` comes from a run of `M` on an arrival order
of `h`'s events; with a FIFO channel, the arrival order is a linear
extension of `h`'s order. -/
theorem fiber_sub [PO O] {M : SM.Machine Q P O} (h : OccInp C P k M) (o : O)
    (hS : (spec k M).S h o) :
    ∃ w : List (Ev C P), w.Nodup ∧ (∀ e, e ∈ w ↔ h.val.mem e) ∧
      (∃ q, SM.Runs M M.q0 (w.map Ev.payload) q ∧ M.obs q = o) ∧
      (k = .fifo → w.Pairwise fun a b => ¬ h.val.lt b a) := by
  obtain ⟨β, f, hr, hi, ho⟩ := (spec_iff _ _).1 hS
  obtain ⟨hv, hocc⟩ := h
  dsimp only at hi ⊢
  subst hi
  have I := reach_inv β f hr
  refine ⟨recvs β, recvs_nodup hr, fun e => mem_recvs, ⟨f.q, I.runs, ho⟩, fun hk => ?_⟩
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

/-- Send then receive each event in turn. -/
def pairs : List (Ev C P) → List (Act C P O)
  | [] => []
  | e :: l => .send e :: .recv e :: pairs l

theorem pairs_append : ∀ (l l' : List (Ev C P)),
    (pairs (l ++ l') : List (Act C P O)) = pairs l ++ pairs l'
  | [], _ => rfl
  | e :: l, l' => by simp [pairs, pairs_append l l']

theorem recvs_pairs : ∀ (l : List (Ev C P)), recvs (pairs l : List (Act C P O)) = l
  | [] => rfl
  | e :: l => by simp [pairs, recvs_pairs l]

theorem chanRecv_single (k : ChanKind) (e : Ev C P) : chanRecv k [e] e [] := by
  cases k
  · exact ⟨[], [], rfl, rfl⟩
  · rfl

section single
variable {k : ChanKind} {M : SM.Machine Q P O}

/-- The single client's sends are `evs 0` of their payloads. -/
theorem reach_unit :
    ∀ (β : List (Act Unit P O)) (f : Flat Unit P Q), Reach k M β f →
      f.cnt () = (sends β).length ∧ sends β = evs 0 ((sends β).map Ev.payload) := by
  refine reach_induction (C := Unit) (k := k) (M := M) ⟨rfl, rfl⟩ ?_
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

/-- With a FIFO channel, the single client's received events are `evs 0` of
their payloads. -/
theorem recvs_canon {β : List (Act Unit P O)} {f : Flat Unit P Q} (hr : Reach .fifo M β f) :
    recvs β = evs 0 ((recvs β).map Ev.payload) := by
  have h1 := (reach_unit β f hr).2
  rw [(reach_inv β f hr).fifo rfl] at h1
  rw [List.map_append, evs_append] at h1
  exact (List.append_inj h1 (by rw [evs_length, List.length_map])).1

/-- The canonical execution of a word. -/
theorem reach_pairs (k : ChanKind) (M : SM.Machine Q P O) :
    ∀ (w : List P) (q : Q), SM.Runs M M.q0 w q →
      Reach k M (pairs (evs 0 w) : List (Act Unit P O)) ⟨q, fun _ => w.length, []⟩ := by
  refine snoc_ind ?_ ?_
  · intro q hq
    cases hq
    exact reach_nil.2 rfl
  · intro w p ih q hq
    obtain ⟨q1, h1, h2⟩ := SM.runs_split w [p] hq
    have hs : M.step q1 p q := by
      cases h2 with
      | cons hs hr => cases hr; exact hs
    have r1 := ih q1 h1
    let e : Ev Unit P := ⟨(), w.length, p⟩
    have r2 : Reach k M (pairs (evs 0 w) ++ [.send e])
        ⟨q1, bump (fun _ => w.length) (), [] ++ [e]⟩ :=
      reach_snoc.2 ⟨_, r1, FStep.send _ e rfl⟩
    have r3 : Reach k M ((pairs (evs 0 w) ++ [.send e]) ++ [.recv e])
        ⟨q, bump (fun _ => w.length) (), []⟩ :=
      reach_snoc.2 ⟨_, r2, FStep.recv _ e q [] hs (chanRecv_single k e)⟩
    have hb : bump (fun _ => w.length) () = fun _ => (w ++ [p]).length := by
      funext c; simp [bump]
    have hp : (pairs (evs 0 (w ++ [p])) : List (Act Unit P O)) =
        (pairs (evs 0 w) ++ [.send e]) ++ [.recv e] := by
      simp [evs_append, pairs_append, evs, pairs, e]
    rw [hp, ← hb]
    exact r3

/-- The word of an input: the payloads of its events in sequence order. -/
noncomputable def word (h : OccInp Unit P .fifo M) : SM.Seq P :=
  ⟨(recvs (Classical.choose h.occ)).map Ev.payload⟩

theorem recvs_prefix {β β' : List (Act Unit P O)} {f f' : Flat Unit P Q}
    (hr : Reach .fifo M β f) (hr' : Reach .fifo M β' f')
    (h : ∀ e, Act.recv e ∈ β → Act.recv e ∈ β') :
    ∃ v, (recvs β').map Ev.payload = (recvs β).map Ev.payload ++ v := by
  apply evs_sub_prefix (n := 0)
  intro x hx
  rw [← recvs_canon hr] at hx
  rw [← recvs_canon hr']
  exact mem_recvs.2 (h x (mem_recvs.1 hx))

theorem word_spec (h : OccInp Unit P .fifo M) {β : List (Act Unit P O)} {f : Flat Unit P Q}
    (hr : Reach .fifo M β f) (hi : input β = h.val) :
    (word h).ev = (recvs β).map Ev.payload := by
  have hc := Classical.choose_spec h.occ
  obtain ⟨s0, hx0, hi0⟩ := hc
  have hr0 : Reach .fifo M (Classical.choose h.occ) (toFlat s0) := ⟨s0, hx0, rfl⟩
  have hm : ∀ e, Act.recv e ∈ β ↔ Act.recv e ∈ Classical.choose h.occ := fun e => by
    show (input β).mem e ↔ (input _).mem e
    rw [hi, hi0]
  obtain ⟨v, hv⟩ := recvs_prefix hr hr0 fun e => (hm e).1
  obtain ⟨u, hu⟩ := recvs_prefix hr0 hr fun e => (hm e).2
  exact seq_eq_of_prefix hu hv

theorem lt_iff_unit {β : List (Act Unit P O)} {f : Flat Unit P Q} (hr : Reach k M β f)
    (a b : Ev Unit P) :
    (input β).lt a b ↔ ((input β).mem a ∧ (input β).mem b) ∧ a.seq < b.seq :=
  ⟨fun h => ⟨h.1, seq_lt_of_lt hr h (Subsingleton.elim _ _)⟩,
    fun ⟨⟨ha, hb⟩, hs⟩ => lt_of_seq_lt hr ha hb (Subsingleton.elim _ _) hs⟩

theorem word_le_iff (h h' : OccInp Unit P .fifo M) : h ≼ h' ↔ word h ≼ word h' := by
  obtain ⟨β, s, hx, hi⟩ := h.occ
  obtain ⟨β', s', hx', hi'⟩ := h'.occ
  have hr : Reach .fifo M β (toFlat s) := ⟨s, hx, rfl⟩
  have hr' : Reach .fifo M β' (toFlat s') := ⟨s', hx', rfl⟩
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

theorem word_inj {h h' : OccInp Unit P .fifo M} (he : word h = word h') : h = h' :=
  PO.antisymm ((word_le_iff h h').2 (he ▸ PO.refl _)) ((word_le_iff h' h).2 (he ▸ PO.refl _))

theorem word_surj (w : SM.Seq P) : ∃ h : OccInp Unit P .fifo M, word h = w := by
  obtain ⟨q, hq⟩ := SM.runs_exists M M.q0 w.ev
  have hr := reach_pairs .fifo M w.ev q hq
  refine ⟨occOf hr, ?_⟩
  have := word_spec (occOf hr) hr rfl
  rw [recvs_pairs, evs_payload] at this
  cases w; cases hw : word (occOf hr); rw [hw] at this; cases this; rfl

variable [PO O] in
theorem word_fiber (h : OccInp Unit P .fifo M) (o : O) :
    (spec .fifo M).S h o ↔ (SM.induced M (SM.prefixAbs P)).S (word h) o := by
  constructor
  · intro hS
    obtain ⟨β, f, hr, hi, ho⟩ := (spec_iff _ _).1 hS
    refine ⟨_, f.q, ?_, (reach_inv β f hr).runs, ho⟩
    show SM.Seq.mk _ = word h
    rw [← word_spec h hr hi]
  · rintro ⟨w, q, hw, hq, rfl⟩
    have hr := reach_pairs .fifo M w q hq
    have he : word (occOf hr) = word h := by
      have := word_spec (occOf hr) hr rfl
      rw [recvs_pairs, evs_payload] at this
      rw [← hw]
      cases hx : word (occOf hr); rw [hx] at this; cases this; rfl
    rw [← word_inj he]
    exact spec_of_reach hr

/-- **T2 (single client, FIFO channel).**  Every input is a chain; the map
`word` (payloads in sequence order) is an order isomorphism from the inputs
onto event sequences under the prefix order that carries each fiber to the
fiber of the prefix encoding `SM.induced M (SM.prefixAbs P)`.  Hence the
induced specification is consistent iff the prefix encoding is, and for
deterministic `M` iff `M`'s observations grow along transitions. -/
theorem fifo_single [PO O] (M : SM.Machine Q P O) :
    (∀ h : OccInp Unit P .fifo M, ∀ a b, h.val.mem a → h.val.mem b → a ≠ b →
      h.val.lt a b ∨ h.val.lt b a) ∧
    (∀ h h' : OccInp Unit P .fifo M, h ≼ h' ↔ word h ≼ word h') ∧
    (∀ w : SM.Seq P, ∃ h : OccInp Unit P .fifo M, word h = w) ∧
    (∀ h o, (spec .fifo M).S h o ↔ (SM.induced M (SM.prefixAbs P)).S (word h) o) ∧
    ((spec (C := Unit) .fifo M).Consistent ↔ (SM.induced M (SM.prefixAbs P)).Consistent) ∧
    (SM.Deterministic M → ((spec (C := Unit) .fifo M).Consistent ↔ SM.TransMono M)) := by
  have hcons : (spec (C := Unit) .fifo M).Consistent ↔
      (SM.induced M (SM.prefixAbs P)).Consistent := by
    rw [complete_calm, complete_calm]
    exact liftedMono_transfer _ _ word word_le_iff word_surj word_fiber
  refine ⟨fun h a b ha hb hne => ?_, word_le_iff, word_surj, word_fiber, hcons,
    fun hd => hcons.trans (SM.induced_prefix M hd).2⟩
  obtain ⟨β, s, hx, hi⟩ := h.occ
  rw [← hi] at ha hb ⊢
  exact lt_total_client ⟨s, hx, rfl⟩ ha hb (Subsingleton.elim _ _) hne

end single

end IOM
end CC
