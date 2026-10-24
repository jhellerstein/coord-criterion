import CoordCriterion.CAP.Register

/-!
# Gilbert–Lynch's Theorem 1 from Corollary `cor:gilbert-lynch` (Appendix F)

Supports the last paragraph of `appendices/cap-response.tex` ("Recovering
Gilbert–Lynch": the asynchronous theorem follows from the corollary).

Gilbert and Lynch (2002), Theorem 1: in the asynchronous network model, no
algorithm implements a read/write register that is both available and atomic
in all fair executions, including those in which messages are lost.  This file
models that setting (`Alg`, `GExec`, `Atomic`, `Available`) and proves the
theorem (`gilbert_lynch_async`) *by reduction* to the corollary: the
algorithm's translation `sysOf A` (a `CC.CAP.System` over the register
specification `CC.GL.regSpec`) would have Answering (`sys_answering`) and
Response Partition Consistency at realized histories (`sys_rpc`), which the
corollary forbids (`gilbert_lynch_client`).

## The asynchronous model (modeling choices)

* *Nodes* `Fin N` run input-enabled, possibly nondeterministic state machines
  (`Alg`) over actions `inv a k` (client invokes operation `a`, of kind `k`, at
  this node), `resp a r`, `send dst m`, `recv src m`.  I/O-automaton tasks and
  fairness are not modeled; they enter only through availability (below).
* *Executions* (`GExec`, `IsGExec`) give each node's actions with global times
  (positions in the execution's event sequence): each node follows its machine,
  local order agrees with time, times are distinct, and every receipt is of a
  distinct earlier send to the receiver.  Messages may be lost (sends need not
  be received).  This is equivalent to an alternating state/action sequence.
* *Clients* are well formed (`ClientWF`): each operation id is used once, and
  a node's client invokes only after all its earlier invocations there were
  answered (Lynch's well-formedness).
* *Atomicity* (`AtomicExec`, Lynch, *Distributed Algorithms* §13.1): responses
  are well formed (to an earlier invocation at the same node, at most once),
  and a total order of the completed and some pending operations extends
  real-time precedence and makes every response the sequential register's
  response.  `Atomic A`: every execution with well-formed clients is atomic.
* *Availability* (`Available A`), in the finite form for executions in which
  messages are lost: for every finite execution and invocation pending at node
  `i`, some extension adding no invocation and no receipt (every message is
  lost), with all new events after the old ones, contains a response to it at
  `i`.  Gilbert–Lynch availability implies it: extend the finite execution
  fairly, with no new invocations and every message lost; the response occurs
  at a finite point.  (This direction is argued, not formalized; infinite
  executions are not modeled.)  Since it is implied, the theorem below is at
  least as strong as theirs for this model.

## The reduction

1. *Algorithms are strategies* (`Corr`, `sysOf`).  Participant `p` of a
   two-participant history runs node `p`.  An invocation becomes the input
   event whose input is the node's *view* (its invoked operations, with no
   precedence edges); a response becomes an output event emitting the node's
   *response map* (first response to each operation), with the canonical
   commitment `κ_u` when the map is not exposable; a send is a send.  The
   participant may also re-emit its current map, since Answering requires an
   output event even when nothing is pending.  `atomic_view`: an atomic
   algorithm's response map in the execution where the node is alone lies in
   the fiber at its view; since the node's behaviour depends only on its own
   run, every translated output event is legal (`emit_legal`).
2. *Availability is Answering* (`sys_answering`): availability is applied in
   the execution where the node is alone, once per unanswered operation of its
   view (`answer_all`), then the final map is emitted; it answers every
   operation of the view, so it is in `Q_p`.
3. *Atomicity is Response Partition Consistency at the realized history*
   (`sys_rpc`): an interleaving of a client history is an execution of the
   algorithm (times = positions); its realized history records exactly the
   invoked operations and the real-time precedence; atomicity of that
   execution puts the union of all emitted maps in the fiber at `h_C`
   (`lin_to_regS`).  The precondition that `h_C` expand the current inputs is
   not needed.

The corollary is used in a *client form* (`AnsweringC`, `RealizedRPCC`): its
hypotheses are required only for client histories (`ClientH`: two
participants, empty initial inputs, each input event adds one fresh operation
invoked at that participant after all its earlier ones were answered).  A GL
algorithm says nothing about the paper's richer environment (inputs mentioning
other replicas' operations or precedence edges), so its translation cannot be
expected to satisfy the hypotheses there.  The paper's proof uses only client
histories, so the client form has the same proof (`gilbert_lynch_client`,
copied from `CC.GL.gilbert_lynch`) and implies the paper's form
(`answeringC_of_RA`, `realizedRPCC_of`).

Non-vacuity: the silent algorithm is atomic (`silent_atomic`) and the eager
algorithm is available (`eager_available`).
-/

namespace CC
namespace AsyncGL

open CAP GL

/-! ## Gilbert–Lynch's asynchronous model -/

/-- Actions of a node: invocations (`inv a k`: operation id `a` of kind `k`,
invoked at this node) and message receipts are inputs; responses and sends are
locally controlled. -/
inductive Act (N : Nat) (M : Type) where
  | inv (a : Nat) (k : Kind)
  | resp (a : Nat) (r : Resp)
  | send (dst : Fin N) (m : M)
  | recv (src : Fin N) (m : M)

/-- An algorithm: one (possibly nondeterministic) input-enabled state machine
per node. -/
structure Alg (N : Nat) (M : Type) where
  St : Type
  start : Fin N → St
  step : Fin N → St → Act N M → St → Prop
  inv_enabled : ∀ i s a k, ∃ s', step i s (.inv a k) s'
  recv_enabled : ∀ i s src m, ∃ s', step i s (.recv src m) s'

variable {N : Nat} {M : Type}

/-- A run of node `i`'s state machine along a list of actions. -/
inductive NRun (A : Alg N M) (i : Fin N) : A.St → List (Act N M) → A.St → Prop where
  | nil (s : A.St) : NRun A i s [] s
  | cons {s s' s'' : A.St} {x : Act N M} {l : List (Act N M)} :
      A.step i s x s' → NRun A i s' l s'' → NRun A i s (x :: l) s''

/-- A (finite) execution: each node's actions with their global times (the
position of the event in the execution's sequence of events). -/
structure GExec (N : Nat) (M : Type) where
  tr : Fin N → List (Nat × Act N M)

def acts (l : List (Nat × Act N M)) : List (Act N M) := l.map Prod.snd

/-- `E` is an execution of `A`: every node follows its state machine, local
order agrees with time, times are distinct, and every receipt is of a distinct
earlier send addressed to the receiver (messages may be lost: not every send
is received). -/
def IsGExec (A : Alg N M) (E : GExec N M) : Prop :=
  (∀ i, ∃ s, NRun A i (A.start i) (acts (E.tr i)) s) ∧
  (∀ i, (E.tr i).Pairwise (fun x y => x.1 < y.1)) ∧
  (∀ i j x y, x ∈ E.tr i → y ∈ E.tr j → x.1 = y.1 → i = j ∧ x = y) ∧
  (∃ f : Nat → Nat, ∀ i T src m, (T, Act.recv src m) ∈ E.tr i →
      f T < T ∧ (f T, Act.send i m) ∈ E.tr src ∧
      ∀ i' T' src' m', (T', Act.recv src' m') ∈ E.tr i' → f T' = f T → T' = T)

/-- Well-formed clients: each operation id is used once, and a node's client
invokes a new operation only after every earlier operation it invoked at that
node has been responded to (invocations and responses alternate). -/
def ClientWF (E : GExec N M) : Prop :=
  (∀ i j x y a k k', x ∈ E.tr i → y ∈ E.tr j → x.2 = Act.inv a k → y.2 = Act.inv a k' →
    x.1 = y.1) ∧
  (∀ i T a k T' b k', (T, Act.inv a k) ∈ E.tr i → (T', Act.inv b k') ∈ E.tr i → T' < T →
    ∃ T'' r, T'' < T ∧ (T'', Act.resp b r) ∈ E.tr i)

def IsWriteG (E : GExec N M) (w v : Nat) : Prop := ∃ i T, (T, Act.inv w (.write v)) ∈ E.tr i

/-- Under the linearization `lp` of the operations `inc`, the read `a` returns `v`. -/
def ReadValG (E : GExec N M) (inc : Nat → Prop) (lp : Nat → Nat) (a v : Nat) : Prop :=
  (v = v0 ∧ ∀ w v', IsWriteG E w v' → inc w → ¬ lp w < lp a) ∨
  (∃ w, IsWriteG E w v ∧ inc w ∧ lp w < lp a ∧
    ∀ w' v', IsWriteG E w' v' → inc w' → lp w' < lp a → lp w' ≤ lp w)

def RespOkG (E : GExec N M) (inc : Nat → Prop) (lp : Nat → Nat) (a : Nat) : Kind → Resp → Prop
  | .write _, r => r = .ack
  | .read, r => ∃ v, r = .val v ∧ ReadValG E inc lp a v

/-- Atomicity of one execution (Lynch, *Distributed Algorithms*, 13.1):
responses are well formed (each answers an earlier invocation at the same
node, at most once), and some total order `lp` of the completed operations and
some of the pending ones (`inc`) extends real-time precedence and makes every
response the correct sequential register response. -/
def AtomicExec (E : GExec N M) : Prop :=
  (∀ i T a r, (T, Act.resp a r) ∈ E.tr i →
    (∃ T0 kd, T0 < T ∧ (T0, Act.inv a kd) ∈ E.tr i) ∧
    ∀ j T' r', (T', Act.resp a r') ∈ E.tr j → T' = T) ∧
  ∃ (inc : Nat → Prop) (lp : Nat → Nat),
    (∀ i T a r, (T, Act.resp a r) ∈ E.tr i → inc a) ∧
    (∀ a, inc a → ∃ i T kd, (T, Act.inv a kd) ∈ E.tr i) ∧
    (∀ a b, inc a → inc b → lp a = lp b → a = b) ∧
    (∀ i T a r j T' b kd, (T, Act.resp a r) ∈ E.tr i → (T', Act.inv b kd) ∈ E.tr j →
      T < T' → inc b → lp a < lp b) ∧
    (∀ i T a r j T0 kd, (T, Act.resp a r) ∈ E.tr i → (T0, Act.inv a kd) ∈ E.tr j →
      RespOkG E inc lp a kd r)

/-- Atomic consistency: every execution with well-formed clients is atomic. -/
def Atomic (A : Alg N M) : Prop := ∀ E, IsGExec A E → ClientWF E → AtomicExec E

/-- Availability, in the finite form used under message loss: a pending
invocation at a node is answered in some extension that adds no invocation
and in which every message is lost (no receipt). -/
def Available (A : Alg N M) : Prop :=
  ∀ E, IsGExec A E → ClientWF E → ∀ i T a kd, (T, Act.inv a kd) ∈ E.tr i →
    (∀ T' r, (T', Act.resp a r) ∉ E.tr i) →
    ∃ E', IsGExec A E' ∧
      (∀ j, ∃ β, E'.tr j = E.tr j ++ β ∧ ∀ y ∈ β, (∀ j' x, x ∈ E.tr j' → x.1 < y.1) ∧
        (∀ a k, y.2 ≠ Act.inv a k) ∧ (∀ s m, y.2 ≠ Act.recv s m)) ∧
      ∃ T' r, (T', Act.resp a r) ∈ E'.tr i

/-! ## Views and response maps of a node's trace -/

def invOf (a : Nat) : Act N M → Option Kind
  | .inv b k => if b = a then some k else none
  | _ => none

def respOf (a : Nat) : Act N M → Option Resp
  | .resp b r => if b = a then some r else none
  | _ => none

def firstInv (l : List (Act N M)) (a : Nat) : Option Kind := l.findSome? (invOf a)
def firstResp (l : List (Act N M)) (a : Nat) : Option Resp := l.findSome? (respOf a)

theorem firstInv_some {l : List (Act N M)} {a : Nat} {k : Kind} (h : firstInv l a = some k) :
    Act.inv a k ∈ l := by
  induction l with
  | nil => simp [firstInv] at h
  | cons x l ih =>
    simp only [firstInv, List.findSome?_cons] at h
    cases hx : invOf a x with
    | none => rw [hx] at h; exact List.mem_cons_of_mem _ (ih h)
    | some k' =>
      rw [hx] at h; cases h
      cases x <;> simp [invOf] at hx
      obtain ⟨rfl, rfl⟩ := hx; exact List.mem_cons_self ..

theorem firstInv_none {l : List (Act N M)} {a : Nat} (h : firstInv l a = none) (k : Kind) :
    Act.inv a k ∉ l := by
  intro hm
  simp only [firstInv, List.findSome?_eq_none_iff] at h
  have := h _ hm
  simp [invOf] at this

theorem firstInv_of_mem {l : List (Act N M)} {a : Nat} {k : Kind} (h : Act.inv a k ∈ l) :
    ∃ k', firstInv l a = some k' := by
  cases hf : firstInv l a with
  | none => exact absurd h (firstInv_none hf k)
  | some k' => exact ⟨k', rfl⟩

theorem firstResp_some {l : List (Act N M)} {a : Nat} {r : Resp} (h : firstResp l a = some r) :
    Act.resp a r ∈ l := by
  induction l with
  | nil => simp [firstResp] at h
  | cons x l ih =>
    simp only [firstResp, List.findSome?_cons] at h
    cases hx : respOf a x with
    | none => rw [hx] at h; exact List.mem_cons_of_mem _ (ih h)
    | some k' =>
      rw [hx] at h; cases h
      cases x <;> simp [respOf] at hx
      obtain ⟨rfl, rfl⟩ := hx; exact List.mem_cons_self ..

theorem firstResp_none {l : List (Act N M)} {a : Nat} (h : firstResp l a = none) (r : Resp) :
    Act.resp a r ∉ l := by
  intro hm
  simp only [firstResp, List.findSome?_eq_none_iff] at h
  have := h _ hm
  simp [respOf] at this

theorem firstResp_of_mem {l : List (Act N M)} {a : Nat} {r : Resp} (h : Act.resp a r ∈ l) :
    ∃ r', firstResp l a = some r' := by
  cases hf : firstResp l a with
  | none => exact absurd h (firstResp_none hf r)
  | some r' => exact ⟨r', rfl⟩

theorem firstInv_bound (l : List (Act N M)) : ∃ B, ∀ a, B ≤ a → firstInv l a = none := by
  induction l with
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | cons x l ih =>
    obtain ⟨B, hB⟩ := ih
    cases x with
    | inv b k =>
      refine ⟨max B (b + 1), fun a ha => ?_⟩
      simp only [firstInv, List.findSome?_cons, invOf]
      have : b ≠ a := by omega
      simp only [this, ite_false]
      exact hB a (by omega)
    | _ => exact ⟨B, fun a ha => by simpa [firstInv, invOf] using hB a ha⟩

/-- A node's view: the operations invoked at it, with no precedence edges. -/
def viewOf (p : Nat) (l : List (Act N M)) : Hist where
  ops := fun a => (firstInv l a).map (fun k => ⟨p, k⟩)
  prec := fun _ _ => False
  fin := by
    obtain ⟨B, hB⟩ := firstInv_bound l
    exact ⟨B, fun a ha => by rw [hB a ha]; rfl⟩
  dom := fun _ _ h => h.elim
  irrefl := fun _ h => h
  trans := fun _ _ _ h => h.elim

/-- The response map of a trace: each operation's first response. -/
def rmap (l : List (Act N M)) : RMap := ⟨firstResp l⟩

theorem rmap_mono (l s : List (Act N M)) : rmap l ≼ rmap (l ++ s) := by
  intro a r h
  show firstResp (l ++ s) a = some r
  have h : firstResp l a = some r := h
  simp only [firstResp] at h ⊢
  rw [List.findSome?_append, h]; rfl

/-- Add one operation to a history (no new precedence). -/
def addOp (h : Hist) (x : Nat) (op : Op) : Hist where
  ops := fun a => if a = x then some op else h.ops a
  prec := h.prec
  fin := by
    obtain ⟨B, hB⟩ := h.fin
    refine ⟨max B (x + 1), fun a ha => ?_⟩
    have : a ≠ x := by omega
    simp only [this, ite_false]; exact hB a (by omega)
  dom := by
    intro a b hab
    obtain ⟨h1, h2⟩ := h.dom a b hab
    constructor <;> (split <;> simp_all)
  irrefl := h.irrefl
  trans := h.trans

theorem viewOf_nil (p : Nat) : viewOf (N := N) (M := M) p [] = emptyH :=
  Hist.ext' (by funext a; rfl) rfl

theorem viewOf_snoc_inv (p : Nat) (l : List (Act N M)) (x : Nat) (k : Kind)
    (hx : firstInv l x = none) :
    viewOf p (l ++ [.inv x k]) = addOp (viewOf p l) x ⟨p, k⟩ := by
  refine Hist.ext' ?_ rfl
  funext a
  simp only [viewOf, addOp, firstInv, List.findSome?_append]
  by_cases hax : a = x
  · subst hax
    have : l.findSome? (invOf a) = none := hx
    simp [this, invOf]
  · simp only [hax, ite_false]
    cases h : l.findSome? (invOf a) <;> simp [invOf, Ne.symm hax]

def NoInv (s : List (Act N M)) : Prop := ∀ a k, Act.inv a k ∉ s
def NoResp (s : List (Act N M)) : Prop := ∀ a r, Act.resp a r ∉ s

theorem firstInv_append_noinv {l s : List (Act N M)} (hs : NoInv s) (a : Nat) :
    firstInv (l ++ s) a = firstInv l a := by
  have : s.findSome? (invOf a) = none := by
    rw [List.findSome?_eq_none_iff]
    intro x hx
    cases x with
    | inv b k => simp only [invOf]; split
                 · subst_vars; exact absurd hx (hs _ k)
                 · rfl
    | _ => rfl
  simp only [firstInv, List.findSome?_append, this, Option.or_none]

theorem viewOf_append_noinv (p : Nat) {l s : List (Act N M)} (hs : NoInv s) :
    viewOf p (l ++ s) = viewOf p l :=
  Hist.ext' (by funext a; simp only [viewOf, firstInv_append_noinv hs]) rfl

theorem rmap_append_noresp {l s : List (Act N M)} (hs : NoResp s) :
    rmap (l ++ s) = rmap l := by
  apply RMap.ext'
  funext a
  have : s.findSome? (respOf a) = none := by
    rw [List.findSome?_eq_none_iff]
    intro x hx
    cases x with
    | resp b r => simp only [respOf]; split
                  · subst_vars; exact absurd hx (hs _ r)
                  · rfl
    | _ => rfl
  show firstResp (l ++ s) a = firstResp l a
  simp only [firstResp, List.findSome?_append, this, Option.or_none]

theorem noinv_single_resp (a : Nat) (r : Resp) : NoInv [Act.resp (N := N) (M := M) a r] := by
  intro _ _ h; simp at h
theorem noinv_single_send (d : Fin N) (m : M) : NoInv [Act.send d m] := by
  intro _ _ h; simp at h
theorem noresp_single_inv (a : Nat) (k : Kind) : NoResp [Act.inv (N := N) (M := M) a k] := by
  intro _ _ h; simp at h
theorem noresp_single_send (d : Fin N) (m : M) : NoResp [Act.send d m] := by
  intro _ _ h; simp at h

theorem nrun_append {A : Alg N M} {i : Fin N} :
    ∀ {s s'' : A.St} {l1 l2 : List (Act N M)},
      NRun A i s (l1 ++ l2) s'' ↔ ∃ s', NRun A i s l1 s' ∧ NRun A i s' l2 s''
  | s, s'', [], l2 => ⟨fun h => ⟨s, .nil s, h⟩, fun ⟨_, h1, h2⟩ => by cases h1; exact h2⟩
  | s, s'', x :: l1, l2 => by
    constructor
    · intro h
      cases h with
      | cons hs hr =>
        obtain ⟨s', h1, h2⟩ := nrun_append.1 hr
        exact ⟨s', .cons hs h1, h2⟩
    · rintro ⟨s', h1, h2⟩
      cases h1 with
      | cons hs hr => exact .cons hs (nrun_append.2 ⟨s', hr, h2⟩)


/-! ## Atomicity gives a linearization of any history that records the invoked
operations and (some of) the real-time precedence -/

theorem le_sum_map (f : Nat → Nat) : ∀ {l : List Nat} {x : Nat}, x ∈ l → f x ≤ (l.map f).sum
  | [], _, h => by cases h
  | y :: l, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_map f h; simp; omega

open Classical in
noncomputable def posOf (inc : Nat → Prop) (lp : Nat → Nat) (B x : Nat) : Nat :=
  if inc x then lp x else B + x

theorem posOf_inc {inc : Nat → Prop} {lp : Nat → Nat} {B x : Nat} (h : inc x) :
    posOf inc lp B x = lp x := by simp [posOf, h]

theorem posOf_ninc {inc : Nat → Prop} {lp : Nat → Nat} {B x : Nat} (h : ¬ inc x) :
    posOf inc lp B x = B + x := by simp [posOf, h]

/-- **Atomic responses are explained by a linearization.**  If `E` is atomic,
`h` has exactly the invoked operations of `E` (at their nodes) and only
precedence edges from a response to a later invocation, then every response map
`u` recording responses of `E` lies in the register fiber `S(h)`. -/
theorem lin_to_regS {E : GExec N M} (hat : AtomicExec E) (h : Hist) (u : RMap)
    (h1 : ∀ a op, h.ops a = some op → ∃ i T, (T, Act.inv a op.kind) ∈ E.tr i)
    (h2 : ∀ i T a kd, (T, Act.inv a kd) ∈ E.tr i → h.ops a = some ⟨i.val, kd⟩)
    (h3 : ∀ a b, h.prec a b → ∃ i T r j T' kd, (T, Act.resp a r) ∈ E.tr i ∧
      (T', Act.inv b kd) ∈ E.tr j ∧ T < T')
    (h4 : ∀ a r, u.f a = some r → ∃ i T, (T, Act.resp a r) ∈ E.tr i) :
    regS h u := by
  obtain ⟨hwr, inc, lp, hcomp, hinv, hinj, hrt, hok⟩ := hat
  obtain ⟨Nb, hNb⟩ := h.fin
  let B := ((List.range Nb).map lp).sum + 1
  have hops : ∀ x, inc x → h.ops x ≠ none := by
    intro x hx
    obtain ⟨i, T, kd, hm⟩ := hinv x hx
    rw [h2 i T x kd hm]; simp
  have hlt : ∀ x, inc x → lp x < B := by
    intro x hx
    have : x < Nb := Nat.lt_of_not_le fun hle => hops x hx (hNb x hle)
    have := le_sum_map lp (List.mem_range.2 this)
    show lp x < ((List.range Nb).map lp).sum + 1
    omega
  let pos := posOf inc lp B
  refine ⟨pos, ⟨?_, ?_⟩, ?_⟩
  · intro a b _ _ he
    by_cases ha : inc a <;> by_cases hb : inc b
    · exact hinj a b ha hb (by simpa [pos, posOf_inc ha, posOf_inc hb] using he)
    · have := hlt a ha
      simp only [pos, posOf_inc ha, posOf_ninc hb] at he; omega
    · have := hlt b hb
      simp only [pos, posOf_inc hb, posOf_ninc ha] at he; omega
    · simp only [pos, posOf_ninc ha, posOf_ninc hb] at he; omega
  · intro a b hab
    obtain ⟨i, T, r, j, T', kd, hra, hib, hTT⟩ := h3 a b hab
    have ha := hcomp i T a r hra
    simp only [pos, posOf_inc ha]
    by_cases hb : inc b
    · rw [posOf_inc hb]; exact hrt i T a r j T' b kd hra hib hTT hb
    · rw [posOf_ninc hb]; have := hlt a ha; omega
  · intro a r hu
    obtain ⟨i, T, hra⟩ := h4 a r hu
    obtain ⟨⟨T0, kd, _, hia⟩, _⟩ := hwr i T a r hra
    refine ⟨⟨i.val, kd⟩, h2 i T0 a kd hia, ?_⟩
    have hk := hok i T a r i T0 kd hra hia
    have ha := hcomp i T a r hra
    have hpa : pos a = lp a := posOf_inc ha
    -- writes of `h` are the invoked writes of `E`
    have hw1 : ∀ w v, IsWrite h w v → IsWriteG E w v := by
      rintro w v ⟨rr, hw⟩
      obtain ⟨i', T', hm⟩ := h1 w _ hw
      exact ⟨i', T', hm⟩
    have hnot : ∀ w, ¬ inc w → ¬ pos w < pos a := by
      intro w hw
      simp only [pos, posOf_ninc hw, posOf_inc ha]
      have := hlt a ha; omega
    cases kd with
    | write v => exact hk
    | read =>
      obtain ⟨v, rfl, hv⟩ := hk
      refine ⟨v, rfl, ?_⟩
      rcases hv with ⟨hv0, hno⟩ | ⟨w, hw, hiw, hlw, hmax⟩
      · refine Or.inl ⟨hv0, fun w v' hw hp => ?_⟩
        by_cases hiw : inc w
        · apply hno w v' (hw1 w v' hw) hiw
          simpa [pos, posOf_inc hiw, hpa] using hp
        · exact hnot w hiw hp
      · obtain ⟨i', T', hm⟩ := hw
        refine Or.inr ⟨w, ⟨i'.val, h2 i' T' w _ hm⟩, ?_, ?_⟩
        · simpa [pos, posOf_inc hiw, hpa] using hlw
        · intro w' v' hw' hp
          by_cases hiw' : inc w'
          · have := hmax w' v' (hw1 w' v' hw') hiw' (by simpa [pos, posOf_inc hiw', hpa] using hp)
            simpa [pos, posOf_inc hiw', posOf_inc hiw] using this
          · exact absurd hp (hnot w' hiw')


/-! ## The translation of node traces into participant histories -/

theorem snoc_induction {α : Type} {P : List α → Prop} (h0 : P [])
    (hs : ∀ l x, P l → P (l ++ [x])) : ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact h0
  | cons x r ih => rw [List.reverse_cons]; exact hs _ _ ih

variable {n : Nat}

/-- Participant histories over the register, with messages `(destination, m)`. -/
abbrev PL (N : Nat) (M : Type) (n : Nat) := List (LEv regSpec (Fin N × M) n)

/-- `Corr p t L`: the timed trace `t` of node `p` corresponds to participant
`p`'s local history `L`.  An invocation is an input event whose input is the
node's new view; a response is an output event emitting the trace's response
map (with the canonical commitment, if needed); a send is a send; and the
participant may re-emit its current response map (`stut`).  Each action is
timed by the index of its event in `L`. -/
inductive Corr (p : Nat) : List (Nat × Act N M) → PL N M n → Prop where
  | nil : Corr p [] []
  | inv {t : List (Nat × Act N M)} {L : PL N M n} {a : Nat} {k : Kind} :
      Corr p t L → firstInv (acts t) a = none →
      (∀ b, firstInv (acts t) b ≠ none → firstResp (acts t) b ≠ none) →
      Corr p (t ++ [(L.length, .inv a k)]) (L ++ [.inp (viewOf p (acts t ++ [.inv a k]))])
  | resp {t : List (Nat × Act N M)} {L : PL N M n} {a : Nat} {r : Resp}
      {γ : List (Commitment regSpec)} :
      Corr p t L → (γ = [] ∨ γ = [kc (rmap (acts t ++ [.resp a r]))]) →
      Corr p (t ++ [(L.length, .resp a r)]) (L ++ [.out γ (rmap (acts t ++ [.resp a r]))])
  | send {t : List (Nat × Act N M)} {L : PL N M n} {d : Fin N} {m : M} :
      Corr p t L → Corr p (t ++ [(L.length, .send d m)]) (L ++ [.send none (d, m)])
  | stut {t : List (Nat × Act N M)} {L : PL N M n} {γ : List (Commitment regSpec)} :
      Corr p t L → (γ = [] ∨ γ = [kc (rmap (acts t))]) →
      Corr p t (L ++ [.out γ (rmap (acts t))])

theorem acts_snoc (t : List (Nat × Act N M)) (x : Nat × Act N M) :
    acts (t ++ [x]) = acts t ++ [x.2] := by simp [acts]

theorem mem_acts {t : List (Nat × Act N M)} {x : Act N M} : x ∈ acts t ↔ ∃ T, (T, x) ∈ t := by
  simp [acts]

theorem corr_times {p : Nat} {t : List (Nat × Act N M)} {L : PL N M n} (h : Corr p t L) :
    (∀ x ∈ t, x.1 < L.length) ∧ t.Pairwise (fun x y => x.1 < y.1) := by
  induction h with
  | nil => simp
  | inv _ _ _ ih | resp _ _ ih | send _ ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · have := h1 x hx; simp; omega
      · simp at hx; subst hx; simp
    · rw [List.pairwise_append]
      refine ⟨h2, by simp, fun x hx y hy => ?_⟩
      simp at hy; subst hy; exact h1 x hx
  | stut _ _ ih =>
    obtain ⟨h1, h2⟩ := ih
    exact ⟨fun x hx => by have := h1 x hx; simp; omega, h2⟩

theorem corr_fresh {p : Nat} {t : List (Nat × Act N M)} {L : PL N M n} (h : Corr p t L) :
    ∀ x ∈ t, ∀ y ∈ t, ∀ a k k', x.2 = Act.inv a k → y.2 = Act.inv a k' → x = y := by
  induction h with
  | nil => simp
  | @inv t L a0 k0 _ hf _ ih =>
    intro x hx y hy a k k' hxa hya
    have hnot : ∀ z ∈ t, ∀ kk, z.2 ≠ Act.inv a0 kk := by
      intro z hz kk he
      exact firstInv_none hf kk (mem_acts.2 ⟨z.1, by rw [← he]; exact hz⟩)
    rcases List.mem_append.1 hx with hx | hx <;> rcases List.mem_append.1 hy with hy | hy
    · exact ih x hx y hy a k k' hxa hya
    · simp at hy; subst hy; simp at hya; obtain ⟨rfl, _⟩ := hya
      exact absurd hxa (hnot x hx k)
    · simp at hx; subst hx; simp at hxa; obtain ⟨rfl, _⟩ := hxa
      exact absurd hya (hnot y hy k')
    · simp at hx hy; rw [hx, hy]
  | resp _ _ ih | send _ ih =>
    intro x hx y hy a k k' hxa hya
    rcases List.mem_append.1 hx with hx | hx <;> rcases List.mem_append.1 hy with hy | hy
    · exact ih x hx y hy a k k' hxa hya
    all_goals first
      | (simp at hy; subst hy; simp at hya)
      | (simp at hx; subst hx; simp at hxa)
  | stut _ _ ih => exact ih

theorem corr_norecv {p : Nat} {t : List (Nat × Act N M)} {L : PL N M n} (h : Corr p t L) :
    ∀ x ∈ t, ∀ s m, x.2 ≠ Act.recv s m := by
  induction h with
  | nil => simp
  | inv _ _ _ ih | resp _ _ ih | send _ ih =>
    intro x hx s m
    rcases List.mem_append.1 hx with hx | hx
    · exact ih x hx s m
    · simp at hx; subst hx; simp
  | stut _ _ ih => exact ih

theorem corr_norecvL {p : Nat} {t : List (Nat × Act N M)} {L : PL N M n} (h : Corr p t L) :
    ∀ q k j d, LEv.recv q k j d ∉ L := by
  induction h with
  | nil => simp
  | inv _ _ _ ih | resp _ _ ih | send _ ih | stut _ _ ih =>
    intro q k j d hm
    rcases List.mem_append.1 hm with hm | hm
    · exact ih q k j d hm
    · simp at hm

/-- The last input of a participant history (its current input, from `∅`). -/
def lastInp {D : Type} (L : List (LEv regSpec D n)) : Hist :=
  L.foldl (fun h e => match e with | .inp j => j | _ => h) emptyH

theorem lastInp_snoc {D : Type} (L : List (LEv regSpec D n)) (e : LEv regSpec D n) :
    lastInp (L ++ [e]) = match e with | .inp j => j | _ => lastInp L := by
  simp only [lastInp, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem corr_lastInp {p : Nat} {t : List (Nat × Act N M)} {L : PL N M n} (h : Corr p t L) :
    lastInp L = viewOf p (acts t) := by
  induction h with
  | nil => exact (viewOf_nil p).symm
  | inv _ _ _ _ => rw [lastInp_snoc, acts_snoc]
  | resp _ _ ih =>
    rw [lastInp_snoc, acts_snoc, viewOf_append_noinv p (noinv_single_resp _ _)]; exact ih
  | send _ ih =>
    rw [lastInp_snoc, acts_snoc, viewOf_append_noinv p (noinv_single_send _ _)]; exact ih
  | stut _ _ ih => rw [lastInp_snoc]; exact ih

theorem getElem?_snoc_lt {α : Type} {L : List α} {e : α} {k : Nat} (hk : k < L.length) :
    (L ++ [e])[k]? = L[k]? := List.getElem?_append_left hk

theorem getElem?_snoc_len {α : Type} {L : List α} {e : α} : (L ++ [e])[L.length]? = some e := by
  simp

theorem lt_of_getElem?_snoc {α : Type} {L : List α} {e x : α} {k : Nat}
    (h : (L ++ [e])[k]? = some x) : (k < L.length ∧ L[k]? = some x) ∨ (k = L.length ∧ x = e) := by
  have hk : k < L.length + 1 := by
    have := (List.getElem?_eq_some_iff.1 h).1; simpa using this
  by_cases hlt : k < L.length
  · exact Or.inl ⟨hlt, by rw [getElem?_snoc_lt hlt] at h; exact h⟩
  · have : k = L.length := by omega
    subst this
    rw [getElem?_snoc_len] at h
    exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩

/-- A traced invocation is an input event of `L` whose input records it. -/
theorem corr_inv_ev {p : Nat} {t : List (Nat × Act N M)} {L : PL N M n} (h : Corr p t L) :
    ∀ k a kd, (k, Act.inv a kd) ∈ t → ∃ j, L[k]? = some (LEv.inp j) ∧ j.ops a = some ⟨p, kd⟩ := by
  induction h with
  | nil => simp
  | @inv t L a0 k0 hc hf halt ih =>
    intro k a kd hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨j, hj, hja⟩ := ih k a kd hm
      have := (corr_times hc).1 _ hm
      exact ⟨j, by rw [getElem?_snoc_lt this]; exact hj, hja⟩
    · simp at hm; obtain ⟨rfl, rfl, rfl⟩ := hm
      refine ⟨_, getElem?_snoc_len, ?_⟩
      show (firstInv (acts t ++ [Act.inv a _]) a).map _ = _
      simp only [firstInv, List.findSome?_append]
      have : (acts t).findSome? (invOf a) = none := hf
      simp [this, invOf]
  | resp hc _ ih | send hc ih =>
    intro k a kd hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨j, hj, hja⟩ := ih k a kd hm
      have := (corr_times hc).1 _ hm
      exact ⟨j, by rw [getElem?_snoc_lt this]; exact hj, hja⟩
    · simp at hm
  | stut hc _ ih =>
    intro k a kd hm
    obtain ⟨j, hj, hja⟩ := ih k a kd hm
    have := (corr_times hc).1 _ hm
    exact ⟨j, by rw [getElem?_snoc_lt this]; exact hj, hja⟩

/-- An operation recorded by an input event of `L` was invoked at `p` by then. -/
theorem corr_inp_ev {p : Nat} {t : List (Nat × Act N M)} {L : PL N M n} (h : Corr p t L) :
    ∀ k j a op, L[k]? = some (LEv.inp j) → j.ops a = some op →
      op.rep = p ∧ ∃ k', k' ≤ k ∧ (k', Act.inv a op.kind) ∈ t := by
  induction h with
  | nil => simp
  | @inv t L a0 k0 hc hf halt ih =>
    intro k j a op hk ha
    rcases lt_of_getElem?_snoc hk with ⟨hlt, hk⟩ | ⟨rfl, he⟩
    · obtain ⟨h1, k', hk', hm⟩ := ih k j a op hk ha
      exact ⟨h1, k', hk', List.mem_append_left _ hm⟩
    · cases he
      have ha' : (firstInv (acts t ++ [Act.inv a0 k0]) a).map (fun k => (⟨p, k⟩ : Op)) = some op := ha
      cases hf' : firstInv (acts t ++ [Act.inv a0 k0]) a with
      | none => rw [hf'] at ha'; cases ha'
      | some kk =>
        rw [hf'] at ha'; cases ha'
        refine ⟨rfl, ?_⟩
        have hm := firstInv_some hf'
        have hm' : Act.inv a kk ∈ acts (t ++ [(L.length, Act.inv a0 k0)]) := by
          rw [acts_snoc]; exact hm
        obtain ⟨T, hT⟩ := mem_acts.1 hm'
        have := (corr_times (Corr.inv (k := k0) hc hf halt)).1 _ hT
        simp at this
        exact ⟨T, by omega, hT⟩
  | resp hc _ ih | send hc ih | stut hc _ ih =>
    intro k j a op hk ha
    rcases lt_of_getElem?_snoc hk with ⟨hlt, hk⟩ | ⟨rfl, he⟩
    · obtain ⟨h1, k', hk', hm⟩ := ih k j a op hk ha
      first
        | exact ⟨h1, k', hk', List.mem_append_left _ hm⟩
        | exact ⟨h1, k', hk', hm⟩
    · cases he

/-- A response recorded by an output event of `L` was given at `p` by then. -/
theorem corr_out_ev {p : Nat} {t : List (Nat × Act N M)} {L : PL N M n} (h : Corr p t L) :
    ∀ k γ o a r, L[k]? = some (LEv.out γ o) → o.f a = some r →
      ∃ k', k' ≤ k ∧ (k', Act.resp a r) ∈ t := by
  induction h with
  | nil => simp
  | inv hc _ _ ih | send hc ih =>
    intro k γ o a r hk ha
    rcases lt_of_getElem?_snoc hk with ⟨hlt, hk⟩ | ⟨rfl, he⟩
    · obtain ⟨k', hk', hm⟩ := ih k γ o a r hk ha
      exact ⟨k', hk', List.mem_append_left _ hm⟩
    · cases he
  | @resp t L a0 r0 γ0 hc hγ ih =>
    intro k γ o a r hk ha
    rcases lt_of_getElem?_snoc hk with ⟨hlt, hk⟩ | ⟨rfl, he⟩
    · obtain ⟨k', hk', hm⟩ := ih k γ o a r hk ha
      exact ⟨k', hk', List.mem_append_left _ hm⟩
    · cases he
      have hm := firstResp_some ha
      have hm' : Act.resp a r ∈ acts (t ++ [(L.length, Act.resp a0 r0)]) := by
        rw [acts_snoc]; exact hm
      obtain ⟨T, hT⟩ := mem_acts.1 hm'
      have := (corr_times (Corr.resp (a := a0) (r := r0) hc hγ)).1 _ hT
      simp at this
      exact ⟨T, by omega, hT⟩
  | stut hc _ ih =>
    intro k γ o a r hk ha
    rcases lt_of_getElem?_snoc hk with ⟨hlt, hk⟩ | ⟨rfl, he⟩
    · exact ih k γ o a r hk ha
    · cases he
      obtain ⟨T, hT⟩ := mem_acts.1 (firstResp_some ha)
      have := (corr_times hc).1 _ hT
      exact ⟨T, by omega, hT⟩


/-- Invocations and responses alternate along a corresponding trace. -/
theorem corr_alt {p : Nat} {t : List (Nat × Act N M)} {L : PL N M n} (h : Corr p t L) :
    ∀ T a k T' b k', (T, Act.inv a k) ∈ t → (T', Act.inv b k') ∈ t → T' < T →
      ∃ T'' r, T'' < T ∧ (T'', Act.resp b r) ∈ t := by
  induction h with
  | nil => simp
  | @inv t L a0 k0 hc hf halt ih =>
    intro T a k T' b k' h1 h2 hlt
    have ht := (corr_times hc).1
    rcases List.mem_append.1 h1 with h1 | h1 <;> rcases List.mem_append.1 h2 with h2 | h2
    · obtain ⟨T'', r, h3, h4⟩ := ih T a k T' b k' h1 h2 hlt
      exact ⟨T'', r, h3, List.mem_append_left _ h4⟩
    · simp at h2; have := ht _ h1; simp at this; omega
    · simp at h1; obtain ⟨rfl, -⟩ := h1
      obtain ⟨kk, hkk⟩ := firstInv_of_mem (mem_acts.2 ⟨T', h2⟩)
      have hr := halt b (by rw [hkk]; simp)
      obtain ⟨r, hr'⟩ : ∃ r, firstResp (acts t) b = some r := by
        cases h : firstResp (acts t) b with
        | none => exact absurd h hr
        | some r => exact ⟨r, rfl⟩
      obtain ⟨T'', hT''⟩ := mem_acts.1 (firstResp_some hr')
      exact ⟨T'', r, ht _ hT'', List.mem_append_left _ hT''⟩
    · simp at h1 h2; omega
  | resp _ _ ih | send _ ih =>
    intro T a k T' b k' h1 h2 hlt
    rcases List.mem_append.1 h1 with h1 | h1
    · rcases List.mem_append.1 h2 with h2 | h2
      · obtain ⟨T'', r, h3, h4⟩ := ih T a k T' b k' h1 h2 hlt
        exact ⟨T'', r, h3, List.mem_append_left _ h4⟩
      · simp at h2
    · simp at h1
  | stut _ _ ih => exact ih

/-! ## The translated system -/

def emitted {D : Type} (L : List (LEv regSpec D n)) : List RMap :=
  L.filterMap (fun e => match e with | .out _ o => some o | _ => none)

theorem emitted_snoc {D : Type} (L : List (LEv regSpec D n)) (e : LEv regSpec D n) :
    emitted (L ++ [e]) = emitted L ++ (match e with | .out _ o => [o] | _ => []) := by
  cases e <;> simp [emitted]

/-- Along a corresponding history, the participant's state has current input
the node's view and the residual table of its emitted maps, each of which is
contained in the node's response map. -/
theorem corr_state {p : Nat} {t : List (Nat × Act N M)} {L : PL N M n} (h : Corr p t L) :
    ∀ σ, LRun (canon regSpec emptyH) L σ → σ.cur = viewOf p (acts t) ∧
      Residual σ (emitted L) ∧ ∀ e ∈ emitted L, e ≼ rmap (acts t) := by
  induction h with
  | nil =>
    intro σ hσ; cases hσ
    exact ⟨(viewOf_nil p).symm, residual_canon _ _, by simp [emitted]⟩
  | @inv t L a k _ _ _ ih =>
    intro σ hσ
    obtain ⟨σ1, h1, h2⟩ := lrun_append.1 hσ
    obtain ⟨hc, hres, hle⟩ := ih σ1 h1
    cases h2 with
    | inp hs hr =>
      cases hr
      have hR : rmap (acts (t ++ [(L.length, Act.inv a k)])) = rmap (acts t) := by
        rw [acts_snoc]; exact rmap_append_noresp (noresp_single_inv _ _)
      refine ⟨by rw [(step_input_inv hs).2.1, acts_snoc], ?_, ?_⟩
      · have := residual_step hres hs; simpa [emitted_snoc, outs] using this
      · rw [hR, emitted_snoc]; simpa using hle
  | @resp t L a r γ _ hγ ih =>
    intro σ hσ
    obtain ⟨σ1, h1, h2⟩ := lrun_append.1 hσ
    obtain ⟨hc, hres, hle⟩ := ih σ1 h1
    cases h2 with
    | out ha hs _ hr =>
      cases hr
      have hst := kc_effect hγ ha hs
      refine ⟨?_, ?_, ?_⟩
      · rw [(step_output_inv hst).2.1, hc, acts_snoc,
          viewOf_append_noinv p (noinv_single_resp _ _)]
      · have := residual_step hres hst; simpa [emitted_snoc, outs] using this
      · rw [emitted_snoc, acts_snoc]
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact PO.trans (hle e he) (rmap_mono _ _)
        · simp at he; subst he; exact PO.refl _
  | @send t L d m _ ih =>
    intro σ hσ
    obtain ⟨σ1, h1, h2⟩ := lrun_append.1 hσ
    obtain ⟨hc, hres, hle⟩ := ih σ1 h1
    cases h2 with
    | send hr =>
      cases hr
      have hR : rmap (acts (t ++ [(L.length, Act.send d m)])) = rmap (acts t) := by
        rw [acts_snoc]; exact rmap_append_noresp (noresp_single_send _ _)
      refine ⟨by rw [hc, acts_snoc, viewOf_append_noinv p (noinv_single_send _ _)], ?_, ?_⟩
      · simpa [emitted_snoc] using hres
      · rw [hR, emitted_snoc]; simpa using hle
  | @stut t L γ _ hγ ih =>
    intro σ hσ
    obtain ⟨σ1, h1, h2⟩ := lrun_append.1 hσ
    obtain ⟨hc, hres, hle⟩ := ih σ1 h1
    cases h2 with
    | out ha hs _ hr =>
      cases hr
      have hst := kc_effect hγ ha hs
      refine ⟨by rw [(step_output_inv hst).2.1, hc], ?_, ?_⟩
      · have := residual_step hres hst; simpa [emitted_snoc, outs] using this
      · rw [emitted_snoc]
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact hle e he
        · simp at he; subst he; exact PO.refl _

/-- The system of an algorithm: participant `p` runs node `p`'s state machine.
It may perform an event exactly when its local history, with that event, is
the translation of a run of node `p` (invocations ↦ inputs of the node's view,
responses ↦ output events of the node's response map, sends ↦ sends); the
basis is the canonical commitments. -/
noncomputable def sysOf (A : Alg N M) : System regSpec (Fin N × M) where
  basis := fun c => ∃ u, c = kc u
  strat := fun n _ p pre e => ∃ hp : p.val < N, ∃ t, Corr (n := n) p.val t (pre ++ [e]) ∧
    ∃ s, NRun A ⟨p.val, hp⟩ (A.start ⟨p.val, hp⟩) (acts t) s

/-- Client discipline for a participant history: the initial input is `∅`
and each input event adds one fresh operation invoked at the participant. -/
def ClientLocal {D : Type} (p : Nat) (L : List (LEv regSpec D n)) : Prop :=
  ∀ a e b, L = a ++ e :: b → ∀ j, e = .inp j →
    (∃ x op, op.rep = p ∧ (lastInp a).ops x = none ∧ j = addOp (lastInp a) x op) ∧
    ∀ y op, (lastInp a).ops y = some op → ∃ γ o, LEv.out γ o ∈ a ∧ o.f y ≠ none

theorem clientLocal_snoc {D : Type} {p : Nat} {L : List (LEv regSpec D n)} {e : LEv regSpec D n}
    (h : ClientLocal p (L ++ [e])) : ClientLocal p L ∧ ∀ j, e = .inp j →
      (∃ x op, op.rep = p ∧ (lastInp L).ops x = none ∧ j = addOp (lastInp L) x op) ∧
      ∀ y op, (lastInp L).ops y = some op → ∃ γ o, LEv.out γ o ∈ L ∧ o.f y ≠ none :=
  ⟨fun a e' b hab => h a e' (b ++ [e]) (by rw [hab]; simp), h L e [] rfl⟩

theorem compliant_snoc {E : Type} {A : List E → E → Prop} {l : List E} {e : E}
    (h : Compliant A (l ++ [e])) : Compliant A l ∧ A l e :=
  ⟨fun a e' b hab => h a e' (b ++ [e]) (by rw [hab]; simp), h l e [] rfl⟩

/-- A client history produced by the system of an algorithm is the
translation of a run of the node. -/
theorem corr_of_produced (A : Alg N M) {init : Fin n → Hist} {p : Fin n} (hp : p.val < N) :
    ∀ L : PL N M n, Compliant (Allowed (sysOf A) n init p) L → ClientLocal p.val L →
      ∃ t, Corr p.val t L ∧ ∃ s, NRun A ⟨p.val, hp⟩ (A.start ⟨p.val, hp⟩) (acts t) s := by
  refine snoc_induction ?_ ?_
  · intro _ _; exact ⟨[], .nil, _, .nil _⟩
  · intro L e ih hc hcl
    obtain ⟨hc1, hA⟩ := compliant_snoc hc
    obtain ⟨hcl1, hinp⟩ := clientLocal_snoc hcl
    cases e with
    | inp j =>
      obtain ⟨t, hct, s, hs⟩ := ih hc1 hcl1
      obtain ⟨⟨x, op, hrep, hx, rfl⟩, hans⟩ := hinp j rfl
      rw [corr_lastInp hct] at hx hans ⊢
      have halt : ∀ b, firstInv (acts t) b ≠ none → firstResp (acts t) b ≠ none := by
        intro b hb
        obtain ⟨kk, hkk⟩ : ∃ kk, firstInv (acts t) b = some kk := by
          cases h : firstInv (acts t) b with
          | none => exact absurd h hb
          | some kk => exact ⟨kk, rfl⟩
        obtain ⟨γ, o, hm, ho⟩ := hans b ⟨p.val, kk⟩ (by simp [viewOf, hkk])
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hm
        obtain ⟨r, hr⟩ : ∃ r, o.f b = some r := by
          cases h : o.f b with
          | none => exact absurd h ho
          | some r => exact ⟨r, rfl⟩
        obtain ⟨k', _, hm'⟩ := corr_out_ev hct k γ o b r hk hr
        obtain ⟨r', hr'⟩ := firstResp_of_mem (mem_acts.2 ⟨k', hm'⟩)
        rw [hr']; simp
      have hf : firstInv (acts t) x = none := by
        simp only [viewOf] at hx
        cases h : firstInv (acts t) x with
        | none => rfl
        | some _ => rw [h] at hx; cases hx
      obtain ⟨s', hs'⟩ := A.inv_enabled ⟨p.val, hp⟩ s x op.kind
      have hop : op = ⟨p.val, op.kind⟩ := by cases op; simp at hrep; subst hrep; rfl
      refine ⟨t ++ [(L.length, .inv x op.kind)], ?_, s', ?_⟩
      · have := Corr.inv (k := op.kind) hct hf halt
        rwa [viewOf_snoc_inv _ _ _ _ hf, ← hop] at this
      · rw [acts_snoc]; exact nrun_append.2 ⟨s, hs, .cons hs' (.nil _)⟩
    | out γ o => dsimp only [Allowed, sysOf] at hA; obtain ⟨_, _, t, h1, h2⟩ := hA; exact ⟨t, h1, h2⟩
    | send j d => dsimp only [Allowed, sysOf] at hA; obtain ⟨_, t, h1, h2⟩ := hA; exact ⟨t, h1, h2⟩
    | recv q k j d => dsimp only [Allowed, sysOf] at hA; obtain ⟨_, t, h1, h2⟩ := hA; exact ⟨t, h1, h2⟩


/-! ## Indistinguishability: a lone node's responses are explained by its view -/

/-- The execution in which only node `i` takes steps. -/
def single (i : Fin N) (t : List (Nat × Act N M)) : GExec N M := ⟨fun j => if j = i then t else []⟩

theorem mem_single {i j : Fin N} {t : List (Nat × Act N M)} {x : Nat × Act N M}
    (h : x ∈ (single i t).tr j) : j = i ∧ x ∈ t := by
  simp only [single] at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem single_tr (i : Fin N) (t : List (Nat × Act N M)) : (single i t).tr i = t := by
  simp [single]

theorem pairwise_eq {t : List (Nat × Act N M)} (h : t.Pairwise (fun x y => x.1 < y.1)) :
    ∀ x ∈ t, ∀ y ∈ t, x.1 = y.1 → x = y := by
  induction h with
  | nil => simp
  | @cons z l hz _ ih =>
    intro x hx y hy he
    rcases List.mem_cons.1 hx with hx' | hx' <;> rcases List.mem_cons.1 hy with hy' | hy'
    · rw [hx', hy']
    · subst hx'; have := hz y hy'; omega
    · subst hy'; have := hz x hx'; omega
    · exact ih x hx' y hy' he

theorem single_exec {A : Alg N M} {i : Fin N} {t : List (Nat × Act N M)}
    (hrun : ∃ s, NRun A i (A.start i) (acts t) s) (hpw : t.Pairwise (fun x y => x.1 < y.1))
    (hnr : ∀ x ∈ t, ∀ s m, x.2 ≠ Act.recv s m) : IsGExec A (single i t) := by
  refine ⟨?_, ?_, ?_, ⟨id, ?_⟩⟩
  · intro j
    by_cases hj : j = i
    · subst hj; rw [single_tr]; exact hrun
    · exact ⟨_, by simp only [single, hj, ite_false]; exact .nil _⟩
  · intro j
    by_cases hj : j = i
    · subst hj; rw [single_tr]; exact hpw
    · simp [single, hj]
  · intro j j' x y hx hy he
    obtain ⟨h1, hx'⟩ := mem_single hx
    obtain ⟨h2, hy'⟩ := mem_single hy
    exact ⟨h1.trans h2.symm, pairwise_eq hpw x hx' y hy' he⟩
  · intro j T src m hm
    obtain ⟨_, hm⟩ := mem_single hm
    exact absurd rfl (hnr _ hm src m)

theorem single_clientWF {i : Fin N} {t : List (Nat × Act N M)}
    (hf : ∀ x ∈ t, ∀ y ∈ t, ∀ a k k', x.2 = Act.inv a k → y.2 = Act.inv a k' → x = y)
    (halt : ∀ T a k T' b k', (T, Act.inv a k) ∈ t → (T', Act.inv b k') ∈ t → T' < T →
      ∃ T'' r, T'' < T ∧ (T'', Act.resp b r) ∈ t) :
    ClientWF (single i t) := by
  constructor
  · intro j j' x y a k k' hx hy hxa hya
    obtain ⟨_, hx⟩ := mem_single hx
    obtain ⟨_, hy⟩ := mem_single hy
    rw [hf x hx y hy a k k' hxa hya]
  · intro j T a k T' b k' h1 h2 hlt
    obtain ⟨hj, h1'⟩ := mem_single h1
    obtain ⟨_, h2'⟩ := mem_single h2
    subst hj
    obtain ⟨T'', r, h3, h4⟩ := halt T a k T' b k' h1' h2' hlt
    exact ⟨T'', r, h3, by rw [single_tr]; exact h4⟩

/-- **Item 1 of the correspondence.**  If the algorithm is atomic, the response
map of a run of node `i` alone (no other node takes a step; nothing is
received) lies in the register fiber at the node's view.  Since a node's
behaviour depends only on its own run, this holds for every execution in which
the node is alone in its component of a partition. -/
theorem atomic_view {A : Alg N M} (hat : Atomic A) {i : Fin N} {t : List (Nat × Act N M)}
    (hrun : ∃ s, NRun A i (A.start i) (acts t) s) (hpw : t.Pairwise (fun x y => x.1 < y.1))
    (hnr : ∀ x ∈ t, ∀ s m, x.2 ≠ Act.recv s m)
    (hf : ∀ x ∈ t, ∀ y ∈ t, ∀ a k k', x.2 = Act.inv a k → y.2 = Act.inv a k' → x = y)
    (halt : ∀ T a k T' b k', (T, Act.inv a k) ∈ t → (T', Act.inv b k') ∈ t → T' < T →
      ∃ T'' r, T'' < T ∧ (T'', Act.resp b r) ∈ t) :
    regS (viewOf i.val (acts t)) (rmap (acts t)) := by
  have hE := hat _ (single_exec hrun hpw hnr) (single_clientWF hf halt)
  apply lin_to_regS hE
  · intro a op h
    simp only [viewOf] at h
    cases hk : firstInv (acts t) a with
    | none => rw [hk] at h; cases h
    | some kk =>
      rw [hk] at h; cases h
      obtain ⟨T, hT⟩ := mem_acts.1 (firstInv_some hk)
      exact ⟨i, T, by rw [single_tr]; exact hT⟩
  · intro j T a kd hm0
    obtain ⟨hji, hm⟩ := mem_single hm0
    subst hji
    obtain ⟨kk, hk⟩ := firstInv_of_mem (mem_acts.2 ⟨T, hm⟩)
    obtain ⟨T', hT'⟩ := mem_acts.1 (firstInv_some hk)
    have := hf (T, Act.inv a kd) hm (T', Act.inv a kk) hT' a kd kk rfl rfl
    cases this
    show (firstInv (acts t) a).map _ = _
    rw [hk]; rfl
  · intro a b h; exact h.elim
  · intro a r h
    obtain ⟨T, hT⟩ := mem_acts.1 (firstResp_some h)
    exact ⟨i, T, by rw [single_tr]; exact hT⟩

theorem corr_regS {A : Alg N M} (hat : Atomic A) {p : Nat} (hp : p < N)
    {t : List (Nat × Act N M)} {L : PL N M n} (hc : Corr p t L)
    (hrun : ∃ s, NRun A ⟨p, hp⟩ (A.start ⟨p, hp⟩) (acts t) s) :
    regS (viewOf p (acts t)) (rmap (acts t)) :=
  atomic_view (i := ⟨p, hp⟩) hat hrun (corr_times hc).2 (corr_norecv hc) (corr_fresh hc)
    (corr_alt hc)

/-! ## Answering for the translated system -/

theorem nrun_prefix {A : Alg N M} {i : Fin N} {s : A.St} {l1 l2 : List (Act N M)}
    (h : ∃ s', NRun A i s (l1 ++ l2) s') : ∃ s', NRun A i s l1 s' := by
  obtain ⟨s', h⟩ := h
  obtain ⟨s1, h1, _⟩ := nrun_append.1 h
  exact ⟨s1, h1⟩

/-- The output event emitting the current response map is legal. -/
theorem emit_legal {A : Alg N M} (hat : Atomic A) {p : Nat} (hp : p < N)
    {t : List (Nat × Act N M)} {L : PL N M n} (hc : Corr p t L)
    (_hrun : ∃ s, NRun A ⟨p, hp⟩ (A.start ⟨p, hp⟩) (acts t) s)
    {σ : State regSpec} (hσ : LRun (canon regSpec emptyH) L σ) (t' : List (Nat × Act N M))
    (L' : PL N M n) (hc' : Corr p t' L') (hrun' : ∃ s, NRun A ⟨p, hp⟩ (A.start ⟨p, hp⟩) (acts t') s)
    (hv : viewOf p (acts t') = viewOf p (acts t)) (hle : rmap (acts t) ≼ rmap (acts t')) :
    ∃ γ τ, (γ = [] ∨ γ = [kc (rmap (acts t'))]) ∧
      LRun (D := Fin N × M) (n := n) σ [LEv.out γ (rmap (acts t'))] τ := by
  obtain ⟨hcur, hres, hem⟩ := corr_state hc σ hσ
  have hS := corr_regS hat hp hc' hrun'
  have hR : σ.R σ.cur (rmap (acts t')) := by
    refine (hres _ _).2 ⟨?_, PO.refl _, fun e he => PO.trans (hem e he) hle⟩
    rw [hcur, ← hv]; exact hS
  obtain ⟨γ, σc, hγ, ha, hcu, hexp⟩ := kc_legal hR
  let τ : State regSpec :=
    { cur := σc.cur, R := outputTable σc (rmap (acts t')), sub := fun k x h => σc.sub k x h.1,
      hasCur := ⟨_, hcu, PO.refl _⟩, above := fun k x h => σc.above k x h.1 }
  exact ⟨γ, τ, hγ, .out ha (Step.output σc τ _ hcu rfl rfl) hexp (.nil τ)⟩

/-- Run the node's locally controlled actions `bs` (no invocation, nothing
received) on top of a corresponding history: the translated events are legal
and allowed by the system. -/
theorem extend_corr (A : Alg N M) (hat : Atomic A) {init : Fin n → Hist} {p : Fin n}
    (hp : p.val < N) : ∀ (bs : List (Act N M)) (t : List (Nat × Act N M)) (L : PL N M n)
    (σ : State regSpec), Corr p.val t L → LRun (canon regSpec emptyH) L σ →
    Compliant (Allowed (sysOf A) n init p) L →
    (∃ s, NRun A ⟨p.val, hp⟩ (A.start ⟨p.val, hp⟩) (acts t ++ bs) s) → NoInv bs →
    (∀ s m, Act.recv s m ∉ bs) →
    ∃ t' ext σ', Corr p.val t' (L ++ ext) ∧ acts t' = acts t ++ bs ∧ LRun σ ext σ' ∧
      Compliant (Allowed (sysOf A) n init p) (L ++ ext) ∧
      (∀ j, LEv.inp j ∉ ext) ∧ (∀ q k j d, LEv.recv q k j d ∉ ext)
  | [], t, L, σ, hc, hσ, hcomp, _, _, _ =>
    ⟨t, [], σ, by simpa using hc, by simp, .nil σ, by simpa using hcomp, by simp, by simp⟩
  | x :: bs, t, L, σ, hc, hσ, hcomp, hrun, hni, hnr => by
    have hrun1 : ∃ s, NRun A ⟨p.val, hp⟩ (A.start ⟨p.val, hp⟩) (acts t ++ [x]) s := by
      apply nrun_prefix (l2 := bs); simpa using hrun
    have hni' : NoInv bs := fun a k h => hni a k (List.mem_cons_of_mem _ h)
    have hnr' : ∀ s m, Act.recv s m ∉ bs := fun s m h => hnr s m (List.mem_cons_of_mem _ h)
    cases x with
    | inv a k => exact absurd (List.mem_cons_self ..) (hni a k)
    | recv s m => exact absurd (List.mem_cons_self ..) (hnr s m)
    | resp a r =>
      let t1 := t ++ [(L.length, Act.resp a r)]
      have ha1 : acts t1 = acts t ++ [Act.resp a r] := acts_snoc _ _
      have hc0 : Corr (n := n) p.val t1 (L ++ [.out [] (rmap (acts t ++ [.resp a r]))]) :=
        Corr.resp hc (Or.inl rfl)
      have hrun1' : ∃ s, NRun A ⟨p.val, hp⟩ (A.start ⟨p.val, hp⟩) (acts t1) s := by
        rw [ha1]; exact hrun1
      obtain ⟨γ, τ, hγ, hτ⟩ := emit_legal hat hp hc (nrun_prefix (l2 := [Act.resp a r]) hrun1) hσ t1 _
        hc0 hrun1' (by rw [ha1, viewOf_append_noinv _ (noinv_single_resp _ _)])
        (by rw [ha1]; exact rmap_mono _ _)
      rw [ha1] at hγ hτ
      have hc1 : Corr (n := n) p.val t1 (L ++ [.out γ (rmap (acts t ++ [.resp a r]))]) :=
        Corr.resp hc hγ
      have hcomp1 : Compliant (Allowed (sysOf A) n init p)
          (L ++ [.out γ (rmap (acts t ++ [.resp a r]))]) := by
        apply compliant_append hcomp
        intro a' e b hab
        cases a' with
        | nil =>
          simp at hab; obtain ⟨rfl, _⟩ := hab
          refine ⟨fun c hc' => ?_, hp, t1, by simpa using hc1, hrun1'⟩
          rcases hγ with rfl | rfl
          · cases hc'
          · simp at hc'; exact ⟨_, hc'⟩
        | cons _ _ => simp at hab
      obtain ⟨t', ext, σ', hc', hacts, hrun', hcomp', hni2, hnr2⟩ :=
        extend_corr A hat hp bs t1 _ τ hc1 (lrun_append.2 ⟨σ, hσ, hτ⟩) hcomp1
          (by rw [ha1]; simpa using hrun) hni' hnr'
      refine ⟨t', _ :: ext, σ', by simpa using hc', by rw [hacts, ha1]; simp, ?_, by simpa using hcomp',
        ?_, ?_⟩
      · cases hτ with
        | out h1 h2 h3 h4 => cases h4; exact .out h1 h2 h3 hrun'
      · intro j hj; rcases List.mem_cons.1 hj with h | h
        · cases h
        · exact hni2 j h
      · intro q k j d hj; rcases List.mem_cons.1 hj with h | h
        · cases h
        · exact hnr2 q k j d h
    | send d m =>
      let t1 := t ++ [(L.length, Act.send d m)]
      have ha1 : acts t1 = acts t ++ [Act.send d m] := acts_snoc _ _
      have hc1 : Corr (n := n) p.val t1 (L ++ [.send none (d, m)]) := Corr.send hc
      have hrun1' : ∃ s, NRun A ⟨p.val, hp⟩ (A.start ⟨p.val, hp⟩) (acts t1) s := by
        rw [ha1]; exact hrun1
      have hcomp1 : Compliant (Allowed (sysOf A) n init p) (L ++ [.send none (d, m)]) := by
        apply compliant_append hcomp
        intro a' e b hab
        cases a' with
        | nil =>
          simp at hab; obtain ⟨rfl, _⟩ := hab
          exact ⟨hp, t1, by simpa using hc1, hrun1'⟩
        | cons _ _ => simp at hab
      obtain ⟨t', ext, σ', hc', hacts, hrun', hcomp', hni2, hnr2⟩ :=
        extend_corr A hat hp bs t1 _ σ hc1 (lrun_append.2 ⟨σ, hσ, .send (.nil σ)⟩) hcomp1
          (by rw [ha1]; simpa using hrun) hni' hnr'
      refine ⟨t', _ :: ext, σ', by simpa using hc', by rw [hacts, ha1]; simp, .send hrun',
        by simpa using hcomp', ?_, ?_⟩
      · intro j hj; rcases List.mem_cons.1 hj with h | h
        · cases h
        · exact hni2 j h
      · intro q k j d hj; rcases List.mem_cons.1 hj with h | h
        · cases h
        · exact hnr2 q k j d h


/-- Repeatedly apply Availability (in the execution where the node is alone)
until every operation of the view is answered. -/
theorem answer_all (A : Alg N M) (hat : Atomic A) (hav : Available A) {init : Fin n → Hist}
    {p : Fin n} (hp : p.val < N) : ∀ (P : List Nat) (t : List (Nat × Act N M)) (L : PL N M n)
    (σ : State regSpec), Corr p.val t L → LRun (canon regSpec emptyH) L σ →
    Compliant (Allowed (sysOf A) n init p) L →
    (∃ s, NRun A ⟨p.val, hp⟩ (A.start ⟨p.val, hp⟩) (acts t) s) →
    (∀ a, (viewOf p.val (acts t)).ops a ≠ none → (rmap (acts t)).f a = none → a ∈ P) →
    ∃ t' ext σ', Corr p.val t' (L ++ ext) ∧ LRun σ ext σ' ∧
      Compliant (Allowed (sysOf A) n init p) (L ++ ext) ∧
      (∃ s, NRun A ⟨p.val, hp⟩ (A.start ⟨p.val, hp⟩) (acts t') s) ∧
      viewOf p.val (acts t') = viewOf p.val (acts t) ∧
      (∀ a, (viewOf p.val (acts t)).ops a ≠ none → (rmap (acts t')).f a ≠ none) ∧
      (∀ j, LEv.inp j ∉ ext) ∧ (∀ q k j d, LEv.recv q k j d ∉ ext)
  | [], t, L, σ, hc, hσ, hcomp, hrun, hP =>
    ⟨t, [], σ, by simpa using hc, .nil σ, by simpa using hcomp, hrun, rfl,
      fun a ha h => by have := hP a ha (by simpa using h); simp at this, by simp, by simp⟩
  | a :: P, t, L, σ, hc, hσ, hcomp, hrun, hP => by
    by_cases hpend : (viewOf p.val (acts t)).ops a ≠ none ∧ (rmap (acts t)).f a = none
    · let i : Fin N := ⟨p.val, hp⟩
      obtain ⟨kd, hkd⟩ : ∃ kd, firstInv (acts t) a = some kd := by
        cases h : firstInv (acts t) a with
        | none => exact absurd (by simp [viewOf, h]) hpend.1
        | some kd => exact ⟨kd, rfl⟩
      obtain ⟨T, hT⟩ := mem_acts.1 (firstInv_some hkd)
      have hnoresp : ∀ T' r, (T', Act.resp a r) ∉ (single i t).tr i := by
        intro T' r hm
        rw [single_tr] at hm
        exact firstResp_none hpend.2 r (mem_acts.2 ⟨T', hm⟩)
      obtain ⟨E', hE', hext, T', r, hresp⟩ :=
        hav _ (single_exec hrun (corr_times hc).2 (corr_norecv hc))
          (single_clientWF (corr_fresh hc) (corr_alt hc)) i T a kd (by rw [single_tr]; exact hT) hnoresp
      obtain ⟨β, hβ, hβp⟩ := hext i
      rw [single_tr] at hβ
      have hrunβ : ∃ s, NRun A i (A.start i) (acts t ++ acts β) s := by
        have := hE'.1 i; rw [hβ] at this; simpa [acts] using this
      have hni : NoInv (acts β) := by
        intro a' k hm; obtain ⟨T0, hT0⟩ := mem_acts.1 hm
        exact (hβp _ hT0).2.1 a' k rfl
      have hnr : ∀ s m, Act.recv s m ∉ acts β := by
        intro s m hm; obtain ⟨T0, hT0⟩ := mem_acts.1 hm
        exact (hβp _ hT0).2.2 s m rfl
      obtain ⟨t1, ext1, σ1, hc1, hacts1, hl1, hcomp1, hni1, hnr1⟩ :=
        extend_corr A hat hp (acts β) t L σ hc hσ hcomp hrunβ hni hnr
      have hrun1 : ∃ s, NRun A i (A.start i) (acts t1) s := by rw [hacts1]; exact hrunβ
      have hv1 : viewOf p.val (acts t1) = viewOf p.val (acts t) := by
        rw [hacts1]; exact viewOf_append_noinv _ hni
      have hle1 : rmap (acts t) ≼ rmap (acts t1) := by rw [hacts1]; exact rmap_mono _ _
      have hans : (rmap (acts t1)).f a ≠ none := by
        have hm : Act.resp a r ∈ acts t1 := by
          have : acts t ++ acts β = acts (t ++ β) := by simp [acts]
          rw [hacts1, this]
          rw [hβ] at hresp
          exact mem_acts.2 ⟨T', hresp⟩
        obtain ⟨r', hr'⟩ := firstResp_of_mem hm
        show firstResp (acts t1) a ≠ none
        rw [hr']; simp
      obtain ⟨t2, ext2, σ2, hc2, hl2, hcomp2, hrun2, hv2, hans2, hni2, hnr2⟩ :=
        answer_all A hat hav hp P t1 (L ++ ext1) σ1 hc1 (lrun_append.2 ⟨σ, hσ, hl1⟩) hcomp1 hrun1
          (by
            intro b hb hbn
            rw [hv1] at hb
            have hb0 : (rmap (acts t)).f b = none := by
              cases h : (rmap (acts t)).f b with
              | none => rfl
              | some x => rw [hle1 b x h] at hbn; cases hbn
            rcases List.mem_cons.1 (hP b hb hb0) with rfl | h
            · exact absurd hbn hans
            · exact h)
      refine ⟨t2, ext1 ++ ext2, σ2, by simpa using hc2, lrun_append.2 ⟨σ1, hl1, hl2⟩,
        by simpa using hcomp2, hrun2, by rw [hv2, hv1], ?_, ?_, ?_⟩
      · intro b hb; rw [← hv1] at hb; exact hans2 b hb
      · intro j hj; rcases List.mem_append.1 hj with h | h
        · exact hni1 j h
        · exact hni2 j h
      · intro q k j d hj; rcases List.mem_append.1 hj with h | h
        · exact hnr1 q k j d h
        · exact hnr2 q k j d h
    · exact answer_all A hat hav hp P t L σ hc hσ hcomp hrun (by
        intro b hb hbn
        rcases List.mem_cons.1 (hP b hb hbn) with rfl | h
        · exact absurd ⟨hb, hbn⟩ hpend
        · exact h)

/-! ## The client form of Corollary `cor:gilbert-lynch` -/

def init0 : Fin 2 → Hist := fun _ => emptyH

/-- Client histories: every participant starts from `∅` and each input event
adds one fresh operation invoked at that participant. -/
def ClientH {D : Type} (H : RHist D 2) : Prop := ∀ p, ClientLocal p.val (H p)

/-- Answering (Def. `def:response-availability`(1)) for client histories of
two participants. -/
def AnsweringC {D : Type} (Sys : System regSpec D) : Prop :=
  ∀ (H : RHist D 2) (comp : Fin 2 → Nat), WF init0 H → Produced Sys 2 init0 H →
    Partitioned H comp → ClientH H →
    ∀ c, IsCut H c → ∀ (p : Fin 2) (σ : State regSpec),
      LRun (canon regSpec (init0 p)) ((H p).take (c p)) σ →
      ∃ (H' : RHist D 2) (ext : Fin 2 → List (LEv regSpec D 2)),
        Extends H c H' ext ∧ WF init0 H' ∧ Produced Sys 2 init0 H' ∧ Partitioned H' comp ∧
        (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ j, LEv.inp j ∉ ext p) ∧
        ∃ γ o, regQ p.val σ.cur o ∧ LEv.out γ o ∈ ext p

/-- Response Partition Consistency at realized histories
(`CC.GL.RealizedRPC`) for client histories of two participants. -/
def RealizedRPCC {D : Type} (Sys : System regSpec D) : Prop :=
  ∀ (H : RHist D 2) (comp : Fin 2 → Nat), WF init0 H → Produced Sys 2 init0 H →
    Partitioned H comp → ClientH H →
    ∀ pos, Interleaving H pos → ∀ m c, PrefixCut H pos m c →
    ∀ j, Realized H pos m j →
    (∀ p σ, LRun (canon regSpec (init0 p)) ((H p).take (c p)) σ → σ.cur ≼ j) →
    RPCAt H c j

theorem clientLocal_take {D : Type} {p : Nat} {L : List (LEv regSpec D n)} (h : ClientLocal p L)
    (c : Nat) : ClientLocal p (L.take c) := by
  intro a e b hab
  apply h a e (b ++ L.drop c)
  conv => lhs; rw [← List.take_append_drop c L]
  rw [hab]; simp

/-- **Availability and atomicity give Answering** for the translated system. -/
theorem sys_answering (hN : 2 ≤ N) (A : Alg N M) (hat : Atomic A) (hav : Available A) :
    AnsweringC (sysOf A) := by
  classical
  intro H comp hwf hprod hpart hcl c hcut p σ hσ
  have hp : p.val < N := by have := p.isLt; omega
  let L := (H p).take (c p)
  have hcompL : Compliant (Allowed (sysOf A) 2 init0 p) L := compliant_take (hprod p) (c p)
  obtain ⟨t, hc, hrun⟩ := corr_of_produced A hp L hcompL (clientLocal_take (hcl p) (c p))
  have hσ' : LRun (canon regSpec emptyH) L σ := hσ
  obtain ⟨B, hB⟩ := firstInv_bound (acts t)
  obtain ⟨t1, ext1, σ1, hc1, hl1, hcomp1, hrun1, hv1, hans1, hni1, hnr1⟩ :=
    answer_all A hat hav hp (List.range B) t L σ hc hσ' hcompL hrun (by
      intro a ha _
      refine List.mem_range.2 (Nat.lt_of_not_le fun hle => ha ?_)
      simp [viewOf, hB a hle])
  have hl1' : LRun (canon regSpec emptyH) (L ++ ext1) σ1 := lrun_append.2 ⟨σ, hσ', hl1⟩
  obtain ⟨γ, τ, hγ, hτ⟩ := emit_legal hat hp hc1 hrun1 hl1' t1 _
    (Corr.stut (n := 2) hc1 (Or.inl rfl)) hrun1 rfl (PO.refl _)
  let o := rmap (acts t1)
  have hc2 : Corr p.val t1 ((L ++ ext1) ++ [LEv.out γ o]) := Corr.stut hc1 hγ
  let ext : Fin 2 → List (LEv regSpec (Fin N × M) 2) :=
    fun q => if q = p then ext1 ++ [LEv.out γ o] else []
  have hep : ext p = ext1 ++ [LEv.out γ o] := by simp [ext]
  have heq : ∀ q, q ≠ p → ext q = [] := fun q h => by simp [ext, h]
  have hnr' : ∀ p' q k j d, LEv.recv q k j d ∉ ext p' := by
    intro p' q k j d hm
    by_cases h : p' = p
    · subst h; rw [hep] at hm
      rcases List.mem_append.1 hm with hm | hm
      · exact hnr1 q k j d hm
      · simp at hm
    · rw [heq p' h] at hm; cases hm
  have hext : Extends H c (fun q => (H q).take (c q) ++ ext q) ext := fun _ => rfl
  obtain ⟨hcur, _, _⟩ := corr_state hc σ hσ'
  refine ⟨_, ext, hext, ⟨?_, recvMatched_extend hwf.2 hcut hext hnr'⟩, ?_,
    partitioned_extend hpart hext hnr', fun q hq => heq q (fun h => hq (h ▸ rfl)), ?_,
    γ, o, ⟨?_, ?_⟩, by rw [hep]; simp⟩
  · intro q
    by_cases hqp : q = p
    · subst hqp
      refine ⟨τ, ?_⟩
      show LRun _ (L ++ ext q) τ
      rw [hep, ← List.append_assoc]
      exact lrun_append.2 ⟨σ1, hl1', hτ⟩
    · obtain ⟨τq, hq'⟩ := hwf.1 q
      obtain ⟨σq, hσq⟩ := lrun_take hq' (c q)
      refine ⟨σq, ?_⟩
      show LRun _ ((H q).take (c q) ++ ext q) σq
      rw [heq q hqp, List.append_nil]; exact hσq
  · intro q
    by_cases hqp : q = p
    · subst hqp
      show Compliant _ (L ++ ext q)
      rw [hep, ← List.append_assoc]
      apply compliant_append hcomp1
      intro a e b hab
      cases a with
      | nil =>
        simp at hab; obtain ⟨rfl, _⟩ := hab
        refine ⟨fun c' hc' => ?_, hp, t1, by simpa using hc2, hrun1⟩
        rcases hγ with rfl | rfl
        · cases hc'
        · simp at hc'; exact ⟨_, hc'⟩
      | cons _ _ => simp at hab
    · show Compliant _ ((H q).take (c q) ++ ext q)
      rw [heq q hqp, List.append_nil]; exact compliant_take (hprod q) (c q)
  · intro j hj
    rw [hep] at hj
    rcases List.mem_append.1 hj with h | h
    · exact hni1 j h
    · simp at h
  · rw [hcur, ← hv1]; exact corr_regS hat hp hc1 hrun1
  · intro a op ha _
    rw [hcur] at ha
    exact hans1 a (by rw [ha]; simp)


/-! ## Atomicity gives Response Partition Consistency at the realized history -/

/-- **Item 3 of the correspondence.**  For the translated system, every
prefix of every interleaving of a client history has Response Partition
Consistency at its realized history: the interleaving is an execution of the
algorithm, its realized history records exactly its invocations and real-time
precedence, and atomicity of that execution explains all emitted maps by one
linearization. -/
theorem sys_rpc (hN : 2 ≤ N) (A : Alg N M) (hat : Atomic A) : RealizedRPCC (sysOf A) := by
  classical
  intro H comp _ hprod _ hcl pos hil m c hpc j hreal _
  have hp : ∀ p : Fin 2, p.val < N := fun p => by have := p.isLt; omega
  let nd : Fin 2 → Fin N := fun p => ⟨p.val, hp p⟩
  have hT : ∀ p : Fin 2, ∃ t, Corr p.val t ((H p).take (c p)) ∧
      ∃ s, NRun A (nd p) (A.start (nd p)) (acts t) s := fun p =>
    corr_of_produced A (hp p) _ (compliant_take (hprod p) (c p)) (clientLocal_take (hcl p) (c p))
  obtain ⟨T, hT⟩ := Classical.axiomOfChoice hT
  let rt : Fin 2 → Nat × Act N M → Nat × Act N M := fun p x => (pos p x.1, x.2)
  let E : GExec N M := ⟨fun i => if h : i.val < 2 then (T ⟨i.val, h⟩).map (rt ⟨i.val, h⟩) else []⟩
  have hEnd : ∀ p, E.tr (nd p) = (T p).map (rt p) := by
    intro p; simp only [E, nd, p.isLt, dite_true]
  have memE : ∀ i y, y ∈ E.tr i → ∃ p, i = nd p ∧ ∃ x ∈ T p, y = rt p x := by
    intro i y hy
    simp only [E] at hy
    split at hy
    · rename_i h
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact ⟨⟨i.val, h⟩, rfl, x, hx, rfl⟩
    · cases hy
  have memE' : ∀ p x, x ∈ T p → rt p x ∈ E.tr (nd p) := by
    intro p x hx; rw [hEnd]; exact List.mem_map_of_mem hx
  have hlen : ∀ p x, x ∈ T p → x.1 < c p ∧ x.1 < (H p).length := by
    intro p x hx
    have := (corr_times (hT p).1).1 x hx
    rw [List.length_take] at this
    constructor <;> omega
  have hcut : ∀ (p : Fin 2) k, k < (H p).length → (k < c p ↔ pos p k < m) := fun p k hk =>
    (hpc p).2 k hk
  have htake : ∀ (p : Fin 2) k, k < c p → ((H p).take (c p))[k]? = (H p)[k]? :=
    fun p k hk => List.getElem?_take_of_lt hk
  have hklen : ∀ (p : Fin 2) k (e : LEv regSpec (Fin N × M) 2), (H p)[k]? = some e →
      k < (H p).length := fun p k e h => (List.getElem?_eq_some_iff.1 h).1
  -- traced invocations are invocations of the realized history
  have hinvJ : ∀ i Tm a kd, (Tm, Act.inv a kd) ∈ E.tr i → j.ops a = some ⟨i.val, kd⟩ := by
    intro i Tm a kd hm
    obtain ⟨p, rfl, x, hx, he⟩ := memE i _ hm
    obtain ⟨x1, x2⟩ := x
    simp only [rt, Prod.mk.injEq] at he
    obtain ⟨_, rfl⟩ := he
    obtain ⟨hc1, hc2⟩ := hlen p _ hx
    obtain ⟨j', hj', hja⟩ := corr_inv_ev (hT p).1 x1 a kd hx
    rw [htake p x1 hc1] at hj'
    exact ((hreal.1 a _).2 ⟨p, x1, (hcut p x1 hc2).1 hc1, rfl, j', hj', hja⟩)
  have hpos_le : ∀ (p : Fin 2) k k', k ≤ k' → k' < (H p).length → pos p k ≤ pos p k' := by
    intro p k k' hle hk'
    rcases Nat.lt_or_eq_of_le hle with h | rfl
    · exact Nat.le_of_lt (hil.2.1 p k k' h hk')
    · exact Nat.le_refl _
  have hex : IsGExec A E := by
    refine ⟨?_, ?_, ?_, ⟨id, ?_⟩⟩
    · intro i
      simp only [E]
      split
      · rename_i h
        have := (hT ⟨i.val, h⟩).2
        simpa [acts, rt, Function.comp_def] using this
      · exact ⟨_, .nil _⟩
    · intro i
      simp only [E]
      split
      · rename_i h
        rw [List.pairwise_map]
        refine List.Pairwise.imp_of_mem ?_ (corr_times (hT ⟨i.val, h⟩).1).2
        intro x y hx _ hxy
        exact hil.2.1 _ _ _ hxy (hlen _ y (by assumption)).2
      · exact List.Pairwise.nil
    · intro i i' y y' hy hy' he
      obtain ⟨p, rfl, x, hx, rfl⟩ := memE i y hy
      obtain ⟨p', rfl, x', hx', rfl⟩ := memE i' y' hy'
      obtain ⟨rfl, hk⟩ := hil.1 p x.1 p' x'.1 (hlen p x hx).2 (hlen p' x' hx').2 he
      exact ⟨rfl, by rw [pairwise_eq (corr_times (hT p).1).2 x hx x' hx' hk]⟩
    · intro i Tm src msg hm
      obtain ⟨p, _, x, hx, he⟩ := memE i _ hm
      have : x.2 = Act.recv src msg := by rw [show x.2 = (rt p x).2 from rfl, ← he]
      exact absurd this (corr_norecv (hT p).1 x hx src msg)
  have hcwf : ClientWF E := by
    constructor
    · intro i i' y y' a k k' hy hy' hya hya'
      have e1 := hinvJ i y.1 a k (by rw [← hya]; exact hy)
      have e2 := hinvJ i' y'.1 a k' (by rw [← hya']; exact hy')
      rw [e1] at e2
      simp only [Option.some.injEq, Op.mk.injEq] at e2
      obtain ⟨hii, rfl⟩ := e2
      obtain ⟨p, rfl, x, hx, rfl⟩ := memE i y hy
      obtain ⟨p', rfl, x', hx', rfl⟩ := memE i' y' hy'
      have : p = p' := Fin.ext hii
      subst this
      rw [corr_fresh (hT p).1 x hx x' hx' a k k hya hya']
    · intro i Tm a k Tm' b k' h1 h2 hlt
      obtain ⟨p, rfl, x, hx, he⟩ := memE _ _ h1
      obtain ⟨p', hpp, x', hx', he'⟩ := memE _ _ h2
      have : p' = p := Fin.ext (congrArg Fin.val hpp).symm
      subst this
      obtain ⟨x1, x2⟩ := x
      obtain ⟨x1', x2'⟩ := x'
      simp only [rt, Prod.mk.injEq] at he he'
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨rfl, rfl⟩ := he'
      have hl1 := (hlen p' _ hx).2
      have hl1' := (hlen p' _ hx').2
      have hx1 : x1' < x1 := Nat.lt_of_not_le fun hle => by
        have := hpos_le p' x1 x1' hle hl1'; omega
      obtain ⟨T'', r, h3, h4⟩ := corr_alt (hT p').1 x1 a k x1' b k' hx hx' hx1
      exact ⟨_, r, hil.2.1 p' T'' x1 h3 hl1, memE' p' _ h4⟩
  have hAt := hat E hex hcwf
  let u : RMap := ⟨fun a => if h : ∃ r, ∃ i Tm, (Tm, Act.resp a r) ∈ E.tr i then
    some (Classical.choose h) else none⟩
  have h4 : ∀ a r, u.f a = some r → ∃ i Tm, (Tm, Act.resp a r) ∈ E.tr i := by
    intro a r h
    simp only [u] at h
    split at h
    · rename_i hh; cases h; exact Classical.choose_spec hh
    · cases h
  refine ⟨u, ?_, ?_⟩
  · apply lin_to_regS hAt j u _ hinvJ _ h4
    · intro a op hja
      obtain ⟨p, k, hpk, hrep, h', hk, hh'⟩ := (hreal.1 a op).1 hja
      have hkl := hklen p k _ hk
      have hkc := (hcut p k hkl).2 hpk
      rw [← htake p k hkc] at hk
      obtain ⟨_, k', _, hm⟩ := corr_inp_ev (hT p).1 k h' a op hk hh'
      exact ⟨nd p, _, memE' p _ hm⟩
    · intro a b hab
      obtain ⟨opa, opb, _, hjb, p, k, ⟨_, γ, ρ, hk, hρ⟩, hall⟩ := (hreal.2 a b).1 hab
      obtain ⟨p', k', hpk', hinv'⟩ := (hreal.1 b opb).1 hjb
      have hlt := hall p' k' hinv'
      have hkl := hklen p k _ hk
      have hkc := (hcut p k hkl).2 (Nat.lt_trans hlt hpk')
      rw [← htake p k hkc] at hk
      obtain ⟨r, hr⟩ : ∃ r, ρ.f a = some r := by
        cases h : ρ.f a with
        | none => exact absurd h hρ
        | some r => exact ⟨r, rfl⟩
      obtain ⟨k1, hk1, hm1⟩ := corr_out_ev (hT p).1 k γ ρ a r hk hr
      obtain ⟨hrep', h', hk', hh'⟩ := hinv'
      have hkl' := hklen p' k' _ hk'
      have hkc' := (hcut p' k' hkl').2 hpk'
      rw [← htake p' k' hkc'] at hk'
      obtain ⟨hrep2, k2, hk2, hm2⟩ := corr_inp_ev (hT p').1 k' h' b opb hk' hh'
      obtain ⟨j2, hj2, hj2b⟩ := corr_inv_ev (hT p').1 k2 b opb.kind hm2
      have hk2c : k2 < c p' := Nat.lt_of_le_of_lt hk2 hkc'
      rw [htake p' k2 hk2c] at hj2
      have hopb : opb = ⟨p'.val, opb.kind⟩ := by cases opb; simp at hrep2; simp [hrep2]
      have hlt2 := hall p' k2 ⟨hrep', j2, hj2, by rw [hj2b, ← hopb]⟩
      refine ⟨nd p, _, r, nd p', _, opb.kind, memE' p _ hm1, memE' p' _ hm2, ?_⟩
      show pos p k1 < pos p' k2
      exact Nat.lt_of_le_of_lt (hpos_le p k1 k hk1 hkl) hlt2
  · intro p γ o ho a r hoa
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ho
    obtain ⟨k1, _, hm1⟩ := corr_out_ev (hT p).1 k γ o a r hk hoa
    have hmem := memE' p _ hm1
    have hex' : ∃ r, ∃ i Tm, (Tm, Act.resp a r) ∈ E.tr i := ⟨r, nd p, _, hmem⟩
    show (if h : ∃ r, ∃ i Tm, (Tm, Act.resp a r) ∈ E.tr i then
      some (Classical.choose h) else none) = some r
    rw [dite_eq_left hex']
    obtain ⟨i', Tm', hm'⟩ := Classical.choose_spec hex'
    have hTm := (hAt.1 _ _ a r hmem).2 i' Tm' _ hm'
    obtain ⟨_, he⟩ := hex.2.2.1 i' (nd p) _ _ hm' hmem hTm
    simp only [rt, Prod.mk.injEq, Act.resp.injEq] at he
    rw [he.2.2]


/-! ## The client form of the corollary (same proof as `CC.GL.gilbert_lynch`) -/

theorem clientLocal_nil {D : Type} {p : Nat} : ClientLocal (n := n) (D := D) p [] := by
  intro a e b h; cases a <;> simp at h

theorem clientLocal_one {D : Type} {p x : Nat} {op : Op} (hrep : op.rep = p)
    {l : List (LEv regSpec D n)} (hl : ∀ j, LEv.inp j ∉ l) :
    ClientLocal p (LEv.inp (addOp emptyH x op) :: l) := by
  intro a e b hab j he
  subst he
  cases a with
  | nil =>
    simp only [List.nil_append, List.cons.injEq, LEv.inp.injEq] at hab
    obtain ⟨rfl, _⟩ := hab
    exact ⟨⟨x, op, hrep, rfl, rfl⟩, fun y op' h => by cases h⟩
  | cons y a =>
    simp only [List.cons_append, List.cons.injEq] at hab
    obtain ⟨_, rfl⟩ := hab
    exact absurd (by simp) (hl j)

theorem h1_eq : h1 = addOp emptyH 0 wOp := rfl
theorem h2_eq : h2 = addOp emptyH 1 rOp := rfl

theorem final_contra_c {D : Type} (Sys : System regSpec D) (hRPC : RealizedRPCC Sys)
    {H : RHist D 2} {comp : Fin 2 → Nat}
    (hwf : WF init0 H) (hprod : Produced Sys 2 init0 H) (hpart : Partitioned H comp)
    (hcl : ClientH H)
    (hinj : ∀ p q, comp p = comp q → p = q)
    {A B : List (LEv regSpec D 2)} (hA : H 0 = LEv.inp h1 :: A) (hB : H 1 = LEv.inp h2 :: B)
    (hAi : ∀ j, LEv.inp j ∉ A) (hBi : ∀ j, LEv.inp j ∉ B)
    {γ γ' : List (Commitment regSpec)} {o o' : RMap}
    (ho : LEv.out γ o ∈ A) (hoQ : regQ 0 h1 o) (ho' : LEv.out γ' o' ∈ B)
    (ho'Q : regQ 1 h2 o') : False := by
  have hnr := norecv_of_inj hwf hpart hinj
  have inp0 : ∀ k h, (H 0)[k]? = some (LEv.inp h) → k = 0 ∧ h = h1 := by
    intro k h hk
    rw [hA] at hk
    obtain ⟨hk0, he⟩ := inp_head (P := fun x => ∃ h, x = LEv.inp h)
      (fun x ⟨h, hx⟩ => hx ▸ hAi h) hk ⟨h, rfl⟩
    cases he; exact ⟨hk0, rfl⟩
  have inp1 : ∀ k h, (H 1)[k]? = some (LEv.inp h) → k = 0 ∧ h = h2 := by
    intro k h hk
    rw [hB] at hk
    obtain ⟨hk0, he⟩ := inp_head (P := fun x => ∃ h, x = LEv.inp h)
      (fun x ⟨h, hx⟩ => hx ▸ hBi h) hk ⟨h, rfl⟩
    cases he; exact ⟨hk0, rfl⟩
  have hL0 : (H 0).length = A.length + 1 := by rw [hA]; rfl
  have hL1 : (H 1).length = B.length + 1 := by rw [hB]; rfl
  let L0 := (H 0).length
  let m := (H 0).length + (H 1).length
  have p0 : ∀ k, pos2 L0 0 k = k := fun k => by simp [pos2]
  have p1 : ∀ k, pos2 L0 1 k = L0 + k := fun k => by simp [pos2]
  have il : Interleaving H (pos2 L0) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p k p' k' hk hk' he
      rcases fin2 p with rfl | rfl <;> rcases fin2 p' with rfl | rfl <;>
        simp only [p0, p1] at he <;> refine ⟨?_, ?_⟩ <;> first | rfl | omega
    · intro p k k' hkk _
      rcases fin2 p with rfl | rfl <;> simp only [p0, p1] <;> omega
    · intro p k q k' j d h
      exact absurd h (hnr p k q k' j d)
  have pc : PrefixCut H (pos2 L0) m (fun p => (H p).length) := by
    intro p
    refine ⟨Nat.le_refl _, fun k hk => ⟨fun _ => ?_, fun _ => hk⟩⟩
    rcases fin2 p with rfl | rfl <;> simp only [p0, p1] <;> omega
  have hr : Realized H (pos2 L0) m hj := by
    constructor
    · intro a op
      constructor
      · intro h
        rcases hj_ops h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨0, 0, by rw [p0]; omega, rfl, h1, by rw [hA]; rfl, rfl⟩
        · exact ⟨1, 0, by rw [p1]; omega, rfl, h2, by rw [hB]; rfl, rfl⟩
      · rintro ⟨p, k, _, _, h, hk, hop⟩
        rcases fin2 p with rfl | rfl
        · obtain ⟨_, rfl⟩ := inp0 k h hk
          obtain ⟨rfl, rfl⟩ := h1_ops hop; rfl
        · obtain ⟨_, rfl⟩ := inp1 k h hk
          obtain ⟨rfl, rfl⟩ := h2_ops hop; rfl
    · intro a b
      constructor
      · rintro ⟨rfl, rfl⟩
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ho
        have hkA := (List.getElem?_eq_some_iff.1 hk).1
        refine ⟨wOp, rOp, rfl, rfl, 0, k + 1,
          ⟨rfl, γ, o, by rw [hA]; simpa using hk, hoQ.2 0 wOp rfl rfl⟩, ?_⟩
        rintro p' k' ⟨hrep, _⟩
        have : p' = 1 := Fin.ext hrep
        subst this
        rw [p0, p1]; omega
      · rintro ⟨opa, opb, ha, hb, p, k, ⟨hrep, _⟩, hall⟩
        rcases hj_ops hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have := hall 0 0 ⟨rfl, h1, by rw [hA]; rfl, rfl⟩
          rw [p0] at this; omega
        · rcases hj_ops ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨rfl, rfl⟩
          · have hp : p = 1 := Fin.ext hrep
            subst hp
            have := hall 1 0 ⟨rfl, h2, by rw [hB]; rfl, rfl⟩
            rw [p1, p1] at this; omega
  have hcur : ∀ p σ, LRun (canon regSpec (init0 p)) ((H p).take (H p).length) σ → σ.cur ≼ hj := by
    intro p σ hσ
    rw [List.take_length] at hσ
    rcases fin2 p with rfl | rfl
    · rw [hA] at hσ
      cases hσ with
      | inp hs hr => rw [lrun_noinp hr hAi, (step_input_inv hs).2.1]; exact h1_le
    · rw [hB] at hσ
      cases hσ with
      | inp hs hr => rw [lrun_noinp hr hBi, (step_input_inv hs).2.1]; exact h2_le
  obtain ⟨u, hu, hall⟩ := hRPC H comp hwf hprod hpart hcl (pos2 L0) il m _ pc hj hr hcur
  have hle := hall 1 γ' o' (by rw [List.take_length, hB]; exact List.mem_cons_of_mem _ ho')
  exact hj_noread u hu (hle 1 _ (h2_answer ho'Q))

/-- **Corollary `cor:gilbert-lynch`, client form.**  No system for the
register has Answering and Response Partition Consistency at realized
histories, even if both are required only for client histories of two
participants.  The proof is the paper's (and `CC.GL.gilbert_lynch`'s): its
histories are client histories. -/
theorem gilbert_lynch_client {D : Type} (Sys : System regSpec D) :
    ¬ (AnsweringC Sys ∧ RealizedRPCC Sys) := by
  rintro ⟨hRA, hRPC⟩
  let init : Fin 2 → Hist := init0
  let comp : Fin 2 → Nat := fun p => p.val
  have hinj : ∀ p q : Fin 2, comp p = comp q → p = q := fun p q h => Fin.ext h
  have h01 : comp 1 ≠ comp 0 := by decide
  have h10 : comp 0 ≠ comp 1 := by decide
  let H0 : RHist D 2 := fun _ => []
  have wf0 : WF init H0 :=
    ⟨fun p => ⟨_, LRun.nil _⟩, fun p a q k j d b h => absurd h nil_ne_app⟩
  have prod0 : Produced Sys 2 init H0 := fun p a e b h => absurd h nil_ne_app
  have part0 : Partitioned H0 comp :=
    ⟨⟨0, 1, by decide⟩, fun p a q k j d b h => absurd h nil_ne_app⟩
  have cut0 : IsCut H0 (fun _ => 0) :=
    ⟨fun _ => Nat.zero_le _, fun p a q k j d b h => absurd h nil_ne_app⟩
  -- the environment invokes the write at `p`
  obtain ⟨u1, hu1⟩ := regSpec.total h1
  have hR1 : (canon regSpec emptyH).R h1 u1 := ⟨hu1, empty_le h1⟩
  obtain ⟨H1, ext1, hext1, wf1, prod1, part1, he10, he1q⟩ :=
    extend_single Sys wf0 prod0 part0 cut0 (p := 0) (σ := canon regSpec emptyH)
      (LRun.nil _) (e := LEv.inp h1) (by intro q k j d h; cases h) (inp_lrun hR1) trivial
  have e10 : H1 0 = [LEv.inp h1] := by rw [hext1 0, he10]; rfl
  have e11 : H1 1 = [] := by rw [hext1 1, he1q 1 (by decide)]; rfl
  -- Answering at `p`: `p` acknowledges the write
  have hτ1 : LRun (canon regSpec (init 0)) ((H1 0).take (H1 0).length)
      (inpState (canon regSpec emptyH) h1 u1 hR1) := by
    rw [List.take_length, e10]; exact inp_lrun hR1
  have cl1 : ClientH H1 := by
    intro p; rcases fin2 p with rfl | rfl
    · rw [e10]; exact clientLocal_one (x := 0) (op := wOp) rfl (by simp)
    · rw [e11]; exact clientLocal_nil
  obtain ⟨H2, ext2, hext2, wf2, prod2, part2, hloc2, hni2, γ, o, hQo, hmo⟩ :=
    hRA H1 comp wf1 prod1 part1 cl1 _ (full_cut wf1) 0 _ hτ1
  have hQo : regQ 0 h1 o := hQo
  have e20 : H2 0 = LEv.inp h1 :: ext2 0 := by
    rw [hext2 0, List.take_length, e10]; rfl
  have e21 : H2 1 = [] := by
    rw [hext2 1, List.take_length, e11, hloc2 1 h01]; rfl
  -- the environment invokes the read at `q`
  obtain ⟨u2, hu2⟩ := regSpec.total h2
  have hR2 : (canon regSpec emptyH).R h2 u2 := ⟨hu2, empty_le h2⟩
  obtain ⟨H3, ext3, hext3, wf3, prod3, part3, he31, he3q⟩ :=
    extend_single Sys wf2 prod2 part2 (full_cut wf2) (p := 1) (σ := canon regSpec emptyH)
      (by rw [List.take_length, e21]; exact LRun.nil _) (e := LEv.inp h2)
      (by intro q k j d h; cases h) (inp_lrun hR2) trivial
  have e30 : H3 0 = LEv.inp h1 :: ext2 0 := by
    rw [hext3 0, List.take_length, e20, he3q 0 (by decide)]; simp
  have e31 : H3 1 = [LEv.inp h2] := by
    rw [hext3 1, List.take_length, e21, he31]; rfl
  -- Answering at `q`: `q` answers the read
  have hτ2 : LRun (canon regSpec (init 1)) ((H3 1).take (H3 1).length)
      (inpState (canon regSpec emptyH) h2 u2 hR2) := by
    rw [List.take_length, e31]; exact inp_lrun hR2
  have cl3 : ClientH H3 := by
    intro p; rcases fin2 p with rfl | rfl
    · rw [e30]; exact clientLocal_one (x := 0) (op := wOp) rfl hni2
    · rw [e31]; exact clientLocal_one (x := 1) (op := rOp) rfl (by simp)
  obtain ⟨H4, ext4, hext4, wf4, prod4, part4, hloc4, hni4, γ', o', hQo', hmo'⟩ :=
    hRA H3 comp wf3 prod3 part3 cl3 _ (full_cut wf3) 1 _ hτ2
  have hQo' : regQ 1 h2 o' := hQo'
  have e40 : H4 0 = LEv.inp h1 :: ext2 0 := by
    rw [hext4 0, List.take_length, e30, hloc4 0 h10]; simp
  have e41 : H4 1 = LEv.inp h2 :: ext4 1 := by
    rw [hext4 1, List.take_length, e31]; rfl
  have cl4 : ClientH H4 := by
    intro p; rcases fin2 p with rfl | rfl
    · rw [e40]; exact clientLocal_one (x := 0) (op := wOp) rfl hni2
    · rw [e41]; exact clientLocal_one (x := 1) (op := rOp) rfl hni4
  exact final_contra_c Sys hRPC wf4 prod4 part4 cl4 hinj e40 e41 hni2 hni4 hmo hQo hmo' hQo'

/-- The paper's hypotheses imply the client-form ones, so `gilbert_lynch_client`
strengthens `CC.GL.gilbert_lynch`. -/
theorem answeringC_of_RA {D : Type} {Sys : System regSpec D}
    (h : ResponseAvailability Sys regQn) : AnsweringC Sys := by
  intro H comp hwf hprod hpart _ c hcut p σ hσ
  exact (h 2 init0 H comp hwf hprod hpart c hcut p σ hσ).1

theorem realizedRPCC_of {D : Type} {Sys : System regSpec D} (h : RealizedRPC Sys) :
    RealizedRPCC Sys := by
  intro H comp hwf hprod hpart _ pos hil m c hpc j hr hcur
  exact h 2 init0 H comp hwf hprod hpart pos hil m c hpc j hr hcur

/-! ## Gilbert–Lynch, Theorem 1 -/

/-- **Gilbert–Lynch, Theorem 1 (asynchronous model), by reduction to
Corollary `cor:gilbert-lynch`.**  For any network of at least two nodes, no
algorithm for a read/write register is both available (every pending request
is answered in some extension adding no request and losing every message) and
atomic (every execution with well-formed clients has a linearization).
The algorithm's translation `sysOf A` would satisfy the hypotheses of the
corollary's client form: Answering (`sys_answering`) and Response Partition
Consistency at realized histories (`sys_rpc`). -/
theorem gilbert_lynch_async (hN : 2 ≤ N) (A : Alg N M) : ¬ (Available A ∧ Atomic A) := by
  rintro ⟨hav, hat⟩
  exact gilbert_lynch_client (sysOf A) ⟨sys_answering hN A hat hav, sys_rpc hN A hat⟩


/-! ## Non-vacuity: each of Availability and Atomicity alone is satisfiable -/

/-- The algorithm that never responds. -/
def silentAlg (N : Nat) (M : Type) : Alg N M where
  St := Unit
  start := fun _ => ()
  step := fun _ _ x _ => match x with | .resp _ _ => False | _ => True
  inv_enabled := fun _ _ _ _ => ⟨(), trivial⟩
  recv_enabled := fun _ _ _ _ => ⟨(), trivial⟩

theorem silent_noresp {i : Fin N} {s s' : (silentAlg N M).St} {l : List (Act N M)}
    (h : NRun (silentAlg N M) i s l s') : ∀ a r, Act.resp a r ∉ l := by
  induction h with
  | nil => simp
  | @cons _ _ _ x _ hs _ ih =>
    intro a r hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hs
    · exact ih a r hm

/-- The silent algorithm is atomic. -/
theorem silent_atomic : Atomic (silentAlg N M) := by
  intro E hE _
  have hno : ∀ i T a r, (T, Act.resp a r) ∉ E.tr i := by
    intro i T a r hm
    obtain ⟨_, hr⟩ := hE.1 i
    exact silent_noresp hr a r (mem_acts.2 ⟨T, hm⟩)
  refine ⟨fun i T a r h => absurd h (hno i T a r), fun _ => False, id,
    fun i T a r h => absurd h (hno i T a r), fun _ h => h.elim, fun _ _ h => h.elim,
    fun i T a r _ _ _ _ h => absurd h (hno i T a r), fun i T a r _ _ _ h => absurd h (hno i T a r)⟩

/-- The algorithm that may do anything at any time (e.g. answer at once). -/
def eagerAlg (N : Nat) (M : Type) : Alg N M where
  St := Unit
  start := fun _ => ()
  step := fun _ _ _ _ => True
  inv_enabled := fun _ _ _ _ => ⟨(), trivial⟩
  recv_enabled := fun _ _ _ _ => ⟨(), trivial⟩

theorem eager_run (i : Fin N) : ∀ l : List (Act N M), NRun (eagerAlg N M) i () l ()
  | [] => .nil _
  | _ :: l => .cons (s' := ()) trivial (eager_run i l)

/-- A bound on all times of an execution. -/
theorem exec_time_bound (E : GExec N M) : ∃ B, ∀ i x, x ∈ E.tr i → x.1 < B := by
  let l := (List.finRange N).flatMap (fun i => (E.tr i).map Prod.fst)
  refine ⟨l.sum + 1, fun i x hx => ?_⟩
  have : x.1 ∈ l := List.mem_flatMap.2 ⟨i, List.mem_finRange i, List.mem_map_of_mem hx⟩
  have := le_sum_map id this
  simp at this; omega

/-- The eager algorithm is available: answer the pending request after
everything else. -/
theorem eager_available : Available (eagerAlg N M) := by
  classical
  intro E hE _ i T a kd _ _
  obtain ⟨B, hB⟩ := exec_time_bound E
  let E' : GExec N M := ⟨fun j => if j = i then E.tr j ++ [(B, .resp a .ack)] else E.tr j⟩
  have hmem : ∀ j y, y ∈ E'.tr j → y ∈ E.tr j ∨ (j = i ∧ y = (B, .resp a .ack)) := by
    intro j y hy
    simp only [E'] at hy
    split at hy
    · rcases List.mem_append.1 hy with h | h
      · exact Or.inl h
      · simp at h; exact Or.inr ⟨by assumption, h⟩
    · exact Or.inl hy
  have hold : ∀ j y, y ∈ E.tr j → y ∈ E'.tr j := by
    intro j y hy; simp only [E']; split
    · exact List.mem_append_left _ hy
    · exact hy
  obtain ⟨f, hf⟩ := hE.2.2.2
  refine ⟨E', ⟨fun j => ⟨(), eager_run j _⟩, ?_, ?_, ⟨f, ?_⟩⟩, ?_, B, .ack, ?_⟩
  · intro j
    simp only [E']; split
    · rw [List.pairwise_append]
      exact ⟨hE.2.1 j, by simp, fun x hx y hy => by simp at hy; subst hy; exact hB j x hx⟩
    · exact hE.2.1 j
  · intro j j' x y hx hy he
    rcases hmem j x hx with hx' | ⟨h1, h2⟩ <;> rcases hmem j' y hy with hy' | ⟨h3, h4⟩
    · exact hE.2.2.1 j j' x y hx' hy' he
    · have := hB j x hx'; rw [h4] at he; simp at he; omega
    · have := hB j' y hy'; rw [h2] at he; simp at he; omega
    · exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩
  · intro j T' src m hm
    rcases hmem j _ hm with hm | ⟨_, he⟩
    · obtain ⟨h1, h2, h3⟩ := hf j T' src m hm
      refine ⟨h1, hold _ _ h2, fun i' T'' src' m' hm' he' => ?_⟩
      rcases hmem i' _ hm' with hm' | ⟨_, he''⟩
      · exact h3 i' T'' src' m' hm' he'
      · simp at he''
    · simp at he
  · intro j
    by_cases hj : j = i
    · subst hj
      refine ⟨[(B, .resp a .ack)], by simp [E'], fun y hy => ?_⟩
      simp at hy; subst hy
      exact ⟨fun j' x hx => hB j' x hx, by simp, by simp⟩
    · exact ⟨[], by simp [E', hj], by simp⟩
  · simp [E']

end AsyncGL
end CC
