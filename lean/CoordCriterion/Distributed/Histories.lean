import CoordCriterion.Foundations.Core
import CoordCriterion.Foundations.Runs
import CoordCriterion.FunctionalCALM.Theorem

/-!
# Distributed histories and distributed consistency (Sections 4.1–4.2)

Namespace `CC.Dist`.

* histories, participant runs, happens-before, consistent cuts, endpoints
  (`History`, `cut_prefix`, `endpoint_exists`, `endpoint_unique`);
* cut confluence is confluence of participant runs;
* Prop. distributed-consistency (`consistent_iff_distConsistent`);
* Cor. convergence (`convergence`, `convergence_agree`, via
  `CC.state_by_input`);
* exchanging outputs at the table level (`honor_survivor`,
  `honor_cut_confluent`) and the caveat that an honored table need not be a
  specification state.

The variant without unique send identifiers, and the equivalence with Lifted
Monotonicity, are in `Distributed/Systems.lean`.

Modeling choices (paper: Defs. distributed-history, participant-run,
distributed-consistency):

* Participants are `Fin n`; "every finite participant set" is "every `n`".
* A history assigns each participant a `List` of local events; the list order
  *is* the total local order (item 1).  A history event is a position
  `(p, k)` with `k < (H.ev p).length`.
* Local events are `io e` (an input or output event of the transition
  system), `send x m`, `recv x m`, where `x : Nat` is a message identifier and
  `m = (j, d) : Option I × D` is the message (`none` plays `∅`).
  A receive *matches* a send with the same identifier and message.  We
  require send identifiers to be unique in the history, so that "the matching
  send" is well defined (the paper says "a matching send"; uniqueness of
  message occurrences is the standard reading).  Nothing constrains the
  content `j` of a message or forces the receiver to incorporate it: the paper
  describes incorporation by an `input(k)` as protocol behaviour, not as a
  condition of Def. distributed-history.
* Item 3 (legality) is: `ioOf (H.ev p)` executes from `canon sp (H.init p)`.
  Receives and sends are filtered out by `ioOf`, i.e. they do not change the
  specification state.
* Happens-before is `Relation.TransGen` of local-order and send→receive edges;
  a consistent cut is a set of history events closed downward under it.
  We prove that a cut is a prefix at every participant (`cut_prefix`).
* Endpoints are stated relationally (`Endpoint`), and we prove they exist
  (`endpoint_exists`) and are unique (`endpoint_unique`), so quantifying over
  them is the same as using `σ_p(C)`.
* A continuation `H'` at `C` keeps the initial inputs and agrees with `H` at
  every position of `C` (`Extends`); since `C` is a prefix at each
  participant, the further events of `H'` come after those of `C`.
-/

namespace CC
namespace Dist

/-! ### Determinism and composition of executions -/

section exec
variable {I O : Type} [PO I] [PO O]

theorem exec_append {sp : Spec I O} : ∀ {σ ρ : State sp} (a b : List (Event I O)),
    Exec σ (a ++ b) ρ ↔ ∃ τ, Exec σ a τ ∧ Exec τ b ρ
  | σ, _, [], _ => ⟨fun h => ⟨σ, .nil σ, h⟩, fun ⟨_, h1, h2⟩ => by cases h1; exact h2⟩
  | _, _, e :: a, b => by
    constructor
    · intro h
      cases h with
      | cons hs hr =>
        obtain ⟨τ, h1, h2⟩ := (exec_append a b).1 hr
        exact ⟨τ, .cons hs h1, h2⟩
    · rintro ⟨τ, h1, h2⟩
      cases h1 with
      | cons hs hr => exact .cons hs ((exec_append a b).2 ⟨τ, hr, h2⟩)

end exec

/-! ### Histories -/

/-- Local history events: an input/output event, or a send/receive of the
message `m = (j, d)` with identifier `x`. -/
inductive LEv (I O D : Type) where
  | io (e : Event I O)
  | send (x : Nat) (m : Option I × D)
  | recv (x : Nat) (m : Option I × D)

def LEv.toIO {I O D : Type} : LEv I O D → Option (Event I O)
  | .io e => some e
  | _ => none

/-- The input and output events of a list of local events, in order. -/
def ioOf {I O D : Type} (l : List (LEv I O D)) : List (Event I O) := l.filterMap LEv.toIO

theorem ioOf_append {I O D : Type} (a b : List (LEv I O D)) :
    ioOf (a ++ b) = ioOf a ++ ioOf b := List.filterMap_append

theorem ioOf_map_io {I O D : Type} (es : List (Event I O)) :
    ioOf (es.map (LEv.io (D := D))) = es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map, ioOf, List.filterMap_cons, LEv.toIO] at *; rw [ih]

/-- A distributed history over participants `Fin n`. -/
structure History (I O D : Type) (n : Nat) where
  init : Fin n → I
  ev : Fin n → List (LEv I O D)

section hist
variable {I O D : Type} {n : Nat}

abbrev Pos (n : Nat) := Fin n × Nat

/-- `a` is a history event of `H`. -/
def History.InH (H : History I O D n) (a : Pos n) : Prop := a.2 < (H.ev a.1).length

/-- Generating edges of happens-before. -/
inductive History.Edge (H : History I O D n) : Pos n → Pos n → Prop where
  | loc (p : Fin n) (k k' : Nat) : k < k' → k' < (H.ev p).length → H.Edge (p, k) (p, k')
  | msg (q : Fin n) (s : Nat) (p : Fin n) (r : Nat) (x : Nat) (m : Option I × D) :
      (H.ev q)[s]? = some (.send x m) → (H.ev p)[r]? = some (.recv x m) → H.Edge (q, s) (p, r)

/-- Happens-before. -/
def History.HB (H : History I O D n) : Pos n → Pos n → Prop := Relation.TransGen H.Edge

/-- Consistent cut: a set of history events closed under happens-before. -/
structure History.IsCut (H : History I O D n) (C : Pos n → Prop) : Prop where
  sub : ∀ a, C a → H.InH a
  closed : ∀ a b, H.HB a b → C b → C a

theorem History.edge_src {H : History I O D n} {a b : Pos n} (h : H.Edge a b) : H.InH a := by
  cases h with
  | loc p k k' h1 h2 => show k < (H.ev p).length; omega
  | msg q s p r x m hs _ => exact (List.getElem?_eq_some_iff.1 hs).1

theorem History.hb_src {H : History I O D n} {a b : Pos n} (h : H.HB a b) : H.InH a := by
  induction h with
  | single e => exact History.edge_src e
  | tail _ _ ih => exact ih

/-- All of `H` is a consistent cut of `H` (its final cut). -/
theorem History.isCut_full (H : History I O D n) : H.IsCut H.InH :=
  ⟨fun _ h => h, fun _ _ h _ => History.hb_src h⟩

/-- A downward-closed bounded set of naturals is an initial segment. -/
theorem prefix_of_downclosed (P : Nat → Prop) : ∀ L, (∀ k, P k → k < L) →
    (∀ k k', k < k' → P k' → P k) → ∃ c, c ≤ L ∧ ∀ k, P k ↔ k < c
  | 0, hb, _ => ⟨0, Nat.le_refl _, fun k =>
      ⟨fun h => absurd (hb k h) (Nat.not_lt_zero _), fun h => absurd h (Nat.not_lt_zero _)⟩⟩
  | L + 1, hb, hd => by
    by_cases hL : P L
    · refine ⟨L + 1, Nat.le_refl _, fun k => ⟨hb k, fun hk => ?_⟩⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h | h
      · exact hd k L h hL
      · subst h; exact hL
    · obtain ⟨c, hc, h⟩ := prefix_of_downclosed P L (fun k hk => by
        have := hb k hk
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ this) with h | h
        · exact h
        · subst h; exact absurd hk hL) hd
      exact ⟨c, by omega, h⟩

/-- A consistent cut contains a prefix of each participant's events. -/
theorem History.IsCut.cut_prefix {H : History I O D n} {C : Pos n → Prop} (hC : H.IsCut C)
    (p : Fin n) : ∃ c, c ≤ (H.ev p).length ∧ ∀ k, C (p, k) ↔ k < c :=
  prefix_of_downclosed (fun k => C (p, k)) _ (fun _ hk => hC.sub _ hk)
    (fun k k' hlt hk' => hC.closed _ _ (.single (.loc p k k' hlt (hC.sub _ hk'))) hk')

theorem len_unique {P : Nat → Prop} {c c' : Nat} (h : ∀ k, P k ↔ k < c)
    (h' : ∀ k, P k ↔ k < c') : c = c' := by
  apply Classical.byContradiction
  intro hne
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · exact Nat.lt_irrefl _ ((h c).1 ((h' c).2 hl))
  · exact Nat.lt_irrefl _ ((h' c').1 ((h c').2 hl))

variable [PO I] [PO O]

/-- Well-formed distributed history (Def. distributed-history, items 2–3;
item 1 is the list order). -/
structure History.WF (sp : Spec I O) (H : History I O D n) : Prop where
  recv_match : ∀ p (r : Nat) x m, (H.ev p)[r]? = some (LEv.recv x m) →
    ∃ q, ∃ s : Nat, q ≠ p ∧ (H.ev q)[s]? = some (LEv.send x m)
  send_unique : ∀ q (s : Nat) q' (s' : Nat) x m m', (H.ev q)[s]? = some (LEv.send x m) →
    (H.ev q')[s']? = some (LEv.send x m') → q = q' ∧ s = s'
  legal : ∀ p, ∃ τ : State sp, Exec (canon sp (H.init p)) (ioOf (H.ev p)) τ

/-- `σs` is the endpoint `end(H, C)` (Def. participant-run): `σs p` is the
final state of `p`'s participant run at `C`. -/
def History.Endpoint (sp : Spec I O) (H : History I O D n) (C : Pos n → Prop)
    (σs : Fin n → State sp) : Prop :=
  ∀ p, ∃ c, (∀ k, C (p, k) ↔ k < c) ∧
    Exec (canon sp (H.init p)) (ioOf ((H.ev p).take c)) (σs p)

/-- Participant runs are runs. -/
theorem History.Endpoint.isRun {sp : Spec I O} {H : History I O D n} {C : Pos n → Prop}
    {σs : Fin n → State sp} (h : H.Endpoint sp C σs) (p : Fin n) : IsRun (σs p) := by
  obtain ⟨_, _, hx⟩ := h p
  exact ⟨_, _, hx⟩

theorem History.endpoint_exists {sp : Spec I O} {H : History I O D n} (hW : H.WF sp)
    {C : Pos n → Prop} (hC : H.IsCut C) : ∃ σs, H.Endpoint sp C σs := by
  have h : ∀ p, ∃ σ : State sp, ∃ c, (∀ k, C (p, k) ↔ k < c) ∧
      Exec (canon sp (H.init p)) (ioOf ((H.ev p).take c)) σ := by
    intro p
    obtain ⟨c, _, hc⟩ := hC.cut_prefix p
    obtain ⟨τ, hx⟩ := hW.legal p
    rw [← List.take_append_drop c (H.ev p), ioOf_append, exec_append] at hx
    obtain ⟨σ, h1, _⟩ := hx
    exact ⟨σ, c, hc, h1⟩
  exact ⟨fun p => Classical.choose (h p), fun p => Classical.choose_spec (h p)⟩

theorem History.endpoint_unique {sp : Spec I O} {H : History I O D n} {C : Pos n → Prop}
    {σs σs' : Fin n → State sp} (h : H.Endpoint sp C σs) (h' : H.Endpoint sp C σs') :
    σs = σs' := by
  funext p
  obtain ⟨c, hc, hx⟩ := h p
  obtain ⟨c', hc', hx'⟩ := h' p
  have := len_unique hc hc'
  subst this
  exact exec_det hx hx'

theorem History.endpoint_choose {sp : Spec I O} {H : History I O D n} {C : Pos n → Prop}
    {σs : Fin n → State sp} (h : H.Endpoint sp C σs) :
    ∃ c : Fin n → Nat, ∀ p, (∀ k, C (p, k) ↔ k < c p) ∧
      Exec (canon sp (H.init p)) (ioOf ((H.ev p).take (c p))) (σs p) :=
  ⟨fun p => Classical.choose (h p), fun p => Classical.choose_spec (h p)⟩

/-- Endpoint of the final cut. -/
theorem History.endpoint_full {sp : Spec I O} {H : History I O D n} {σs : Fin n → State sp} :
    H.Endpoint sp H.InH σs ↔ ∀ p, Exec (canon sp (H.init p)) (ioOf (H.ev p)) (σs p) := by
  constructor
  · intro h p
    obtain ⟨c, hc, hx⟩ := h p
    have : (H.ev p).length = c := len_unique (P := fun k => H.InH (p, k)) (fun _ => Iff.rfl) hc
    subst this
    rwa [List.take_length] at hx
  · intro h p
    exact ⟨(H.ev p).length, fun _ => Iff.rfl, by rw [List.take_length]; exact h p⟩

/-- `H'` is a continuation of `H` at the cut `C`: same initial inputs, and it
contains the history events of `C` unchanged (further events come after). -/
def History.Extends (H H' : History I O D n) (C : Pos n → Prop) : Prop :=
  H'.init = H.init ∧ ∀ p k, C (p, k) → (H'.ev p)[k]? = (H.ev p)[k]?

/-- A consistent cut `C` is confluent at `j`: some well-formed continuation's
final cut has endpoint `((j,R))_{p ∈ P}`. -/
def History.CutConfluentAt (sp : Spec I O) (H : History I O D n) (C : Pos n → Prop)
    (j : I) : Prop :=
  ∃ H' : History I O D n, H'.WF sp ∧ H.Extends H' C ∧
    ∃ τ : State sp, τ.cur = j ∧ H'.Endpoint sp H'.InH (fun _ => τ)

end hist

section defs
variable {I O : Type} [PO I] [PO O]

/-- Distributed consistency (Def. distributed-consistency), for message data
of type `D`. -/
def DistConsistent (sp : Spec I O) (D : Type) : Prop :=
  ∀ (n : Nat) (H : History I O D n), H.WF sp → ∀ C, H.IsCut C →
    ∀ σs : Fin n → State sp, H.Endpoint sp C σs →
    ∀ j : I, (∀ p, (σs p).cur ≼ j) → H.CutConfluentAt sp C j

end defs

/-! ### Cut confluence = confluence of participant runs -/

section lemmas
variable {I O D : Type} {n : Nat}

theorem get_ext {l : List (LEv I O D)} {c : Nat} {es : List (Event I O)} {r : Nat}
    {e : LEv I O D} (h : (l.take c ++ es.map LEv.io)[r]? = some e) :
    (r < c ∧ l[r]? = some e) ∨ ∃ e', e = .io e' := by
  by_cases hr : r < (l.take c).length
  · rw [List.getElem?_append_left hr, List.getElem?_take] at h
    split at h
    · exact Or.inl ⟨by assumption, h⟩
    · cases h
  · rw [List.getElem?_append_right (by omega), List.getElem?_map] at h
    right
    cases hx : es[r - (l.take c).length]? with
    | none => rw [hx] at h; cases h
    | some e' => rw [hx] at h; cases h; exact ⟨e', rfl⟩

theorem get_ext_lt {l X : List (LEv I O D)} {c r : Nat} (h1 : r < c) (h2 : r < l.length) :
    (l.take c ++ X)[r]? = l[r]? := by
  have : r < (l.take c).length := by simp; omega
  rw [List.getElem?_append_left this, List.getElem?_take_of_lt h1]

variable [PO I] [PO O]

/-- "History events at different participants are independent": a consistent
cut is confluent at `j` iff its participant runs are confluent at `j`. -/
theorem cut_confluent_iff {sp : Spec I O} {H : History I O D n} (hW : H.WF sp)
    {C : Pos n → Prop} (hC : H.IsCut C) {σs : Fin n → State sp} (hE : H.Endpoint sp C σs)
    (j : I) :
    H.CutConfluentAt sp C j ↔ ∃ τ : State sp, τ.cur = j ∧ ∀ p, Reach (σs p) τ := by
  constructor
  · rintro ⟨H', _, ⟨hinit, hext⟩, τ, hτ, hend'⟩
    rw [History.endpoint_full] at hend'
    refine ⟨τ, hτ, fun p => ?_⟩
    obtain ⟨c, hc, hx⟩ := hE p
    have htake : (H'.ev p).take c = (H.ev p).take c := by
      apply List.ext_getElem?
      intro i
      rw [List.getElem?_take, List.getElem?_take]
      split
      · exact hext p i ((hc i).2 ‹_›)
      · rfl
    have h := hend' p
    rw [← List.take_append_drop c (H'.ev p), ioOf_append, exec_append] at h
    obtain ⟨ρ, h1, h2⟩ := h
    rw [hinit, htake] at h1
    have := exec_det h1 hx
    subst this
    exact ⟨_, h2⟩
  · rintro ⟨τ, hτ, hr⟩
    obtain ⟨c, hc⟩ := History.endpoint_choose hE
    have hes : ∀ p, ∃ es, Exec (σs p) es τ := hr
    let es := fun p => Classical.choose (hes p)
    have hes' : ∀ p, Exec (σs p) (es p) τ := fun p => Classical.choose_spec (hes p)
    let H' : History I O D n :=
      ⟨H.init, fun p => (H.ev p).take (c p) ++ (es p).map LEv.io⟩
    have hlegal : ∀ p, Exec (canon sp (H'.init p)) (ioOf (H'.ev p)) τ := by
      intro p
      show Exec _ (ioOf ((H.ev p).take (c p) ++ (es p).map LEv.io)) τ
      rw [ioOf_append, ioOf_map_io]
      exact (exec_append _ _).2 ⟨σs p, (hc p).2, hes' p⟩
    -- sends of `H'` at positions in the cut are those of `H`
    have hcut : ∀ q s, C (q, s) → (H'.ev q)[s]? = (H.ev q)[s]? := fun q s hs =>
      get_ext_lt (((hc q).1 s).1 hs) (hC.sub _ hs)
    refine ⟨H', ⟨?_, ?_, fun p => ⟨τ, hlegal p⟩⟩, ⟨rfl, hcut⟩, τ, hτ,
      History.endpoint_full.2 hlegal⟩
    · intro p r x m h
      rcases get_ext h with ⟨hrc, hr'⟩ | ⟨_, he⟩
      · obtain ⟨q, s, hqp, hs⟩ := hW.recv_match p r x m hr'
        have hCp : C (p, r) := ((hc p).1 r).2 hrc
        have hCq : C (q, s) := hC.closed _ _ (.single (.msg q s p r x m hs hr')) hCp
        exact ⟨q, s, hqp, by rw [hcut q s hCq]; exact hs⟩
      · cases he
    · intro q s q' s' x m m' h h'
      rcases get_ext h with ⟨_, hs⟩ | ⟨_, he⟩
      · rcases get_ext h' with ⟨_, hs'⟩ | ⟨_, he'⟩
        · exact hW.send_unique q s q' s' x m m' hs hs'
        · cases he'
      · cases he

end lemmas

/-! ### Proposition distributed-consistency -/

section main
variable {I O : Type} [PO I] [PO O]

/-- **Proposition (Consistency and distributed consistency).**  For any type
`D` of message data, an ordered specification is consistent iff it has
distributed consistency. -/
theorem consistent_iff_distConsistent (sp : Spec I O) (D : Type) :
    sp.Consistent ↔ DistConsistent sp D := by
  constructor
  · intro hc n H hW C hC σs hE j hj
    rw [cut_confluent_iff hW hC hE]
    obtain ⟨τ, hτ, h⟩ := hc (List.ofFn σs)
      (fun σ hσ => by obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hσ; exact hE.isRun p) j
      (fun σ hσ => by obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hσ; exact hj p)
    exact ⟨τ, hτ, fun p => h _ (List.mem_ofFn.2 ⟨p, rfl⟩)⟩
  · intro hd fam hrun j hj
    -- the message-free history with one participant per run
    have hr : ∀ p : Fin fam.length, ∃ i es, Exec (canon sp i) es (fam[p.1]'p.2) :=
      fun p => hrun _ (List.getElem_mem p.2)
    let ip := fun p => Classical.choose (hr p)
    let esp := fun p => Classical.choose (Classical.choose_spec (hr p))
    have hx : ∀ p, Exec (canon sp (ip p)) (esp p) (fam[p.1]'p.2) :=
      fun p => Classical.choose_spec (Classical.choose_spec (hr p))
    let H : History I O D fam.length := ⟨ip, fun p => (esp p).map LEv.io⟩
    have hnoio : ∀ p (r : Nat) (e : LEv I O D), (H.ev p)[r]? = some e → ∃ e', e = .io e' := by
      intro p r e h
      change ((esp p).map LEv.io)[r]? = some e at h
      rw [List.getElem?_map] at h
      cases hx' : (esp p)[r]? with
      | none => rw [hx'] at h; cases h
      | some e' => rw [hx'] at h; cases h; exact ⟨e', rfl⟩
    have hlegal : ∀ p, Exec (canon sp (H.init p)) (ioOf (H.ev p)) (fam[p.1]'p.2) := by
      intro p
      show Exec _ (ioOf ((esp p).map LEv.io)) _
      rw [ioOf_map_io]; exact hx p
    have hW : H.WF sp := by
      refine ⟨fun p r x m h => ?_, fun q s _ _ x m _ h _ => ?_, fun p => ⟨_, hlegal p⟩⟩
      · obtain ⟨_, he⟩ := hnoio p r _ h; cases he
      · obtain ⟨_, he⟩ := hnoio q s _ h; cases he
    have hE : H.Endpoint sp H.InH (fun p => fam[p.1]'p.2) := History.endpoint_full.2 hlegal
    have hcc := hd fam.length H hW H.InH H.isCut_full _ hE j
      (fun p => hj _ (List.getElem_mem p.2))
    obtain ⟨τ, hτ, hreach⟩ := (cut_confluent_iff hW H.isCut_full hE j).1 hcc
    refine ⟨τ, hτ, fun σ hσ => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hσ
    exact hreach ⟨i, hi⟩

/-! ### Corollary convergence -/

/-- **Corollary (Convergence).**  At any consistent cut of any history of a
consistent functional specification, a participant whose current input is
`j` is in the canonical state `σ_S(j)`. -/
theorem convergence {D : Type} {n : Nat} {sp : Spec I O} (hc : sp.Consistent)
    (hf : sp.Functional) {H : History I O D n} {C : Pos n → Prop}
    {σs : Fin n → State sp} (hE : H.Endpoint sp C σs) (p : Fin n) {j : I}
    (hj : (σs p).cur = j) : σs p = canon sp j := by
  rw [← hj]; exact CC.state_by_input hf hc (hE.isRun p)

/-- Participants with the same current input agree, whatever the history. -/
theorem convergence_agree {D : Type} {n : Nat} {sp : Spec I O} (hc : sp.Consistent)
    (hf : sp.Functional) {H : History I O D n} {C : Pos n → Prop}
    {σs : Fin n → State sp} (hE : H.Endpoint sp C σs) (p q : Fin n)
    (h : (σs p).cur = (σs q).cur) : σs p = σs q := by
  exact (convergence hc hf hE p h).trans (convergence hc hf hE q rfl).symm

end main

/-! ### Exchanging outputs -/

section honor
variable {I O : Type} [PO I] [PO O]

/-- Silently honoring outputs `os`: restrict a table to `R[out ⪰ o]`, `o ∈ os`. -/
def honor (R : Table I O) (os : List O) : Table I O := fun k u => R k u ∧ ∀ o ∈ os, o ≼ u

/-- **Exchanging outputs (table level).**  Each member of the family is a
state `σ` with residual shape for its emitted outputs `E` (every run has this
shape, `IsRun.residual`) and a list `os` of honored outputs, each emitted by
some member.  Then a row at `j` survives the honored tables iff it survives
the original ones; with `survivor_test`, honoring cannot change confluence. -/
theorem honor_survivor {sp : Spec I O} (fam : List (State sp × List O × List O))
    (hres : ∀ x ∈ fam, Residual x.1 x.2.1)
    (hos : ∀ x ∈ fam, ∀ o ∈ x.2.2, ∃ y ∈ fam, o ∈ y.2.1) (j : I) :
    (∃ u, sp.S j u ∧ ∀ x ∈ fam, honor x.1.R x.2.2 j u) ↔
      (∃ u, sp.S j u ∧ ∀ x ∈ fam, x.1.R j u) := by
  constructor
  · -- cannot help: honoring only removes rows
    rintro ⟨u, hu, h⟩
    exact ⟨u, hu, fun x hx => (h x hx).1⟩
  · -- cannot hurt: a surviving row already refines every emitted output
    rintro ⟨u, hu, h⟩
    refine ⟨u, hu, fun x hx => ⟨h x hx, fun o ho => ?_⟩⟩
    obtain ⟨y, hy, hoy⟩ := hos x hx o ho
    exact ((hres y hy j u).1 (h y hy)).2.2 o hoy

omit [PO I] [PO O] in
theorem mem_outs_ioOf {D : Type} {o : O} :
    ∀ {l : List (LEv I O D)}, LEv.io (.output o) ∈ l → o ∈ outs (ioOf l)
  | [], h => by cases h
  | e :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [ioOf, LEv.toIO, outs]
    · have ih := mem_outs_ioOf h
      cases e with
      | io e =>
        cases e with
        | input _ => simpa [ioOf, LEv.toIO, outs] using ih
        | output _ => simp [ioOf, LEv.toIO, outs] at ih ⊢; exact Or.inr ih
      | send _ _ => exact ih
      | recv _ _ => exact ih

/-- `o` is emitted by an output event in the cut `C`. -/
def History.EmittedIn {D : Type} {n : Nat} (H : History I O D n) (C : Pos n → Prop)
    (o : O) : Prop :=
  ∃ q k, C (q, k) ∧ (H.ev q)[k]? = some (.io (.output o))

/-- **Exchanging outputs (history level).**  If each participant silently
honors outputs `os p` emitted earlier in the cut, the survivor test on the
honored tables still decides confluence of the cut, exactly as before. -/
theorem honor_cut_confluent {D : Type} {n : Nat} {sp : Spec I O} {H : History I O D n}
    (hW : H.WF sp) {C : Pos n → Prop} (hC : H.IsCut C) {σs : Fin n → State sp}
    (hE : H.Endpoint sp C σs) (os : Fin n → List O) (hos : ∀ p, ∀ o ∈ os p, H.EmittedIn C o)
    (j : I) (hj : ∀ p, (σs p).cur ≼ j) :
    H.CutConfluentAt sp C j ↔ ∃ u, sp.S j u ∧ ∀ p, honor (σs p).R (os p) j u := by
  obtain ⟨c, hc⟩ := History.endpoint_choose hE
  rw [cut_confluent_iff hW hC hE]
  have hsurv := survivor_test (List.ofFn σs)
    (fun σ hσ => by obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hσ; exact hE.isRun p) j
    (fun σ hσ => by obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hσ; exact hj p)
  have hres : ∀ p, Residual (σs p) (outs (ioOf ((H.ev p).take (c p)))) :=
    fun p => run_residual (hc p).2
  constructor
  · rintro ⟨τ, hτ, hr⟩
    obtain ⟨u, hu, hall⟩ := hsurv.1 ⟨τ, hτ, fun σ hσ => by
      obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hσ; exact hr p⟩
    refine ⟨u, hu, fun p => ⟨hall _ (List.mem_ofFn.2 ⟨p, rfl⟩), fun o ho => ?_⟩⟩
    obtain ⟨q, k, hk, hko⟩ := hos p o ho
    have hmem : LEv.io (.output o) ∈ (H.ev q).take (c q) := by
      apply List.mem_of_getElem? (i := k)
      rw [List.getElem?_take_of_lt (((hc q).1 k).1 hk)]
      exact hko
    exact ((hres q j u).1 (hall _ (List.mem_ofFn.2 ⟨q, rfl⟩))).2.2 o (mem_outs_ioOf hmem)
  · rintro ⟨u, hu, h⟩
    obtain ⟨τ, hτ, hr⟩ := hsurv.2 ⟨u, hu, fun σ hσ => by
      obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hσ; exact (h p).1⟩
    exact ⟨τ, hτ, fun p => hr _ (List.mem_ofFn.2 ⟨p, rfl⟩)⟩

end honor

/-! ### Caveat: an honored table need not be a specification state

Inputs and outputs are `V3 = Fin 3` with `x ≼ y ↔ x = y ∨ y = 2`, and
`S x y ↔ x = y` (functional and monotone, hence consistent).  Participant `p`
is at `σ_S(0)`; participant `q` at `σ_S(1)` may emit `1`.  Honoring `1` at `p`
leaves no row at `p`'s current input `0`, so `R[out ⪰ 1]` is not the table of
a specification state (Def. specification state requires a row at the current
input) — yet the row `(2,2)` survives, and the cut stays confluent at `2`.
So "silent honoring" is meaningful only as a table restriction, as in
`honor_survivor`. -/

def V3 := Fin 3

def v (k : Fin 3) : V3 := k

instance : PO V3 where
  le x y := x = y ∨ y = v 2
  refl _ := Or.inl rfl
  trans := by
    intro a b c h1 h2
    rcases h2 with rfl | h2
    · exact h1
    · exact Or.inr h2
  antisymm := by
    intro a b h1 h2
    rcases h1 with h1 | h1
    · exact h1
    · rcases h2 with h2 | h2
      · exact h2.symm
      · exact h2.trans h1.symm

def spV3 : Spec V3 V3 where
  S x y := x = y
  total i := ⟨i, rfl⟩

theorem honor_counterexample :
    (canon spV3 (v 1)).R (v 1) (v 1) ∧                -- `q` can emit `1`
    (¬ ∃ x, honor (canon spV3 (v 0)).R [v 1] (v 0) x) ∧ -- no row at `p`'s input
    honor (canon spV3 (v 0)).R [v 1] (v 2) (v 2) ∧       -- `(2,2)` survives honoring
    (canon spV3 (v 1)).R (v 2) (v 2) := by
  refine ⟨⟨rfl, Or.inl rfl⟩, ?_, ⟨⟨rfl, Or.inr rfl⟩, ?_⟩, ⟨rfl, Or.inr rfl⟩⟩
  · rintro ⟨x, ⟨hx, _⟩, ho⟩
    have h := ho (v 1) (List.mem_singleton.2 rfl)
    change v 0 = x at hx
    subst hx
    change (v 1 = v 0 ∨ v 0 = v 2) at h
    rcases h with h | h <;> cases h
  · intro o ho
    rw [List.mem_singleton.1 ho]
    exact Or.inr rfl

end Dist
end CC
