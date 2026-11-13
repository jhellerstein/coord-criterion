import CoordCriterion.Instances.BKTransducers

/-!
# Baccaert and Ketsman's characterization: the sufficiency half

Namespace `CC.BK`.  `Instances/BKTransducers.lean` formalizes Baccaert and
Ketsman's operational model (node programs under Id+Ord, fair runs,
`Computes`, `Characterizes`) and proves their Prop. 11 (necessity).  This file
proves the converse, their Prop. 10, and with it their Thm. 5 and the
computability form obtained with their Lemma 4.

## The program (`qProg B`)

A node's state holds its record (the facts it has heard of, a sub-instance of
the global instance), the decisions it knows (pairs `(J, D)` with `D` a row of
`B` at `J`), the (sender, record) pairs it has read, and a step counter.  At
each step it reads messages, merges records and decisions, and broadcasts one
message carrying its id, its record and its decisions.  A node *decides* when
it has taken at least two earlier steps, its id is the least node of its
record `I`, it has read from every other node of `I` a message whose record is
exactly `I`, and `I` is not yet decided; it must then pick some `D ∈ B(I)`
extending every decision it knows (any such `D`; if none exists it does not
decide).  A node's output is the union, over the decisions it knows, of their
facts at its own node.

## Why it works

* Records only grow, so two decided quorums that share a node are nested or
  equal (`dec_lam`), a quorum is decided once (`dec_once`), and a decided
  `J ⊊ I` is known to `I`'s decider when it decides (`dec_mono`): `J`'s
  decider confirmed `I` after deciding `J`.  Hence decisions are monotone.
* Node monotonicity, applied to the maximal known decisions and the undecided
  remainder, gives a suitable decision whenever the conditions hold
  (`suitable`).
* Liveness: eventually every record is the whole instance, the least node has
  read every other node's confirmation of it, and the whole instance is
  decided; every node then adopts that decision, and every other decision lies
  below it (`computes_strong`).
* The two-step delay lets a run reach every row of `B` (`characterizes_qProg`):
  in the witness run every node first hears from all others, so the first
  decision is the whole instance and may pick the target row.

## Readings

* `LocatedFin B`: rows at nonempty finite networks have their output facts at
  nodes of the network.  This is Baccaert and Ketsman's Def. 1 condition
  `netw(K) ⊆ netw(H)`; `Spec` does not impose it, and no program can output
  facts at nodes outside the network.
* As in `BKTransducers.lean`, programs need not be generic or domain
  preserving.  The characterization is exact for this class of programs.
-/

namespace CC
namespace BK

open CAP
open QRef (ExtInp netAdm Netw union)
open CALM (PSet)

/-! ## Combining decisions -/

section Combine

variable {F Out : Type} {loc : F → Nat}

/-- Two instances have disjoint networks. -/
def DisjNet (loc : F → Nat) (A C : PSet F) : Prop := ∀ x, Netw loc A x → ¬ Netw loc C x

/-- Two instances are nested or have disjoint networks. -/
def Lam (loc : F → Nat) (A C : PSet F) : Prop := A ≼ C ∨ C ≼ A ∨ DisjNet loc A C

/-- The union of the instances of a list of decisions. -/
def unionL (L : List (PSet F × PSet (Nat × Out))) : PSet F := ⟨fun f => ∃ e ∈ L, e.1.mem f⟩

/-- Rows at nonempty finite networks have their output facts at nodes of the
network (Baccaert–Ketsman Def. 1: `netw(K) ⊆ netw(H)`). -/
def LocatedFin (loc : F → Nat) (B : Spec (LInp loc) (PSet (Nat × Out))) : Prop :=
  ∀ H K, FinNet loc H → (∃ f, H.mem f) → B.P ⟨H⟩ K → ∀ z, K.mem z → Netw loc H z.1

theorem finNet_sub {G s : PSet F} (hG : FinNet loc G) (h : ∀ x, Netw loc s x → Netw loc G x) :
    FinNet loc s := by
  classical
  obtain ⟨l, hnd, hl⟩ := hG
  refine ⟨l.filter (fun x => decide (Netw loc s x)), hnd.filter _, fun x => ?_⟩
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h' => h'.2, fun h' => ⟨(hl x).2 (h x h'), h'⟩⟩

theorem netw_mono {s t : PSet F} (h : s ≼ t) : ∀ x, Netw loc s x → Netw loc t x :=
  fun _ ⟨f, hf, hfl⟩ => ⟨f, h f hf, hfl⟩

/-- A maximal element of a nonempty list under a preorder. -/
theorem exists_max {α : Type} (r : α → α → Prop) (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c) :
    ∀ (L : List α), L ≠ [] → ∃ m ∈ L, ∀ e ∈ L, r m e → r e m
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, fun e he _ => by simp at he; subst he; exact hrefl _⟩
  | a :: b :: l, _ => by
    obtain ⟨m, hm, hmax⟩ := exists_max r hrefl htrans (b :: l) (by simp)
    by_cases h : r m a ∧ ¬ r a m
    · refine ⟨a, by simp, fun e he hae => ?_⟩
      rcases List.mem_cons.1 he with rfl | he'
      · exact hrefl _
      · exact htrans _ _ _ (hmax e he' (htrans _ _ _ h.1 hae)) h.1
    · refine ⟨m, List.mem_cons_of_mem _ hm, fun e he hme => ?_⟩
      rcases List.mem_cons.1 he with rfl | he'
      · exact Classical.byContradiction fun hn => h ⟨hme, hn⟩
      · exact hmax e he' hme

theorem linp_eq {s t : PSet F} (h : ∀ f, s.mem f ↔ t.mem f) : (⟨s⟩ : LInp loc) = ⟨t⟩ := by
  rw [pset_ext h]

variable {B : Spec (LInp loc) (PSet (Nat × Out))}

/-- Decisions that are pairwise nested-or-disjoint and monotone have a common
extension at the union of their instances. -/
theorem combine (hB : NodeMonoFin loc B) {G : PSet F} (hG : FinNet loc G) :
    ∀ (n : Nat) (L : List (PSet F × PSet (Nat × Out))), L.length ≤ n →
    (∀ e ∈ L, NodeClosed loc G e.1 ∧ (∃ f, e.1.mem f) ∧ B.P ⟨e.1⟩ e.2) →
    (∀ e ∈ L, ∀ e' ∈ L, Lam loc e.1 e'.1) →
    (∀ e ∈ L, ∀ e' ∈ L, e.1 ≼ e'.1 → e.2 ≼ e'.2) →
    ∃ K, B.P ⟨unionL L⟩ K ∧ ∀ e ∈ L, e.2 ≼ K := by
  classical
  intro n
  induction n with
  | zero =>
    intro L hL _ _ _
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    obtain ⟨K, hK⟩ := B.total ⟨unionL []⟩
    exact ⟨K, hK, by simp⟩
  | succ n ih =>
    intro L hL hok hlam hmono
    by_cases hnil : L = []
    · subst hnil
      obtain ⟨K, hK⟩ := B.total ⟨unionL []⟩
      exact ⟨K, hK, by simp⟩
    obtain ⟨e0, he0, hmax⟩ := exists_max (fun e e' : PSet F × PSet (Nat × Out) => e.1 ≼ e'.1)
      (fun _ => PO.refl _) (fun _ _ _ h1 h2 => PO.trans h1 h2) L hnil
    let Lo := L.filter (fun e => !decide (e.1 ≼ e0.1))
    have hLo : ∀ e, e ∈ Lo ↔ e ∈ L ∧ ¬ e.1 ≼ e0.1 := fun e => by
      simp [Lo, List.mem_filter]
    have hlen : Lo.length < L.length :=
      List.length_filter_lt_length_iff_exists.2 ⟨e0, he0, by simp [PO.refl]⟩
    have hsub : ∀ e ∈ Lo, e ∈ L := fun e he => ((hLo e).1 he).1
    obtain ⟨K', hK', hK'all⟩ := ih Lo (by omega) (fun e he => hok e (hsub e he))
      (fun e he e' he' => hlam e (hsub e he) e' (hsub e' he'))
      (fun e he e' he' => hmono e (hsub e he) e' (hsub e' he'))
    have hdisj : ∀ e ∈ Lo, DisjNet loc e0.1 e.1 := by
      intro e he
      obtain ⟨heL, hne⟩ := (hLo e).1 he
      rcases hlam e0 he0 e heL with h | h | h
      · exact absurd (hmax e heL h) hne
      · exact absurd h hne
      · exact h
    have hunion : ∀ f, (unionL L).mem f ↔ (union e0.1 (unionL Lo)).mem f := by
      intro f
      constructor
      · rintro ⟨e, he, hf⟩
        by_cases hle : e.1 ≼ e0.1
        · exact Or.inl (hle f hf)
        · exact Or.inr ⟨e, (hLo e).2 ⟨he, hle⟩, hf⟩
      · rintro (hf | ⟨e, he, hf⟩)
        · exact ⟨e0, he0, hf⟩
        · exact ⟨e, hsub e he, hf⟩
    by_cases hLo0 : Lo = []
    · have hall : ∀ e ∈ L, e.1 ≼ e0.1 := fun e he =>
        Classical.byContradiction fun hn => by
          have := (hLo e).2 ⟨he, hn⟩; rw [hLo0] at this; simp at this
      have hu : ∀ f, (unionL L).mem f ↔ e0.1.mem f := fun f =>
        ⟨fun ⟨e, he, hf⟩ => hall e he f hf, fun hf => ⟨e0, he0, hf⟩⟩
      refine ⟨e0.2, ?_, fun e he => hmono e he e0 he0 (hall e he)⟩
      rw [linp_eq hu]; exact (hok e0 he0).2.2
    · obtain ⟨e1, he1⟩ := List.exists_mem_of_ne_nil Lo hLo0
      obtain ⟨g, hg⟩ := (hok e1 (hsub e1 he1)).2.1
      have hfin0 : FinNet loc e0.1 :=
        finNet_sub hG (netw_mono fun f hf => ((hok e0 he0).1 f hf).1)
      have hfinLo : FinNet loc (unionL Lo) := finNet_sub hG (netw_mono fun f ⟨e, he, hf⟩ =>
        ((hok e (hsub e he)).1 f hf).1)
      obtain ⟨K, hK, h1, h2⟩ := hB e0.1 (unionL Lo) hfin0 hfinLo (hok e0 he0).2.1
        ⟨g, e1, he1, hg⟩ (fun x hx ⟨f, ⟨e, he, hf⟩, hfl⟩ => hdisj e he x hx ⟨f, hf, hfl⟩)
        e0.2 K' (hok e0 he0).2.2 hK'
      refine ⟨K, by rw [linp_eq hunion]; exact hK, fun e he => ?_⟩
      by_cases hle : e.1 ≼ e0.1
      · exact PO.trans (hmono e he e0 he0 hle) h1
      · exact PO.trans (hK'all e ((hLo e).2 ⟨he, hle⟩)) h2

/-- A suitable decision exists at a node-closed nonempty `I` extending a
family of nested-or-disjoint, monotone decisions inside `I`. -/
theorem suitable (hB : NodeMonoFin loc B) {G I : PSet F} (hG : FinNet loc G)
    (hI : NodeClosed loc G I) (hIne : ∃ f, I.mem f) (L : List (PSet F × PSet (Nat × Out)))
    (hok : ∀ e ∈ L, NodeClosed loc G e.1 ∧ (∃ f, e.1.mem f) ∧ B.P ⟨e.1⟩ e.2 ∧ e.1 ≼ I)
    (hlam : ∀ e ∈ L, ∀ e' ∈ L, Lam loc e.1 e'.1)
    (hmono : ∀ e ∈ L, ∀ e' ∈ L, e.1 ≼ e'.1 → e.2 ≼ e'.2) :
    ∃ K, B.P ⟨I⟩ K ∧ ∀ e ∈ L, e.2 ≼ K := by
  classical
  obtain ⟨KU, hKU, hKUall⟩ := combine hB hG L.length L (Nat.le_refl _)
    (fun e he => ⟨(hok e he).1, (hok e he).2.1, (hok e he).2.2.1⟩) hlam hmono
  let U := unionL L
  let R : PSet F := ⟨fun f => I.mem f ∧ ¬ U.mem f⟩
  have hUI : U ≼ I := fun f ⟨e, he, hf⟩ => (hok e he).2.2.2 f hf
  have hUnc : ∀ f, U.mem f → ∀ g, G.mem g → loc g = loc f → U.mem g :=
    fun f ⟨e, he, hf⟩ g hg hgl => ⟨e, he, ((hok e he).1 f hf).2 g hg hgl⟩
  by_cases hU : ∃ f, U.mem f
  · by_cases hR : ∃ f, R.mem f
    · obtain ⟨KR, hKR⟩ := B.total ⟨R⟩
      have hfinU : FinNet loc U := finNet_sub hG (netw_mono fun f hf => (hI f (hUI f hf)).1)
      have hfinR : FinNet loc R := finNet_sub hG (netw_mono fun f hf => (hI f hf.1).1)
      obtain ⟨K, hK, h1, _⟩ := hB U R hfinU hfinR hU hR
        (fun x ⟨f, hf, hfl⟩ ⟨g, hg, hgl⟩ =>
          hg.2 (hUnc f hf g (hI g hg.1).1 (hgl.trans hfl.symm))) KU KR hKU hKR
      refine ⟨K, ?_, fun e he => PO.trans (hKUall e he) h1⟩
      have : ∀ f, I.mem f ↔ (union U R).mem f := fun f =>
        ⟨fun hf => if h : U.mem f then Or.inl h else Or.inr ⟨hf, h⟩,
         fun hf => hf.elim (hUI f) (·.1)⟩
      rw [linp_eq this]; exact hK
    · have : ∀ f, I.mem f ↔ U.mem f := fun f =>
        ⟨fun hf => Classical.byContradiction fun hn => hR ⟨f, hf, hn⟩, hUI f⟩
      exact ⟨KU, by rw [linp_eq this]; exact hKU, hKUall⟩
  · obtain ⟨K, hK⟩ := B.total ⟨I⟩
    refine ⟨K, hK, fun e he => ?_⟩
    obtain ⟨f, hf⟩ := (hok e he).2.1
    exact absurd ⟨f, e, he, hf⟩ hU

end Combine

/-! ## The program -/

section Prog

variable {F Out : Type}

/-- A decision: an instance and a row of the behavior at it. -/
abbrev QDec (F Out : Type) := PSet F × PSet (Nat × Out)

/-- A message: sender id, record, known decisions. -/
abbrev QMsg (F Out : Type) := Nat × PSet F × List (QDec F Out)

/-- A node's state. -/
structure QSt (F Out : Type) where
  me : Option Nat
  rcd : PSet F
  decs : List (QDec F Out)
  conf : List (Nat × PSet F)
  cnt : Nat

def QSt.start : QSt F Out := ⟨none, ⟨fun _ => False⟩, [], [], 0⟩

open Classical in
/-- The id of a node with own facts `h`. -/
noncomputable def myId (loc : F → Nat) (h : PSet F) : Nat :=
  if hh : ∃ f, h.mem f then loc (Classical.choose hh) else 0

namespace Q

variable (loc : F → Nat)

noncomputable def idOf (h : PSet F) (s : QSt F Out) : Nat := s.me.getD (myId loc h)

def recN (h : PSet F) (s : QSt F Out) (R : List (QMsg F Out)) : PSet F :=
  ⟨fun f => s.rcd.mem f ∨ h.mem f ∨ ∃ m ∈ R, m.2.1.mem f⟩

def decs0 (s : QSt F Out) (R : List (QMsg F Out)) : List (QDec F Out) :=
  s.decs ++ R.flatMap (fun m => m.2.2)

def confN (s : QSt F Out) (R : List (QMsg F Out)) : List (Nat × PSet F) :=
  s.conf ++ R.map (fun m => (m.1, m.2.1))

/-- The deciding condition. -/
def Cond (h : PSet F) (s : QSt F Out) (R : List (QMsg F Out)) : Prop :=
  2 ≤ s.cnt ∧ (∀ f, (recN h s R).mem f → idOf loc h s ≤ loc f) ∧
  (∀ f, (recN h s R).mem f → loc f ≠ idOf loc h s → (loc f, recN h s R) ∈ confN s R) ∧
  ∀ D, (recN h s R, D) ∉ decs0 s R

/-- A suitable decision. -/
def Suit (B : Spec (LInp loc) (PSet (Nat × Out))) (h : PSet F) (s : QSt F Out)
    (R : List (QMsg F Out)) (D : PSet (Nat × Out)) : Prop :=
  B.P ⟨recN h s R⟩ D ∧ ∀ e ∈ decs0 s R, e.2 ≼ D

noncomputable def nxt (h : PSet F) (s : QSt F Out) (R : List (QMsg F Out))
    (d : Option (PSet (Nat × Out))) : QSt F Out :=
  ⟨some (idOf loc h s), recN h s R, decs0 s R ++ (d.map (fun D => (recN h s R, D))).toList,
    confN s R, s.cnt + 1⟩

/-- Allowed decision choices. -/
def Ok (B : Spec (LInp loc) (PSet (Nat × Out))) (h : PSet F) (s : QSt F Out)
    (R : List (QMsg F Out)) : Option (PSet (Nat × Out)) → Prop
  | none => ¬ (Cond loc h s R ∧ ∃ D, Suit loc B h s R D)
  | some D => Cond loc h s R ∧ Suit loc B h s R D

end Q

/-- The output of a state: the facts at its own node of every known decision. -/
def qOut (s : QSt F Out) : PSet Out :=
  ⟨fun a => ∃ i, s.me = some i ∧ ∃ e ∈ s.decs, e.2.mem (i, a)⟩

/-- **The program.** -/
noncomputable def qProg (loc : F → Nat) (B : Spec (LInp loc) (PSet (Nat × Out))) :
    Prog F (QMsg F Out) (QSt F Out) Out where
  start := QSt.start
  step h s R s' W := ∃ d, Q.Ok loc B h s R d ∧ s' = Q.nxt loc h s R d ∧
    W = [(Q.idOf loc h s, Q.recN h s R, (Q.nxt loc h s R d).decs)]
  total h s R := by
    classical
    by_cases hc : Q.Cond loc h s R ∧ ∃ D, Q.Suit loc B h s R D
    · obtain ⟨hc, D, hD⟩ := hc
      exact ⟨_, _, some D, ⟨hc, hD⟩, rfl, rfl⟩
    · exact ⟨_, _, none, hc, rfl, rfl⟩
  out := qOut
  mono := by
    rintro h s R s' W ⟨d, -, rfl, -⟩ a ⟨i, hi, e, he, ha⟩
    refine ⟨i, ?_, e, List.mem_append_left _ (List.mem_append_left _ he), ha⟩
    simp [Q.nxt, Q.idOf, hi]

end Prog

/-! ## Runs of the program: invariants -/

section Run

variable {F Out : Type} {loc : F → Nat} (B : Spec (LInp loc) (PSet (Nat × Out)))
  {H : PSet F} (net : Net loc H) (ρ : Nat → Tr net.N (QMsg F Out) (QSt F Out))

set_option quotPrecheck false in
local notation "SS" t:max x:max => (cfgAt (qProg loc B) ρ t).S x

theorem S_succ_self (t : Nat) : SS (t+1) (ρ t).x = (ρ t).s := upd_same _ _ _

theorem S_succ_other (t : Nat) {y : Fin net.N} (h : y ≠ (ρ t).x) : SS (t+1) y = SS t y :=
  upd_other _ _ h

theorem log_succ (t : Nat) : (cfgAt (qProg loc B) ρ (t+1)).log =
    (cfgAt (qProg loc B) ρ t).log ++ (ρ t).W.map (fun m => ((ρ t).x, m)) := rfl

theorem myId_own (y : Fin net.N) : myId loc (net.own y) = net.node y := by
  have hh : ∃ f, (net.own y).mem f := by obtain ⟨f, hf, hfl⟩ := net.net y; exact ⟨f, hf, hfl⟩
  unfold myId; rw [dite_eq_left_of_eq_true (eq_true hh)]; exact (Classical.choose_spec hh).2

theorem own_nc (y : Fin net.N) : NodeClosed loc H (net.own y) :=
  fun _ hf => ⟨hf.1, fun g hg hgl => ⟨hg, hgl.trans hf.2⟩⟩

/-- `e` was decided at step `t`. -/
def DecAt (t : Nat) (e : QDec F Out) : Prop :=
  Q.Cond loc (net.own (ρ t).x) (SS t (ρ t).x) (ρ t).R ∧
  e.1 = Q.recN (net.own (ρ t).x) (SS t (ρ t).x) (ρ t).R ∧
  Q.Suit loc B (net.own (ρ t).x) (SS t (ρ t).x) (ρ t).R e.2 ∧
  e ∈ (SS (t+1) (ρ t).x).decs

/-- The per-node invariant. -/
structure NInv (t : Nat) (y : Fin net.N) : Prop where
  me : (SS t y).me = none ∨ (SS t y).me = some (net.node y)
  me_decs : (SS t y).me = none → (SS t y).decs = []
  nc : NodeClosed loc H (SS t y).rcd
  decs : ∀ e ∈ (SS t y).decs, e.1 ≼ (SS t y).rcd ∧ ∃ t', t' < t ∧ DecAt B net ρ t' e
  conf : ∀ p ∈ (SS t y).conf, ∃ z s, s < t ∧ net.node z = p.1 ∧ (SS (s+1) z).rcd = p.2 ∧
    ∀ e ∈ (SS (s+1) z).decs, e ∈ (SS t y).decs

/-- The log invariant: every logged message is its sender's state after the
step that sent it. -/
def LInv (t : Nat) : Prop :=
  ∀ y m, (y, m) ∈ (cfgAt (qProg loc B) ρ t).log → ∃ s, s < t ∧ (ρ s).x = y ∧
    m = (net.node y, (SS (s+1) y).rcd, (SS (s+1) y).decs)

variable (hv : ∀ t, Enabled (qProg loc B) net.own (cfgAt (qProg loc B) ρ t) (ρ t))
include hv

theorem step_at (t : Nat) : ∃ d, Q.Ok loc B (net.own (ρ t).x) (SS t (ρ t).x) (ρ t).R d ∧
    SS (t+1) (ρ t).x = Q.nxt loc (net.own (ρ t).x) (SS t (ρ t).x) (ρ t).R d ∧
    (ρ t).W = [(Q.idOf loc (net.own (ρ t).x) (SS t (ρ t).x),
      Q.recN (net.own (ρ t).x) (SS t (ρ t).x) (ρ t).R,
      (Q.nxt loc (net.own (ρ t).x) (SS t (ρ t).x) (ρ t).R d).decs)] := by
  obtain ⟨⟨d, hd, hs, hW⟩, _⟩ := hv t
  exact ⟨d, hd, by rw [S_succ_self]; exact hs, hW⟩

theorem reads_at (t : Nat) : ∀ m ∈ (ρ t).R, ∃ y, y ≠ (ρ t).x ∧
    (y, m) ∈ (cfgAt (qProg loc B) ρ t).log := (hv t).2

omit hv in
theorem idOf_eq {t : Nat} {y : Fin net.N} (h : NInv B net ρ t y) :
    Q.idOf loc (net.own y) (SS t y) = net.node y := by
  unfold Q.idOf
  rcases h.me with h' | h' <;> rw [h'] <;> simp [myId_own]

theorem inv_all : ∀ t, (∀ t', t' ≤ t → ∀ y, NInv B net ρ t' y) ∧ LInv B net ρ t := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun t' ht' y => ?_, fun y m hm => by simp [cfgAt, Cfg.start] at hm⟩
    obtain rfl : t' = 0 := by omega
    exact ⟨Or.inl rfl, fun _ => rfl, fun f hf => hf.elim, fun e he => by simp [cfgAt, Cfg.start, qProg, QSt.start] at he,
      fun p hp => by simp [cfgAt, Cfg.start, qProg, QSt.start] at hp⟩
  | succ t ih =>
    obtain ⟨hN, hL⟩ := ih
    obtain ⟨d, hd, hS, hW⟩ := step_at B net ρ hv t
    have hNx := hN t (Nat.le_refl _) (ρ t).x
    -- the messages read
    have hR : ∀ m ∈ (ρ t).R, ∃ z s, s < t ∧ NInv B net ρ (s+1) z ∧
        m = (net.node z, (SS (s+1) z).rcd, (SS (s+1) z).decs) := by
      intro m hm
      obtain ⟨z, _, hz⟩ := reads_at B net ρ hv t m hm
      obtain ⟨s, hs, hsx, rfl⟩ := hL z m hz
      exact ⟨z, s, hs, hN (s+1) (by omega) z, rfl⟩
    have hNt1 : ∀ y, NInv B net ρ (t+1) y := by
      intro y
      by_cases hy : y = (ρ t).x
      · rw [hy]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [hS]
        · exact Or.inr (by simp [Q.nxt, idOf_eq B net ρ hNx])
        · exact fun h => by simp [Q.nxt] at h
        · -- node-closed record
          rintro f (hf | hf | ⟨m, hm, hf⟩)
          · obtain ⟨h1, h2⟩ := hNx.nc f hf
            exact ⟨h1, fun g hg hgl => Or.inl (h2 g hg hgl)⟩
          · obtain ⟨h1, h2⟩ := own_nc net _ f hf
            exact ⟨h1, fun g hg hgl => Or.inr (Or.inl (h2 g hg hgl))⟩
          · obtain ⟨z, s, _, hz, rfl⟩ := hR m hm
            obtain ⟨h1, h2⟩ := hz.nc f hf
            exact ⟨h1, fun g hg hgl => Or.inr (Or.inr ⟨_, hm, h2 g hg hgl⟩)⟩
        · -- decisions
          intro e he
          simp only [Q.nxt, Q.decs0, List.mem_append, List.mem_flatMap] at he
          rcases he with (he | ⟨m, hm, he⟩) | he
          · obtain ⟨h1, t', ht', h2⟩ := hNx.decs e he
            exact ⟨fun f hf => Or.inl (h1 f hf), t', by omega, h2⟩
          · obtain ⟨z, s, hs, hz, rfl⟩ := hR m hm
            obtain ⟨h1, t', ht', h2⟩ := hz.decs e he
            exact ⟨fun f hf => Or.inr (Or.inr ⟨_, hm, h1 f hf⟩), t', by omega, h2⟩
          · cases d with
            | none => simp at he
            | some D =>
              simp at he; subst he
              refine ⟨fun f hf => hf, t, by omega, hd.1, rfl, hd.2, ?_⟩
              rw [hS]; simp [Q.nxt]
        · -- confirmations
          intro p hp
          simp only [Q.nxt, Q.confN, List.mem_append, List.mem_map] at hp
          rcases hp with hp | ⟨m, hm, rfl⟩
          · obtain ⟨z, s, hs, h1, h2, h3⟩ := hNx.conf p hp
            exact ⟨z, s, by omega, h1, h2, fun e he => by
              simp only [Q.nxt, Q.decs0, List.mem_append]; exact Or.inl (Or.inl (h3 e he))⟩
          · obtain ⟨z, s, hs, _, rfl⟩ := hR m hm
            exact ⟨z, s, by omega, rfl, rfl, fun e he => by
              simp only [Q.nxt, Q.decs0, List.mem_append, List.mem_flatMap]
              exact Or.inl (Or.inr ⟨_, hm, he⟩)⟩
      · have hNy := hN t (Nat.le_refl _) y
        have hSy := S_succ_other B net ρ t hy
        refine ⟨?_, ?_, ?_, fun e he => ?_, fun p hp => ?_⟩
        · rw [hSy]; exact hNy.me
        · rw [hSy]; exact hNy.me_decs
        · rw [hSy]; exact hNy.nc
        · rw [hSy] at he ⊢
          obtain ⟨h1, t', ht', h2⟩ := hNy.decs e he
          exact ⟨h1, t', by omega, h2⟩
        · rw [hSy] at hp ⊢
          obtain ⟨z, s, hs, h1, h2, h3⟩ := hNy.conf p hp
          exact ⟨z, s, by omega, h1, h2, h3⟩
    refine ⟨fun t' ht' y => ?_, fun y m hm => ?_⟩
    · rcases Nat.lt_or_ge t' (t+1) with h | h
      · exact hN t' (by omega) y
      · obtain rfl : t' = t + 1 := by omega
        exact hNt1 y
    · rw [log_succ, hW] at hm
      rcases List.mem_append.1 hm with hm | hm
      · obtain ⟨s, hs, h1, h2⟩ := hL y m hm
        exact ⟨s, by omega, h1, h2⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        refine ⟨t, by omega, rfl, ?_⟩
        rw [hS, idOf_eq B net ρ hNx]; rfl

theorem ninv (t : Nat) (y : Fin net.N) : NInv B net ρ t y := (inv_all B net ρ hv t).1 t (Nat.le_refl _) y

theorem linv (t : Nat) : LInv B net ρ t := (inv_all B net ρ hv t).2

theorem S_succ_cases (t : Nat) (y : Fin net.N) : SS (t+1) y = SS t y ∨
    (y = (ρ t).x ∧ ∃ d, SS (t+1) y = Q.nxt loc (net.own y) (SS t y) (ρ t).R d) := by
  by_cases hy : y = (ρ t).x
  · subst hy
    obtain ⟨d, _, hS, _⟩ := step_at B net ρ hv t
    exact Or.inr ⟨rfl, d, hS⟩
  · exact Or.inl (S_succ_other B net ρ t hy)

theorem rcd_mono {t t' : Nat} (h : t ≤ t') (y : Fin net.N) : (SS t y).rcd ≼ (SS t' y).rcd := by
  induction h with
  | refl => exact PO.refl _
  | @step t' _ ih =>
    refine PO.trans ih ?_
    rcases S_succ_cases B net ρ hv t' y with h | ⟨_, d, h⟩
    · rw [h]; exact PO.refl _
    · rw [h]; exact fun f hf => Or.inl hf

theorem decs_mono {t t' : Nat} (h : t ≤ t') (y : Fin net.N) {e : QDec F Out}
    (he : e ∈ (SS t y).decs) : e ∈ (SS t' y).decs := by
  induction h with
  | refl => exact he
  | @step t' _ ih =>
    rcases S_succ_cases B net ρ hv t' y with h | ⟨_, d, h⟩
    · rw [h]; exact ih
    · rw [h]; simp only [Q.nxt, Q.decs0, List.mem_append]; exact Or.inl (Or.inl ih)

theorem conf_mono {t t' : Nat} (h : t ≤ t') (y : Fin net.N) {p : Nat × PSet F}
    (hp : p ∈ (SS t y).conf) : p ∈ (SS t' y).conf := by
  induction h with
  | refl => exact hp
  | @step t' _ ih =>
    rcases S_succ_cases B net ρ hv t' y with h | ⟨_, d, h⟩
    · rw [h]; exact ih
    · rw [h]; simp only [Q.nxt, Q.confN, List.mem_append]; exact Or.inl ih

theorem cnt_mono {t t' : Nat} (h : t ≤ t') (y : Fin net.N) : (SS t y).cnt ≤ (SS t' y).cnt := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step t' _ ih =>
    rcases S_succ_cases B net ρ hv t' y with h | ⟨_, d, h⟩
    · rw [h]; exact ih
    · rw [h]; simp only [Q.nxt]; omega

/-! ### Decisions -/

theorem dec_facts {t : Nat} {e : QDec F Out} (h : DecAt B net ρ t e) :
    (SS (t+1) (ρ t).x).rcd = e.1 ∧ (∀ f, e.1.mem f → net.node (ρ t).x ≤ loc f) ∧
    net.own (ρ t).x ≼ e.1 ∧ NodeClosed loc H e.1 ∧ B.P ⟨e.1⟩ e.2 := by
  obtain ⟨hc, h1, hsu, _⟩ := h
  obtain ⟨d, _, hS, _⟩ := step_at B net ρ hv t
  have hrcd : (SS (t+1) (ρ t).x).rcd = e.1 := by rw [hS, h1]; rfl
  have hid := idOf_eq B net ρ (ninv B net ρ hv t (ρ t).x)
  refine ⟨hrcd, fun f hf => ?_, fun f hf => by rw [h1]; exact Or.inr (Or.inl hf), ?_, ?_⟩
  · rw [← hid]; exact hc.2.1 f (h1 ▸ hf)
  · rw [← hrcd]; exact (ninv B net ρ hv (t+1) (ρ t).x).nc
  · rw [h1]; exact hsu.1

theorem dec_ne {t : Nat} {e : QDec F Out} (h : DecAt B net ρ t e) : ∃ f, e.1.mem f := by
  obtain ⟨f, hf, hfl⟩ := net.net (ρ t).x
  exact ⟨f, (dec_facts B net ρ hv h).2.2.1 f ⟨hf, hfl⟩⟩

theorem dec_node {t : Nat} {e : QDec F Out} (h : DecAt B net ρ t e) :
    Netw loc e.1 (net.node (ρ t).x) := by
  obtain ⟨f, hf, hfl⟩ := net.net (ρ t).x
  exact ⟨f, (dec_facts B net ρ hv h).2.2.1 f ⟨hf, hfl⟩, hfl⟩

/-- Every node of a decided quorum had that record at some time. -/
theorem had_rec {t : Nat} {e : QDec F Out} (h : DecAt B net ρ t e) :
    ∀ z, Netw loc e.1 z → ∃ y t', net.node y = z ∧ (SS t' y).rcd = e.1 := by
  intro z ⟨f, hf, hfl⟩
  have hfacts := dec_facts B net ρ hv h
  by_cases hz : z = net.node (ρ t).x
  · exact ⟨(ρ t).x, t+1, hz.symm, hfacts.1⟩
  · obtain ⟨hc, h1, _, _⟩ := h
    obtain ⟨d, _, hS, _⟩ := step_at B net ρ hv t
    have hid := idOf_eq B net ρ (ninv B net ρ hv t (ρ t).x)
    have hconf := hc.2.2.1 f (h1 ▸ hf) (by rw [hid, hfl]; exact hz)
    have : (loc f, e.1) ∈ (SS (t+1) (ρ t).x).conf := by rw [hS, h1]; exact hconf
    obtain ⟨y, s, _, hy, hr, _⟩ := (ninv B net ρ hv (t+1) (ρ t).x).conf _ this
    exact ⟨y, s+1, hy.trans hfl, hr⟩

theorem dec_lam {t t' : Nat} {e e' : QDec F Out} (h : DecAt B net ρ t e)
    (h' : DecAt B net ρ t' e') : Lam loc e.1 e'.1 := by
  by_cases hz : ∃ z, Netw loc e.1 z ∧ Netw loc e'.1 z
  · obtain ⟨z, hz1, hz2⟩ := hz
    obtain ⟨y, s, hy, hs⟩ := had_rec B net ρ hv h z hz1
    obtain ⟨y', s', hy', hs'⟩ := had_rec B net ρ hv h' z hz2
    obtain rfl : y = y' := net.inj _ _ (hy.trans hy'.symm)
    rcases Nat.le_total s s' with hle | hle
    · exact Or.inl (hs ▸ hs' ▸ rcd_mono B net ρ hv hle y)
    · exact Or.inr (Or.inl (hs ▸ hs' ▸ rcd_mono B net ρ hv hle y))
  · exact Or.inr (Or.inr fun z h1 h2 => hz ⟨z, h1, h2⟩)

theorem dec_new {t : Nat} {e : QDec F Out} (h : DecAt B net ρ t e) :
    (SS (t+1) (ρ t).x).decs = Q.decs0 (SS t (ρ t).x) (ρ t).R ++ [e] := by
  obtain ⟨hc, h1, _, hm⟩ := h
  obtain ⟨d, _, hS, _⟩ := step_at B net ρ hv t
  rw [hS] at hm ⊢
  simp only [Q.nxt] at hm ⊢
  rcases List.mem_append.1 hm with hm | hm
  · exact absurd (by rw [← h1]; exact hm) (hc.2.2.2 e.2)
  · cases d with
    | none => simp at hm
    | some D => simp at hm ⊢; rw [hm]

theorem dec_same_time {t : Nat} {e e' : QDec F Out} (h : DecAt B net ρ t e)
    (h' : DecAt B net ρ t e') : e = e' := by
  have h1 := dec_new B net ρ hv h
  have h2 := dec_new B net ρ hv h'
  rw [h1] at h2
  have := List.append_cancel_left h2
  simpa using this

theorem dec_decider {t t' : Nat} {e e' : QDec F Out} (h : DecAt B net ρ t e)
    (h' : DecAt B net ρ t' e') (heq : e.1 = e'.1) : (ρ t).x = (ρ t').x := by
  have a := (dec_facts B net ρ hv h).2.1
  have a' := (dec_facts B net ρ hv h').2.1
  obtain ⟨f, hf, hfl⟩ := dec_node B net ρ hv h
  obtain ⟨f', hf', hfl'⟩ := dec_node B net ρ hv h'
  have h1 := a f' (heq ▸ hf')
  have h2 := a' f (heq ▸ hf)
  rw [hfl'] at h1; rw [hfl] at h2
  exact net.inj _ _ (Nat.le_antisymm h1 h2)

/-- A quorum is decided at most once. -/
theorem dec_once {t t' : Nat} {e e' : QDec F Out} (h : DecAt B net ρ t e)
    (h' : DecAt B net ρ t' e') (heq : e.1 = e'.1) : e = e' := by
  have hx := dec_decider B net ρ hv h h' heq
  have key : ∀ {t t' : Nat} {e e' : QDec F Out}, DecAt B net ρ t e → DecAt B net ρ t' e' →
      e.1 = e'.1 → (ρ t).x = (ρ t').x → ¬ t < t' := by
    intro t t' e e' h h' heq hx hlt
    have hm := decs_mono B net ρ hv (show t + 1 ≤ t' by omega) (ρ t).x h.2.2.2
    rw [hx] at hm
    obtain ⟨hc', h1', _, _⟩ := h'
    apply hc'.2.2.2 e.2
    rw [← h1', ← heq]
    exact List.mem_append_left _ hm
  rcases Nat.lt_trichotomy t t' with hlt | rfl | hlt
  · exact absurd hlt (key h h' heq hx)
  · exact dec_same_time B net ρ hv h h'
  · exact absurd hlt (key h' h heq.symm hx.symm)

/-- Decisions are monotone: a decided sub-quorum's decision lies below. -/
theorem dec_mono {t t' : Nat} {e e' : QDec F Out} (h : DecAt B net ρ t e)
    (h' : DecAt B net ρ t' e') (hle : e'.1 ≼ e.1) : e'.2 ≼ e.2 := by
  by_cases heq : e'.1 = e.1
  · rw [dec_once B net ρ hv h' h heq]; exact PO.refl _
  have hsu := h.2.2.1
  apply hsu.2
  -- `e'` is known to `e`'s decider
  have hfx := dec_facts B net ρ hv h
  have hfw := dec_facts B net ρ hv h'
  have hnew := dec_new B net ρ hv h
  suffices hin : e' ∈ (SS (t+1) (ρ t).x).decs by
    rw [hnew] at hin
    rcases List.mem_append.1 hin with hin | hin
    · exact hin
    · simp at hin; subst hin; exact absurd rfl heq
  by_cases hw : (ρ t').x = (ρ t).x
  · rcases Nat.lt_or_ge t' t with hlt | hge
    · have := decs_mono B net ρ hv (show t' + 1 ≤ t + 1 by omega) (ρ t').x h'.2.2.2
      rw [hw] at this; exact this
    · have := rcd_mono B net ρ hv (show t + 1 ≤ t' + 1 by omega) (ρ t).x
      rw [← hw, hfw.1] at this
      rw [hw, hfx.1] at this
      exact absurd (PO.antisymm hle this) heq
  · obtain ⟨f, hf, hfl⟩ := dec_node B net ρ hv h'
    have hid := idOf_eq B net ρ (ninv B net ρ hv t (ρ t).x)
    obtain ⟨hc, h1, _, _⟩ := h
    obtain ⟨d, _, hS, _⟩ := step_at B net ρ hv t
    have hfI : (Q.recN (net.own (ρ t).x) (SS t (ρ t).x) (ρ t).R).mem f := h1 ▸ hle f hf
    have hconf := hc.2.2.1 f hfI (by
      rw [hid, hfl]; exact fun hn => hw (net.inj _ _ hn))
    have : (loc f, e.1) ∈ (SS (t+1) (ρ t).x).conf := by rw [hS, h1]; exact hconf
    obtain ⟨z, s, _, hz, hr, hsub⟩ := (ninv B net ρ hv (t+1) (ρ t).x).conf _ this
    obtain rfl : z = (ρ t').x := net.inj _ _ (hz.trans hfl)
    rcases Nat.lt_or_ge t' s with hlt | hge
    · exact hsub e' (decs_mono B net ρ hv (show t' + 1 ≤ s + 1 by omega) _ h'.2.2.2)
    · have := rcd_mono B net ρ hv (show s + 1 ≤ t' + 1 by omega) (ρ t').x
      rw [hr, hfw.1] at this
      exact absurd (PO.antisymm hle this) heq

end Run

/-! ## Liveness: every fair run computes `B` -/

theorem finNet_of_net {F : Type} {loc : F → Nat} {H : PSet F} (net : Net loc H) : FinNet loc H := by
  refine ⟨(List.finRange net.N).map net.node, ?_, fun x => ?_⟩
  · exact List.Pairwise.map net.node (fun a b hab h => hab (net.inj a b h)) (List.nodup_finRange net.N)
  · simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨y, rfl⟩; exact net.net y
    · rintro ⟨f, hf, rfl⟩; obtain ⟨y, hy⟩ := net.cover f hf; exact ⟨y, hy⟩

theorem exists_min_list {n : Nat} (g : Fin n → Nat) :
    ∀ l : List (Fin n), l ≠ [] → ∃ m ∈ l, ∀ y ∈ l, g m ≤ g y
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, fun y hy => by simp at hy; subst hy; exact Nat.le_refl _⟩
  | a :: b :: l, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_min_list g (b :: l) (by simp)
    by_cases h : g a ≤ g m
    · exact ⟨a, by simp, fun y hy => by
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Nat.le_refl _
        · exact Nat.le_trans h (hmin y hy)⟩
    · exact ⟨m, List.mem_cons_of_mem _ hm, fun y hy => by
        rcases List.mem_cons.1 hy with rfl | hy
        · omega
        · exact hmin y hy⟩

section Live

variable {F Out : Type} {loc : F → Nat} (B : Spec (LInp loc) (PSet (Nat × Out)))
  {H : PSet F} (net : Net loc H) (ρ : Nat → Tr net.N (QMsg F Out) (QSt F Out))

set_option quotPrecheck false in
local notation "SS" t:max x:max => (cfgAt (qProg loc B) ρ t).S x

variable (hf : FairRun (qProg loc B) net.own ρ)
include hf

/-- A message sent at step `t` is read by every other node at some later step. -/
theorem sent_read (t : Nat) (y : Fin net.N) (hy : y ≠ (ρ t).x) :
    ∃ t', t + 1 ≤ t' ∧ (ρ t').x = y ∧
      (Q.idOf loc (net.own (ρ t).x) (SS t (ρ t).x), (SS (t+1) (ρ t).x).rcd,
        (SS (t+1) (ρ t).x).decs) ∈ (ρ t').R := by
  obtain ⟨d, _, hS, hW⟩ := step_at B net ρ hf.valid t
  have hlog : ((ρ t).x, (Q.idOf loc (net.own (ρ t).x) (SS t (ρ t).x), (SS (t+1) (ρ t).x).rcd,
      (SS (t+1) (ρ t).x).decs)) ∈ (cfgAt (qProg loc B) ρ (t+1)).log := by
    rw [log_succ, hW, hS]; simp [Q.nxt]
  obtain ⟨t', ht', hx, hm⟩ := hf.reads (t+1) _ _ y hlog (fun h => hy h.symm)
  exact ⟨t', ht', hx, hm⟩

/-- What a node has after reading a message. -/
theorem after_read {t : Nat} {m : QMsg F Out} (hm : m ∈ (ρ t).R) :
    m.2.1 ≼ (SS (t+1) (ρ t).x).rcd ∧ (∀ e ∈ m.2.2, e ∈ (SS (t+1) (ρ t).x).decs) ∧
      (m.1, m.2.1) ∈ (SS (t+1) (ρ t).x).conf := by
  obtain ⟨d, _, hS, _⟩ := step_at B net ρ hf.valid t
  rw [hS]
  refine ⟨fun f hf' => Or.inr (Or.inr ⟨m, hm, hf'⟩), fun e he => ?_, ?_⟩
  · simp only [Q.nxt, Q.decs0, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨m, hm, he⟩)
  · simp only [Q.nxt, Q.confN, List.mem_append, List.mem_map]
    exact Or.inr ⟨m, hm, rfl⟩

theorem own_eventually (x y : Fin net.N) : ∃ T, net.own y ≼ (SS T x).rcd := by
  obtain ⟨t0, _, hx0⟩ := hf.active y 0
  obtain ⟨d, _, hS, _⟩ := step_at B net ρ hf.valid t0
  have hown : net.own y ≼ (SS (t0+1) (ρ t0).x).rcd := by
    rw [hS]; intro f hf'; rw [hx0] at *; exact Or.inr (Or.inl hf')
  by_cases hxy : x = y
  · subst hxy; rw [hx0] at hown; exact ⟨t0+1, hown⟩
  · obtain ⟨t', _, hx', hm⟩ := sent_read B net ρ hf t0 x (by rw [hx0]; exact hxy)
    have := (after_read B net ρ hf hm).1
    rw [hx'] at this
    exact ⟨t'+1, PO.trans hown this⟩

theorem rcd_full : ∃ T0, ∀ t, T0 ≤ t → ∀ x, (SS t x).rcd = H := by
  have hT : ∀ x y, ∃ T, net.own y ≼ (SS T x).rcd := own_eventually B net ρ hf
  let T := fun x y => Classical.choose (hT x y)
  have hTs : ∀ x y, net.own y ≼ (SS (T x y) x).rcd := fun x y => Classical.choose_spec (hT x y)
  have hbx : ∀ x, ∃ b, ∀ y, T x y < b := fun x => exists_bound (T x)
  let bx := fun x => Classical.choose (hbx x)
  obtain ⟨T0, hT0⟩ := exists_bound bx
  refine ⟨T0, fun t ht x => PO.antisymm (fun f hf' => ((ninv B net ρ hf.valid t x).nc f hf').1) ?_⟩
  intro f hfH
  obtain ⟨y, hy⟩ := net.cover f hfH
  have h1 := hTs x y f ⟨hfH, hy.symm⟩
  have h2 : T x y ≤ t := by
    have := Classical.choose_spec (hbx x) y
    have := hT0 x
    simp only [bx] at *
    omega
  exact rcd_mono B net ρ hf.valid h2 x f h1

theorem exists_min_node : ∃ m : Fin net.N, ∀ y, net.node m ≤ net.node y := by
  have hpos : 0 < net.N := (ρ 0).x.pos
  obtain ⟨m, _, hm⟩ := exists_min_list net.node (List.finRange net.N)
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hpos⟩))
  exact ⟨m, fun y => hm y (List.mem_finRange y)⟩

theorem cnt_eventually (x : Fin net.N) : ∃ T, 2 ≤ (SS T x).cnt := by
  have hstep : ∀ t, (ρ t).x = x → (SS (t+1) x).cnt = (SS t x).cnt + 1 := by
    intro t hx
    obtain ⟨d, _, hS, _⟩ := step_at B net ρ hf.valid t
    rw [hx] at hS; rw [hS]; rfl
  obtain ⟨t1, _, h1⟩ := hf.active x 0
  obtain ⟨t2, h2t, h2⟩ := hf.active x (t1+1)
  refine ⟨t2+1, ?_⟩
  have a := hstep t1 h1
  have b := hstep t2 h2
  have c := cnt_mono B net ρ hf.valid h2t x
  omega

theorem conf_eventually {T0 : Nat} (hT0 : ∀ t, T0 ≤ t → ∀ x, (SS t x).rcd = H) (m y : Fin net.N)
    (hy : y ≠ m) : ∃ T, (net.node y, H) ∈ (SS T m).conf := by
  obtain ⟨t, ht, hx⟩ := hf.active y T0
  obtain ⟨t', _, hx', hm⟩ := sent_read B net ρ hf t m (by rw [hx]; exact fun h => hy h.symm)
  have := (after_read B net ρ hf hm).2.2
  rw [hx'] at this
  rw [idOf_eq B net ρ (ninv B net ρ hf.valid t _), hx, hT0 (t+1) (by omega)] at this
  exact ⟨t'+1, this⟩

variable (hB : NodeMonoFin loc B)
include hB

/-- The whole instance is eventually decided. -/
theorem full_decided : ∃ t e, DecAt B net ρ t e ∧ e.1 = H := by
  classical
  have hv := hf.valid
  obtain ⟨T0, hT0⟩ := rcd_full B net ρ hf
  obtain ⟨m, hm⟩ := exists_min_node B net ρ hf
  have hc : ∀ y, ∃ T, y ≠ m → (net.node y, H) ∈ (SS T m).conf := fun y =>
    if h : y = m then ⟨0, fun h' => absurd h h'⟩ else
      let ⟨T, hT⟩ := conf_eventually B net ρ hf hT0 m y h; ⟨T, fun _ => hT⟩
  let Tc := fun y => Classical.choose (hc y)
  obtain ⟨Bc, hBc⟩ := exists_bound Tc
  obtain ⟨Tn, hTn⟩ := cnt_eventually B net ρ hf m
  obtain ⟨t, ht, hx⟩ := hf.active m (T0 + Bc + Tn)
  obtain ⟨d, hd, hS, _⟩ := step_at B net ρ hv t
  let I := Q.recN (net.own (ρ t).x) (SS t (ρ t).x) (ρ t).R
  have hI : I = H := by
    have : (SS (t+1) (ρ t).x).rcd = I := by rw [hS]; rfl
    rw [← this]; exact hT0 (t+1) (by omega) _
  have hid := idOf_eq B net ρ (ninv B net ρ hv t (ρ t).x)
  rw [hx] at hid
  by_cases hdec : ∃ D, (I, D) ∈ Q.decs0 (SS t (ρ t).x) (ρ t).R
  · obtain ⟨D, hD⟩ := hdec
    have hin : (I, D) ∈ (SS (t+1) (ρ t).x).decs := by
      rw [hS]; exact List.mem_append_left _ hD
    obtain ⟨_, t', _, h'⟩ := (ninv B net ρ hv (t+1) _).decs _ hin
    exact ⟨t', _, h', hI⟩
  · have hcond : Q.Cond loc (net.own (ρ t).x) (SS t (ρ t).x) (ρ t).R := by
      refine ⟨?_, fun f hfI => ?_, fun f hfI hne => ?_, fun D hD => hdec ⟨D, hD⟩⟩
      · have := cnt_mono B net ρ hv (show Tn ≤ t by omega) m
        rw [hx]; omega
      · rw [hx, hid]
        have hfH : H.mem f := hI ▸ hfI
        obtain ⟨y, hy⟩ := net.cover f hfH
        rw [← hy]; exact hm y
      · have hfH : H.mem f := hI ▸ hfI
        obtain ⟨y, hy⟩ := net.cover f hfH
        have hym : y ≠ m := fun h => by rw [hx, hid, ← hy, h] at hne; exact hne rfl
        have h1 := Classical.choose_spec (hc y) hym
        have h2 : Tc y ≤ t := by have := hBc y; simp only [Tc] at *; omega
        have h3 := conf_mono B net ρ hv h2 m h1
        rw [← hx] at h3
        rw [← hy]
        show (net.node y, I) ∈ _
        rw [hI]
        exact List.mem_append_left _ h3
    have hsuit : ∃ D, Q.Suit loc B (net.own (ρ t).x) (SS t (ρ t).x) (ρ t).R D := by
      have hsub : ∀ e ∈ Q.decs0 (SS t (ρ t).x) (ρ t).R, e ∈ (SS (t+1) (ρ t).x).decs := by
        intro e he; rw [hS]; exact List.mem_append_left _ he
      have hdecs : ∀ e ∈ Q.decs0 (SS t (ρ t).x) (ρ t).R, e.1 ≼ I ∧ ∃ t', DecAt B net ρ t' e := by
        intro e he
        obtain ⟨h1, t', _, h2⟩ := (ninv B net ρ hv (t+1) _).decs e (hsub e he)
        have : (SS (t+1) (ρ t).x).rcd = I := by rw [hS]; rfl
        exact ⟨this ▸ h1, t', h2⟩
      obtain ⟨D, hD, hDall⟩ := suitable hB (finNet_of_net net) (G := H) (I := I)
        (by rw [hI]; exact fun f hf' => ⟨hf', fun g hg _ => hg⟩)
        (by obtain ⟨f, hf', hfl⟩ := net.net (ρ t).x; exact ⟨f, Or.inr (Or.inl ⟨hf', hfl⟩)⟩)
        (Q.decs0 (SS t (ρ t).x) (ρ t).R)
        (fun e he => by
          obtain ⟨h1, t', h2⟩ := hdecs e he
          have hf2 := dec_facts B net ρ hv h2
          exact ⟨hf2.2.2.2.1, dec_ne B net ρ hv h2, hf2.2.2.2.2, h1⟩)
        (fun e he e' he' => by
          obtain ⟨_, _, h2⟩ := hdecs e he
          obtain ⟨_, _, h2'⟩ := hdecs e' he'
          exact dec_lam B net ρ hv h2 h2')
        (fun e he e' he' hle => by
          obtain ⟨_, _, h2⟩ := hdecs e he
          obtain ⟨_, _, h2'⟩ := hdecs e' he'
          exact dec_mono B net ρ hv h2' h2 hle)
      exact ⟨D, hD, hDall⟩
    cases d with
    | none => exact absurd ⟨hcond, hsuit⟩ hd
    | some D =>
      refine ⟨t, (I, D), ⟨hcond, rfl, hd.2, ?_⟩, hI⟩
      rw [hS]; simp [Q.nxt, I]

omit hB in
/-- Every node eventually knows a given decision. -/
theorem adopt {t2 : Nat} {e : QDec F Out} (h : DecAt B net ρ t2 e) (y : Fin net.N) :
    ∃ T, e ∈ (SS T y).decs := by
  have hv := hf.valid
  by_cases hy : y = (ρ t2).x
  · rw [hy]; exact ⟨t2+1, h.2.2.2⟩
  · obtain ⟨t, ht, hx⟩ := hf.active (ρ t2).x (t2+1)
    have hm := decs_mono B net ρ hv (show t2 + 1 ≤ t + 1 by omega) _ h.2.2.2
    rw [← hx] at hm
    obtain ⟨t', _, hx', hr⟩ := sent_read B net ρ hf t y (by rw [hx]; exact hy)
    have := (after_read B net ρ hf hr).2.1 e hm
    rw [hx'] at this
    exact ⟨t'+1, this⟩

/-- **Every fair run of `qProg B` decides the whole instance once, and its
output is eventually that decision.** -/
theorem computes_strong (hLoc : LocatedFin loc B) :
    ∃ t2 e, DecAt B net ρ t2 e ∧ e.1 = H ∧ ∃ T, ∀ t, T ≤ t → dout (qProg loc B) net.node
      (cfgAt (qProg loc B) ρ t) = e.2 := by
  classical
  have hv := hf.valid
  obtain ⟨t2, e, he, heH⟩ := full_decided B net ρ hf hB
  refine ⟨t2, e, he, heH, ?_⟩
  have ha : ∀ y, ∃ T, e ∈ (SS T y).decs := adopt B net ρ hf he
  let Ta := fun y => Classical.choose (ha y)
  obtain ⟨T3, hT3⟩ := exists_bound Ta
  refine ⟨T3, fun t ht => ?_⟩
  have hin : ∀ y, e ∈ (SS t y).decs := fun y =>
    decs_mono B net ρ hv (show Ta y ≤ t by have := hT3 y; omega) y (Classical.choose_spec (ha y))
  have hme : ∀ y, (SS t y).me = some (net.node y) := fun y => by
    rcases (ninv B net ρ hv t y).me with h | h
    · have := (ninv B net ρ hv t y).me_decs h
      have := hin y; simp_all
    · exact h
  have hBH : B.P ⟨H⟩ e.2 := heH ▸ (dec_facts B net ρ hv he).2.2.2.2
  have hfin := finNet_of_net net
  have hne : ∃ f, H.mem f := by
    obtain ⟨f, hf', _⟩ := net.net (ρ 0).x; exact ⟨f, hf'⟩
  apply pset_ext
  intro z
  constructor
  · rintro ⟨x, hzx, i, hi, e', he', hz⟩
    rw [hme x] at hi; cases hi
    obtain ⟨h1, t', _, h2⟩ := (ninv B net ρ hv t x).decs e' he'
    have hle : e'.1 ≼ e.1 := by
      rw [heH]; exact PO.trans h1 (fun f hf' => ((ninv B net ρ hv t x).nc f hf').1)
    have := dec_mono B net ρ hv he h2 hle _ hz
    rw [← hzx] at this; exact this
  · intro hz
    obtain ⟨f, hf', hfl⟩ := hLoc H e.2 hfin hne hBH z hz
    obtain ⟨x, hx⟩ := net.cover f hf'
    refine ⟨x, (hx.trans hfl).symm, net.node x, hme x, e, hin x, ?_⟩
    have : (net.node x, z.2) = z := by rw [hx, hfl]
    rw [this]; exact hz

omit hf in
theorem computes_qProg (hLoc : LocatedFin loc B) : Computes (qProg loc B) B := by
  intro H net ρ hfair
  obtain ⟨t2, e, he, heH, T, hT⟩ := computes_strong B net ρ hfair hB hLoc
  refine ⟨T, fun t ht => by rw [hT t ht, hT T (Nat.le_refl _)], ?_⟩
  rw [hT T (Nat.le_refl _), ← heH]
  exact (dec_facts B net ρ hfair.valid he).2.2.2.2

end Live

/-! ## A run reaching a given row -/

section Round

variable {F Msg St Out : Type} {Pg : Prog F Msg St Out} {N : Nat}

/-- One round: distinct nodes each take one transition from the current
configuration. -/
theorem seq_round (own : Fin N → PSet F) (f : Fin N → Tr N Msg St) (hfx : ∀ x, (f x).x = x) :
    ∀ (l : List (Fin N)) (c : Cfg N Msg St), l.Nodup →
    (∀ x ∈ l, Pg.step (own x) (c.S x) (f x).R (f x).s (f x).W ∧
      ∀ m ∈ (f x).R, ∃ y, y ≠ x ∧ (y, m) ∈ c.log) →
    SeqOK Pg own c (l.map f) ∧
    (∀ x, (seqCfg c (l.map f)).S x = if x ∈ l then (f x).s else c.S x) ∧
    (∀ e, e ∈ c.log → e ∈ (seqCfg c (l.map f)).log) ∧
    (∀ x ∈ l, ∀ m ∈ (f x).W, (x, m) ∈ (seqCfg c (l.map f)).log) := by
  intro l
  induction l with
  | nil => intro c _ _; exact ⟨trivial, fun x => by simp [seqCfg], fun e he => he, by simp⟩
  | cons x l ih =>
    intro c hnd hok
    have hx : x ∉ l := (List.nodup_cons.1 hnd).1
    have hl : l.Nodup := (List.nodup_cons.1 hnd).2
    let c' := c.apply (f x)
    have hS' : ∀ y, y ≠ x → c'.S y = c.S y := fun y hy => by
      show upd c.S (f x).x (f x).s y = c.S y
      rw [upd_other _ _ (by rw [hfx]; exact hy)]
    have hlog' : ∀ e, e ∈ c.log → e ∈ c'.log := fun e he => List.mem_append_left _ he
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih c' hl (fun y hy => by
      have hyx : y ≠ x := fun h => hx (h ▸ hy)
      obtain ⟨h1, h2⟩ := hok y (List.mem_cons_of_mem _ hy)
      refine ⟨by rw [hS' y hyx]; exact h1, fun m hm => ?_⟩
      obtain ⟨z, hz, hz'⟩ := h2 m hm
      exact ⟨z, hz, hlog' _ hz'⟩)
    obtain ⟨hx1, hx2⟩ := hok x (List.mem_cons_self ..)
    refine ⟨⟨⟨by rw [hfx]; exact hx1, by rw [hfx]; exact hx2⟩, ih1⟩, fun y => ?_,
      fun e he => ih3 e (hlog' e he), fun y hy m hm => ?_⟩
    · show (seqCfg c' (l.map f)).S y = _
      rw [ih2 y]
      by_cases hyl : y ∈ l
      · simp [hyl]
      · by_cases hyx : y = x
        · subst hyx
          simp only [hyl, if_false, List.mem_cons_self, if_true]
          show upd c.S (f y).x (f y).s y = _
          rw [hfx]; exact upd_same _ _ _
        · simp only [hyl, if_false, List.mem_cons, hyx, false_or]
          exact hS' y hyx
    · rcases List.mem_cons.1 hy with rfl | hy
      · apply ih3
        show (y, m) ∈ c.log ++ (f y).W.map (fun m => ((f y).x, m))
        rw [hfx]; exact List.mem_append_right _ (List.mem_map.2 ⟨m, hm, rfl⟩)
      · exact ih4 y hy m hm

end Round

section Witness

variable {F Out : Type} {loc : F → Nat} (B : Spec (LInp loc) (PSet (Nat × Out)))
  {H : PSet F} (net : Net loc H)

/-- Round 1: every node steps without reading. -/
noncomputable def s1 (x : Fin net.N) : QSt F Out := Q.nxt loc (net.own x) QSt.start [] none
noncomputable def msg1 (x : Fin net.N) : QMsg F Out :=
  (Q.idOf loc (net.own x) (QSt.start : QSt F Out),
    Q.recN (net.own x) (QSt.start : QSt F Out) ([] : List (QMsg F Out)), (s1 (Out := Out) net x).decs)
noncomputable def R2 (x : Fin net.N) : List (QMsg F Out) :=
  ((List.finRange net.N).filter (fun y => decide (y ≠ x))).map (msg1 net)
/-- Round 2: every node reads every other node's round-1 message. -/
noncomputable def s2 (x : Fin net.N) : QSt F Out := Q.nxt loc (net.own x) (s1 (Out := Out) net x) (R2 (Out := Out) net x) none
noncomputable def msg2 (x : Fin net.N) : QMsg F Out :=
  (Q.idOf loc (net.own x) (s1 (Out := Out) net x),
    Q.recN (net.own x) (s1 (Out := Out) net x) (R2 (Out := Out) net x), (s2 (Out := Out) net x).decs)

theorem s1_decs (x : Fin net.N) : (s1 (Out := Out) net x).decs = [] := by
  simp [s1, Q.nxt, Q.decs0, QSt.start]

theorem s1_rcd (x : Fin net.N) (f : F) : (s1 (Out := Out) net x).rcd.mem f ↔ (net.own x).mem f := by
  simp [s1, Q.nxt, Q.recN, QSt.start]

theorem idOf_start (x : Fin net.N) : Q.idOf loc (net.own x) (QSt.start : QSt F Out) = net.node x := by
  unfold Q.idOf
  rw [show (QSt.start : QSt F Out).me = none from rfl]
  exact myId_own net x

theorem idOf_s1 (x : Fin net.N) : Q.idOf loc (net.own x) (s1 (Out := Out) net x) = net.node x := by
  unfold Q.idOf
  rw [show (s1 (Out := Out) net x).me = some (Q.idOf loc (net.own x) (QSt.start : QSt F Out)) from rfl,
    idOf_start]
  rfl

theorem s2_decs (x : Fin net.N) : (s2 (Out := Out) net x).decs = [] := by
  simp only [s2, Q.nxt, Q.decs0, s1_decs, List.nil_append, Option.map_none, Option.toList_none,
    List.append_nil, List.flatMap_eq_nil_iff, R2, List.mem_map]
  rintro m ⟨y, _, rfl⟩
  show (s1 (Out := Out) net y).decs = []
  exact s1_decs net y

theorem recN2 (x : Fin net.N) (f : F) :
    (Q.recN (net.own x) (s1 (Out := Out) net x) (R2 (Out := Out) net x)).mem f ↔ H.mem f := by
  constructor
  · rintro (hf | hf | ⟨m, hm, hf⟩)
    · exact ((s1_rcd net x f).1 hf).1
    · exact hf.1
    · simp only [R2, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hm
      obtain ⟨y, _, rfl⟩ := hm
      simp only [msg1, Q.recN, QSt.start] at hf
      rcases hf with hf | hf | ⟨_, hm', _⟩
      · exact hf.elim
      · exact hf.1
      · simp at hm'
  · intro hf
    obtain ⟨y, hy⟩ := net.cover f hf
    by_cases hyx : y = x
    · subst hyx; exact Or.inr (Or.inl ⟨hf, hy.symm⟩)
    · refine Or.inr (Or.inr ⟨msg1 (Out := Out) net y, ?_, ?_⟩)
      · simp only [R2, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
          decide_eq_true_eq]
        exact ⟨y, hyx, rfl⟩
      · exact Or.inr (Or.inl ⟨hf, hy.symm⟩)

theorem s2_rcd (x : Fin net.N) (f : F) : (s2 (Out := Out) net x).rcd.mem f ↔ H.mem f := by
  simp only [s2, Q.nxt]; exact recN2 net x f

/-- Round 3: the least node reads every other node's round-2 message. -/
noncomputable def R3 (m : Fin net.N) : List (QMsg F Out) :=
  ((List.finRange net.N).filter (fun y => decide (y ≠ m))).map (msg2 net)

theorem recN3 (m : Fin net.N) (f : F) :
    (Q.recN (net.own m) (s2 (Out := Out) net m) (R3 (Out := Out) net m)).mem f ↔ H.mem f := by
  constructor
  · rintro (hf | hf | ⟨m', hm, hf⟩)
    · exact (s2_rcd net m f).1 hf
    · exact hf.1
    · simp only [R3, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hm
      obtain ⟨y, _, rfl⟩ := hm
      exact (recN2 net y f).1 hf
  · intro hf; exact Or.inl ((s2_rcd net m f).2 hf)

theorem decs0_3 (m : Fin net.N) : Q.decs0 (s2 (Out := Out) net m) (R3 (Out := Out) net m) = [] := by
  simp only [Q.decs0, s2_decs, List.nil_append, List.flatMap_eq_nil_iff, R3, List.mem_map]
  rintro _ ⟨y, _, rfl⟩
  show (s2 (Out := Out) net y).decs = []
  exact s2_decs net y

theorem witness_cond (m : Fin net.N) (hm : ∀ y, net.node m ≤ net.node y) :
    Q.Cond loc (net.own m) (s2 (Out := Out) net m) (R3 (Out := Out) net m) := by
  have hid : Q.idOf loc (net.own m) (s2 (Out := Out) net m) = net.node m := by
    unfold Q.idOf
    rw [show (s2 (Out := Out) net m).me = some (Q.idOf loc (net.own m) (s1 (Out := Out) net m)) from rfl,
      idOf_s1]
    rfl
  refine ⟨by simp [s2, s1, Q.nxt, QSt.start], fun f hf => ?_, fun f hf hne => ?_, fun D hD => ?_⟩
  · rw [hid]
    obtain ⟨y, hy⟩ := net.cover f ((recN3 net m f).1 hf)
    rw [← hy]; exact hm y
  · obtain ⟨y, hy⟩ := net.cover f ((recN3 net m f).1 hf)
    have hym : y ≠ m := fun h => hne (by rw [hid, ← hy, h])
    have heq : Q.recN (net.own y) (s1 (Out := Out) net y) (R2 (Out := Out) net y) =
        Q.recN (net.own m) (s2 (Out := Out) net m) (R3 (Out := Out) net m) :=
      pset_ext fun g => (recN2 net y g).trans (recN3 net m g).symm
    refine List.mem_append_right _ (List.mem_map.2 ⟨msg2 (Out := Out) net y, ?_, ?_⟩)
    · simp only [R3, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq]
      exact ⟨y, hym, rfl⟩
    · simp only [msg2, idOf_s1, hy, heq]
  · rw [decs0_3] at hD; cases hD

end Witness

section Char

variable {F Out : Type} {loc : F → Nat} (B : Spec (LInp loc) (PSet (Nat × Out)))

/-- **Sufficiency (Baccaert–Ketsman Prop. 10).**  A node monotone behavior
whose rows have their outputs at network nodes is characterized by a node
program under Id+Ord. -/
theorem characterizes_qProg (hB : NodeMonoFin loc B) (hLoc : LocatedFin loc B) :
    Characterizes (qProg loc B) B := by
  classical
  refine ⟨computes_qProg B hB hLoc, fun H K hfin hne hK => ?_⟩
  obtain ⟨net, -, -, -⟩ := extend_net (n := 0) (node := Fin.elim0) (⟨H⟩ : LInp loc)
    (fun p => p.elim0) (fun _ h => h) (fun p => p.elim0) hfin
  have hpos : 0 < net.N := by
    obtain ⟨f, hf⟩ := hne; obtain ⟨y, _⟩ := net.cover f hf; exact y.pos
  obtain ⟨m, _, hm⟩ := exists_min_list net.node (List.finRange net.N)
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hpos⟩))
  have hm' : ∀ y, net.node m ≤ net.node y := fun y => hm y (List.mem_finRange y)
  let τ1 : Fin net.N → Tr net.N (QMsg F Out) (QSt F Out) := fun x => ⟨x, [], s1 (Out := Out) net x, [msg1 (Out := Out) net x]⟩
  let τ2 : Fin net.N → Tr net.N (QMsg F Out) (QSt F Out) := fun x => ⟨x, R2 (Out := Out) net x, s2 (Out := Out) net x, [msg2 (Out := Out) net x]⟩
  let s3 : QSt F Out := Q.nxt loc (net.own m) (s2 (Out := Out) net m) (R3 (Out := Out) net m) (some K)
  let τ3 : Tr net.N (QMsg F Out) (QSt F Out) :=
    ⟨m, R3 (Out := Out) net m, s3, [(Q.idOf loc (net.own m) (s2 (Out := Out) net m),
      Q.recN (net.own m) (s2 (Out := Out) net m) (R3 (Out := Out) net m), s3.decs)]⟩
  let l := List.finRange net.N
  have hnd : l.Nodup := List.nodup_finRange _
  -- round 1
  obtain ⟨ok1, S1, _, W1⟩ := seq_round (Pg := (qProg loc B)) net.own τ1 (fun _ => rfl) l (Cfg.start (qProg loc B)) hnd
    (fun x _ => ⟨⟨none, fun h => absurd h.1.1 (by show ¬ 2 ≤ 0; omega), rfl, rfl⟩,
      fun m' hm' => by cases hm'⟩)
  let c1 := seqCfg (Cfg.start (qProg loc B)) (l.map τ1)
  have hS1 : ∀ x, c1.S x = s1 (Out := Out) net x := fun x => by
    rw [S1 x, if_pos (List.mem_finRange x)]
  -- round 2
  obtain ⟨ok2, S2, L2, W2⟩ := seq_round (Pg := (qProg loc B)) net.own τ2 (fun _ => rfl) l c1 hnd
    (fun x _ => ⟨by
        rw [hS1 x]
        exact ⟨none, fun h => absurd h.1.1 (by show ¬ 2 ≤ 0 + 1; omega), rfl, rfl⟩,
      fun m' hm' => by
        simp only [τ2, R2, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
          decide_eq_true_eq] at hm'
        obtain ⟨y, hy, rfl⟩ := hm'
        exact ⟨y, hy, W1 y (List.mem_finRange y) _ (List.mem_singleton_self _)⟩⟩)
  let c2 := seqCfg c1 (l.map τ2)
  have hS2 : ∀ x, c2.S x = s2 (Out := Out) net x := fun x => by
    rw [S2 x, if_pos (List.mem_finRange x)]
  -- round 3
  have hen3 : Enabled (qProg loc B) net.own c2 τ3 := by
    refine ⟨?_, fun m' hm' => ?_⟩
    · show (qProg loc B).step (net.own m) (c2.S m) _ _ _
      rw [hS2 m]
      refine ⟨some K, ⟨witness_cond net m hm', ?_, ?_⟩, rfl, rfl⟩
      · have : Q.recN (net.own m) (s2 (Out := Out) net m) (R3 (Out := Out) net m) = H :=
          pset_ext fun g => recN3 net m g
        rw [this]; exact hK
      · intro e he
        rw [decs0_3] at he; cases he
    · simp only [τ3, R3, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq] at hm'
      obtain ⟨y, hy, rfl⟩ := hm'
      exact ⟨y, hy, W2 y (List.mem_finRange y) _ (List.mem_singleton_self _)⟩
  let pre := l.map τ1 ++ l.map τ2 ++ [τ3]
  have hok : SeqOK (qProg loc B) net.own (Cfg.start (qProg loc B)) pre := by
    rw [seqOK_append, seqOK_append]
    refine ⟨⟨ok1, ok2⟩, ?_⟩
    rw [seqCfg_append]
    exact ⟨hen3, trivial⟩
  obtain ⟨ρ, hfair, hcfg⟩ := fair_extension net.own hpos pre hok
  -- the whole instance is decided with `K`
  have hlast : seqCfg (Cfg.start (qProg loc B)) pre = c2.apply τ3 := by
    simp only [pre, seqCfg_append]; rfl
  have hmem : (Q.recN (net.own m) (s2 (Out := Out) net m) (R3 (Out := Out) net m), K) ∈
      ((cfgAt (qProg loc B) ρ pre.length).S m).decs := by
    rw [hcfg, hlast]
    show _ ∈ (upd c2.S m s3 m).decs
    rw [upd_same]; simp [s3, Q.nxt]
  obtain ⟨_, t', _, hdec⟩ := (ninv B net ρ hfair.valid pre.length m).decs _ hmem
  obtain ⟨t2, e, he, heH, T, hT⟩ := computes_strong B net ρ hfair hB hLoc
  have hrec : Q.recN (net.own m) (s2 (Out := Out) net m) (R3 (Out := Out) net m) = H := pset_ext fun g => recN3 net m g
  have := dec_once B net ρ hfair.valid hdec he (by rw [heH]; exact hrec)
  refine ⟨net, ρ, hfair, T, fun t ht => by rw [hT t ht, hT T (Nat.le_refl _)], ?_⟩
  rw [hT T (Nat.le_refl _), ← this]

/-- **Baccaert–Ketsman Thm. 5.**  A behavior is characterized by some node
program under Id+Ord if and only if it is node monotone and its rows have
their outputs at network nodes. -/
theorem bk_characterized_iff :
    (∃ (Msg St : Type) (Pg : Prog F Msg St Out), Characterizes Pg B) ↔
      NodeMonoFin loc B ∧ LocatedFin loc B := by
  constructor
  · rintro ⟨Msg, St, Pg, hCh⟩
    refine ⟨nodeMono_of_characterizes hCh, fun H K hfin hne hK z hz => ?_⟩
    obtain ⟨net, ρ, _, T, _, hout⟩ := hCh.2 H K hfin hne hK
    rw [← hout] at hz
    obtain ⟨x, hx, _⟩ := hz
    rw [hx]; exact net.net x
  · rintro ⟨hB, hLoc⟩
    exact ⟨_, _, qProg loc B, characterizes_qProg B hB hLoc⟩

/-- Quiescent outputs of a run agree. -/
theorem quiescent_eq {Msg St : Type} {Pg : Prog F Msg St Out} {N : Nat} {node : Fin N → Nat}
    {ρ : Nat → Tr N Msg St} {T T' : Nat} (h : Quiescent Pg node ρ T) (h' : Quiescent Pg node ρ T') :
    dout Pg node (cfgAt Pg ρ T) = dout Pg node (cfgAt Pg ρ T') := by
  rw [← h (max T T') (Nat.le_max_left _ _), h' (max T T') (Nat.le_max_right _ _)]

/-- **Baccaert–Ketsman Lemma 4 with Thm. 5.**  A behavior is computed by some
node program under Id+Ord if and only if it contains a node monotone behavior
whose rows have their outputs at network nodes. -/
theorem bk_computable_iff :
    (∃ (Msg St : Type) (Pg : Prog F Msg St Out), Computes Pg B) ↔
      ∃ B' : Spec (LInp loc) (PSet (Nat × Out)), (∀ i K, B'.P i K → B.P i K) ∧
        NodeMonoFin loc B' ∧ LocatedFin loc B' := by
  classical
  constructor
  · rintro ⟨Msg, St, Pg, hC⟩
    -- the behavior characterizing `Pg`: its quiescent outputs on nonempty finite networks
    let Run : PSet F → PSet (Nat × Out) → Prop := fun H K =>
      FinNet loc H ∧ (∃ f, H.mem f) ∧ ∃ (net : Net loc H) (ρ : Nat → Tr net.N Msg St),
        FairRun Pg net.own ρ ∧ ∃ T, Quiescent Pg net.node ρ T ∧ dout Pg net.node (cfgAt Pg ρ T) = K
    let B' : Spec (LInp loc) (PSet (Nat × Out)) :=
      ⟨fun i K => Run i.set K ∨ (¬ (FinNet loc i.set ∧ ∃ f, i.set.mem f) ∧ B.P i K), fun i => by
        by_cases hi : FinNet loc i.set ∧ ∃ f, i.set.mem f
        · obtain ⟨hfin, hne⟩ := hi
          obtain ⟨net, -, -, -⟩ := extend_net (n := 0) (node := Fin.elim0) (⟨i.set⟩ : LInp loc)
            (fun p => p.elim0) (fun _ h => h) (fun p => p.elim0) hfin
          have hpos : 0 < net.N := by
            obtain ⟨f, hf⟩ := hne; obtain ⟨y, _⟩ := net.cover f hf; exact y.pos
          obtain ⟨ρ, hfair, _⟩ := fair_extension net.own hpos [] trivial
          obtain ⟨T, hq, _⟩ := hC i.set net ρ hfair
          exact ⟨_, Or.inl ⟨hfin, hne, net, ρ, hfair, T, hq, rfl⟩⟩
        · obtain ⟨K, hK⟩ := B.total i
          exact ⟨K, Or.inr ⟨hi, hK⟩⟩⟩
    have hsub : ∀ i K, B'.P i K → B.P i K := by
      rintro i K (⟨_, _, net, ρ, hfair, T, hq, rfl⟩ | ⟨_, hK⟩)
      · obtain ⟨T', hq', hB'⟩ := hC i.set net ρ hfair
        rw [quiescent_eq hq hq']; exact hB'
      · exact hK
    have hCh : Characterizes Pg B' := by
      refine ⟨fun H net ρ hfair => ?_, fun H K hfin hne hK => ?_⟩
      · obtain ⟨T, hq, _⟩ := hC H net ρ hfair
        have hpos : 0 < net.N := (ρ 0).x.pos
        obtain ⟨f, hf, _⟩ := net.net ⟨0, hpos⟩
        exact ⟨T, hq, Or.inl ⟨finNet_of_net net, ⟨f, hf⟩, net, ρ, hfair, T, hq, rfl⟩⟩
      · rcases hK with ⟨_, _, h⟩ | ⟨hn, _⟩
        · exact h
        · exact absurd ⟨hfin, hne⟩ hn
    exact ⟨B', hsub, (bk_characterized_iff B').1 ⟨Msg, St, Pg, hCh⟩⟩
  · rintro ⟨B', hsub, hB, hLoc⟩
    refine ⟨_, _, qProg loc B', fun H net ρ hfair => ?_⟩
    obtain ⟨T, hq, hK⟩ := computes_qProg B' hB hLoc H net ρ hfair
    exact ⟨T, hq, hsub _ _ hK⟩

end Char

end BK
end CC
