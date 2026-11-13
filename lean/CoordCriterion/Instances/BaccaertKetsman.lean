import CoordCriterion.Instances.QueryRefinements
import CoordCriterion.CAP.AvailabilityAtEnd

/-!
# Baccaert and Ketsman's setting in our system model (Section 6.1)

Namespace `CC.BK` (and `CC.CAP` for the cluster predicate).  Baccaert and
Ketsman (PODS 2023; Information Systems 138, 2026) study *behaviors*: total
relations from distributed instances (facts located at nodes) to distributed
instances, computed by networks of relational transducers.  This file maps
their setting into the system model of `CAP/Model.lean`.

* *Anonymous clusters* (`CAP.System.Anonymous`, `CAP.System.cluster`).  Every
  participant runs one strategy that sees only its own initial input and the
  anonymized local history (`LEvA`): a receive shows its content, not its
  sender or the position of the matching send.  Sends carry no destination,
  so a send is a broadcast: each other participant may receive it, at most
  once (`WFB`, `RecvUniqueAt`; the point-to-point model `CAP.WF` allows one
  receive per send).  A cluster strategy does not see the participant set.
  Histories are causal (`CAP.Acyclic`, part of `WFB`).
* *Located inputs* are instances of facts `F` with a location `loc : F → Nat`,
  ordered by network input extension (`QRef.netAdm loc`: new facts only at
  nodes not yet in the network), as in `QRef.NodeMono`.
* *Placement* (`Placed`) is a constraint on legal inputs.  Participants are
  the nodes of a global instance `G` (`node` is a bijection onto `netw(G)`);
  each participant's initial input is its own facts; every later input event
  contains only facts the participant *holds* (`Holds`: its own facts, or
  facts carried by an earlier receive whose sender held them when it sent),
  and is closed under nodes (`NodeClosed`: with a fact at node `x` it
  contains all of `G`'s facts at `x`).  `Holds` is inductive, so a causal
  cycle of receives cannot justify an invented fact.  A participant learns of
  other nodes only through messages.  Since facts carry their location, a
  participant knows its own node and the order on node numbers: this is
  Baccaert and Ketsman's `Id + Ord`, without `All`.
* *Correctness* (`PlacedConsistent`): at the end of every placed broadcast history the
  system produces, the participants' states are confluent at every common
  input extension of their current inputs.
* *Realized rows* (`Emits`, `realized`): `(G, o)` when some placed history
  over `G` produced by the system emits `o`.  This is the analogue of the
  behavior a transducer network characterizes.
* `nodeMono_of_placedConsistent` (their Prop. 11, necessity): an anonymous
  cluster that is consistent on placed histories gives, for two realized rows
  over instances with disjoint networks, a common output extension in `P` at
  the union.  The proof puts the two witness histories side by side
  (`sideBySide`); the anonymous strategy cannot tell the difference
  (`compliant_embed`), and placement carries over (`placed_glue`).
-/

namespace CC

/-! ## Anonymous clusters -/

namespace CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type}

/-- Anonymized local events: a receive shows only its content. -/
inductive LEvA (sp : Spec I O) (D : Type) where
  | inp (j : I)
  | out (o : O)
  | commitment (γ : List (Commitment sp))
  | send (j : Option I) (d : D)
  | recv (j : Option I) (d : D)

/-- Forget the sender of a receive and the position of its send. -/
def LEvN.anon : LEvN sp D → LEvA sp D
  | .inp j => .inp j
  | .out o => .out o
  | .commitment γ => .commitment γ
  | .send j d => .send j d
  | .recv _ _ j d => .recv j d

/-- An anonymous cluster: one strategy for every participant, seeing only the
participant's own initial input and its anonymized local history. -/
def System.Anonymous (Sys : System sp D) : Prop :=
  ∃ F : I → List (LEvA sp D) → LEvA sp D → Prop,
    ∀ p x pre e, Sys.rule p x pre e ↔ F x (pre.map LEvN.anon) e.anon

/-- The cluster with basis `B` and shared strategy `F`. -/
def System.cluster (B : Commitment sp → Prop) (F : I → List (LEvA sp D) → LEvA sp D → Prop) :
    System sp D :=
  ⟨B, fun _ x pre e => F x (pre.map LEvN.anon) e.anon⟩

theorem System.cluster_anonymous (B : Commitment sp → Prop)
    (F : I → List (LEvA sp D) → LEvA sp D → Prop) :
    (System.cluster (sp := sp) (D := D) B F).Anonymous :=
  ⟨F, fun _ _ _ _ => Iff.rfl⟩

/-- An anonymous cluster is replicated. -/
theorem System.Anonymous.replicated {Sys : System sp D} (h : Sys.Anonymous) : Sys.Replicated := by
  obtain ⟨F, hF⟩ := h
  exact ⟨fun x pre e => F x (pre.map LEvN.anon) e.anon, fun n init p pre e => hF _ _ _ _⟩

/-! ### Renaming participants -/

/-- Rename the senders of receives along `f`. -/
def LEv.mapP {n m : Nat} (f : Fin n → Fin m) : LEv sp D n → LEv sp D m
  | .inp j => .inp j
  | .out o => .out o
  | .commitment γ => .commitment γ
  | .send j d => .send j d
  | .recv q k j d => .recv (f q) k j d

theorem LEv.anon_erase_mapP {n m : Nat} (f : Fin n → Fin m) (e : LEv sp D n) :
    (LEv.erase (e.mapP f)).anon = (LEv.erase e).anon := by
  cases e <;> rfl

theorem lrun_mapP {n m : Nat} (f : Fin n → Fin m) {σ τ : State sp} {l : List (LEv sp D n)} :
    LRun σ (l.map (LEv.mapP f)) τ ↔ LRun σ l τ := by
  induction l generalizing σ with
  | nil => exact ⟨fun h => by cases h; exact .nil _, fun h => by cases h; exact .nil _⟩
  | cons e l ih =>
    cases e with
    | inp j => exact ⟨fun h => by cases h with | inp hs hr => exact .inp hs (ih.1 hr),
        fun h => by cases h with | inp hs hr => exact .inp hs (ih.2 hr)⟩
    | out o => exact ⟨fun h => by cases h with | out hs hr => exact .out hs (ih.1 hr),
        fun h => by cases h with | out hs hr => exact .out hs (ih.2 hr)⟩
    | commitment γ => exact ⟨fun h => by cases h with
          | commitment hne ha hr => exact .commitment hne ha (ih.1 hr),
        fun h => by cases h with | commitment hne ha hr => exact .commitment hne ha (ih.2 hr)⟩
    | send j d => exact ⟨fun h => by cases h with | send hr => exact .send (ih.1 hr),
        fun h => by cases h with | send hr => exact .send (ih.2 hr)⟩
    | recv q k j d => exact ⟨fun h => by cases h with | recv hr => exact .recv (ih.1 hr),
        fun h => by cases h with | recv hr => exact .recv (ih.2 hr)⟩

/-- An anonymous strategy does not change when participants are renamed. -/
theorem strat_mapP {Sys : System sp D} (hA : Sys.Anonymous) {n m : Nat} (f : Fin n → Fin m)
    {init : Fin n → I} {init' : Fin m → I} {p : Fin n} {q : Fin m} (hi : init' q = init p)
    (pre : List (LEv sp D n)) (e : LEv sp D n) :
    Sys.strat m init' q (pre.map (LEv.mapP f)) (e.mapP f) ↔ Sys.strat n init p pre e := by
  obtain ⟨F, hF⟩ := hA
  have hl : ((pre.map (LEv.mapP f)).map LEv.erase).map LEvN.anon =
      (pre.map LEv.erase).map LEvN.anon := by
    simp only [List.map_map]
    exact List.map_congr_left (fun e _ => LEv.anon_erase_mapP f e)
  simp only [System.strat, hF, hi, hl, LEv.anon_erase_mapP]

theorem allowed_mapP {Sys : System sp D} (hA : Sys.Anonymous) {n m : Nat} (f : Fin n → Fin m)
    {init : Fin n → I} {init' : Fin m → I} {p : Fin n} {q : Fin m} (hi : init' q = init p)
    (pre : List (LEv sp D n)) (e : LEv sp D n) :
    Allowed Sys m init' q (pre.map (LEv.mapP f)) (e.mapP f) ↔ Allowed Sys n init p pre e := by
  have hs := strat_mapP hA f hi pre e
  cases e with
  | inp j => exact Iff.rfl
  | out o =>
    simp only [LEv.mapP] at hs ⊢
    simp only [Allowed, hi, lrun_mapP, hs]
  | commitment γ =>
    simp only [LEv.mapP] at hs ⊢
    simp only [Allowed, hs]
  | send j d =>
    simp only [LEv.mapP] at hs ⊢
    simp only [Allowed, hs]
  | recv q' k j d => exact Iff.rfl

/-- Inverting a mapped list at a split point. -/
theorem map_split {α β : Type} {g : α → β} {l : List α} {a b : List β} {x : β}
    (h : l.map g = a ++ x :: b) :
    ∃ a' x' b', l = a' ++ x' :: b' ∧ a = a'.map g ∧ x = g x' ∧ b = b'.map g := by
  obtain ⟨l1, l2, rfl, h1, h2⟩ := List.map_eq_append_iff.1 h
  obtain ⟨x', b', rfl, hx, hb⟩ := List.map_eq_cons_iff.1 h2
  exact ⟨l1, x', b', rfl, h1.symm, hx.symm, hb.symm⟩

theorem compliant_mapP {Sys : System sp D} (hA : Sys.Anonymous) {n m : Nat} (f : Fin n → Fin m)
    {init : Fin n → I} {init' : Fin m → I} {p : Fin n} {q : Fin m} (hi : init' q = init p)
    {l : List (LEv sp D n)} (hc : Compliant (Allowed Sys n init p) l) :
    Compliant (Allowed Sys m init' q) (l.map (LEv.mapP f)) := by
  intro a e b h
  obtain ⟨a', e', b', rfl, rfl, rfl, rfl⟩ := map_split h
  exact (allowed_mapP hA f hi a' e').2 (hc a' e' b' rfl)

theorem mapP_eq_recv {n m : Nat} {f : Fin n → Fin m} {e : LEv sp D n} {q : Fin m} {k : Nat}
    {j : Option I} {d : D} (h : e.mapP f = .recv q k j d) :
    ∃ q', e = .recv q' k j d ∧ q = f q' := by
  cases e with
  | recv q' k' j' d' =>
    simp only [LEv.mapP, LEv.recv.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨q', rfl, rfl⟩
  | _ => simp [LEv.mapP] at h

theorem mapP_eq_inp {n m : Nat} {f : Fin n → Fin m} {e : LEv sp D n} {j : I}
    (h : e.mapP f = .inp j) : e = .inp j := by
  cases e <;> simp_all [LEv.mapP]

theorem mapP_eq_out {n m : Nat} {f : Fin n → Fin m} {e : LEv sp D n} {o : O}
    (h : e.mapP f = .out o) : e = .out o := by
  cases e <;> simp_all [LEv.mapP]

/-! ### Two histories side by side -/

/-- The history whose first `n₁` participants run `H₁` and last `n₂` run `H₂`. -/
def sideBySide {n₁ n₂ : Nat} (H₁ : History sp D n₁) (H₂ : History sp D n₂) : History sp D (n₁ + n₂) :=
  Fin.addCases (motive := fun _ => List (LEv sp D (n₁ + n₂)))
    (fun p => (H₁ p).map (LEv.mapP (Fin.castAdd n₂)))
    (fun p => (H₂ p).map (LEv.mapP (Fin.natAdd n₁)))

theorem sideBySide_left {n₁ n₂ : Nat} (H₁ : History sp D n₁) (H₂ : History sp D n₂) (p : Fin n₁) :
    sideBySide H₁ H₂ (Fin.castAdd n₂ p) = (H₁ p).map (LEv.mapP (Fin.castAdd n₂)) := by
  simp [sideBySide]

theorem sideBySide_right {n₁ n₂ : Nat} (H₁ : History sp D n₁) (H₂ : History sp D n₂) (p : Fin n₂) :
    sideBySide H₁ H₂ (Fin.natAdd n₁ p) = (H₂ p).map (LEv.mapP (Fin.natAdd n₁)) := by
  simp [sideBySide]

/-- Glue two families. -/
def gF {α : Type} {n₁ n₂ : Nat} (f₁ : Fin n₁ → α) (f₂ : Fin n₂ → α) : Fin (n₁ + n₂) → α :=
  Fin.addCases (motive := fun _ => α) f₁ f₂

@[simp] theorem gF_left {α : Type} {n₁ n₂ : Nat} (f₁ : Fin n₁ → α) (f₂ : Fin n₂ → α)
    (p : Fin n₁) : gF f₁ f₂ (Fin.castAdd n₂ p) = f₁ p := by simp [gF]

@[simp] theorem gF_right {α : Type} {n₁ n₂ : Nat} (f₁ : Fin n₁ → α) (f₂ : Fin n₂ → α)
    (p : Fin n₂) : gF f₁ f₂ (Fin.natAdd n₁ p) = f₂ p := by simp [gF]

theorem castAdd_ne_natAdd {n₁ n₂ : Nat} (p : Fin n₁) (q : Fin n₂) :
    Fin.castAdd n₂ p ≠ Fin.natAdd n₁ q := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem castAdd_inj {n₁ n₂ : Nat} {p q : Fin n₁} (h : Fin.castAdd n₂ p = Fin.castAdd n₂ q) :
    p = q := Fin.ext (by have := congrArg Fin.val h; simpa using this)

theorem natAdd_inj {n₁ n₂ : Nat} {p q : Fin n₂} (h : Fin.natAdd n₁ p = Fin.natAdd n₁ q) :
    p = q := Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

/-- Receives in an embedded history stay matched. -/
theorem recvMatched_embed {n m : Nat} {g : Fin n → Fin m} (hg : ∀ p q, g p = g q → p = q)
    {H : History sp D n} {H' : History sp D m} (hH : ∀ p, H' (g p) = (H p).map (LEv.mapP g))
    (hm : RecvMatched H) (p : Fin n) :
    ∀ (a : List (LEv sp D m)) (q : Fin m) (k : Nat) (j : Option I) (d : D) b,
      H' (g p) = a ++ LEv.recv q k j d :: b → q ≠ g p ∧ (H' q)[k]? = some (LEv.send j d) := by
  intro a q k j d b h
  rw [hH] at h
  obtain ⟨a', e', b', hl, _, he, _⟩ := map_split h
  obtain ⟨q', rfl, rfl⟩ := mapP_eq_recv he.symm
  obtain ⟨hne, hs⟩ := hm p a' q' k j d b' hl
  refine ⟨fun h => hne (hg _ _ h), ?_⟩
  rw [hH, List.getElem?_map, hs]; rfl

theorem produced_glue {Sys : System sp D} (hA : Sys.Anonymous) {n₁ n₂ : Nat}
    {init₁ : Fin n₁ → I} {init₂ : Fin n₂ → I} {H₁ : History sp D n₁} {H₂ : History sp D n₂}
    (h₁ : Produced Sys n₁ init₁ H₁) (h₂ : Produced Sys n₂ init₂ H₂) :
    Produced Sys (n₁ + n₂) (gF init₁ init₂) (sideBySide H₁ H₂) := by
  intro p
  refine Fin.addCases (motive := fun p => Compliant (Allowed Sys (n₁ + n₂) (gF init₁ init₂) p)
      (sideBySide H₁ H₂ p)) (fun p => ?_) (fun p => ?_) p
  · rw [sideBySide_left]; exact compliant_mapP hA _ (gF_left _ _ p) (h₁ p)
  · rw [sideBySide_right]; exact compliant_mapP hA _ (gF_right _ _ p) (h₂ p)

theorem causal_sideBySide {n₁ n₂ : Nat} {H₁ : History sp D n₁} {H₂ : History sp D n₂}
    (h₁ : Causal H₁) (h₂ : Causal H₂) : Causal (sideBySide H₁ H₂) := by
  obtain ⟨t₁, m₁, r₁⟩ := h₁
  obtain ⟨t₂, m₂, r₂⟩ := h₂
  refine ⟨gF t₁ t₂, fun p => ?_, fun p => ?_⟩
  · refine Fin.addCases (motive := fun p => ∀ k k', k < k' → gF t₁ t₂ p k < gF t₁ t₂ p k')
      (fun p => ?_) (fun p => ?_) p
    · simpa using m₁ p
    · simpa using m₂ p
  · refine Fin.addCases (motive := fun p => ∀ (a : List (LEv sp D (n₁ + n₂))) q k j d b,
        sideBySide H₁ H₂ p = a ++ LEv.recv q k j d :: b → gF t₁ t₂ q k < gF t₁ t₂ p a.length)
      (fun p => ?_) (fun p => ?_) p
    · intro a q k j d b h
      rw [sideBySide_left] at h
      obtain ⟨a', e', b', hl, rfl, he, _⟩ := map_split h
      obtain ⟨q', rfl, rfl⟩ := mapP_eq_recv he.symm
      simpa using r₁ p a' q' k j d b' hl
    · intro a q k j d b h
      rw [sideBySide_right] at h
      obtain ⟨a', e', b', hl, rfl, he, _⟩ := map_split h
      obtain ⟨q', rfl, rfl⟩ := mapP_eq_recv he.symm
      simpa using r₂ p a' q' k j d b' hl

/-! ### Broadcast histories -/

/-- Broadcast: a participant receives a given send at most once (different
participants may each receive it). -/
def RecvUniqueAt {n : Nat} (H : History sp D n) : Prop :=
  ∀ (p : Fin n) (a : List (LEv sp D n)) (q : Fin n) (k : Nat) (j : Option I) (d : D) b
    (a' : List (LEv sp D n)) (j' : Option I) (d' : D) b',
    H p = a ++ LEv.recv q k j d :: b → H p = a' ++ LEv.recv q k j' d' :: b' → a.length = a'.length

/-- A well-formed broadcast history (for clusters): as `WF`, except that a
send may be received once by each other participant. -/
structure WFB {n : Nat} (init : Fin n → I) (H : History sp D n) : Prop where
  runs : ∀ p, ∃ τ, LRun (canon sp (init p)) (H p) τ
  matched : RecvMatched H
  uniqueAt : RecvUniqueAt H
  acyclic : Acyclic H

/-- A point-to-point history is a broadcast history. -/
theorem WF.toWFB {n : Nat} {init : Fin n → I} {H : History sp D n} (h : WF init H) : WFB init H :=
  ⟨h.runs, h.matched, fun p a q k j d b a' j' d' b' h1 h2 =>
    (h.unique p a q k j d b p a' j' d' b' h1 h2).2, h.acyclic⟩

theorem recvUniqueAt_extend {n : Nat} {H H' : History sp D n} {c : Fin n → Nat}
    {ext : Fin n → List (LEv sp D n)} (hu : RecvUniqueAt H)
    (hext : Extends H c H' ext) (hnr : ∀ p q k j d, LEv.recv q k j d ∉ ext p) :
    RecvUniqueAt H' := by
  intro p a q k j d b a' j' d' b' h h'
  rw [hext p] at h h'
  obtain ⟨b1, hb1⟩ := split_left h (hnr p q k j d)
  obtain ⟨b2, hb2⟩ := split_left h' (hnr p q k j' d')
  exact hu p a q k j d _ a' j' d' _ (take_split hb1) (take_split hb2)

/-- A continuation at a cut that adds no receive, with legal participant runs,
is a well-formed broadcast history. -/
theorem wfb_extend {n : Nat} {init : Fin n → I} {H H' : History sp D n} {c : Fin n → Nat}
    {ext : Fin n → List (LEv sp D n)} (hw : WFB init H) (hc : IsCut H c)
    (hext : Extends H c H' ext) (hnr : ∀ p q k j d, LEv.recv q k j d ∉ ext p)
    (hr : ∀ p, ∃ τ, LRun (canon sp (init p)) (H' p) τ) : WFB init H' :=
  ⟨hr, recvMatched_extend hw.matched hc hext hnr, recvUniqueAt_extend hw.uniqueAt hext hnr,
    acyclic_extend hw.matched hw.acyclic hc hext hnr⟩

theorem WFB.causal {n : Nat} {init : Fin n → I} {H : History sp D n} (h : WFB init H) : Causal H :=
  causal_of_acyclic h.matched h.acyclic

theorem recvUniqueAt_embed {n m : Nat} {g : Fin n → Fin m} (hg : ∀ p q, g p = g q → p = q)
    {H : History sp D n} {H' : History sp D m} (hH : ∀ p, H' (g p) = (H p).map (LEv.mapP g))
    (hu : RecvUniqueAt H) (p : Fin n) :
    ∀ (a : List (LEv sp D m)) (q : Fin m) (k : Nat) (j : Option I) (d : D) b
      (a' : List (LEv sp D m)) (j' : Option I) (d' : D) b',
      H' (g p) = a ++ LEv.recv q k j d :: b → H' (g p) = a' ++ LEv.recv q k j' d' :: b' →
        a.length = a'.length := by
  intro a q k j d b a' j' d' b' h h'
  rw [hH] at h h'
  obtain ⟨a1, e1, b1, hl1, rfl, he1, _⟩ := map_split h
  obtain ⟨a2, e2, b2, hl2, rfl, he2, _⟩ := map_split h'
  obtain ⟨q1, rfl, hq1⟩ := mapP_eq_recv he1.symm
  obtain ⟨q2, rfl, hq2⟩ := mapP_eq_recv he2.symm
  simp only [List.length_map]
  have : q1 = q2 := hg _ _ (hq1.symm.trans hq2)
  subst this
  exact hu p a1 q1 k j d b1 a2 j' d' b2 hl1 hl2

theorem wfb_glue {n₁ n₂ : Nat} {init₁ : Fin n₁ → I} {init₂ : Fin n₂ → I}
    {H₁ : History sp D n₁} {H₂ : History sp D n₂} (h₁ : WFB init₁ H₁) (h₂ : WFB init₂ H₂) :
    WFB (gF init₁ init₂) (sideBySide H₁ H₂) := by
  refine ⟨fun p => ?_, fun p => ?_, fun p => ?_,
    acyclic_of_causal (causal_sideBySide h₁.causal h₂.causal)⟩
  · refine Fin.addCases (motive := fun p => ∃ τ, LRun (canon sp (gF init₁ init₂ p)) (sideBySide H₁ H₂ p) τ)
      (fun p => ?_) (fun p => ?_) p
    · obtain ⟨τ, hτ⟩ := h₁.1 p
      exact ⟨τ, by rw [sideBySide_left, gF_left, lrun_mapP]; exact hτ⟩
    · obtain ⟨τ, hτ⟩ := h₂.1 p
      exact ⟨τ, by rw [sideBySide_right, gF_right, lrun_mapP]; exact hτ⟩
  · refine Fin.addCases (motive := fun p => ∀ a q k j d b, sideBySide H₁ H₂ p = a ++ LEv.recv q k j d :: b →
        q ≠ p ∧ (sideBySide H₁ H₂ q)[k]? = some (LEv.send j d)) (fun p => ?_) (fun p => ?_) p
    · exact recvMatched_embed (fun _ _ => castAdd_inj) (sideBySide_left H₁ H₂) h₁.2 p
    · exact recvMatched_embed (fun _ _ => natAdd_inj) (sideBySide_right H₁ H₂) h₂.2 p
  · refine Fin.addCases (motive := fun p => ∀ (a : List (LEv sp D (n₁ + n₂))) q k j d b a' j' d' b',
        sideBySide H₁ H₂ p = a ++ LEv.recv q k j d :: b →
        sideBySide H₁ H₂ p = a' ++ LEv.recv q k j' d' :: b' → a.length = a'.length)
      (fun p => ?_) (fun p => ?_) p
    · exact recvUniqueAt_embed (fun _ _ => castAdd_inj) (sideBySide_left H₁ H₂) h₁.uniqueAt p
    · exact recvUniqueAt_embed (fun _ _ => natAdd_inj) (sideBySide_right H₁ H₂) h₂.uniqueAt p

/-- Along a participant run the current input is the starting one or the
input of some input event. -/
theorem lrun_cur_cases {n : Nat} {σ τ : State sp} {l : List (LEv sp D n)} (h : LRun σ l τ) :
    τ.cur = σ.cur ∨ ∃ (a : List (LEv sp D n)) (j : I) (b : List (LEv sp D n)), l = a ++ LEv.inp j :: b ∧ τ.cur = j := by
  induction h with
  | nil => exact Or.inl rfl
  | @inp σ τ' ρ j es hs _ ih =>
    have hc : τ'.cur = j := (step_input_inv hs).2.1
    rcases ih with h | ⟨a, j', b, rfl, h⟩
    · exact Or.inr ⟨[], j, es, rfl, h.trans hc⟩
    · exact Or.inr ⟨LEv.inp j :: a, j', b, rfl, h⟩
  | @out σ τ' ρ o es hs _ ih =>
    have hc : τ'.cur = σ.cur := (step_output_inv hs).2.1
    rcases ih with h | ⟨a, j', b, rfl, h⟩
    · exact Or.inl (h.trans hc)
    · exact Or.inr ⟨LEv.out o :: a, j', b, rfl, h⟩
  | @commitment σ τ' ρ γ es _ ha _ ih =>
    have hc : τ'.cur = σ.cur := (applySeq_spec γ σ τ' ha).1
    rcases ih with h | ⟨a, j', b, rfl, h⟩
    · exact Or.inl (h.trans hc)
    · exact Or.inr ⟨LEv.commitment γ :: a, j', b, rfl, h⟩
  | @send σ ρ j d es _ ih =>
    rcases ih with h | ⟨a, j', b, rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨LEv.send j d :: a, j', b, rfl, h⟩
  | @recv σ ρ q k j d es _ ih =>
    rcases ih with h | ⟨a, j', b, rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨LEv.recv q k j d :: a, j', b, rfl, h⟩

end CAP

/-! ## Placement -/

namespace BK

open CAP
open QRef (ExtInp netAdm Netw union)
open CALM (PSet)

variable {F : Type} (loc : F → Nat)

/-- Located inputs, ordered by network input extension. -/
abbrev LInp := ExtInp (netAdm loc)

/-- `s` is closed under nodes of `G`: with a fact at node `x` it contains all
of `G`'s facts at `x` (and only facts of `G`). -/
def NodeClosed (G s : PSet F) : Prop :=
  ∀ f, s.mem f → G.mem f ∧ ∀ g, G.mem g → loc g = loc f → s.mem g

variable {O : Type} [PO O] {sp : Spec (LInp loc) O} {D : Type}

/-- `Holds G node H p k f`: after its first `k` events, participant `p` holds
fact `f`: it is one of `p`'s own facts, or it was carried by an earlier
receive whose sender held it when it sent. -/
inductive Holds (G : PSet F) {n : Nat} (node : Fin n → Nat) (H : History sp D n) :
    Fin n → Nat → F → Prop
  | own {p : Fin n} {k : Nat} {f : F} : G.mem f → loc f = node p → Holds G node H p k f
  | recv {p : Fin n} {k m : Nat} {q : Fin n} {k' : Nat} {j : LInp loc} {d : D} {f : F} :
      (H p)[m]? = some (LEv.recv q k' (some j) d) → m < k → j.set.mem f →
      Holds G node H q k' f → Holds G node H p k f

/-- Def. (placement): `H` is a placed history over the global instance `G`.
Its participants are the nodes of `G` (`node` is a bijection onto
`netw(G)`), each starts from its own facts, and every input event contains
only facts the participant holds and is closed under nodes of `G`.  (Placed
histories are taken with `WFB`, whose histories are causal.) -/
structure Placed (G : PSet F) {n : Nat} (node : Fin n → Nat) (init : Fin n → LInp loc)
    (H : History sp D n) : Prop where
  node_inj : ∀ p q, node p = node q → p = q
  node_net : ∀ p, Netw loc G (node p)
  net_node : ∀ f, G.mem f → ∃ p, node p = loc f
  init_own : ∀ p f, (init p).set.mem f ↔ G.mem f ∧ loc f = node p
  inp_held : ∀ p a j b, H p = a ++ LEv.inp j :: b → ∀ f, j.set.mem f →
    Holds loc G node H p a.length f
  inp_closed : ∀ p a j b, H p = a ++ LEv.inp j :: b → NodeClosed loc G j.set

variable {loc}

theorem nodeClosed_le {G s : PSet F} (h : NodeClosed loc G s) :
    (⟨s⟩ : LInp loc) ≼ ⟨G⟩ := by
  refine ⟨fun f hf => (h f hf).1, fun g hg hgs ⟨f, hf, hfl⟩ => hgs ((h f hf).2 g hg hfl.symm)⟩

/-- In a placed history, every current input is closed under nodes of `G`. -/
theorem placed_cur_closed {G : PSet F} {n : Nat} {node : Fin n → Nat} {init : Fin n → LInp loc}
    {H : History sp D n} (hP : Placed loc G node init H) (p : Fin n) {σ : State sp}
    (hσ : LRun (canon sp (init p)) (H p) σ) : NodeClosed loc G σ.cur.set := by
  rcases lrun_cur_cases hσ with h | ⟨a, j, b, hab, h⟩
  · rw [h]
    intro f hf
    obtain ⟨hG, hl⟩ := (hP.init_own p f).1 hf
    exact ⟨hG, fun g hg hgl => (hP.init_own p g).2 ⟨hg, hgl.trans hl⟩⟩
  · rw [h]; exact hP.inp_closed p a j b hab

/-! ## Correctness and realized rows -/

/-- Correctness on placed histories: at the end of every placed history the
system produces, the participants can be brought to one state at every common
input extension of their current inputs (with Partition Consistency's
continuations, `CAP.PartitionConsistencyAtEnd`). -/
def PlacedConsistent (Sys : System sp D) : Prop :=
  ∀ (n : Nat) (G : PSet F) (node : Fin n → Nat) (init : Fin n → LInp loc) (H : History sp D n),
    Placed loc G node init H → WFB init H → Produced Sys n init H →
    ∀ j : LInp loc, (∀ p σ, LRun (canon sp (init p)) (H p) σ → σ.cur ≼ j) →
    ∃ τ : State sp, τ.cur = j ∧ ∃ ext : Fin n → List (LEv sp D n),
      WFB init (fun q => H q ++ ext q) ∧ ∀ p, LRun (canon sp (init p)) (H p ++ ext p) τ

/-- Some placed history over `G` produced by the system emits `o`. -/
def Emits (Sys : System sp D) (G : PSet F) (o : O) : Prop :=
  ∃ (n : Nat) (node : Fin n → Nat) (init : Fin n → LInp loc) (H : History sp D n) (p : Fin n),
    Placed loc G node init H ∧ WFB init H ∧ Produced Sys n init H ∧ LEv.out o ∈ H p

/-- The rows a system realizes on placed histories (`A_Sys`). -/
def realized (Sys : System sp D) : Table (LInp loc) O := fun i o => Emits Sys i.set o

/-- Node monotonicity of `B` relative to rows `A`: rows of `A` at inputs with
disjoint networks have a common output extension in `B` at the union.  With
`A = B.P` and outputs ordered by inclusion this is `QRef.NodeMono`. -/
def NodeMonoFor (B : Spec (LInp loc) O) (A : Table (LInp loc) O) : Prop :=
  ∀ H₁ H₂ : PSet F, (∀ x, Netw loc H₁ x → ¬ Netw loc H₂ x) →
    ∀ K₁ K₂, A ⟨H₁⟩ K₁ → A ⟨H₂⟩ K₂ → ∃ K, B.P ⟨union H₁ H₂⟩ K ∧ K₁ ≼ K ∧ K₂ ≼ K

theorem nodeMonoFor_self_iff {G' : Type} (B : Spec (LInp loc) (PSet G')) :
    NodeMonoFor B B.P ↔ QRef.NodeMono loc B := Iff.rfl

/-! ## Placement of two histories side by side -/

/-- Holding carries over to an embedded history. -/
theorem holds_embed {G G' : PSet F} {n m : Nat} {node : Fin n → Nat} {node' : Fin m → Nat}
    {g : Fin n → Fin m} {H : History sp D n} {H' : History sp D m}
    (hGG : ∀ f, G.mem f → G'.mem f) (hnode : ∀ p, node' (g p) = node p)
    (hH : ∀ p, H' (g p) = (H p).map (LEv.mapP g)) {p : Fin n} {k : Nat} {f : F}
    (h : Holds loc G node H p k f) : Holds loc G' node' H' (g p) k f := by
  induction h with
  | own hG hl => exact .own (hGG _ hG) (hl.trans (hnode _).symm)
  | @recv p k m q k' j d f hm hmk hj _ ih =>
    refine .recv (q := g q) (j := j) (d := d) (m := m) (k' := k') ?_ hmk hj ih
    rw [hH, List.getElem?_map, hm]; rfl

theorem nodeClosed_union_left {G₁ G₂ s : PSet F} (hd : ∀ x, Netw loc G₁ x → ¬ Netw loc G₂ x)
    (h : NodeClosed loc G₁ s) : NodeClosed loc (union G₁ G₂) s := by
  intro f hf
  obtain ⟨hG, hcl⟩ := h f hf
  refine ⟨Or.inl hG, fun g hg hgl => ?_⟩
  rcases hg with hg | hg
  · exact hcl g hg hgl
  · exact absurd ⟨g, hg, hgl⟩ (hd _ ⟨f, hG, rfl⟩)

theorem nodeClosed_union_right {G₁ G₂ s : PSet F} (hd : ∀ x, Netw loc G₁ x → ¬ Netw loc G₂ x)
    (h : NodeClosed loc G₂ s) : NodeClosed loc (union G₁ G₂) s := by
  intro f hf
  obtain ⟨hG, hcl⟩ := h f hf
  refine ⟨Or.inr hG, fun g hg hgl => ?_⟩
  rcases hg with hg | hg
  · exact absurd ⟨f, hG, rfl⟩ (hd _ ⟨g, hg, hgl⟩)
  · exact hcl g hg hgl

/-- Input events of an embedded history keep holding and node closure. -/
theorem inp_embed {G G' : PSet F} {n m : Nat} {node : Fin n → Nat} {node' : Fin m → Nat}
    {g : Fin n → Fin m} {init : Fin n → LInp loc} {H : History sp D n} {H' : History sp D m}
    (hP : Placed loc G node init H) (hGG : ∀ f, G.mem f → G'.mem f)
    (hcl : ∀ s, NodeClosed loc G s → NodeClosed loc G' s) (hnode : ∀ p, node' (g p) = node p)
    (hH : ∀ p, H' (g p) = (H p).map (LEv.mapP g)) (p : Fin n) :
    ∀ a j b, H' (g p) = a ++ LEv.inp j :: b →
      (∀ f, j.set.mem f → Holds loc G' node' H' (g p) a.length f) ∧ NodeClosed loc G' j.set := by
  intro a j b h
  rw [hH] at h
  obtain ⟨a', e', b', hl, rfl, he, _⟩ := map_split h
  have he' := mapP_eq_inp he.symm
  subst he'
  refine ⟨fun f hf => ?_, hcl _ (hP.inp_closed p a' j b' hl)⟩
  rw [List.length_map]
  exact holds_embed hGG hnode hH (hP.inp_held p a' j b' hl f hf)

theorem placed_glue {G₁ G₂ : PSet F} (hd : ∀ x, Netw loc G₁ x → ¬ Netw loc G₂ x)
    {n₁ n₂ : Nat} {node₁ : Fin n₁ → Nat} {node₂ : Fin n₂ → Nat}
    {init₁ : Fin n₁ → LInp loc} {init₂ : Fin n₂ → LInp loc}
    {H₁ : History sp D n₁} {H₂ : History sp D n₂}
    (h₁ : Placed loc G₁ node₁ init₁ H₁) (h₂ : Placed loc G₂ node₂ init₂ H₂) :
    Placed loc (union G₁ G₂) (gF node₁ node₂) (gF init₁ init₂) (sideBySide H₁ H₂) := by
  have hne : ∀ p q, node₁ p ≠ node₂ q := fun p q h => hd _ (h₁.node_net p) (h ▸ h₂.node_net q)
  refine ⟨fun p q => ?_, fun p => ?_, fun f hf => ?_, fun p f => ?_, ?_, ?_⟩
  · refine Fin.addCases (motive := fun p => gF node₁ node₂ p = gF node₁ node₂ q → p = q)
      (fun p => ?_) (fun p => ?_) p <;>
    refine Fin.addCases (motive := fun q => _ = gF node₁ node₂ q → _ = q)
      (fun q => ?_) (fun q => ?_) q <;> simp only [gF_left, gF_right] <;> intro h
    · rw [h₁.node_inj p q h]
    · exact absurd h (hne p q)
    · exact absurd h.symm (hne q p)
    · rw [h₂.node_inj p q h]
  · refine Fin.addCases (motive := fun p => Netw loc (union G₁ G₂) (gF node₁ node₂ p))
      (fun p => ?_) (fun p => ?_) p
    · obtain ⟨f, hf, hl⟩ := h₁.node_net p; exact ⟨f, Or.inl hf, by simpa using hl⟩
    · obtain ⟨f, hf, hl⟩ := h₂.node_net p; exact ⟨f, Or.inr hf, by simpa using hl⟩
  · rcases hf with hf | hf
    · obtain ⟨p, hp⟩ := h₁.net_node f hf; exact ⟨Fin.castAdd n₂ p, by simpa using hp⟩
    · obtain ⟨p, hp⟩ := h₂.net_node f hf; exact ⟨Fin.natAdd n₁ p, by simpa using hp⟩
  · refine Fin.addCases (motive := fun p => (gF init₁ init₂ p).set.mem f ↔
        (union G₁ G₂).mem f ∧ loc f = gF node₁ node₂ p) (fun p => ?_) (fun p => ?_) p
    · simp only [gF_left, h₁.init_own]
      constructor
      · rintro ⟨hf, hl⟩; exact ⟨Or.inl hf, hl⟩
      · rintro ⟨hf | hf, hl⟩
        · exact ⟨hf, hl⟩
        · exact absurd ⟨f, hf, hl⟩ (hd _ (h₁.node_net p))
    · simp only [gF_right, h₂.init_own]
      constructor
      · rintro ⟨hf, hl⟩; exact ⟨Or.inr hf, hl⟩
      · rintro ⟨hf | hf, hl⟩
        · exact absurd (hl ▸ h₂.node_net p) (hd _ ⟨f, hf, rfl⟩)
        · exact ⟨hf, hl⟩
  · intro p
    refine Fin.addCases (motive := fun p => ∀ a j b, sideBySide H₁ H₂ p = a ++ LEv.inp j :: b → ∀ f,
        j.set.mem f → Holds loc (union G₁ G₂) (gF node₁ node₂) (sideBySide H₁ H₂) p a.length f)
      (fun p => ?_) (fun p => ?_) p
    · intro a j b h
      exact (inp_embed h₁ (fun _ h => Or.inl h) (fun _ => nodeClosed_union_left hd) (gF_left node₁ node₂)
        (sideBySide_left H₁ H₂) p a j b h).1
    · intro a j b h
      exact (inp_embed h₂ (fun _ h => Or.inr h) (fun _ => nodeClosed_union_right hd) (gF_right node₁ node₂)
        (sideBySide_right H₁ H₂) p a j b h).1
  · intro p
    refine Fin.addCases (motive := fun p => ∀ a j b, sideBySide H₁ H₂ p = a ++ LEv.inp j :: b →
        NodeClosed loc (union G₁ G₂) j.set) (fun p => ?_) (fun p => ?_) p
    · intro a j b h
      exact (inp_embed h₁ (fun _ h => Or.inl h) (fun _ => nodeClosed_union_left hd) (gF_left node₁ node₂)
        (sideBySide_left H₁ H₂) p a j b h).2
    · intro a j b h
      exact (inp_embed h₂ (fun _ h => Or.inr h) (fun _ => nodeClosed_union_right hd) (gF_right node₁ node₂)
        (sideBySide_right H₁ H₂) p a j b h).2

/-! ## Baccaert and Ketsman's Prop. 11 in our model -/

/-- **Necessity (Baccaert–Ketsman, Prop. 11).**  If an anonymous cluster is
consistent on placed histories, then two rows it realizes over instances with
disjoint networks have a common output extension in `P` at the union.  Put
the two witness histories side by side: the strategy cannot tell, the result
is a placed history over the union, and its participants' current inputs all
lie below the union. -/
theorem nodeMono_of_placedConsistent {Sys : System sp D} (hA : Sys.Anonymous)
    (hc : PlacedConsistent Sys) : NodeMonoFor sp (realized (loc := loc) Sys) := by
  intro G₁ G₂ hd o₁ o₂ ⟨n₁, node₁, init₁, H₁, p₁, hP₁, hW₁, hR₁, hm₁⟩
    ⟨n₂, node₂, init₂, H₂, p₂, hP₂, hW₂, hR₂, hm₂⟩
  have hP := placed_glue hd hP₁ hP₂
  have hW := wfb_glue hW₁ hW₂
  have hR := produced_glue hA hR₁ hR₂
  obtain ⟨τ, hτ, ext, _, hrun⟩ := hc _ _ _ _ _ hP hW hR ⟨union G₁ G₂⟩
    (fun p σ hσ => by
      have := nodeClosed_le (placed_cur_closed hP p hσ)
      exact this)
  obtain ⟨u, hu⟩ := τ.hasCur
  rw [hτ] at hu
  refine ⟨u, τ.sub _ _ hu, ?_, ?_⟩
  · have hm : LEv.out o₁ ∈ sideBySide H₁ H₂ (Fin.castAdd n₂ p₁) ++ ext (Fin.castAdd n₂ p₁) := by
      rw [sideBySide_left]; exact List.mem_append_left _ (List.mem_map.2 ⟨_, hm₁, rfl⟩)
    exact lrun_out_mem (hrun _) hm _ _ hu
  · have hm : LEv.out o₂ ∈ sideBySide H₁ H₂ (Fin.natAdd n₁ p₂) ++ ext (Fin.natAdd n₁ p₂) := by
      rw [sideBySide_right]; exact List.mem_append_left _ (List.mem_map.2 ⟨_, hm₂, rfl⟩)
    exact lrun_out_mem (hrun _) hm _ _ hu

end BK
end CC
