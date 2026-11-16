import CoordCriterion.Appendix.RealTimeTies
import CoordCriterion.CAP.AvailabilityAtEnd

/-!
# Mahajan, Alvisi, and Dahlin's RTC theorem from ours (Appendix `app:rtc`)

Mahajan, Alvisi, and Dahlin (UTCS TR-11-22, "Consistency, availability, and
convergence"), Theorem 3.1: "No consistency semantics stronger than real time
causal consistency can be implemented using a one-way convergent and always
available distributed storage implementation."  This file formalizes their
definitions as far as the correspondence of Appendix `app:rtc` needs them,
proves that correspondence, and derives their theorem from ours.

## Their check (§2.1 of the report)

An execution is *real time causally consistent* when some HB graph, a strict
partial order `≺_G` on its operations, satisfies

* CC1 (serial ordering at each node): operations of one node are ordered by
  `≺_G` as they are issued;
* CC2 (a read returns the latest preceding concurrent writes): `r`'s
  writeList is `{w | w ≺_G r ∧ ¬∃ w', w ≺_G w' ≺_G r}` (`WL`);
* CC3 (time doesn't travel backward): `u.endTime < v.startTime ⇒ v ⊀_G u`.

Their proof also uses two properties of the executions an implementation
produces: a write delivered to a read's node before the read precedes the read
(their Lemma 3.2, which they derive from one-way convergence), and a read
returns only writes delivered to its node (their Lemma 3.3).  `HBCheck` is
this check for the reads of one replica `p`, with our program order for CC1,
our causal precedence `→` for delivery and our `≺` for real time.  Their reads
return a set; ours return one source, so CC2 reads "the writeList is
`{s(r)}`" (`∅` for `v₀`).

* `rview_iff_check`: the real-time causal views are exactly the source maps
  of `p`'s reads that pass this check.  The order is `hb` plus "each
  overwritten write precedes the source" (`Kv` at `hbRt i`).
* `wl_member_not_rview`: taking `s(r)` merely as *one element* of a
  set-valued writeList is weaker; CC3 allows the writeList `{a, b}` when `a`
  ended before `b` began, and returning `a` there is not a real-time causal
  view.  (So "ours return one" means a singleton writeList.)

## The hypotheses (App. A of the report)

* *Always available*: every read and write completes in every environment,
  whatever messages are lost.  Ours: `T` selects a tuple at every input,
  whose `p`-coordinate answers every read of `p` (`sel_total`,
  `sel_answers`), and its restriction `e_p` is authorized for `p`
  (`sel_owner_row`); with Deployment Availability, in every partition, each
  replica emits it using only its own block (`always_available`).
* *One-way convergent*: once `s` has sent its updates to `d`, `d` reflects
  them.  Ours: the input records delivery, and the environment may supply
  any delivery (`deliver`); views must respect `→`, so every delivered write
  is the source of a later read or precedes it in the check's order
  (`check_reflects`, `one_way_convergence`).
* *Does not observe real time*: an implementation's answers are a function of
  the environment without real time.  Ours: an abstract implementation
  `MImpl` returns set-valued writeLists; `NoRealTime` says they depend only on
  the history.  Its strengthening `MImpl.str` selects the real-time causal
  tuples whose sources come from those writeLists, and it is real-time blind
  (`MImpl.rblind`).  Their proof uses the assumption to move one concurrent
  write after another in real time (their execution `e''`); ours adds the
  real-time edges "overwritten write before the source", each between writes
  not ordered the other way (`forceRt_swap`).

## Their theorem from ours

`mahajan_rtc`: for a strict, real-time blind strengthening `T` of the
real-time causal product interface, every system for `T`'s specification with
Deployment Availability under the owner deployment produces a partitioned,
message-free history in which every replica emits a real-time causal view at
one input `i`, yet no row of `T` at `i` extends them all: the execution the
replicas produce is real-time causal and rejected by `T`.  So no such system
has Partition Consistency (`mahajan_rtc_not_partitionConsistency`).

The proof is carried by Prop. `prop:rtc-maximal`'s step `rtc_locCons` (where
blindness is used) and Theorem `thm:product-frontier`(2) in witness form
(`strengthening_witness`), whose separable family the system realizes by
Deployment Availability (`da_realize`, as in the necessity proof of Complete
CAP); the last step is reconciliation (`realized_reconciled`).

Modeling choices: real time is a strict partial order `≺` (theirs comes from
interval endpoints); "stronger than RTC" is `T.Strict` (`T` selects a proper
subset of the real-time causal tuples); "implements" is that the replicas'
answers together are a row of `T`, which Partition Consistency guarantees
after reconnection.
-/

namespace CC
namespace Deploy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CC.CAP (LEv LRun History WF Produced Partitioned IsCut Extends PartitionConsistency
  System lrun_out_mem lrun_mono lrun_noinp wf_of_ne lrun_append)

/-! ## Their check for one replica's reads -/

section Check
variable {α : Type} {n : Nat} {G : OpSig α n}

/-- CC2's writeList for the order `HB`: the writes preceding `r` that no
write between them and `r` overwrites. -/
def WL (G : OpSig α n) (HB : α → α → Prop) (r w : α) : Prop :=
  G.isW w = true ∧ HB w r ∧ ¬ ∃ w', G.isW w' = true ∧ HB w w' ∧ HB w' r

/-- Mahajan et al.'s RTC check for the reads of replica `p` with sources `v`,
witnessed by the HB order `HB`. -/
structure HBCheck (i : RHist G) (p : Fin n) (v : SMap α) (HB : α → α → Prop) : Prop where
  mem : ∀ a b, HB a b → i.h.mem a ∧ i.h.mem b
  irrefl : ∀ a, ¬ HB a a
  trans : ∀ a b c, HB a b → HB b c → HB a c
  /-- CC1: one replica's operations are ordered as issued (program order). -/
  cc1 : ∀ a b, i.h.mem a → i.h.mem b → G.rep a = G.rep b → a ≠ b → (HB a b ↔ i.h.hb a b)
  /-- Each visible (delivered) write precedes the read (their Lemma 3.2). -/
  vis : ∀ r w, PRead G i.h p r → G.isW w = true → i.h.hb w r → HB w r
  /-- CC2 with single sources: the writeList is `{s(r)}`, or `∅` for `v₀`. -/
  cc2 : ∀ r s, v.f r = some s → ∀ w, (WL G HB r w ↔ s = some w)
  /-- CC3: time doesn't travel backward. -/
  cc3 : ∀ a b, i.rt a b → ¬ HB b a
  /-- Only delivered writes are returned (their Lemma 3.3). -/
  rcv : ∀ r w, v.f r = some (some w) → i.h.hb w r

/-- `v` answers exactly the reads of `p`, and some HB order passes the check. -/
def RTCCheck (G : OpSig α n) (p : Fin n) (i : RHist G) (v : SMap α) : Prop :=
  (∀ r, (∃ s, v.f r = some s) ↔ PRead G i.h p r) ∧ ∃ HB, HBCheck i p v HB

/-- The input `i` with real-time precedence replaced by causal precedence. -/
def hbRt (i : RHist G) : RHist G where
  h := i.h
  rt := i.h.hb
  rt_mem := i.h.hb_mem
  rt_irrefl := i.h.irrefl
  rt_trans := i.h.trans
  hb_rt _ _ h := h
  po := i.po

theorem rview_good_hbRt {i : RHist G} {p : Fin n} {v : SMap α} (hv : RView G p i v) :
    RGood G (hbRt i) p v := by
  have hg := rview_good G hv
  refine ⟨fun r s e => ⟨(hg.1 r s e).1, ?_⟩, hg.2.1, hg.2.2⟩
  have h := (hg.1 r s e).2
  cases s with
  | none => exact h
  | some w => exact ⟨h.1, h.2.1, fun w' h1 h2 h3 => h.2.2 w' h1 h2 (i.hb_rt _ _ h3)⟩

theorem kv_hbRt_le {i : RHist G} {v : SMap α} {a b : α} (h : Kv G (hbRt i) v a b) :
    Kv G i v a b := by
  rcases h with h | ⟨r, x, w, e, ha, hb⟩
  · exact Or.inl (i.hb_rt _ _ h)
  · exact Or.inr ⟨r, x, w, e, ha.imp_right (i.hb_rt _ _), hb.imp_right (i.hb_rt _ _)⟩

/-- A visible write is the source or precedes it. -/
theorem kv_to_src {i : RHist G} {v : SMap α} {r s u : α} (hr : v.f r = some (some s))
    (hu : G.isW u = true) (hur : i.h.hb u r) : u = s ∨ Kv G (hbRt i) v u s := by
  by_cases e : u = s
  · exact Or.inl e
  · exact Or.inr (Or.inr ⟨r, u, s, ⟨hr, hu, hur, e⟩, Or.inl rfl, Or.inl rfl⟩)

/-- A write preceding a read of `p` in the order is below a visible write. -/
theorem kv_into_read {i : RHist G} {p : Fin n} {v : SMap α} (hv : RView G p i v) {r y : α}
    (pr : PRead G i.h p r) (hy : G.isW y = true) (h : Kv G (hbRt i) v y r) :
    ∃ u, G.isW u = true ∧ i.h.hb u r ∧ (y = u ∨ Kv G (hbRt i) v y u) := by
  rcases h with h | ⟨r', x, w0, ed, hx, hw⟩
  · exact ⟨y, hy, h, Or.inl rfl⟩
  · have hW0 : G.isW w0 = true := (hv.2.1 r' _ ed.1).2.1
    rcases hw with e | hw
    · subst e; exact absurd (hW0.symm.trans pr.2.1) (by decide)
    · exact ⟨w0, hW0, hw, Or.inr (Or.inr ⟨r', x, w0, ed, hx, Or.inl rfl⟩)⟩

/-- Every real-time causal view passes the check, with the order "`→`, and
each overwritten write precedes the source". -/
theorem rview_check {i : RHist G} {p : Fin n} {v : SMap α} (hv : RView G p i v) :
    HBCheck i p v (Kv G (hbRt i) v) := by
  have hg := rview_good_hbRt hv
  have hgi := rview_good G hv
  refine ⟨kv_mem hg, kv_irrefl hg, kv_trans hg, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb hrep hne
    refine ⟨fun h => ?_, fun h => Or.inl h⟩
    rcases i.po a b ha hb hrep hne with h' | h'
    · exact h'
    · exact absurd (kv_trans hg _ _ _ h (Or.inl h')) (kv_irrefl hg a)
  · intro r w _ _ h; exact Or.inl h
  · intro r s e w
    have pr : PRead G i.h p r := (hv.1 r).1 ⟨s, e⟩
    cases s with
    | none =>
      have hno : ∀ w, G.isW w = true → ¬ i.h.hb w r := hv.2.1 r none e
      refine ⟨fun ⟨hw, hwr, _⟩ => ?_, fun h => by cases h⟩
      obtain ⟨u, hu, hur, _⟩ := kv_into_read hv pr hw hwr
      exact absurd hur (hno u hu)
    | some s =>
      have hs := hv.2.1 r (some s) e
      have below : ∀ y, G.isW y = true → Kv G (hbRt i) v y r →
          y = s ∨ Kv G (hbRt i) v y s := by
        intro y hy hyr
        obtain ⟨u, hu, hur, hyu⟩ := kv_into_read hv pr hy hyr
        rcases kv_to_src e hu hur with e' | hus
        · subst e'; exact hyu
        · rcases hyu with e'' | hyu
          · subst e''; exact Or.inr hus
          · exact Or.inr (kv_trans hg _ _ _ hyu hus)
      constructor
      · rintro ⟨hw, hwr, hmax⟩
        rcases below w hw hwr with e' | hws
        · rw [e']
        · exact absurd ⟨s, hs.2.1, hws, Or.inl hs.1⟩ hmax
      · intro h
        obtain rfl := Option.some.inj h
        refine ⟨hs.2.1, Or.inl hs.1, ?_⟩
        rintro ⟨w', hw', h1, h2⟩
        rcases below w' hw' h2 with e' | h3
        · subst e'; exact kv_irrefl hg _ h1
        · exact kv_irrefl hg _ (kv_trans hg _ _ _ h1 h3)
  · intro a b hab hba
    exact kv_irrefl hgi _ (kv_trans hgi _ _ _ (Or.inl hab) (kv_hbRt_le hba))
  · intro r w e; exact (hv.2.1 r _ e).1

/-- Under the check, a write preceding a read is in the writeList or precedes
a write in it. -/
theorem check_above {i : RHist G} {p : Fin n} {v : SMap α} {HB : α → α → Prop}
    (hc : HBCheck i p v HB) {r w : α} (hw : G.isW w = true) (hwr : HB w r) :
    ∃ m, WL G HB r m ∧ (w = m ∨ HB w m) := by
  classical
  obtain ⟨l, hl⟩ := i.h.fin
  obtain ⟨σ, hσ, hσE⟩ := linExt HB hc.irrefl hc.trans l i.h.mem hl
  let B : α → Prop := fun b => G.isW b = true ∧ (w = b ∨ HB w b) ∧ HB b r
  obtain ⟨m, hm, hmax⟩ := sto_max hσ l B (fun b h => (hc.mem _ _ h.2.2).1)
    (fun b h => hl b (hc.mem _ _ h.2.2).1) ⟨w, hw, Or.inl rfl, hwr⟩
  refine ⟨m, ⟨hm.1, hm.2.2, ?_⟩, hm.2.1⟩
  rintro ⟨w', hw', h1, h2⟩
  have hww' : w = w' ∨ HB w w' := by
    rcases hm.2.1 with e | h
    · subst e; exact Or.inr h1
    · exact Or.inr (hc.trans _ _ _ h h1)
  have hσ1 : σ m w' := hσE m w' (hc.mem _ _ h1).1 (hc.mem _ _ h1).2 h1
  rcases hmax w' ⟨hw', hww', h2⟩ with e | h
  · subst e; exact hc.irrefl _ h1
  · exact hσ.irrefl _ (hσ.trans hσ1 h)

/-- Views must respect `→`: under the check, every write visible to a read
of `p` is its source or precedes the source. -/
theorem check_reflects {i : RHist G} {p : Fin n} {v : SMap α} {HB : α → α → Prop}
    (hc : HBCheck i p v HB) {r w : α} {s : Option α} (hr : v.f r = some s)
    (pr : PRead G i.h p r) (hw : G.isW w = true) (hwr : i.h.hb w r) :
    ∃ m, s = some m ∧ (w = m ∨ HB w m) := by
  obtain ⟨m, hm, hwm⟩ := check_above hc hw (hc.vis r w pr hw hwr)
  exact ⟨m, (hc.cc2 r s hr m).1 hm, hwm⟩

/-- Every source map passing the check is a real-time causal view. -/
theorem check_rview {i : RHist G} {p : Fin n} {v : SMap α} (h : RTCCheck G p i v) :
    RView G p i v := by
  obtain ⟨hdom, HB, hc⟩ := h
  refine ⟨hdom, fun r s e => ?_, ?_⟩
  · have pr := (hdom r).1 ⟨s, e⟩
    cases s with
    | none =>
      intro w hw hwr
      obtain ⟨m, hm, _⟩ := check_reflects hc e pr hw hwr
      cases hm
    | some s =>
      have hs : WL G HB r s := (hc.cc2 r (some s) e s).2 rfl
      refine ⟨hc.rcv r s e, hs.1, fun w' hw' hw'r hrt => ?_⟩
      obtain ⟨m, hm, hwm⟩ := check_reflects hc e pr hw' hw'r
      obtain rfl := Option.some.inj hm
      rcases hwm with e' | h
      · subst e'; exact i.rt_irrefl _ hrt
      · exact hc.cc3 _ _ hrt h
  · intro r₁ r₂ w e2 pr₁ h12 hw1
    obtain ⟨s₁, e1⟩ := (hdom r₁).2 pr₁
    have pr₂ := (hdom r₂).1 ⟨_, e2⟩
    have hw2 : WL G HB r₂ w := (hc.cc2 r₂ _ e2 w).2 rfl
    obtain ⟨m, hm, hwm⟩ := check_reflects hc e1 pr₁ hw2.1 hw1
    subst hm
    rcases hwm with e' | h
    · subst e'; exact e1
    · exfalso
      have hm1 : WL G HB r₁ m := (hc.cc2 r₁ _ e1 m).2 rfl
      have hne : r₁ ≠ r₂ := fun e => by subst e; exact i.h.irrefl _ h12
      have h12' : HB r₁ r₂ :=
        (hc.cc1 r₁ r₂ pr₁.1 pr₂.1 (pr₁.2.2.trans pr₂.2.2.symm) hne).2 h12
      exact hw2.2.2 ⟨m, hm1.1, h, hc.trans _ _ _ hm1.2.1 h12'⟩

/-- **The real-time causal views are Mahajan et al.'s check** for the order
that `p`'s reads expose, with single-source writeLists. -/
theorem rview_iff_check (G : OpSig α n) (p : Fin n) (i : RHist G) (v : SMap α) :
    RView G p i v ↔ RTCCheck G p i v :=
  ⟨fun hv => ⟨hv.1, _, rview_check hv⟩, check_rview⟩

end Check

/-! ### One element of a set-valued writeList is not enough -/

namespace Tie

/-- Real time for the two-write history: additionally `a ≺ b`. -/
def rt1 (x y : Fin 3) : Prop := hb0 x y ∨ (x = 0 ∧ y = 1)

instance (x y : Fin 3) : Decidable (rt1 x y) := by unfold rt1; infer_instance

/-- `a → r`, `b → r`, and `a` ended before `b` began. -/
def i1 : RHist G where
  h := h0
  rt := rt1
  rt_mem _ _ _ := ⟨trivial, trivial⟩
  rt_irrefl := by decide
  rt_trans := by decide
  hb_rt _ _ h := Or.inl h
  po := i0.po

/-- The map in which `r` returns `a`. -/
def va : SMap (Fin 3) := ⟨fun x => if x = 2 then some (some 0) else none⟩

theorem wl_two (w : Fin 3) (hw : w = 0 ∨ w = 1) : WL G hb0 2 w := by
  refine ⟨(isW_iff w).2 (by rcases hw with rfl | rfl <;> decide), ⟨hw, rfl⟩, ?_⟩
  rintro ⟨w', _, h1, h2⟩
  rw [h1.2] at h2
  rcases h2.1 with h | h <;> exact absurd h (by decide)

end Tie

/-- **Their reads return all concurrent latest writes; ours return one.**
Reading a single source as merely *one element* of their writeList would be
weaker: at the two-write history where `a` ended before `b` began, the order
`→` passes CC1, delivery and CC3 with writeList `{a, b}` for `r`, but
returning `a` is not a real-time causal view (item (2)).  So the single-source
form of CC2 is "the writeList is `{s(r)}`" (`HBCheck.cc2`). -/
theorem wl_member_not_rview :
    (∀ a, ¬ Tie.hb0 a a) ∧ (∀ a b c, Tie.hb0 a b → Tie.hb0 b c → Tie.hb0 a c) ∧
    (∀ a b, Tie.i1.h.hb a b ↔ Tie.hb0 a b) ∧
    (∀ a b, Tie.i1.rt a b → ¬ Tie.hb0 b a) ∧
    WL Tie.G Tie.hb0 2 0 ∧ WL Tie.G Tie.hb0 2 1 ∧ Tie.i1.rt 0 1 ∧
    ¬ RView Tie.G 0 Tie.i1 Tie.va := by
  refine ⟨by decide, by decide, fun _ _ => Iff.rfl,
    (show ∀ a b, Tie.rt1 a b → ¬ Tie.hb0 b a by decide), Tie.wl_two 0 (Or.inl rfl),
    Tie.wl_two 1 (Or.inr rfl), Or.inr ⟨rfl, rfl⟩, fun hv => ?_⟩
  have h := hv.2.1 2 (some 0) (by simp [Tie.va])
  exact h.2.2 1 (by decide) (show Tie.hb0 1 2 by decide) (Or.inr ⟨rfl, rfl⟩)

/-! ## One-way convergence: the environment supplies delivery -/

section Deliver
variable {α : Type} {n : Nat} {G : OpSig α n}

/-- Add a read `r` of replica `d` that has received the causally closed set
`S` of operations (containing `d`'s own), and that began after every
operation of `i` ended. -/
def deliver (i : RHist G) (d : Fin n) (S : α → Prop) (hSm : ∀ a, S a → i.h.mem a)
    (hSc : ∀ a b, i.h.hb a b → S b → S a) (hSd : ∀ a, i.h.mem a → G.rep a = d → S a)
    (r : α) (hr : ¬ i.h.mem r) (hrd : G.rep r = d) : RHist G where
  h :=
    { mem := fun a => i.h.mem a ∨ a = r
      hb := fun a b => i.h.hb a b ∨ (b = r ∧ S a)
      fin := by
        obtain ⟨l, hl⟩ := i.h.fin
        exact ⟨r :: l, fun a ha => ha.elim (fun h => List.mem_cons_of_mem _ (hl a h))
          (fun e => e ▸ List.mem_cons_self ..)⟩
      hb_mem := by
        rintro a b (h | ⟨rfl, hS⟩)
        · exact ⟨Or.inl (i.h.hb_mem _ _ h).1, Or.inl (i.h.hb_mem _ _ h).2⟩
        · exact ⟨Or.inl (hSm a hS), Or.inr rfl⟩
      irrefl := by
        rintro a (h | ⟨rfl, hS⟩)
        · exact i.h.irrefl a h
        · exact hr (hSm _ hS)
      trans := by
        rintro a b c (h1 | ⟨rfl, hS1⟩) (h2 | ⟨rfl, hS2⟩)
        · exact Or.inl (i.h.trans _ _ _ h1 h2)
        · exact Or.inr ⟨rfl, hSc _ _ h1 hS2⟩
        · exact absurd (i.h.hb_mem _ _ h2).1 hr
        · exact absurd (hSm _ hS2) hr }
  rt := fun a b => i.rt a b ∨ (b = r ∧ i.h.mem a)
  rt_mem := by
    rintro a b (h | ⟨rfl, ha⟩)
    · exact ⟨Or.inl (i.rt_mem _ _ h).1, Or.inl (i.rt_mem _ _ h).2⟩
    · exact ⟨Or.inl ha, Or.inr rfl⟩
  rt_irrefl := by
    rintro a (h | ⟨rfl, ha⟩)
    · exact i.rt_irrefl a h
    · exact hr ha
  rt_trans := by
    rintro a b c (h1 | ⟨rfl, ha⟩) (h2 | ⟨rfl, hb⟩)
    · exact Or.inl (i.rt_trans _ _ _ h1 h2)
    · exact Or.inr ⟨rfl, (i.rt_mem _ _ h1).1⟩
    · exact absurd (i.rt_mem _ _ h2).1 hr
    · exact absurd hb hr
  hb_rt := by
    rintro a b (h | ⟨rfl, hS⟩)
    · exact Or.inl (i.hb_rt _ _ h)
    · exact Or.inr ⟨rfl, hSm _ hS⟩
  po := by
    rintro a b (ha | rfl) (hb | rfl) hrep hne
    · exact (i.po a b ha hb hrep hne).imp Or.inl Or.inl
    · exact Or.inl (Or.inr ⟨rfl, hSd a ha (hrep.trans hrd)⟩)
    · exact Or.inr (Or.inr ⟨rfl, hSd b hb (hrep.symm.trans hrd)⟩)
    · exact absurd rfl hne

/-- **One-way convergence needs no separate hypothesis.**  For any input `i`,
replica `d`, and causally closed set `S` of operations of `i` containing
`d`'s own (for one-way convergence from `s`: `s`'s operations, their causal
past, and `d`'s operations), the environment supplies an input extension in
which a new read `r` of `d` has received `S`; and every real-time causal view
of `d` there returns for `r` a write such that each write of `S` is that
write or precedes it, in every order passing Mahajan et al.'s check. -/
theorem one_way_convergence (i : RHist G) (d : Fin n) (S : α → Prop)
    (hSm : ∀ a, S a → i.h.mem a) (hSc : ∀ a b, i.h.hb a b → S b → S a)
    (hSd : ∀ a, i.h.mem a → G.rep a = d → S a)
    (r : α) (hr : ¬ i.h.mem r) (hrW : G.isW r = false) (hrd : G.rep r = d) :
    ∃ j : RHist G, i ≼ j ∧ PRead G j.h d r ∧ (∀ a, S a → j.h.hb a r) ∧
      ∀ v, RView G d j v → (∃ HB, HBCheck j d v HB) ∧
        ∀ HB, HBCheck j d v HB → ∀ w, S w → G.isW w = true →
          ∃ m, v.f r = some (some m) ∧ (w = m ∨ HB w m) := by
  let j := deliver i d S hSm hSc hSd r hr hrd
  have pr : PRead G j.h d r := ⟨Or.inr rfl, hrW, hrd⟩
  have hjS : ∀ a, S a → j.h.hb a r := fun a ha => Or.inr ⟨rfl, ha⟩
  have hle : i ≼ j := by
    refine ⟨⟨fun a ha => Or.inl ha, ?_, ?_⟩, ?_⟩
    · rintro a b (h | ⟨rfl, hS⟩) hb
      · exact (i.h.hb_mem _ _ h).1
      · exact hSm a hS
    · intro a b ha hb
      refine ⟨fun h => h.elim id ?_, Or.inl⟩
      rintro ⟨rfl, _⟩; exact absurd hb hr
    · intro a b ha hb
      refine ⟨fun h => h.elim id ?_, Or.inl⟩
      rintro ⟨rfl, _⟩; exact absurd hb hr
  refine ⟨j, hle, pr, hjS, fun v hv => ⟨⟨_, rview_check hv⟩, fun HB hc w hS hw => ?_⟩⟩
  obtain ⟨s, hs⟩ := (hv.1 r).2 pr
  obtain ⟨m, rfl, hwm⟩ := check_reflects hc hs pr hw (hjS w hS)
  exact ⟨m, hs, hwm⟩

end Deliver

/-! ## Implementations that do not observe real time -/

section Impl
variable {α : Type} {n : Nat} {G : OpSig α n}

/-- An abstract implementation, at the level of its executions: at each
environment `i` (the workload and deliveries `i.h`, the timing `i.rt`), read
`r` returns the writeList `{w | wl i r w}` (Mahajan et al.'s reads return
sets). -/
structure MImpl (G : OpSig α n) where
  wl : RHist G → α → α → Prop

/-- "The implementation does not have access to real time": its answers
depend only on the history. -/
def MImpl.NoRealTime (I : MImpl G) : Prop :=
  ∀ i i' : RHist G, i.h = i'.h → I.wl i = I.wl i'

/-- A single source drawn from a writeList (`v₀` from an empty one). -/
def FromWL (W : α → Prop) : Option α → Prop
  | none => ∀ w, ¬ W w
  | some w => W w

/-- The strengthening of the real-time causal product interface induced by an
implementation: the tuples of real-time causal views whose sources come from
its writeLists. -/
def MImpl.str (I : MImpl G) : NormStr (W := fun _ => SMap α) (RView G) where
  sel i y := (∀ p, RView G p i (y p)) ∧
    ∀ p r s, (y p).f r = some s → FromWL (I.wl i r) s
  sub _ _ h := h.1

/-- **Real-time blindness is "does not observe real time".**  The
strengthening of an implementation that does not observe real time is
real-time blind: a selected tuple stays selected with fewer real-time edges,
provided its views are still real-time causal there. -/
theorem MImpl.rblind (I : MImpl G) (h : I.NoRealTime) : RBlind I.str := by
  intro i i' hh _ y hy hv
  refine ⟨hv, ?_⟩
  have e : I.wl i = I.wl i' := h i i' hh.symm
  rw [e]
  exact hy.2

/-- Their proof uses the assumption to make one of two concurrent writes end
before the other begins (execution `e''`).  Ours forces a view `v` with the
input `forceRt`, which has the same history and more real-time edges; each
added edge puts a write `x` that a read `r` saw but did not return before
`r`'s source `w`, and `w ≺ x` did not hold. -/
theorem forceRt_swap {i : RHist G} {p : Fin n} {v : SMap α} (hv : RView G p i v)
    {r x w : α} (e : Ed G i v r x w) :
    (forceRt i (rview_good G hv)).h = i.h ∧
    (∀ a b, i.rt a b → (forceRt i (rview_good G hv)).rt a b) ∧
    (forceRt i (rview_good G hv)).rt x w ∧ ¬ i.rt w x :=
  ⟨rfl, fun _ _ h => Or.inl h, Or.inr ⟨r, x, w, e, Or.inl rfl, Or.inl rfl⟩,
   (hv.2.1 r _ e.1).2.2 x e.2.1 e.2.2.1⟩

end Impl

/-! ## Always availability: totality and Deployment Availability -/

section Avail
variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {n : Nat} {D : Type}

/-- The empty history: every participant at its canonical state. -/
theorem da_start {Dp : Deployment sp n} (Sys : System sp D)
    (hDA : DeploymentAvailability Sys Dp) (comp : Fin n → Nat) (hcomp : ∃ p q, comp p ≠ comp q)
    (i : I) (p : Fin n) (o : O) (ho : Dp.A p i o) :
    ∃ ext : History sp D n, WF (fun _ => i) ext ∧ Produced Sys n (fun _ => i) ext ∧
      Partitioned ext comp ∧ (∀ q, comp q ≠ comp p → ext q = []) ∧
      (∀ q j, LEv.inp j ∉ ext q) ∧ LEv.out o ∈ ext p := by
  let H0 : History sp D n := fun _ => []
  have hwf0 : WF (fun _ => i) H0 :=
    wf_of_ne (fun p => ⟨_, .nil _⟩) (by intro p a q k j d b h; simp [H0] at h)
  have hprod0 : Produced Sys n (fun _ => i) H0 := fun p a e b h => by simp [H0] at h
  have hpart0 : Partitioned H0 comp := ⟨hcomp, by intro p a q k j d b h; simp [H0] at h⟩
  have hcut : IsCut H0 (fun _ => 0) :=
    ⟨fun _ => Nat.zero_le _, by intro p a q k j d b h; simp [H0] at h⟩
  have hσ : LRun (canon sp i) ((H0 p).take 0) (canon sp i) := .nil _
  obtain ⟨H', ext, hext, hwf, hprod, hpart, hout, hnoinp, hγ⟩ :=
    hDA (fun _ => i) H0 comp hwf0 hprod0 hpart0 _ hcut p _ hσ o
      ⟨Dp.sub _ _ _ ho, PO.refl i⟩ ho
  have e : H' = ext := funext fun q => by rw [hext q]; simp [H0]
  subst e
  exact ⟨H', hwf, hprod, hpart, hout, hnoinp, hγ⟩

/-- Deployment Availability realizes any one-shot family: with every
participant in its own block, each emits its authorized row at `i` in a
message-free, input-free run of the system. -/
theorem da_realize (hn : 2 ≤ n) {Dp : Deployment sp n} (Sys : System sp D)
    (hDA : DeploymentAvailability Sys Dp) (i : I) (o : Fin n → O) (ho : ∀ p, Dp.A p i (o p)) :
    ∃ H : History sp D n, WF (fun _ => i) H ∧ Produced Sys n (fun _ => i) H ∧
      Partitioned H (fun p => p.val) ∧ (∀ p q k j d, LEv.recv q k j d ∉ H p) ∧
      (∀ p j, LEv.inp j ∉ H p) ∧ ∀ p, LEv.out (o p) ∈ H p := by
  have hcomp : ∃ p q : Fin n, p.val ≠ q.val :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have hL : ∀ p, ∃ ext : History sp D n, WF (fun _ => i) ext ∧ Produced Sys n (fun _ => i) ext ∧
      Partitioned ext (fun p => p.val) ∧ (∀ q, q.val ≠ p.val → ext q = []) ∧
      (∀ q j, LEv.inp j ∉ ext q) ∧ LEv.out (o p) ∈ ext p :=
    fun p => da_start Sys hDA _ hcomp i p (o p) (ho p)
  let E : Fin n → History sp D n := fun p => Classical.choose (hL p)
  have hE : ∀ p, _ := fun p => Classical.choose_spec (hL p)
  let H : History sp D n := fun p => E p p
  have hnr : ∀ p q k j d, LEv.recv q k j d ∉ H p := by
    intro p q k j d hm
    obtain ⟨a, b, hab⟩ := List.append_of_mem hm
    have h1 := ((hE p).1.matched p a q k j d b hab).1
    have h2 := (hE p).2.2.1.2 p a q k j d b hab
    exact h1 (Fin.ext h2)
  refine ⟨H, ?_, fun p => (hE p).2.1 p, ⟨hcomp, ?_⟩, hnr, fun p => (hE p).2.2.2.2.1 p,
    fun p => (hE p).2.2.2.2.2⟩
  · exact CAP.wf_of_noRecv (fun p => (hE p).1.runs p) hnr
  · intro p a q k j d b h
    exact absurd (by rw [h]; simp) (hnr p q k j d)

/-- Reconciliation: if the system has Partition Consistency, the outputs of a
realized one-shot family have a common output extension in `P(i)`. -/
theorem realized_reconciled (Sys : System sp D) (hPC : PartitionConsistency Sys)
    (i : I) (o : Fin n → O) (H : History sp D n) (hwf : WF (fun _ => i) H)
    (hprod : Produced Sys n (fun _ => i) H) (hpart : Partitioned H (fun p => p.val))
    (hni : ∀ p j, LEv.inp j ∉ H p) (hout : ∀ p, LEv.out (o p) ∈ H p) :
    ∃ u, sp.P i u ∧ ∀ p, o p ≼ u := by
  have hj : ∀ p σ, LRun (canon sp ((fun _ => i) p)) (H p) σ → σ.cur ≼ i := by
    intro p σ h
    rw [lrun_noinp h (hni p)]; exact PO.refl _
  obtain ⟨τ, hτj, ext, _, hτ⟩ :=
    (CAP.partitionConsistency_iff_atEnd Sys).1 hPC n (fun _ => i) H _ hwf hprod hpart i hj
  obtain ⟨u, hu⟩ := τ.hasCur
  rw [hτj] at hu
  refine ⟨u, τ.sub _ _ hu, fun p => ?_⟩
  obtain ⟨σ', h2, h3⟩ := lrun_append.1 (hτ p)
  exact lrun_out_mem h2 (hout p) i u ((lrun_mono h3).2 i u hu)

end Avail

section Correspondence
variable {α : Type} {n : Nat} {G : OpSig α n}

/-- `T` selects a tuple at every input: its specification is total. -/
theorem sel_total (T : NormStr (W := fun _ => SMap α) (RView G))
    (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.P i x ↔ T.table i x) (i : RHist G) : ∃ y, T.sel i y := by
  obtain ⟨x, hx⟩ := sp.total i
  obtain ⟨y, hy, _⟩ := (hsp _ _).1 hx
  exact ⟨y, hy⟩

/-- A selected tuple answers every read of every replica. -/
theorem sel_answers (T : NormStr (W := fun _ => SMap α) (RView G)) {i : RHist G}
    {y : Fin n → SMap α} (h : T.sel i y) (p : Fin n) (r : α) :
    PRead G i.h p r ↔ ∃ s, (y p).f r = some s :=
  ((T.sub i y h p).1 r).symm

/-- A selected tuple's restriction to `p` is a row authorized for `p`. -/
theorem sel_owner_row (T : NormStr (W := fun _ => SMap α) (RView G))
    (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.P i x ↔ T.table i x) {i : RHist G} {y : Fin n → SMap α}
    (h : T.sel i y) (p : Fin n) : (ownerD sp).A p i (restrictTo y p) := by
  refine ⟨(hsp _ _).2 ⟨y, h, fun q => ?_⟩, fun q hq => by simp [restrictTo, hq]⟩
  by_cases hq : q = p
  · subst hq; right; simp [restrictTo]
  · left; simp [restrictTo, hq]

/-- **Always availability.**  `T` selects a tuple at every input, and with
Deployment Availability, in every partition, at every input, each replica
emits that tuple's view for its own reads (answering every read of `p`) in
a run of the system that uses only its own block and no new input. -/
theorem always_available (T : NormStr (W := fun _ => SMap α) (RView G))
    (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.P i x ↔ T.table i x) {D : Type} (Sys : System sp D)
    (hDA : DeploymentAvailability Sys (ownerD sp)) (comp : Fin n → Nat)
    (hcomp : ∃ p q, comp p ≠ comp q) (i : RHist G) (p : Fin n) :
    ∃ (y : Fin n → SMap α) (ext : History sp D n), T.sel i y ∧
      (∀ r, PRead G i.h p r ↔ ∃ s, (y p).f r = some s) ∧
      WF (fun _ => i) ext ∧ Produced Sys n (fun _ => i) ext ∧ Partitioned ext comp ∧
      (∀ q, comp q ≠ comp p → ext q = []) ∧ (∀ q j, LEv.inp j ∉ ext q) ∧
      LEv.out (restrictTo y p) ∈ ext p := by
  obtain ⟨y, hy⟩ := sel_total T sp hsp i
  obtain ⟨ext, h⟩ := da_start Sys hDA comp hcomp i p _ (sel_owner_row T sp hsp hy p)
  exact ⟨y, ext, hy, sel_answers T hy p, h⟩

/-- **Mahajan et al.'s Theorem 3.1, from ours.**  Let `T` be a strict ("stronger
than RTC"), real-time blind ("does not observe real time") strengthening of
the real-time causal product interface, with `|𝒩| ≥ 2`, and let `Sys` be any
system for `T`'s specification with Deployment Availability under the owner
deployment ("always available").  Then `Sys` produces a partitioned,
message-free history in which every replica `p`, at one input `i`, emits a
real-time causal view `y p` of its reads, and the tuple `y` (a real-time
causal execution) is not selected by `T`: no row of `T` at `i` extends all
the outputs.

Carried by `rtc_locCons` (the step of Prop. `prop:rtc-maximal`) and
`strengthening_witness` (Theorem `thm:product-frontier`(2)); `da_realize`
runs the separable family in the system. -/
theorem mahajan_rtc (hn : 2 ≤ n) (T : NormStr (W := fun _ => SMap α) (RView G))
    (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.P i x ↔ T.table i x) (hbl : RBlind T) (hst : T.Strict)
    {D : Type} (Sys : System sp D) (hDA : DeploymentAvailability Sys (ownerD sp)) :
    ∃ (i : RHist G) (y : Fin n → SMap α) (H : History sp D n),
      (∀ p, RView G p i (y p)) ∧ ¬ T.sel i y ∧
      WF (fun _ => i) H ∧ Produced Sys n (fun _ => i) H ∧ Partitioned H (fun p => p.val) ∧
      (∀ p q k j d, LEv.recv q k j d ∉ H p) ∧ (∀ p j, LEv.inp j ∉ H p) ∧
      (∀ p, LEv.out (restrictTo y p) ∈ H p) ∧
      ¬ ∃ u, sp.P i u ∧ ∀ p, restrictTo y p ≼ u := by
  obtain ⟨i, y, hyV, hny, hauth, hno⟩ :=
    strengthening_witness (RView G) rview_antichain T sp hsp (rtc_locCons T sp hsp hbl) hst
  obtain ⟨H, h⟩ := da_realize hn Sys hDA i (restrictTo y) hauth
  exact ⟨i, y, H, hyV, hny, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, hno⟩

/-- ... so no such system has Partition Consistency: the replicas' answers
cannot be reconciled after the partition heals. -/
theorem mahajan_rtc_not_partitionConsistency (hn : 2 ≤ n)
    (T : NormStr (W := fun _ => SMap α) (RView G))
    (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.P i x ↔ T.table i x) (hbl : RBlind T) (hst : T.Strict)
    {D : Type} (Sys : System sp D) (hDA : DeploymentAvailability Sys (ownerD sp)) :
    ¬ PartitionConsistency Sys := by
  intro hPC
  obtain ⟨i, y, H, _, _, hwf, hprod, hpart, _, hni, hout, hno⟩ :=
    mahajan_rtc hn T sp hsp hbl hst Sys hDA
  exact hno (realized_reconciled Sys hPC i (restrictTo y) H hwf hprod hpart hni hout)

/-- The same for an implementation: an implementation that does not observe
real time, whose induced strengthening is strict and selects a tuple at every
input, has no always-available (Deployment Availability) system with
Partition Consistency. -/
theorem mahajan_rtc_impl (hn : 2 ≤ n) (Im : MImpl G) (hrt : Im.NoRealTime)
    (sp : Spec (RHist G) (PTd (fun _ : Fin n => SMap α)))
    (hsp : ∀ i x, sp.P i x ↔ Im.str.table i x) (hst : Im.str.Strict)
    {D : Type} (Sys : System sp D) (hDA : DeploymentAvailability Sys (ownerD sp)) :
    ¬ PartitionConsistency Sys :=
  mahajan_rtc_not_partitionConsistency hn Im.str sp hsp (Im.rblind hrt) hst Sys hDA

end Correspondence

end Deploy
end CC
