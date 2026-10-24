import CoordCriterion.CAP.CompleteCAP
import CoordCriterion.CAP.AvailabilityAtEnd

/-!
# Necessity of Lifted Monotonicity, as in the paper

The paper's proof of (1)⇒(2) of Theorem `thm:complete-cap` uses only two
participants at a time.  For rows `(i_1,o_1),…,(i_k,o_k)` with a common
expansion `j` it builds `u_0,…,u_k ∈ S(j)`, each `u_m` refining
`o_1,…,o_m`: totality gives `u_0`, and the step from `u_{m-1}` to `u_m` puts
one participant at `j` (emitting `u_{m-1}`) and one at `i_m` (emitting `o_m`)
in separate components.  `cap_two_step` is that step; `cap_necessary_two`
is the induction.  Both use the paper's end-of-history forms
`AvailabilityAtEnd` and `PartitionConsistencyAtEnd`.
-/

namespace CC
namespace CAP

variable {I O : Type} [PO I] [PO O] {sp : Spec I O} {D : Type}

/-- The induction step: two rows with a common expansion `j` have a common
refinement in `S(j)`.  Two participants in separate components start at `i₁`
and `i₂`; by Availability each emits its output without messages; by
Partition Consistency they reach one state `(j,R)`, whose row `(j,u)`
refines both outputs. -/
theorem cap_two_step (Sys : System sp D) (hA : AvailabilityAtEnd Sys)
    (hP : PartitionConsistencyAtEnd Sys) {i₁ i₂ j : I} {o₁ o₂ : O}
    (h₁ : sp.S i₁ o₁) (h₂ : sp.S i₂ o₂) (hj₁ : i₁ ≼ j) (hj₂ : i₂ ≼ j) :
    ∃ u, sp.S j u ∧ o₁ ≼ u ∧ o₂ ≼ u := by
  classical
  let row : Fin 2 → I × O := fun p => if p.val = 0 then (i₁, o₁) else (i₂, o₂)
  have hrow : ∀ p, sp.S (row p).1 (row p).2 ∧ (row p).1 ≼ j := by
    intro p; simp only [row]; split
    · exact ⟨h₁, hj₁⟩
    · exact ⟨h₂, hj₂⟩
  let init : Fin 2 → I := fun p => (row p).1
  let comp : Fin 2 → Nat := fun p => p.val
  have hcomp2 : ∃ p q : Fin 2, comp p ≠ comp q := ⟨0, 1, by simp [comp]⟩
  -- the empty history: each participant at its canonical state
  let H0 : History sp D 2 := fun _ => []
  have hwf0 : WF init H0 :=
    ⟨fun p => ⟨_, .nil _⟩, by intro p a q k j d b h; simp [H0] at h⟩
  have hprod0 : Produced Sys 2 init H0 := fun p a e b h => by simp [H0] at h
  have hpart0 : Partitioned H0 comp := ⟨hcomp2, by intro p a q k j d b h; simp [H0] at h⟩
  -- Availability: each participant emits its output within its component
  have hL : ∀ p : Fin 2, ∃ L : List (LEv sp D 2),
      (∃ τ, LRun (canon sp (init p)) L τ) ∧ (∀ (q : Fin 2) k j d, LEv.recv q k j d ∉ L) ∧
      Compliant (Allowed Sys 2 init p) L ∧ (∀ j, LEv.inp j ∉ L) ∧
      ∃ γ, LEv.out γ (row p).2 ∈ L := by
    intro p
    have hσ : LRun (canon sp (init p)) (H0 p) (canon sp (init p)) := .nil _
    have ho : (canon sp (init p)).R (canon sp (init p)).cur (row p).2 :=
      ⟨(hrow p).1, PO.refl _⟩
    obtain ⟨ext, hwf', hprod', hpart', _, hnoinp, γ, hγ⟩ :=
      hA 2 init H0 comp hwf0 hprod0 hpart0 p _ hσ _ ho
    have hH' : H0 p ++ ext p = ext p := by simp [H0]
    refine ⟨ext p, ?_, ?_, ?_, hnoinp p, ⟨γ, hγ⟩⟩
    · obtain ⟨τ, h⟩ := hwf'.1 p; exact ⟨τ, hH' ▸ h⟩
    · intro q k j d hm
      obtain ⟨a, b, hab⟩ := List.append_of_mem hm
      have hab' : (fun q => H0 q ++ ext q) p = a ++ LEv.recv q k j d :: b := by
        show H0 p ++ ext p = _; rw [hH']; exact hab
      exact (hwf'.2 p a q k j d b hab').1 (Fin.ext (hpart'.2 p a q k j d b hab'))
    · have := hprod' p; simp only [H0, List.nil_append] at this; exact this
  let Lf : History sp D 2 := fun p => Classical.choose (hL p)
  have hLs : ∀ p, _ := fun p => Classical.choose_spec (hL p)
  have hnrecv : ∀ (p : Fin 2) a (q : Fin 2) k (j' : Option I) (d : D) b,
      Lf p ≠ a ++ LEv.recv q k j' d :: b := by
    intro p a q k j' d b h
    have hm : LEv.recv q k j' d ∈ Lf p := by rw [h]; simp
    exact (hLs p).2.1 q k j' d hm
  -- the two message-free runs form one partitioned history the system produces
  have hwfc : WF init Lf :=
    ⟨fun p => (hLs p).1, fun p a q k j' d b h => absurd h (hnrecv p a q k j' d b)⟩
  have hprodc : Produced Sys 2 init Lf := fun p => (hLs p).2.2.1
  have hpartc : Partitioned Lf comp :=
    ⟨hcomp2, fun p a q k j' d b h => absurd h (hnrecv p a q k j' d b)⟩
  -- no inputs were added, so `j` is still a common expansion
  have hjall : ∀ p σ, LRun (canon sp (init p)) (Lf p) σ → σ.cur ≼ j := by
    intro p σ h
    rw [lrun_noinp h (hLs p).2.2.2.1]
    exact (hrow p).2
  -- Partition Consistency: one state `(j,R)`, with a row `(j,u)`
  obtain ⟨τ, hτj, ext'', _, hτ⟩ := hP 2 init Lf comp hwfc hprodc hpartc j hjall
  obtain ⟨u, hu⟩ := τ.hasCur
  rw [hτj] at hu
  -- rows are never added, and emitting `o` keeps only rows refining `o`
  have href : ∀ p : Fin 2, (row p).2 ≼ u := by
    intro p
    obtain ⟨σ', h2, h3⟩ := lrun_append.1 (hτ p)
    obtain ⟨γ, hγ⟩ := (hLs p).2.2.2.2
    exact lrun_out_mem h2 hγ j u ((lrun_mono h3).2 j u hu)
  exact ⟨u, τ.sub _ _ hu, by simpa [row] using href 0, by simpa [row] using href 1⟩

/-- (1)⇒(2) of Theorem `thm:complete-cap`, by the paper's induction: from
`u_{m-1}` (a common refinement in `S(j)` of the earlier rows) and the next
row, `cap_two_step` gives `u_m`; totality gives `u_0`. -/
theorem cap_necessary_two (Sys : System sp D) (hA : AvailabilityAtEnd Sys)
    (hP : PartitionConsistencyAtEnd Sys) : sp.LiftedMono := by
  apply (liftedMono_iff_commonExpansion _).2
  intro rows hrows j hj
  induction rows with
  | nil => obtain ⟨u, hu⟩ := sp.total j; exact ⟨u, hu, by simp⟩
  | cons r rs ih =>
    obtain ⟨u', hu', hrs⟩ := ih (fun x hx => hrows x (List.mem_cons_of_mem _ hx))
      (fun x hx => hj x (List.mem_cons_of_mem _ hx))
    obtain ⟨u, hu, h1, h2⟩ := cap_two_step Sys hA hP hu' (hrows r (List.mem_cons_self ..))
      (PO.refl j) (hj r (List.mem_cons_self ..))
    refine ⟨u, hu, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h2
    · exact PO.trans (hrs x hx) h1

end CAP
end CC
