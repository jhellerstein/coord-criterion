import CoordCriterion.Instances.QueryRefinements

/-!
# Placement models and the input orders they justify (Section 6.1)

Supports the sentences of `sec:query-instance` (`paper/instances.tex`)
"We model each data placement by an input order.  For the placement that
Ameloot et al. call “policy-aware”, `I ∪ J` extends `I` only when `J` is
domain-distinct from `I`; for “domain-guided” placement, only when `J` is
domain-disjoint from `I`.  Under these orders, functional monotonicity is
exactly domain-distinct- and domain-disjoint-monotonicity, so Functional CALM
gives their characterizations."  The first sentence is a modeling declaration;
this file checks that each order matches the placement model it stands for.

Source.  The text cites the TODS paper of Ameloot, Ketsman, Neven and Zinn,
"Weaker forms of monotonicity for declarative networking" (2015).  Its PODS
2014 version is local (`references-papers/ameloot-weaker.pdf`).  Its §4.1.1
defines a distribution policy `P` (a total function from facts to non-empty
node sets) and a domain-guided policy (`P(R(a₁,…,aₖ)) = ⋃ᵢ α(aᵢ)` for a domain
assignment `α`), and its policy-aware transducers can query the policy for
facts over their known values (`MyAdom`, `policy_R`).  Its Definition 1 gives
the two weaker forms of monotonicity.  These are Zinn, Green and Ludäscher's
models (ICDT 2012, `references-papers/zinn.pdf`), there called `N1` and `N2`;
the definitions below follow them:

* `N0` (the original model): input is placed arbitrarily, no node knows how.
* `N1` (policy-aware): a partitioning policy `P` assigns every fact to a
  non-empty set of nodes, the input is placed by `P`, and "node `nⱼ` can answer
  the boolean query 'Is `nⱼ ∈ P(f)`?' for facts `f` that `nⱼ` can construct"
  (Zinn, CoRR 1202.0242, §2.2), i.e. whose constants are all known to it.
* `N2` (domain-guided): as `N1`, for policies compatible with some
  `F : dom → 2^N \ {∅}`: `P(R(c₁,…,cₙ)) = ⋃ᵢ F(cᵢ)` for non-nullary `R`.

What the Lean models.  A *scenario* is a policy `P` and a global input `H`.
A node `x`, after it has received the complete local inputs of a set `C ∋ x`
of nodes (`C = {x}` before any message; this is the state coordination-freeness
is about), holds `known P H C`.  Its *view* is the local input of each
`z ∈ C` and, in the policy-aware models, each `z ∈ C`'s policy answer for the
facts constructible from `known P H C` (`SameView`).  This grants the node at
least what it can learn, so "cannot rule out" is not understated.  It cannot
rule out `H'` when some admissible `P'` gives the same view (`Model.Unruled`).
It *knows which facts over its known values are absent* when every such fact
is assigned to some node of `C` (`Complete`); whether this holds depends only
on the view (`complete_of_sameView`).

Results (correspondence).  For a complete view and a node not yet heard from
(`¬ C y`), the unruled global inputs are exactly the extensions of
`known P H C` in the domain-distinct order under policy-aware placement
(`policyAware_unruled`), in the domain-disjoint order under domain-guided
placement (`domainGuided_unruled`, assuming every value has a fact whose only
value it is, e.g. `R(v,…,v)`), and in plain inclusion under `N0`
(`oblivious_unruled`).  Without completeness the policy-aware node also cannot
rule out constructible facts it has not heard about; completeness is the
"can learn which facts are absent" of the text.

Results (their CALM variants from ours).  `CFComputes M x Q out` is the
knowledge-level reading of "coordination-free computation of `Q`": `out` is
node `x`'s output as a function of its view; it is sound (never outside
`Q(H)`), complete once `x` has heard from every node, and coordination-free:
when the policy places all input at `x` (the only policy of the one-node
network in Zinn's proof of Lemma 3.7), `x` outputs `Q(H)` before any message.
`cf_iff_consistent` shows, for any model that justifies an order in the
sense above, that such a computation exists exactly when the graph of `Q` over
that order is consistent; the proof is the correspondence plus Functional CALM
(`QRef.rmono_iff_consistent`, i.e. `functional_calm`).  Instantiated:
coordination-free under policy-aware placement iff domain-distinct-monotone
(`policyAware_cf_iff`), under domain-guided placement iff
domain-disjoint-monotone (`domainGuided_cf_iff`), under `N0` iff monotone
(`oblivious_cf_iff`).  Transducer runs (relational programs, message buffers,
fairness, genericity) are not modeled; `out` may be any function of the view.
-/

namespace CC
namespace Place

open CC.CALM (PSet)
open CC.QRef (InAdom DistinctFrom DisjointFrom distinctAdm disjointAdm allAdm ExtInp Adm)
open CC.Comp (Monotone graph)

variable {F V N : Type}

/-! ## Policies, local inputs, views -/

/-- A distribution policy: `P f z` says fact `f` is placed at node `z`. -/
abbrev Policy (F N : Type) := F → N → Prop

/-- Every fact is assigned to a non-empty set of nodes (Zinn §2.2). -/
def Total (P : Policy F N) : Prop := ∀ f, ∃ z, P f z

/-- Domain-guided (Zinn's `N2`-compatible) policy: some `α : V → 2^N \ {∅}`
with `P(f) = ⋃_{v ∈ f} α(v)` for every non-nullary `f`. -/
def DomainGuided (vals : F → V → Prop) (P : Policy F N) : Prop :=
  Total P ∧ ∃ α : V → N → Prop, (∀ v, ∃ z, α v z) ∧
    ∀ f, (∃ v, vals f v) → ∀ z, (P f z ↔ ∃ v, vals f v ∧ α v z)

/-- Every fact placed at `x`: the only policy of a one-node network. -/
def allAt (x : N) : Policy F N := fun _ z => z = x

/-- Local input of node `z`. -/
def loc (P : Policy F N) (H : PSet F) (z : N) : PSet F := ⟨fun f => H.mem f ∧ P f z⟩

/-- What a node holds after receiving the local inputs of the nodes in `C`. -/
def known (P : Policy F N) (H : PSet F) (C : N → Prop) : PSet F :=
  ⟨fun f => ∃ z, C z ∧ (loc P H z).mem f⟩

/-- `f` can be constructed from `K`: all its values are in `adom(K)`. -/
def Cons (vals : F → V → Prop) (K : PSet F) (f : F) : Prop := ∀ v, vals f v → InAdom vals K v

/-- The nodes of `C` have the same local inputs in both scenarios. -/
def SameLocal (P : Policy F N) (H : PSet F) (P' : Policy F N) (H' : PSet F) (C : N → Prop) :
    Prop :=
  ∀ z, C z → ∀ f, (loc P H z).mem f ↔ (loc P' H' z).mem f

/-- Same view under policy awareness: same local inputs, and the same policy
answers of the nodes of `C` on every constructible fact. -/
def SameView (vals : F → V → Prop) (P : Policy F N) (H : PSet F) (P' : Policy F N)
    (H' : PSet F) (C : N → Prop) : Prop :=
  SameLocal P H P' H' C ∧ ∀ z, C z → ∀ f, Cons vals (known P H C) f → (P f z ↔ P' f z)

/-- The node knows which facts over its known values are absent: each is
assigned to a node it has heard from completely. -/
def Complete (vals : F → V → Prop) (P : Policy F N) (H : PSet F) (C : N → Prop) : Prop :=
  ∀ f, Cons vals (known P H C) f → ∃ z, C z ∧ P f z

theorem known_eq {P P' : Policy F N} {H H' : PSet F} {C : N → Prop}
    (h : SameLocal P H P' H' C) : known P H C = known P' H' C :=
  QRef.PSet.ext' fun f =>
    ⟨fun ⟨z, hz, hf⟩ => ⟨z, hz, (h z hz f).1 hf⟩, fun ⟨z, hz, hf⟩ => ⟨z, hz, (h z hz f).2 hf⟩⟩

theorem sameLocal_symm {P P' : Policy F N} {H H' : PSet F} {C : N → Prop}
    (h : SameLocal P H P' H' C) : SameLocal P' H' P H C :=
  fun z hz f => (h z hz f).symm

theorem sameView_symm {vals : F → V → Prop} {P P' : Policy F N} {H H' : PSet F} {C : N → Prop}
    (h : SameView vals P H P' H' C) : SameView vals P' H' P H C :=
  ⟨sameLocal_symm h.1, fun z hz f hf => (h.2 z hz f (known_eq h.1 ▸ hf)).symm⟩

/-- Completeness is read off the view: the node can tell when it holds. -/
theorem complete_of_sameView {vals : F → V → Prop} {P P' : Policy F N} {H H' : PSet F}
    {C : N → Prop} (h : SameView vals P H P' H' C) (hc : Complete vals P H C) :
    Complete vals P' H' C := fun f hf => by
  have hf' : Cons vals (known P H C) f := known_eq h.1 ▸ hf
  obtain ⟨z, hz, hP⟩ := hc f hf'
  exact ⟨z, hz, (h.2 z hz f hf').1 hP⟩

theorem known_sub (P : Policy F N) (H : PSet F) (C : N → Prop) : known P H C ≼ H :=
  fun _ ⟨_, _, hf, _⟩ => hf

theorem known_allAt (x : N) (H : PSet F) : known (allAt x) H (· = x) = H :=
  QRef.PSet.ext' fun _ => ⟨fun ⟨_, _, hf, _⟩ => hf, fun hf => ⟨x, rfl, hf, rfl⟩⟩

theorem known_univ {P : Policy F N} (hP : Total P) (H : PSet F) : known P H (fun _ => True) = H :=
  QRef.PSet.ext' fun f => ⟨fun ⟨_, _, hf, _⟩ => hf, fun hf =>
    let ⟨z, hz⟩ := hP f; ⟨z, trivial, hf, hz⟩⟩

theorem cons_of_mem (vals : F → V → Prop) {K : PSet F} {f : F} (hf : K.mem f) : Cons vals K f :=
  fun _ hv => ⟨f, hf, hv⟩

theorem cons_of_not_distinct (vals : F → V → Prop) {K : PSet F} {f : F}
    (h : ¬ DistinctFrom vals K f) : Cons vals K f :=
  fun v hv => Classical.byContradiction fun hn => h ⟨v, hv, hn⟩

theorem not_cons_of_distinct (vals : F → V → Prop) {K : PSet F} {f : F}
    (h : DistinctFrom vals K f) : ¬ Cons vals K f :=
  fun hc => let ⟨v, hv, hn⟩ := h; hn (hc v hv)

/-! ## Placement models -/

/-- A placement model: admissible policies, when two scenarios give a node
that has heard from `C` the same view, and when that node knows which facts
over its known values are absent. -/
structure Model (F N : Type) where
  adm : Policy F N → Prop
  same : Policy F N → PSet F → Policy F N → PSet F → (N → Prop) → Prop
  complete : Policy F N → PSet F → (N → Prop) → Prop
  adm_total : ∀ {P}, adm P → Total P
  same_local : ∀ {P H P' H' C}, same P H P' H' C → SameLocal P H P' H' C
  same_refl : ∀ P H C, same P H P H C
  same_symm : ∀ {P H P' H' C}, same P H P' H' C → same P' H' P H C
  complete_same : ∀ {P H P' H' C}, same P H P' H' C → complete P H C → complete P' H' C

/-- The node cannot rule out global input `H'`: some admissible policy gives
the same view. -/
def Model.Unruled (M : Model F N) (P : Policy F N) (H : PSet F) (C : N → Prop) (H' : PSet F) :
    Prop :=
  ∃ P', M.adm P' ∧ M.same P H P' H' C

/-- `M` justifies the input order `ExtInp a`: at a complete view, the unruled
inputs extend `known P H C` in that order, and while some node `y` has not
been heard from, every such extension is unruled. -/
structure Model.Justifies (M : Model F N) (a : Adm F) (y : N) : Prop where
  unruled_le : ∀ P H C H', M.adm P → M.complete P H C → M.Unruled P H C H' →
    (⟨known P H C⟩ : ExtInp a) ≼ ⟨H'⟩
  le_unruled : ∀ P H C H', M.adm P → ¬ C y → M.complete P H C →
    (⟨known P H C⟩ : ExtInp a) ≼ ⟨H'⟩ → M.Unruled P H C H'

/-- Original model (`N0`): any placement, no knowledge of it; the view is the
local inputs. -/
def oblivious (F N : Type) : Model F N where
  adm := Total
  same := SameLocal
  complete _ _ _ := True
  adm_total h := h
  same_local h := h
  same_refl _ _ _ _ _ _ := Iff.rfl
  same_symm h := sameLocal_symm h
  complete_same _ _ := trivial

/-- Policy-aware placement (Zinn's `N1`). -/
def policyAware (vals : F → V → Prop) (N : Type) : Model F N where
  adm := Total
  same := SameView vals
  complete := Complete vals
  adm_total h := h
  same_local h := h.1
  same_refl _ _ _ := ⟨fun _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩
  same_symm h := sameView_symm h
  complete_same h hc := complete_of_sameView h hc

/-- Domain-guided placement (Zinn's `N2`). -/
def domainGuided (vals : F → V → Prop) (N : Type) : Model F N where
  adm := DomainGuided vals
  same := SameView vals
  complete := Complete vals
  adm_total h := h.1
  same_local h := h.1
  same_refl _ _ _ := ⟨fun _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩
  same_symm h := sameView_symm h
  complete_same h hc := complete_of_sameView h hc

/-! ## Which inputs a node cannot rule out -/

/-- Send the facts of `H' \ K` to `y`, keep `P` elsewhere. -/
def redirect (P : Policy F N) (K H' : PSet F) (y : N) : Policy F N := fun f z =>
  (H'.mem f ∧ ¬ K.mem f ∧ z = y) ∨ (¬ (H'.mem f ∧ ¬ K.mem f) ∧ P f z)

theorem redirect_total {P : Policy F N} (hP : Total P) (K H' : PSet F) (y : N) :
    Total (redirect P K H' y) := fun f => by
  by_cases h : H'.mem f ∧ ¬ K.mem f
  · exact ⟨y, Or.inl ⟨h.1, h.2, rfl⟩⟩
  · obtain ⟨z, hz⟩ := hP f; exact ⟨z, Or.inr ⟨h, hz⟩⟩

theorem redirect_eq {P : Policy F N} {K H' : PSet F} {y : N} {f : F}
    (h : ¬ (H'.mem f ∧ ¬ K.mem f)) (z : N) : redirect P K H' y f z ↔ P f z :=
  ⟨fun h' => h'.elim (fun ⟨a, b, _⟩ => absurd ⟨a, b⟩ h) (·.2), fun h' => Or.inr ⟨h, h'⟩⟩

/-- Redirecting `H' \ known` to an unheard node keeps the local inputs of `C`. -/
theorem redirect_sameLocal {P : Policy F N} {H H' : PSet F} {C : N → Prop} {y : N}
    (hy : ¬ C y) (hle : known P H C ≼ H') :
    SameLocal P H (redirect P (known P H C) H' y) H' C := by
  intro z hz f
  constructor
  · intro hf
    have hk : (known P H C).mem f := ⟨z, hz, hf⟩
    exact ⟨hle f hk, Or.inr ⟨fun h => h.2 hk, hf.2⟩⟩
  · rintro ⟨hf, h | ⟨hn, hP⟩⟩
    · exact absurd (h.2.2 ▸ hz) hy
    · have hk : (known P H C).mem f := Classical.byContradiction fun hk => hn ⟨hf, hk⟩
      obtain ⟨w, _, hH, _⟩ := hk
      exact ⟨hH, hP⟩

/-- `N0`: a node cannot rule out any superset of what it holds (ordinary
inclusion). -/
theorem oblivious_unruled {P : Policy F N} {H : PSet F} {C : N → Prop} {y : N}
    (hP : Total P) (hy : ¬ C y) (H' : PSet F) :
    (oblivious F N).Unruled P H C H' ↔ (⟨known P H C⟩ : ExtInp (allAdm F)) ≼ ⟨H'⟩ := by
  constructor
  · rintro ⟨P', _, hs⟩
    refine ⟨fun f hf => ?_, fun _ _ _ => trivial⟩
    rw [known_eq hs] at hf
    exact known_sub P' H' C f hf
  · intro hle
    exact ⟨_, redirect_total hP _ H' y, redirect_sameLocal hy hle.1⟩

theorem oblivious_justifies (y : N) : (oblivious F N).Justifies (allAdm F) y where
  unruled_le _ _ C H' _ _ := fun ⟨P', _, hs⟩ =>
    ⟨fun f hf => known_sub P' H' C f (known_eq hs ▸ hf), fun _ _ _ => trivial⟩
  le_unruled _ _ _ H' hP hy _ hle := ⟨_, redirect_total hP _ H' y, redirect_sameLocal hy hle.1⟩

/-- Policy-aware, the bound: at a complete view, every unruled input extends
what the node holds by domain-distinct facts. -/
theorem policyAware_unruled_le (vals : F → V → Prop) {P : Policy F N} {H : PSet F}
    {C : N → Prop} (hc : Complete vals P H C) {H' : PSet F}
    (hu : (policyAware vals N).Unruled P H C H') :
    (⟨known P H C⟩ : ExtInp (distinctAdm vals)) ≼ ⟨H'⟩ := by
  obtain ⟨P', _, hs⟩ := hu
  refine ⟨fun f hf => known_sub P' H' C f (known_eq hs.1 ▸ hf), fun f hf hk => ?_⟩
  show DistinctFrom vals (known P H C) f
  refine Classical.byContradiction fun hd => ?_
  have hcf := cons_of_not_distinct vals hd
  obtain ⟨z, hz, hPz⟩ := hc f hcf
  exact hk ⟨z, hz, (hs.1 z hz f).2 ⟨hf, (hs.2 z hz f hcf).1 hPz⟩⟩

/-- Policy-aware, attainment: while some node `y` is unheard, every
domain-distinct extension is unruled (no completeness needed). -/
theorem policyAware_le_unruled (vals : F → V → Prop) {P : Policy F N} {H : PSet F}
    {C : N → Prop} {y : N} (hP : Total P) (hy : ¬ C y) {H' : PSet F}
    (hle : (⟨known P H C⟩ : ExtInp (distinctAdm vals)) ≼ ⟨H'⟩) :
    (policyAware vals N).Unruled P H C H' := by
  refine ⟨_, redirect_total hP _ H' y, redirect_sameLocal hy hle.1, fun z _ f hcf => ?_⟩
  have hn : ¬ (H'.mem f ∧ ¬ (known P H C).mem f) := fun ⟨hf, hk⟩ =>
    not_cons_of_distinct vals (hle.2 f hf hk) hcf
  exact (redirect_eq hn z).symm

/-- **Policy-aware placement justifies the domain-distinct order.**  At a
complete view, with some node not yet heard from, the inputs the node cannot
rule out are exactly the domain-distinct extensions of what it holds. -/
theorem policyAware_unruled (vals : F → V → Prop) {P : Policy F N} {H : PSet F}
    {C : N → Prop} {y : N} (hP : Total P) (hy : ¬ C y) (hc : Complete vals P H C)
    (H' : PSet F) :
    (policyAware vals N).Unruled P H C H' ↔ (⟨known P H C⟩ : ExtInp (distinctAdm vals)) ≼ ⟨H'⟩ :=
  ⟨policyAware_unruled_le vals hc, policyAware_le_unruled vals hP hy⟩

theorem policyAware_justifies (vals : F → V → Prop) (y : N) :
    (policyAware vals N).Justifies (distinctAdm vals) y where
  unruled_le _ _ _ _ _ hc hu := policyAware_unruled_le vals hc hu
  le_unruled _ _ _ _ hP hy _ hle := policyAware_le_unruled vals hP hy hle

/-- Every value `v` has a fact whose only value is `v` (e.g. `R(v,…,v)`). -/
def HasDiag (vals : F → V → Prop) : Prop := ∀ v, ∃ g, ∀ w, vals g w ↔ w = v

/-- Domain-guided, the bound: at a complete view, every unruled input extends
what the node holds by domain-disjoint facts. -/
theorem domainGuided_unruled_le (vals : F → V → Prop) (hd : HasDiag vals) {P : Policy F N}
    {H : PSet F} {C : N → Prop} (hc : Complete vals P H C) {H' : PSet F}
    (hu : (domainGuided vals N).Unruled P H C H') :
    (⟨known P H C⟩ : ExtInp (disjointAdm vals)) ≼ ⟨H'⟩ := by
  obtain ⟨P', ⟨_, α, _, hα⟩, hs⟩ := hu
  refine ⟨fun f hf => known_sub P' H' C f (known_eq hs.1 ▸ hf), fun f hf hk => ?_⟩
  -- `f` placed at a node of `C` would already be held
  have held : ∀ z, C z → ¬ P' f z := fun z hz hPz => hk ⟨z, hz, (hs.1 z hz f).2 ⟨hf, hPz⟩⟩
  show DisjointFrom vals (known P H C) f
  refine ⟨?_, fun v hv hvK => ?_⟩
  · -- nullary facts are constructible, hence placed at a node already heard from
    refine Classical.byContradiction fun hne => ?_
    have hcf : Cons vals (known P H C) f := fun v hv => absurd ⟨v, hv⟩ hne
    obtain ⟨z, hz, hPz⟩ := hc f hcf
    exact held z hz ((hs.2 z hz f hcf).1 hPz)
  · -- a known value `v` has a responsible node in `C`, and `f` is placed there too
    obtain ⟨g, hg⟩ := hd v
    have hcg : Cons vals (known P H C) g := fun w hw => (hg w).1 hw ▸ hvK
    obtain ⟨z, hz, hPz⟩ := hc g hcg
    have hP'g := (hs.2 z hz g hcg).1 hPz
    obtain ⟨w, hw, hαw⟩ := (hα g ⟨v, (hg v).2 rfl⟩ z).1 hP'g
    have hαv : α v z := (hg w).1 hw ▸ hαw
    exact held z hz ((hα f ⟨v, hv⟩ z).2 ⟨v, hv, hαv⟩)

/-- Domain-guided, attainment: while some node `y` is unheard, every
domain-disjoint extension is unruled.  The witness keeps `α` on known values
and sends every new value to `y`. -/
theorem domainGuided_le_unruled (vals : F → V → Prop) {P : Policy F N} {H : PSet F}
    {C : N → Prop} {y : N} (hP : DomainGuided vals P) (hy : ¬ C y) {H' : PSet F}
    (hle : (⟨known P H C⟩ : ExtInp (disjointAdm vals)) ≼ ⟨H'⟩) :
    (domainGuided vals N).Unruled P H C H' := by
  obtain ⟨hT, α, hαne, hα⟩ := hP
  let K := known P H C
  let α' : V → N → Prop := fun v z => (InAdom vals K v ∧ α v z) ∨ (¬ InAdom vals K v ∧ z = y)
  let P' : Policy F N := fun f z => ((¬ ∃ v, vals f v) ∧ P f z) ∨ ∃ v, vals f v ∧ α' v z
  have hα' : ∀ v, ∃ z, α' v z := fun v => by
    by_cases h : InAdom vals K v
    · obtain ⟨z, hz⟩ := hαne v; exact ⟨z, Or.inl ⟨h, hz⟩⟩
    · exact ⟨y, Or.inr ⟨h, rfl⟩⟩
  have hdg : DomainGuided vals P' := by
    refine ⟨fun f => ?_, α', hα', fun f hne z => ⟨fun h => h.elim (fun h' => absurd hne h'.1) id,
      Or.inr⟩⟩
    by_cases hne : ∃ v, vals f v
    · obtain ⟨v, hv⟩ := hne
      obtain ⟨z, hz⟩ := hα' v
      exact ⟨z, Or.inr ⟨v, hv, hz⟩⟩
    · obtain ⟨z, hz⟩ := hT f; exact ⟨z, Or.inl ⟨hne, hz⟩⟩
  -- on constructible facts `P'` agrees with `P`
  have hagree : ∀ f, Cons vals K f → ∀ z, (P f z ↔ P' f z) := fun f hcf z => by
    by_cases hne : ∃ v, vals f v
    · rw [hα f hne z]
      constructor
      · rintro ⟨v, hv, hz⟩; exact Or.inr ⟨v, hv, Or.inl ⟨hcf v hv, hz⟩⟩
      · rintro (⟨hn, _⟩ | ⟨v, hv, (⟨_, hz⟩ | ⟨hn, _⟩)⟩)
        · exact absurd hne hn
        · exact ⟨v, hv, hz⟩
        · exact absurd (hcf v hv) hn
    · exact ⟨fun h => Or.inl ⟨hne, h⟩, fun h => h.elim (·.2) fun ⟨v, hv, _⟩ => absurd ⟨v, hv⟩ hne⟩
  refine ⟨P', hdg, fun z hz f => ⟨fun hf => ?_, fun ⟨hf, hPz⟩ => ?_⟩, fun z _ f hcf => hagree f hcf z⟩
  · have hk : K.mem f := ⟨z, hz, hf⟩
    exact ⟨hle.1 f hk, (hagree f (cons_of_mem vals hk) z).1 hf.2⟩
  · by_cases hk : K.mem f
    · exact ⟨known_sub P H C f hk, (hagree f (cons_of_mem vals hk) z).2 hPz⟩
    · obtain ⟨hne, hall⟩ := hle.2 f hf hk
      rcases hPz with ⟨hn, _⟩ | ⟨v, hv, (⟨hvK, _⟩ | ⟨_, rfl⟩)⟩
      · exact absurd hne hn
      · exact absurd hvK (hall v hv)
      · exact absurd hz hy

/-- **Domain-guided placement justifies the domain-disjoint order.**  At a
complete view, with some node not yet heard from, the inputs the node cannot
rule out are exactly the domain-disjoint extensions of what it holds. -/
theorem domainGuided_unruled (vals : F → V → Prop) (hd : HasDiag vals) {P : Policy F N}
    {H : PSet F} {C : N → Prop} {y : N} (hP : DomainGuided vals P) (hy : ¬ C y)
    (hc : Complete vals P H C) (H' : PSet F) :
    (domainGuided vals N).Unruled P H C H' ↔ (⟨known P H C⟩ : ExtInp (disjointAdm vals)) ≼ ⟨H'⟩ :=
  ⟨domainGuided_unruled_le vals hd hc, domainGuided_le_unruled vals hP hy⟩

theorem domainGuided_justifies (vals : F → V → Prop) (hd : HasDiag vals) (y : N) :
    (domainGuided vals N).Justifies (disjointAdm vals) y where
  unruled_le _ _ _ _ _ hc hu := domainGuided_unruled_le vals hd hc hu
  le_unruled _ _ _ _ hP hy _ hle := domainGuided_le_unruled vals hP hy hle

/-! ## Their CALM variants from Functional CALM -/

/-- Knowledge-level coordination-free computation of `Q` at node `x`: the
output `out P H C` of `x` after hearing from `C` depends only on its view, is
always contained in `Q(H)`, is all of `Q(H)` once `x` has heard from every
node, and is all of `Q(H)` before any message when all input is placed at `x`. -/
structure CFComputes {A : Type} (M : Model F N) (x : N) (Q : PSet F → PSet A)
    (out : Policy F N → PSet F → (N → Prop) → PSet A) : Prop where
  view : ∀ P H P' H' C, M.adm P → M.adm P' → M.same P H P' H' C → out P H C = out P' H' C
  sound : ∀ P H C, M.adm P → C x → out P H C ≼ Q H
  eventually : ∀ P H, M.adm P → Q H ≼ out P H (fun _ => True)
  coordFree : ∀ H, Q H ≼ out (allAt x) H (· = x)

/-- The strategy "output `Q` of what you hold once you know which facts over
your known values are absent". -/
def waitComplete {A : Type} (M : Model F N) (Q : PSet F → PSet A) :
    Policy F N → PSet F → (N → Prop) → PSet A :=
  fun P H C => ⟨fun q => M.complete P H C ∧ (Q (known P H C)).mem q⟩

/-- **Coordination-free under a placement model iff consistent under the order
it justifies.**  The correspondence (`M.Justifies a y`) turns coordination-free
computation into monotonicity of `J ↦ Q(J)` over `ExtInp a` and back, and
Functional CALM (`QRef.rmono_iff_consistent`) turns that into consistency of
the graph of `Q`. -/
theorem cf_iff_consistent {A : Type} (M : Model F N) (a : Adm F) {x y : N} (hxy : x ≠ y)
    (hJ : M.Justifies a y) (hall : M.adm (allAt x))
    (hallc : ∀ H, M.complete (allAt x) H (· = x))
    (huniv : ∀ P H, M.adm P → M.complete P H (fun _ => True)) (Q : PSet F → PSet A) :
    (∃ out, CFComputes M x Q out) ↔ (graph (fun I : ExtInp a => Q I.set)).Consistent := by
  rw [QRef.rmono_iff_consistent, QRef.rmono_iff_monotone]
  constructor
  · rintro ⟨out, hcf⟩ ⟨H⟩ ⟨H'⟩ hle
    have hle' : (⟨known (allAt x) H (· = x)⟩ : ExtInp a) ≼ ⟨H'⟩ := by
      rw [known_allAt]; exact hle
    obtain ⟨P', hP', hs⟩ :=
      hJ.le_unruled (allAt x) H (· = x) H' hall (fun h => hxy h.symm) (hallc H) hle'
    have h1 := hcf.coordFree H
    rw [hcf.view _ _ _ _ _ hall hP' hs] at h1
    exact PO.trans h1 (hcf.sound P' H' (· = x) hP' rfl)
  · intro hmono
    refine ⟨waitComplete M Q, ⟨?_, ?_, ?_, ?_⟩⟩
    · intro P H P' H' C _ _ hs
      have hk := known_eq (M.same_local hs)
      have hc : M.complete P H C ↔ M.complete P' H' C :=
        ⟨M.complete_same hs, M.complete_same (M.same_symm hs)⟩
      exact QRef.PSet.ext' fun q => by simp only [waitComplete, hk, hc]
    · rintro P H C hP _ q ⟨hc, hq⟩
      exact hmono ⟨known P H C⟩ ⟨H⟩ (hJ.unruled_le P H C H hP hc ⟨P, hP, M.same_refl P H C⟩) q hq
    · intro P H hP q hq
      exact ⟨huniv P H hP, by rw [known_univ (M.adm_total hP)]; exact hq⟩
    · intro H q hq
      exact ⟨hallc H, by rw [known_allAt]; exact hq⟩

theorem allAt_total (x : N) : Total (allAt x : Policy F N) := fun _ => ⟨x, rfl⟩

theorem allAt_domainGuided (vals : F → V → Prop) (x : N) :
    DomainGuided vals (allAt x : Policy F N) :=
  ⟨allAt_total x, fun _ z => z = x, fun _ => ⟨x, rfl⟩,
    fun _ ⟨v, hv⟩ _ => ⟨fun h => ⟨v, hv, h⟩, fun ⟨_, _, h⟩ => h⟩⟩

theorem complete_allAt (vals : F → V → Prop) (x : N) (H : PSet F) :
    Complete vals (allAt x) H (· = x) := fun _ _ => ⟨x, rfl, rfl⟩

theorem complete_univ (vals : F → V → Prop) {P : Policy F N} (hP : Total P) (H : PSet F) :
    Complete vals P H (fun _ => True) := fun f _ => let ⟨z, hz⟩ := hP f; ⟨z, trivial, hz⟩

/-- Policy-aware placement: a coordination-free computation exists iff `Q` is
domain-distinct-monotone (Zinn's `F[N1] = M_adom` in TODS's corrected form). -/
theorem policyAware_cf_iff {A : Type} (vals : F → V → Prop) {x y : N} (hxy : x ≠ y)
    (Q : PSet F → PSet A) :
    (∃ out, CFComputes (policyAware vals N) x Q out) ↔ QRef.DistinctMono vals Q := by
  rw [cf_iff_consistent _ _ hxy (policyAware_justifies vals y) (allAt_total x)
    (complete_allAt vals x) (fun _ H hP => complete_univ vals hP H)]
  exact (QRef.distinctMono_iff vals Q).2

/-- Domain-guided placement: a coordination-free computation exists iff `Q`
is domain-disjoint-monotone (Zinn's `F[N2] = M_weak-adom`). -/
theorem domainGuided_cf_iff {A : Type} (vals : F → V → Prop) (hd : HasDiag vals) {x y : N}
    (hxy : x ≠ y) (Q : PSet F → PSet A) :
    (∃ out, CFComputes (domainGuided vals N) x Q out) ↔ QRef.DisjointMono vals Q := by
  rw [cf_iff_consistent _ _ hxy (domainGuided_justifies vals hd y) (allAt_domainGuided vals x)
    (complete_allAt vals x) (fun _ H hP => complete_univ vals hP.1 H)]
  exact (QRef.disjointMono_iff vals Q).2

/-- Original model: a coordination-free computation exists iff `Q` is
monotone (Ameloot et al.'s CALM Theorem at this level). -/
theorem oblivious_cf_iff {A : Type} {x y : N} (hxy : x ≠ y) (Q : PSet F → PSet A) :
    (∃ out, CFComputes (oblivious F N) x Q out) ↔ ∀ J J' : PSet F, J ≼ J' → Q J ≼ Q J' := by
  rw [cf_iff_consistent _ _ hxy (oblivious_justifies y) (allAt_total x) (fun _ => trivial)
    (fun _ _ _ => trivial), QRef.rmono_iff_consistent]
  exact QRef.allAdm_rmono_iff Q

end Place
end CC
