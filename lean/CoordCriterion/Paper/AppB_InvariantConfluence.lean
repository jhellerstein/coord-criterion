import CoordCriterion.Instances.Examples

/-!
# Paper App. B, subsection "Invariant confluence" (`appendices/proof-machinery.tex`, `app:iconfluence`)

Statement layer for subsection `app:iconfluence` of
`appendices/proof-machinery.tex` (the model behind Prop.
`prop:iconfluence-lm` and its proof).  Read it side by side with the
`.tex`: entries follow the paper's paragraphs in order; each quotes the
claim it formalizes.  Unlabeled claims are named `«app:iconfluence/<slug>»`;
the proposition itself is stated as `«prop:iconfluence-lm»` in
`Paper/S5_Instances.lean`, and its proof steps here are
`«app:iconfluence/proof-…»`.

Library: `Instances/InvariantConfluence.lean` (namespace `CC.IConf`), plus
`Inst.pre_sub`, `Inst.locValid_sub` in `Instances/Examples.lean`.

Representation (see the module docstring of `Instances/InvariantConfluence`):
states are `IConf.St V := V → Prop` ordered by inclusion, merged by
`St.union`; a history `IConf.Hist Tx` labels finitely many natural-number
event ids with transactions and carries a strict order `lt` (visibility),
numbered along a linear extension; `a ≼ b` means `a` is a downward-closed
sub-order of `b` in which every event keeps its label and exactly its
predecessors (the paper's "`b` expands `a`").  A downward-closed sub-history
is written `j.restrict P _` for a downward-closed id predicate `P`; the
disjoint union is `Hist.dunion` (even/odd ids); adding an event above all
others is `Hist.addTop`.
-/

namespace CC
namespace Paper

/-! ## The model -/

/-- "A transaction history `h` … is a finite partial order of transaction
events, each labeled by a transaction in `T`; `e' < e` means that `e'` was
visible to the replica that ran `e`."  Lean: `IConf.Hist Tx`. -/
abbrev «app:iconfluence/history» (Tx : Type) : Type := IConf.Hist Tx

/-- "History `h'` expands `h` when `h` is a downward-closed sub-order of `h'`,
so an event keeps exactly the predecessors it had."  Lean: `h ≼ h'` unfolds
to: labels of `h` are labels of `h'`, and `h.lt x y ↔ h'.lt x y ∧ y ∈ h`. -/
theorem «app:iconfluence/expansion-order» {Tx : Type} (h h' : IConf.Hist Tx) :
    h ≼ h' ↔ (∀ e t, h.lab e = some t → h'.lab e = some t) ∧
      (∀ x y, h.lt x y ↔ (h'.lt x y ∧ h.ev y)) :=
  Iff.rfl

/-- "The state of a history is computed event by event: `e` runs on
`pre(e) = s₀ ∪ ⋃_{e'<e} post(e')` and produces `post(e) = t_e(pre(e))` …
and `eval(h) = s₀ ∪ ⋃_{e∈h} post(e)`."  Lean: `IConf.pre`, `IConf.post`
(through `IConf.step`, which applies an event's label) and `IConf.eval`. -/
theorem «app:iconfluence/eval» {V Tx : Type} (M : IConf.Model V Tx) (h : IConf.Hist Tx) (e : Nat) :
    (IConf.pre M h e = fun v => M.s0 v ∨ ∃ x, h.lt x e ∧ IConf.post M h x v) ∧
      IConf.post M h e = IConf.step M (h.lab e) (IConf.pre M h e) ∧
      (IConf.eval M h = fun v => M.s0 v ∨ ∃ e, h.ev e ∧ IConf.post M h e v) :=
  ⟨rfl, IConf.post_eq M h e, rfl⟩

/-- "A downward-closed sub-history keeps each event's predecessors, and so
its `pre` and `post`." -/
theorem «app:iconfluence/sub-keeps-pre-post» {V Tx : Type} (M : IConf.Model V Tx)
    {c h : IConf.Hist Tx} (hc : c ≼ h) {e : Nat} (he : c.ev e) :
    IConf.pre M c e = IConf.pre M h e ∧ IConf.post M c e = IConf.post M h e :=
  ⟨Inst.pre_sub M hc he, IConf.post_sub M hc he⟩

/-- "Hence the state of a union of downward-closed sub-histories is the union
of their states."  Lean: if the events of `c ≼ j` are those of `a ≼ j` and
`b ≼ j`, then `eval c = eval a ∪ eval b`. -/
theorem «app:iconfluence/eval-union» {V Tx : Type} (M : IConf.Model V Tx)
    {a b c j : IConf.Hist Tx} (ha : a ≼ j) (hb : b ≼ j) (hc : c ≼ j)
    (hev : ∀ e, c.ev e ↔ a.ev e ∨ b.ev e) :
    IConf.eval M c = (IConf.eval M a).union (IConf.eval M b) :=
  IConf.eval_union M ha hb hc hev

/-- "Because `h` is a partial order and transactions are inflationary
(`t(s) ⊇ s`), `pre(e)` is the state of the sub-history strictly below `e` and
`post(e)` is the state of the sub-history at or below `e`." -/
theorem «app:iconfluence/pre-post-as-eval» {V Tx : Type} (M : IConf.Model V Tx)
    (h : IConf.Hist Tx) (e : Nat) (he : h.ev e) :
    IConf.pre M h e = IConf.eval M (h.restrict (fun x => h.lt x e) (IConf.downset_closed h e)) ∧
      IConf.post M h e =
        IConf.eval M (h.restrict (fun x => h.lt x e ∨ x = e) (IConf.downset'_closed h e)) :=
  ⟨IConf.pre_eq_eval M h e, IConf.post_eq_eval M h e he⟩

/-- "A history is locally valid when every `pre(e)` and `post(e)` satisfies
`𝓘` … It is valid when every downward-closed sub-history `c` has
`𝓘(eval(c))`." -/
theorem «app:iconfluence/valid-def» {V Tx : Type} (M : IConf.Model V Tx) (h : IConf.Hist Tx) :
    (IConf.LocValid M h ↔ ∀ e, h.ev e → M.Inv (IConf.pre M h e) ∧ M.Inv (IConf.post M h e)) ∧
      (IConf.Valid M h ↔ ∀ c, c ≼ h → M.Inv (IConf.eval M c)) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- (Used in the proof) A valid history is locally valid, since `pre(e)` and
`post(e)` are states of downward-closed sub-histories. -/
theorem «app:iconfluence/valid-locally-valid» {V Tx : Type} (M : IConf.Model V Tx)
    {h : IConf.Hist Tx} (hv : IConf.Valid M h) : IConf.LocValid M h :=
  IConf.valid_locValid M hv

/-! ## The specification `S_𝓘` -/

/-- "The specification `S_𝓘` has the locally valid histories as inputs; a
downward-closed sub-order of a locally valid history is locally valid, so the
inputs are closed under the order."  Lean: inputs are the subtype
`IConf.Inp M`; closure is `Inst.locValid_sub`. -/
theorem «app:iconfluence/inputs-closed» {V Tx : Type} (M : IConf.Model V Tx)
    {c h : IConf.Hist Tx} (hc : c ≼ h) (hl : IConf.LocValid M h) : IConf.LocValid M c :=
  Inst.locValid_sub M hc hl

/-- "An output is a state, and `u` covers `s` when `s ⊆ u`. At input `h`, the
system may expose the state of any valid sub-history:
`S_𝓘(h) = {eval(g) : g a downward-closed, valid sub-history of h}`." -/
theorem «app:iconfluence/spec» {V Tx : Type} (M : IConf.Model V Tx) (h : IConf.Inp M)
    (s u : IConf.St V) :
    ((IConf.SI M).S h s ↔ ∃ g, g ≼ h.1 ∧ IConf.Valid M g ∧ IConf.eval M g = s) ∧
      (s ≼ u ↔ ∀ v, s v → u v) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- "Taking `g` empty gives `s₀`, so the specification is total." -/
theorem «app:iconfluence/total» {V Tx : Type} (M : IConf.Model V Tx) (h : IConf.Inp M) :
    (IConf.SI M).S h M.s0 :=
  ⟨IConf.Hist.empty, IConf.Hist.empty_le _, IConf.valid_empty M,
    IConf.eval_noev M IConf.Hist.empty_noev⟩

/-! ## Proof of Proposition `prop:iconfluence-lm` -/

/-- "We use the common-expansion form of Lifted Monotonicity
(Prop. `prop:common-expansion-form`)."  Lean: the proposition in that form. -/
theorem «app:iconfluence/proof-common-expansion-form» {V Tx : Type} (M : IConf.Model V Tx) :
    M.IConfluent ↔ (IConf.SI M).CommonExpansion :=
  IConf.ic_iff_commonExpansion M

/-- First step: "the state of a valid history `g` is reachable, by induction
on `g`." -/
theorem «app:iconfluence/proof-valid-reachable» {V Tx : Type} (M : IConf.Model V Tx)
    {g : IConf.Hist Tx} (hg : IConf.Valid M g) : IConf.Reach M (IConf.eval M g) :=
  IConf.valid_reach M hg

/-- (⇒), key step: "Let `g = g₁ ∪ ⋯ ∪ g_k` … Invariant confluence makes each
successive union valid … Thus `g` is valid."  Lean: two sub-histories
`g₁, g₂ ≼ j` (the list case iterates it inside `ic_commonExpansion`); their
union is the restriction of `j` to the events of `g₁` or `g₂`. -/
theorem «app:iconfluence/proof-union-valid» {V Tx : Type} (M : IConf.Model V Tx)
    (hic : M.IConfluent) {j g₁ g₂ : IConf.Hist Tx} (h₁ : g₁ ≼ j) (h₂ : g₂ ≼ j)
    (v₁ : IConf.Valid M g₁) (v₂ : IConf.Valid M g₂) :
    IConf.Valid M (j.restrict (fun e => g₁.ev e ∨ g₂.ev e) (fun _ _ hl hy =>
      hy.elim (fun h => Or.inl (IConf.Hist.le_down h₁ hl h))
        (fun h => Or.inr (IConf.Hist.le_down h₂ hl h)))) :=
  IConf.union_valid M hic h₁ h₂ v₁ v₂

/-- (⇒), inline: "a valid merge of reachable states is reachable" (a
constructor of `IConf.Reach`). -/
theorem «app:iconfluence/proof-merge-reachable» {V Tx : Type} (M : IConf.Model V Tx)
    {s₁ s₂ : IConf.St V} :
    IConf.Reach M s₁ → IConf.Reach M s₂ → M.Inv (s₁.union s₂) → IConf.Reach M (s₁.union s₂) :=
  IConf.Reach.merge

/-- (⇒): "`eval(g) ∈ S_𝓘(j)` covers every `eval(g_r)`.  For `k = 0`, take `g`
empty." -/
theorem «app:iconfluence/proof-forward» {V Tx : Type} (M : IConf.Model V Tx) :
    M.IConfluent → (IConf.SI M).CommonExpansion :=
  IConf.ic_commonExpansion M

/-- (⇐): "Let `g₁` and `g₂` be valid histories, and let `j` be their disjoint
union, with events renamed apart and no order between the two parts. … `j` is
locally valid."  Lean: locally valid histories are closed under `dunion`, and
`eval (dunion g₁ g₂) = eval g₁ ∪ eval g₂`. -/
theorem «app:iconfluence/proof-disjoint-union» {V Tx : Type} (M : IConf.Model V Tx)
    {g₁ g₂ : IConf.Hist Tx} :
    (IConf.LocValid M g₁ → IConf.LocValid M g₂ → IConf.LocValid M (IConf.Hist.dunion g₁ g₂)) ∧
      IConf.eval M (IConf.Hist.dunion g₁ g₂) = (IConf.eval M g₁).union (IConf.eval M g₂) :=
  ⟨IConf.locValid_dunion M, IConf.eval_dunion M g₁ g₂⟩

/-- (⇐): "… and `eval(g₁), eval(g₂) ∈ S_𝓘(j)`."  Lean: each part of the
disjoint union, as a sub-history, is valid with the state of its component
(`side g₁ g₂ 0 = g₁`, `side g₁ g₂ 1 = g₂`). -/
theorem «app:iconfluence/proof-parts» {V Tx : Type} (M : IConf.Model V Tx) {g₁ g₂ : IConf.Hist Tx}
    {k : Nat} (hk : k < 2) (hv : IConf.Valid M (IConf.Hist.side g₁ g₂ k)) :
    ∃ L, L ≼ IConf.Hist.dunion g₁ g₂ ∧ IConf.Valid M L ∧
      IConf.eval M L = IConf.eval M (IConf.Hist.side g₁ g₂ k) :=
  IConf.part_row M hk hv

/-- (⇐): "Every downward-closed `c ⊆ j` is the disjoint union of `c ∩ g₁` and
`c ∩ g₂`."  Lean: the state of `c ≼ dunion g₁ g₂` is the union of the states of
its two halves `half c 0 ≼ g₁`, `half c 1 ≼ g₂`. -/
theorem «app:iconfluence/proof-halves» {V Tx : Type} (M : IConf.Model V Tx)
    {g₁ g₂ c : IConf.Hist Tx} (hc : c ≼ IConf.Hist.dunion g₁ g₂) :
    IConf.eval M c = (IConf.eval M (IConf.Hist.half c 0)).union (IConf.eval M (IConf.Hist.half c 1)) ∧
      IConf.Hist.half c 0 ≼ g₁ ∧ IConf.Hist.half c 1 ≼ g₂ :=
  ⟨IConf.eval_half M hc, IConf.Hist.half_le hc (by decide), IConf.Hist.half_le hc (by decide)⟩

/-- (⇐): "Directed Outputs gives a valid sub-history `g` of `j` with
`eval(g) ⊇ eval(g₁) ∪ eval(g₂) = eval(j) ⊇ eval(g)`, so
`𝓘(eval(g₁) ∪ eval(g₂))`. … `j` is valid.  Valid histories are therefore
closed under disjoint union, and under adding an event above all others when
its transaction step is valid." -/
theorem «app:iconfluence/proof-pair» {V Tx : Type} (M : IConf.Model V Tx)
    (hlm : (IConf.SI M).LiftedMono) {g₁ g₂ g : IConf.Hist Tx} (v₁ : IConf.Valid M g₁)
    (v₂ : IConf.Valid M g₂) (vg : IConf.Valid M g) (t : Tx)
    (hi : M.Inv (M.app t (IConf.eval M g))) :
    M.Inv ((IConf.eval M g₁).union (IConf.eval M g₂)) ∧
      IConf.Valid M (IConf.Hist.dunion g₁ g₂) ∧
      IConf.Valid M (IConf.Hist.addTop g t) ∧
      IConf.eval M (IConf.Hist.addTop g t) = M.app t (IConf.eval M g) :=
  ⟨IConf.pair_inv M hlm v₁ v₂, IConf.valid_dunion M hlm v₁ v₂, IConf.valid_addTop M vg t hi,
    IConf.eval_addTop M g t⟩

/-- (⇐): "By induction on derivations, every reachable state is the state of
a valid history." -/
theorem «app:iconfluence/proof-reachable-valid» {V Tx : Type} (M : IConf.Model V Tx)
    (hlm : (IConf.SI M).LiftedMono) {s : IConf.St V} (hs : IConf.Reach M s) :
    ∃ g, IConf.Valid M g ∧ IConf.eval M g = s :=
  IConf.reach_valid M hlm hs

/-- (⇐): "… and the pairwise argument gives `𝓘(s₁ ∪ s₂)` for all reachable
`s₁, s₂`." -/
theorem «app:iconfluence/proof-backward» {V Tx : Type} (M : IConf.Model V Tx) :
    (IConf.SI M).LiftedMono → M.IConfluent :=
  IConf.lm_ic M

/-- (⇐): "Only Directed Outputs is needed." -/
theorem «app:iconfluence/proof-directed-suffices» {V Tx : Type} (M : IConf.Model V Tx) :
    (IConf.SI M).DirectedOutputs → M.IConfluent :=
  IConf.directed_ic M

end Paper
end CC
