import CoordCriterion.Instances.HATTaxonomy
import CoordCriterion.Appendix.DeploymentCAP

/-!
# The HAT taxonomy: highly available and sticky available guarantees

The read rules of Bailis et al. as explicit relations, and the classification
they give through our theorems (see `Instances/HATTaxonomy.lean` for the model).

## The read rules

* `Stable h c n p` is Bailis's *pending stable* (§5.1.2 and App. B of the
  extended paper): before point `p`, every replica of every item transaction
  `(c,n)` wrote has received its write.  App. B's servers learn this by counting
  acknowledgments from the other replicas ("if all acks received for all
  replicas for ts's sibs then good.add(w)"); in the input it is read off the
  delivery events `dl`, which happen before `p`.
* `DepStable h c n p` adds the dependencies of §5.1.3: the session guarantees
  "can be achieved by forcing servers to wait to reveal new writes ... until each
  write's respective dependencies are visible on all replicas", where the
  dependencies of WFR are Lamport's happens-before.  So every transaction whose
  commit happens before `(c,n)`'s is pending stable as well.
* `Rev false h c p k v`: version `v` of `k` is revealed at `p`: its transaction is
  dependency-stable.  `Rev true` (the sticky rule) also reveals the client's own
  earlier committed writes: under stickiness the client's server holds them
  (§4.1: a client "might cache its reads and writes"; §5.1.3: "read your writes is
  provided by default in a sticky system").
* The read rule (`outR s`): a transaction reads, for each item, the highest
  version revealed at *every* one of its reads so far.  This is the
  transaction-boundary lower bound of §5.1.2 ("at the start of each transaction,
  clients can choose a read timestamp that is lower than or equal to this global
  lower bound ... if this lower bound is advanced along transactional
  boundaries, clients will observe MAV"), and it also realizes the client-side
  read cache that gives cut isolation (§5.1.1: "transactions store a copy of any
  read data at the client").  With `s = true` the rule answers only sticky reads.

## Results (each through Complete CAP for an explicit relation)

* `ha_of_rule`: for RC and MAV (under the timestamp condition) and for I-CI,
  P-CI, MR, MW, WFR, the rule `outR false` is an explicit relation contained in
  the guarantee's specification, monotone, and answering every read; so
  (`CAP.complete_cap_for`, via `highlyAvailable_iff`) some system has
  Availability for it and Partition Consistency: these guarantees are highly
  available.
* `sticky_of_rule`: for RYW, PRAM, causal consistency (and every guarantee
  above), the sticky rule `outR true` answers every sticky read and is
  contained in the specification and monotone: these guarantees are sticky
  available.
* `stickyD`: the deployment that lets participant `srv c` (the client's sticky
  server) emit the sticky rule's answers for `c`'s reads.  It is monotone
  across partitions (`stickyD_monoAcross`, via
  `Deploy.monoAcrossPartitions_of_consistentOn`), so by the existence half of
  Prop. `thm:complete-cap-deployment` (`Deploy.deployment_complete_cap`) some
  system has Deployment Availability and Partition Consistency for it
  (`stickyD_available`); it authorizes each participant to answer every sticky
  read of its clients (`stickyD_answers`).
-/

namespace CC
namespace HATTax
open HATRC (Ts tsLt tsInit tsLt_trans tsLt_irrefl no_cycle)
open IConf (Hist St)
open HATSpec (Ev Inp WF Lamport Ver Inst Next CTs wwI lab_ev lab_sub lab_sup lt_sub lt_sup
  exists_max allTs mem_allTs max_unique tsLt_total not_lt_init init_lt cts_unique cts_ne next_lt)

variable {reps : Nat → List Nat} {lam : Bool}

/-! ## Stability and the read rule -/

section Defs
variable (reps)

/-- Pending stable (Bailis App. B): `(c,n)` committed before `p`, and every replica of
every item it wrote received its write before `p`. -/
def Stable (h : Hist Ev) (c n p : Nat) : Prop :=
  ∃ f t ks, h.lab f = some (.cm c n t ks) ∧ h.lt f p ∧
    ∀ k ∈ ks, ∀ r ∈ reps k, ∃ d, h.lab d = some (.dl c n k r) ∧ h.lt d p

/-- Dependency-stable (Bailis §5.1.3): `(c,n)` and every transaction committed
before it are pending stable before `p`. -/
def DepStable (h : Hist Ev) (c n p : Nat) : Prop :=
  Stable reps h c n p ∧ ∀ f f' t ks c' n' t' ks', h.lab f = some (.cm c n t ks) →
    h.lab f' = some (.cm c' n' t' ks') → h.lt f' f → Stable reps h c' n' p

/-- Version `v` of `k` is revealed at `p` to client `c₀`. -/
def Rev (s : Bool) (h : Hist Ev) (c₀ p k : Nat) (v : Ts) : Prop :=
  (∃ f c n ks, h.lab f = some (.cm c n v ks) ∧ k ∈ ks ∧ DepStable reps h c n p) ∨
  (s = true ∧ ∃ f n ks, h.lab f = some (.cm c₀ n v ks) ∧ k ∈ ks ∧ h.lt f p)

/-- Candidates for transaction `(c,n)`'s read `e` of `k`: versions revealed at
every read of the transaction up to `e`. -/
def SnapC (s : Bool) (h : Hist Ev) (e c n k : Nat) (v : Ts) : Prop :=
  v = tsInit ∨ ∀ e', (e' = e ∨ h.lt e' e) → IsRead h e' c n → Rev reps s h c e' k v

end Defs

section Lemmas
variable {j : SInp reps lam}

theorem stable_mono {h : Hist Ev} {c n p q : Nat} (hpq : h.lt p q) (hs : Stable reps h c n p) :
    Stable reps h c n q := by
  obtain ⟨f, t, ks, hf, hfp, hall⟩ := hs
  refine ⟨f, t, ks, hf, h.lt_trans hfp hpq, fun k hk r hr => ?_⟩
  obtain ⟨d, hd, hdp⟩ := hall k hk r hr
  exact ⟨d, hd, h.lt_trans hdp hpq⟩

theorem depStable_mono {h : Hist Ev} {c n p q : Nat} (hpq : h.lt p q)
    (hs : DepStable reps h c n p) : DepStable reps h c n q :=
  ⟨stable_mono hpq hs.1, fun f f' t ks c' n' t' ks' hf hf' hl =>
    stable_mono hpq (hs.2 f f' t ks c' n' t' ks' hf hf' hl)⟩

theorem rev_mono {s : Bool} {h : Hist Ev} {c₀ p q k : Nat} {v : Ts} (hpq : h.lt p q)
    (hr : Rev reps s h c₀ p k v) : Rev reps s h c₀ q k v := by
  rcases hr with ⟨f, c, n, ks, hf, hk, hd⟩ | ⟨hs, f, n, ks, hf, hk, hl⟩
  · exact Or.inl ⟨f, c, n, ks, hf, hk, depStable_mono hpq hd⟩
  · exact Or.inr ⟨hs, f, n, ks, hf, hk, h.lt_trans hl hpq⟩

/-- Dependency-stability passes to transactions committed earlier. -/
theorem depStable_pred {c n c' n' p f f' : Nat} {t t' : Ts} {ks ks' : List Nat}
    (hd : DepStable reps j.1 c n p) (hf : j.1.lab f = some (.cm c n t ks))
    (hf' : j.1.lab f' = some (.cm c' n' t' ks')) (hl : j.1.lt f' f) :
    DepStable reps j.1 c' n' p :=
  ⟨hd.2 f f' t ks c' n' t' ks' hf hf' hl, fun g g' u ls d m u' ls' hg hg' hl' => by
    have := j.2.1.1.cm_unique hg hf'; subst this
    exact hd.2 f g' t ks d m u' ls' hf hg' (j.1.lt_trans hl' hl)⟩

/-- A revealed version has a commit before the point, by a transaction that is not
the reader's own. -/
theorem rev_commit {s : Bool} {c₀ p k : Nat} {v : Ts} (hr : Rev reps s j.1 c₀ p k v) :
    ∃ f c n ks, j.1.lab f = some (.cm c n v ks) ∧ k ∈ ks ∧ j.1.lt f p := by
  rcases hr with ⟨f, c, n, ks, hf, hk, hd⟩ | ⟨-, f, n, ks, hf, hk, hl⟩
  · obtain ⟨f', t, ks', hf', hl, -⟩ := hd.1
    have := j.2.1.1.cm_unique hf hf'; subst this
    exact ⟨f, c, n, ks, hf, hk, hl⟩
  · exact ⟨f, c₀, n, ks, hf, hk, hl⟩

/-- Revealing does not depend on the item, beyond its being written. -/
theorem rev_item {s : Bool} {c₀ p k k' : Nat} {v : Ts} (hr : Rev reps s j.1 c₀ p k v)
    (hv : v ≠ tsInit) (hi : Inst j.inp k' v) : Rev reps s j.1 c₀ p k' v := by
  obtain ⟨g, d, m, ls, hg, hk'⟩ := inst_commit hi hv
  rcases hr with ⟨f, c, n, ks, hf, hk, hd⟩ | ⟨hs, f, n, ks, hf, hk, hl⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hf hg
    exact Or.inl ⟨f, c, n, ks, hf, hk', hd⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hf hg
    exact Or.inr ⟨hs, f, n, ks, hf, hk', hl⟩

/-- The candidates of a transaction's reads do not depend on the read. -/
theorem snapC_txn {s : Bool} {e₁ e₂ c n k : Nat} {v : Ts} (h₁ : IsRead j.1 e₁ c n)
    (h₂ : IsRead j.1 e₂ c n) (hv : SnapC reps s j.1 e₁ c n k v) : SnapC reps s j.1 e₂ c n k v := by
  rcases hv with hv | hv
  · exact Or.inl hv
  · right
    intro e' he' hr'
    by_cases h1 : e' = e₁
    · subst h1; exact hv _ (Or.inl rfl) hr'
    · rcases j.2.2.txn_order hr' h₁ h1 with hl | hl
      · exact hv e' (Or.inr hl) hr'
      · exact rev_mono hl (hv e₁ (Or.inl rfl) h₁)

/-- A version revealed at every read of a transaction up to `e` is revealed at `e`. -/
theorem snapC_rev {s : Bool} {e c n k : Nat} {v : Ts} (h : IsRead j.1 e c n)
    (hv : SnapC reps s j.1 e c n k v) : v = tsInit ∨ Rev reps s j.1 c e k v :=
  hv.imp id fun hv => hv e (Or.inl rfl) h

/-- Candidates grow along a session: a transaction's candidates are candidates of
every later transaction of the same client. -/
theorem snapC_sess {s : Bool} {f₁ f₂ e₁ e₂ c n₁ n₂ k : Nat} {t₁ t₂ : Ts} {ks₁ ks₂ : List Nat}
    {v : Ts} (hf₁ : j.1.lab f₁ = some (.cm c n₁ t₁ ks₁)) (hf₂ : j.1.lab f₂ = some (.cm c n₂ t₂ ks₂))
    (hl : j.1.lt f₁ f₂) (h₁ : IsRead j.1 e₁ c n₁) (h₂ : IsRead j.1 e₂ c n₂)
    (hv : SnapC reps s j.1 e₁ c n₁ k v) : SnapC reps s j.1 e₂ c n₂ k v := by
  rcases snapC_rev h₁ hv with hv | hv
  · exact Or.inl hv
  · right
    intro e' _ hr'
    exact rev_mono (j.1.lt_trans (read_before h₁ hf₁) (j.2.2.seq hf₁ hf₂ hl hr')) hv

/-! ### Stability under input extension -/

theorem stable_iff {a b : Hist Ev} (hab : a ≼ b) {c n p : Nat} (hp : a.ev p) :
    Stable reps a c n p ↔ Stable reps b c n p := by
  constructor
  · rintro ⟨f, t, ks, hf, hl, hall⟩
    refine ⟨f, t, ks, lab_sub hab hf, lt_sub hab hl, fun k hk r hr => ?_⟩
    obtain ⟨d, hd, hdl⟩ := hall k hk r hr
    exact ⟨d, lab_sub hab hd, lt_sub hab hdl⟩
  · rintro ⟨f, t, ks, hf, hl, hall⟩
    have hl' := lt_sup hab hl hp
    refine ⟨f, t, ks, lab_sup hab (IConf.Hist.ev_of_lt_left hl') hf, hl', fun k hk r hr => ?_⟩
    obtain ⟨d, hd, hdl⟩ := hall k hk r hr
    have hdl' := lt_sup hab hdl hp
    exact ⟨d, lab_sup hab (IConf.Hist.ev_of_lt_left hdl') hd, hdl'⟩

theorem depStable_iff {i j : SInp reps lam} (hij : i ≼ j) {c n p : Nat} (hp : i.1.ev p) :
    DepStable reps i.1 c n p ↔ DepStable reps j.1 c n p := by
  have hab : i.1 ≼ j.1 := hij
  constructor
  · rintro ⟨hs, hall⟩
    refine ⟨(stable_iff hab hp).1 hs, fun f f' t ks c' n' t' ks' hf hf' hl => ?_⟩
    obtain ⟨g, u, ls, hg, hgl, -⟩ := hs
    have hfg := j.2.1.1.cm_unique hf (lab_sub hab hg); subst hfg
    have hge : i.1.ev f := IConf.Hist.ev_of_lt_left hgl
    have hl' := lt_sup hab hl hge
    exact (stable_iff hab hp).1 (hall f f' u ls c' n' t' ks' hg
      (lab_sup hab (IConf.Hist.ev_of_lt_left hl') hf') hl')
  · rintro ⟨hs, hall⟩
    refine ⟨(stable_iff hab hp).2 hs, fun f f' t ks c' n' t' ks' hf hf' hl => ?_⟩
    exact (stable_iff hab hp).2 (hall f f' t ks c' n' t' ks' (lab_sub hab hf) (lab_sub hab hf')
      (lt_sub hab hl))

theorem rev_iff {i j : SInp reps lam} (hij : i ≼ j) {s : Bool} {c₀ p k : Nat} {v : Ts}
    (hp : i.1.ev p) : Rev reps s i.1 c₀ p k v ↔ Rev reps s j.1 c₀ p k v := by
  have hab : i.1 ≼ j.1 := hij
  constructor
  · rintro (⟨f, c, n, ks, hf, hk, hd⟩ | ⟨hs, f, n, ks, hf, hk, hl⟩)
    · exact Or.inl ⟨f, c, n, ks, lab_sub hab hf, hk, (depStable_iff hij hp).1 hd⟩
    · exact Or.inr ⟨hs, f, n, ks, lab_sub hab hf, hk, lt_sub hab hl⟩
  · rintro (⟨f, c, n, ks, hf, hk, hd⟩ | ⟨hs, f, n, ks, hf, hk, hl⟩)
    · have hd' := (depStable_iff hij hp).2 hd
      obtain ⟨g, u, ls, hg, hgl, -⟩ := hd'.1
      have hfg := j.2.1.1.cm_unique hf (lab_sub hab hg); subst hfg
      have h2 := lab_sub hab hg; rw [hf] at h2; cases h2
      exact Or.inl ⟨f, c, n, ks, hg, hk, hd'⟩
    · have hl' := lt_sup hab hl hp
      exact Or.inr ⟨hs, f, n, ks, lab_sup hab (IConf.Hist.ev_of_lt_left hl') hf, hk, hl'⟩

theorem snapC_iff {i j : SInp reps lam} (hij : i ≼ j) {s : Bool} {e c n k : Nat} {v : Ts}
    (he : i.1.ev e) : SnapC reps s i.1 e c n k v ↔ SnapC reps s j.1 e c n k v := by
  have hab : i.1 ≼ j.1 := hij
  have hev : ∀ e', (e' = e ∨ j.1.lt e' e) → i.1.ev e' := by
    rintro e' (rfl | hl)
    · exact he
    · exact IConf.Hist.ev_of_lt_left (lt_sup hab hl he)
  constructor
  · rintro (hv | hv)
    · exact Or.inl hv
    · right; intro e' he' hr'
      have hi := hev e' he'
      refine (rev_iff hij hi).1 (hv e' ?_ (isRead_sup hab hi hr'))
      rcases he' with rfl | hl
      · exact Or.inl rfl
      · exact Or.inr (lt_sup hab hl he)
  · rintro (hv | hv)
    · exact Or.inl hv
    · right; intro e' he' hr'
      have hi : i.1.ev e' := by
        rcases he' with rfl | hl
        · exact he
        · exact IConf.Hist.ev_of_lt_left hl
      refine (rev_iff hij hi).2 (hv e' ?_ (isRead_sub hab hr'))
      rcases he' with rfl | hl
      · exact Or.inl rfl
      · exact Or.inr (lt_sub hab hl)

theorem reflects_sub {i j : SInp reps lam} (hij : i ≼ j) {e c r : Nat} (he : i.1.ev e)
    (h : Reflects (reps := reps) i.1 e c r) : Reflects (reps := reps) j.1 e c r := by
  have hab : i.1 ≼ j.1 := hij
  intro f n' t ks k hf hl hk hr
  have hl' := lt_sup hab hl he
  obtain ⟨d, hd, hdl⟩ := h f n' t ks k (lab_sup hab (IConf.Hist.ev_of_lt_left hl') hf) hl' hk hr
  exact ⟨d, lab_sub hab hd, lt_sub hab hdl⟩

end Lemmas

/-! ## The rule, its complete history and its explicit relation -/

section Rule
variable (s : Bool) (j : SInp reps lam)

theorem snapC_max {e c n : Nat} (k : Nat) (he : IsRead j.1 e c n) :
    ∃ v, IsMax (SnapC reps s j.1 e c n k) v :=
  isMax_exists _ (Or.inl rfl) fun v hv => by
    rcases snapC_rev he hv with rfl | hv
    · exact Or.inl rfl
    · obtain ⟨f, c', n', ks, hf, -, -⟩ := rev_commit hv
      exact Or.inr ⟨f, c', n', ks, hf⟩

/-- The rule's answer to access `(e, k)`. -/
def RAns (e k : Nat) (v : Ts) : Prop :=
  ∃ c n r, Acc j.1 e c n k r ∧ IsMax (SnapC reps s j.1 e c n k) v

/-- The complete history of the rule: every access gets the rule's answer. -/
noncomputable def ruleHist : CH2 j where
  val e k := @dite _ (∃ v, RAns s j e k v) (Classical.propDecidable _)
    (fun h => Classical.choose h) (fun _ => tsInit)
  ok e c n k r ha := by
    have hx : ∃ v, RAns s j e k v := by
      obtain ⟨v, hv⟩ := snapC_max s j k ha.isRead; exact ⟨v, c, n, r, ha, hv⟩
    simp only [dif_pos hx]
    obtain ⟨c₁, n₁, r₁, ha₁, hv, -⟩ := Classical.choose_spec hx
    obtain ⟨rfl, rfl, rfl⟩ := acc_unique ha ha₁
    rcases snapC_rev ha.isRead hv with hv | hv
    · exact Or.inl hv
    · obtain ⟨f, c', n', ks, hf, hk, hl⟩ := rev_commit hv
      refine Or.inr ⟨f, c', n', ks, hf, hk, fun e' => ?_⟩
      simp only [Prod.mk.injEq] at e'; obtain ⟨rfl, rfl⟩ := e'
      have h1 := j.1.lt_num (read_before ha.isRead hf)
      have h2 := j.1.lt_num hl
      omega

variable {s j}

theorem ruleHist_val {e c n k r : Nat} (ha : Acc j.1 e c n k r) :
    IsMax (SnapC reps s j.1 e c n k) ((ruleHist s j).val e k) := by
  have hx : ∃ v, RAns s j e k v := by
    obtain ⟨v, hv⟩ := snapC_max s j k ha.isRead; exact ⟨v, c, n, r, ha, hv⟩
  show IsMax _ (@dite _ _ (Classical.propDecidable _) _ _)
  rw [dif_pos hx]
  obtain ⟨c₁, n₁, r₁, ha₁, hv⟩ := Classical.choose_spec hx
  obtain ⟨rfl, rfl, rfl⟩ := acc_unique ha₁ ha
  exact hv

theorem isMax_congr {P Q : Ts → Prop} {v w : Ts} (h : ∀ u, P u ↔ Q u) (hv : IsMax P v)
    (hw : IsMax Q w) : v = w :=
  isMax_unique hv ⟨(h w).2 hw.1, fun u hu => hw.2 u ((h u).1 hu)⟩

/-- Two accesses of one transaction to one item get the same answer. -/
theorem val_txn {e₁ e₂ c n k r₁ r₂ : Nat} (h₁ : Acc j.1 e₁ c n k r₁) (h₂ : Acc j.1 e₂ c n k r₂) :
    (ruleHist s j).val e₁ k = (ruleHist s j).val e₂ k :=
  isMax_congr (fun _ => ⟨snapC_txn h₁.isRead h₂.isRead, snapC_txn h₂.isRead h₁.isRead⟩)
    (ruleHist_val h₁) (ruleHist_val h₂)

theorem snapC_item {e c n k k' : Nat} {v : Ts} (h : SnapC reps s j.1 e c n k v) (hv : v ≠ tsInit)
    (hi : Inst j.inp k' v) : SnapC reps s j.1 e c n k' v :=
  h.imp id fun h e' he' hr => rev_item (h e' he' hr) hv hi

/-- A version revealed after a later session write is revealed with it (the rule's
dependencies include the session order). -/
theorem rev_sess {c₀ p y x c ni nj fi fj : Nat} {ti tj : Ts} {ksi ksj : List Nat}
    (hr : Rev reps s j.1 c₀ p y tj) (hfi : j.1.lab fi = some (.cm c ni ti ksi))
    (hfj : j.1.lab fj = some (.cm c nj tj ksj)) (hl : j.1.lt fi fj) (hx : x ∈ ksi) :
    Rev reps s j.1 c₀ p x ti := by
  rcases hr with ⟨f, c', n', ks, hf, -, hd⟩ | ⟨hs, f, n', ks, hf, -, hfl⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hfj hf
    exact Or.inl ⟨fi, c, ni, ksi, hfi, hx, depStable_pred hd hfj hfi hl⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hfj hf
    exact Or.inr ⟨hs, fi, ni, ksi, hfi, hx, j.1.lt_trans hl hfl⟩

/-- Writes follow reads for the rule: a version revealed to a transaction's read
is revealed with that transaction's write. -/
theorem rev_wfr {c₂ n₂ c₃ e₁ p x y f₂ : Nat} {t₁ t₂ : Ts} {ks₂ : List Nat}
    (h₁ : Rev reps s j.1 c₂ e₁ x t₁) (he₁ : IsRead j.1 e₁ c₂ n₂)
    (hf₂ : j.1.lab f₂ = some (.cm c₂ n₂ t₂ ks₂)) (h₂ : Rev reps s j.1 c₃ p y t₂) :
    Rev reps s j.1 c₃ p x t₁ := by
  have hl₁ := read_before he₁ hf₂
  rcases h₂ with ⟨f, c', n', ks, hf, -, hd⟩ | ⟨hs, f, n', ks, hf, -, hfl⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hf₂ hf
    obtain ⟨g, d, m, ls, hg, hx, hgl⟩ := rev_commit h₁
    exact Or.inl ⟨g, d, m, ls, hg, hx, depStable_pred hd hf hg (j.1.lt_trans hgl hl₁)⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hf₂ hf
    have hep : j.1.lt e₁ p := j.1.lt_trans hl₁ hfl
    rcases h₁ with ⟨g, d, m, ls, hg, hx, hd⟩ | ⟨-, g, m, ls, hg, hx, hgl⟩
    · exact Or.inl ⟨g, d, m, ls, hg, hx, depStable_mono hep hd⟩
    · exact Or.inr ⟨hs, g, m, ls, hg, hx, j.1.lt_trans hgl hep⟩

/-! ### The rule avoids the phenomena -/

theorem rule_IMP : ¬ IMP (ruleHist s j) := by
  rintro ⟨x, a, b, t, hab, ⟨-, -, e, c, n, r, he, ⟨f, ks, hf⟩, rfl⟩,
    ⟨-, -, e', c', n', r', he', ⟨f', ks', hf'⟩, rfl⟩⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hf hf'
  exact hab (val_txn (Or.inl he) (Or.inl he'))

theorem rule_PMP : ¬ PMP (ruleHist s j) := by
  rintro ⟨e₁, e₂, c, n, r₁, r₂, ks₁, ks₂, t, he₁, he₂, -, hne⟩
  apply hne; intro u
  have hv : ∀ x ∈ ks₁.filter (· ∈ ks₂), (ruleHist s j).val e₁ x = (ruleHist s j).val e₂ x := by
    intro x hx
    simp only [List.mem_filter, decide_eq_true_eq] at hx
    exact val_txn (Or.inr ⟨ks₁, he₁, hx.1⟩) (Or.inr ⟨ks₂, he₂, hx.2⟩)
  constructor
  · rintro ⟨x, hx, hn, hv'⟩; exact ⟨x, hx, hn, by rw [← hv x hx]; exact hv'⟩
  · rintro ⟨x, hx, hn, hv'⟩; exact ⟨x, hx, hn, by rw [hv x hx]; exact hv'⟩

theorem rule_OTV : ¬ OTV (ruleHist s j) := by
  rintro ⟨e₁, e₂, c, n, r₁, r₂, x, y, ti, tj, he₁, he₂, -, -, hv₁, ⟨-, hix, -⟩, hrw⟩
  obtain ⟨hlt, hiy⟩ := rwWw_lt hrw
  have hj0 : tj ≠ tsInit := fun h => not_lt_init _ (h ▸ hlt)
  have h1 := (ruleHist_val (s := s) (j := j) (Or.inl he₁)).1
  rw [hv₁] at h1
  have h2 := snapC_txn (Or.inl ⟨x, r₁, he₁⟩) (Or.inl ⟨y, r₂, he₂⟩) (snapC_item h1 hj0 hiy)
  exact not_le_lt ((ruleHist_val (Or.inl he₂)).2 _ h2) hlt

theorem rule_NMR : ¬ NMR (ruleHist s j) := by
  rintro ⟨ti, tj, tl, x, e, c, n, r, hs, he, ⟨g, ks, hg⟩, hrw, ⟨-, -, e', c', n', r', he', ⟨g', ks', hg'⟩, hv'⟩⟩
  obtain ⟨f, f', d, ni, nj, ksi, ksj, hf, hf', hl⟩ := sess_tg hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hg hf'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hg' hf
  have hsub : ∀ v, SnapC reps s j.1 e' _ _ x v → SnapC reps s j.1 e _ _ x v :=
    fun v h => snapC_sess hf hf' hl (Or.inl ⟨x, r', he'⟩) (Or.inl ⟨x, r, he⟩) h
  have := isMax_le (ruleHist_val (s := s) (j := j) (Or.inl he')) (ruleHist_val (Or.inl he)) hsub
  rw [hv'] at this
  exact not_le_lt this (rwWw_lt hrw).1

theorem rule_NMW : ¬ NMW (ruleHist s j) := by
  rintro (⟨ti, tj, hs, hw⟩ | ⟨ti, tj, tk, x, y, e, c, n, r, hs, ⟨-, -, e₂, c₂, n₂, r₂, he₂, ⟨g, ks, hg⟩, hv₂⟩,
    he, ⟨g', ks', hg'⟩, -, hrw⟩)
  · exact tsLt_irrefl _ (tsLt_trans (sess_tg_lt hs) (tg_lt' (fun _ _ ⟨_, h⟩ => next_lt h) hw))
  · obtain ⟨fi, fj, d, ni, nj, ksi, ksj, hfi, hfj, hl⟩ := sess_tg hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hg hg'
    obtain ⟨hlt, hix⟩ := rwWw_lt hrw
    have hi0 : ti ≠ tsInit := cts_ne (j := j.inp) ⟨fi, ksi, hfi⟩
    obtain ⟨g₁, d₁, m₁, ls₁, hg₁, hx₁⟩ := inst_commit hix hi0
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hfi hg₁
    have hj0 : tj ≠ tsInit := cts_ne (j := j.inp) ⟨fj, ksj, hfj⟩
    have h1 := (ruleHist_val (s := s) (j := j) (Or.inl he₂)).1
    rw [hv₂] at h1
    have h2 : SnapC reps s j.1 e₂ c₂ n₂ x ti := by
      rcases h1 with h1 | h1
      · exact absurd h1 hj0
      · exact Or.inr fun e' he' hr => rev_sess (h1 e' he' hr) hfi hfj hl hx₁
    have h3 := snapC_txn (Or.inl ⟨y, r₂, he₂⟩) (Or.inl ⟨x, r, he⟩) h2
    exact not_le_lt ((ruleHist_val (Or.inl he)).2 _ h3) hlt

theorem rule_MRWD : ¬ MRWD (ruleHist s j) := by
  rintro ⟨t₁, t₂, t₃, x, y, e, c, n, r, ⟨-, -, e₁, c₂, n₂, r₁, he₁, ⟨f₂, ks₂, hf₂⟩, hv₁⟩,
    ⟨-, -, e₂, c₃, n₃, r₂, he₂, ⟨f₃, ks₃, hf₃⟩, hv₂⟩, he, ⟨g, ks, hg⟩, -, hn⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hf₃ hg
  have h10 : t₁ ≠ tsInit := fun h => not_lt_init _ (h ▸ next_lt hn)
  have h20 : t₂ ≠ tsInit := cts_ne (j := j.inp) ⟨f₂, ks₂, hf₂⟩
  have hA := (ruleHist_val (s := s) (j := j) (Or.inl he₁)).1
  rw [hv₁] at hA
  have hA' := (snapC_rev (Or.inl ⟨x, r₁, he₁⟩) hA).resolve_left h10
  have hB := (ruleHist_val (s := s) (j := j) (Or.inl he₂)).1
  rw [hv₂] at hB
  have h2 : SnapC reps s j.1 e₂ c₃ n₃ x t₁ := by
    rcases hB with hB | hB
    · exact absurd hB h20
    · exact Or.inr fun e' he' hr => rev_wfr hA' (Or.inl ⟨x, r₁, he₁⟩) hf₂ (hB e' he' hr)
  have h3 := snapC_txn (Or.inl ⟨y, r₂, he₂⟩) (Or.inl ⟨x, r, he⟩) h2
  exact not_le_lt ((ruleHist_val (Or.inl he)).2 _ h3) (next_lt hn)

theorem rule_MYR (j : SInp reps lam) : ¬ MYR (ruleHist true j) := by
  rintro ⟨ti, tj, x, e, c, n, r, hs, he, ⟨g, ks, hg⟩, -, hrw⟩
  obtain ⟨fi, fj, d, ni, nj, ksi, ksj, hfi, hfj, hl⟩ := sess_tg hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hfj hg
  obtain ⟨hlt, hix⟩ := rwWw_lt hrw
  have hi0 : ti ≠ tsInit := cts_ne (j := j.inp) ⟨fi, ksi, hfi⟩
  obtain ⟨g₁, d₁, m₁, ls₁, hg₁, hx₁⟩ := inst_commit hix hi0
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ts_inj hfi hg₁
  have h2 : SnapC reps true j.1 e d nj x ti :=
    Or.inr fun e' _ hr => Or.inr ⟨rfl, fi, ni, ksi, hfi, hx₁, j.2.2.seq hfi hfj hl hr⟩
  exact not_le_lt ((ruleHist_val (Or.inl he)).2 _ h2) hlt

theorem rule_G1c (j : SInp reps true) : ¬ G1c (ruleHist false j) := by
  have hwr : ∀ x a b, wr2 (ruleHist false j) x a b → tsLt a b := by
    rintro x a b ⟨-, -, e, c, n, r, he, ⟨f, ks, hf⟩, rfl⟩
    rcases snapC_rev (Or.inl ⟨x, r, he⟩) (ruleHist_val (s := false) (j := j) (Or.inl he)).1 with h | h
    · rw [h]; exact init_lt (cts_ne (j := j.inp) ⟨f, ks, hf⟩)
    · rcases h with ⟨g, c', n', ls, hg, hx, hd⟩ | ⟨h, -⟩
      · obtain ⟨g', u, ls', hg', -, hall⟩ := hd.1
        have := j.2.1.1.cm_unique hg hg'; subst this
        rw [hg] at hg'; cases hg'
        obtain ⟨d, hd', hdl⟩ := hall x hx r (j.2.2.rd_rep he)
        exact j.2.1.2 rfl he hd' hdl hf hg
      · cases h
  rintro ⟨t, h⟩
  exact no_cycle (fun a b h => h.elim (fun ⟨_, h⟩ => next_lt h) (fun ⟨k, h⟩ => hwr k a b h)) h

theorem g0_false (j : SInp reps lam) : ¬ HATSpec.G0 j.inp :=
  fun ⟨t, h⟩ => no_cycle (fun _ _ ⟨_, h⟩ => next_lt h) h

/-! ### The explicit relations -/

variable (s j)

/-- The rule's output: its answers to every read access (with `s = true`, to every
sticky read access). -/
def outR : St Fact2
  | .rv e k v => (∃ c n r, Acc j.1 e c n k r ∧ (s = true → Reflects (reps := reps) j.1 e c r)) ∧
      RAns s j e k v

/-- The explicit relation of the rule. -/
def ruleE : Table (SInp reps lam) (St Fact2) := fun i o => o = outR s i

variable {s j}

theorem outR_facts : outR s j ≼ (ruleHist s j).facts := by
  rintro ⟨e, k, v⟩ ⟨⟨c, n, r, ha, -⟩, c', n', r', ha', hv⟩
  exact ⟨⟨c, n, r, ha⟩, isMax_unique (ruleHist_val ha') hv⟩

theorem acc_rep {e c n k r : Nat} (ha : Acc j.1 e c n k r) : r ∈ reps k := by
  rcases ha with h | ⟨ks, h, hk⟩
  · exact j.2.2.rd_rep h
  · exact j.2.2.prd_rep h hk

theorem outR_vis : (vstore (reps := reps) (lam := lam)).P j (outR s j) := by
  rintro e k v ⟨⟨c, n, r, ha, hst⟩, c', n', r', ha', hv⟩
  obtain ⟨rfl, rfl, rfl⟩ := acc_unique ha ha'
  refine ⟨c, n, r, ha, ?_⟩
  rcases snapC_rev ha.isRead hv.1 with h | h
  · exact Or.inl h
  · right
    rcases h with ⟨f, c₁, n₁, ks, hf, hk, hd⟩ | ⟨hs, f, n₁, ks, hf, hk, hl⟩
    · obtain ⟨f', u, ks', hf', -, hall⟩ := hd.1
      have := j.2.1.1.cm_unique hf hf'; subst this
      rw [hf] at hf'; cases hf'
      obtain ⟨d, hd', hdl⟩ := hall k hk r (acc_rep ha)
      exact ⟨d, c₁, n₁, f, ks, hd', hdl, hf⟩
    · obtain ⟨d, hd', hdl⟩ := hst hs f n₁ v ks k hf hl hk (acc_rep ha)
      exact ⟨d, c, n₁, f, ks, hd', hdl, hf⟩

theorem outR_mono {i j : SInp reps lam} (hij : i ≼ j) : outR s i ≼ outR s j := by
  have hab : i.1 ≼ j.1 := hij
  rintro ⟨e, k, v⟩ ⟨⟨c, n, r, ha, hst⟩, c', n', r', ha', hv⟩
  have he : i.1.ev e := acc_ev ha
  refine ⟨⟨c, n, r, acc_sub hab ha, fun h => reflects_sub hij he (hst h)⟩, c', n', r',
    acc_sub hab ha', (snapC_iff hij he).1 hv.1, fun w hw => hv.2 w ((snapC_iff hij he).2 hw)⟩

theorem outR_answers (j : SInp reps lam) : AnswersAll j (outR false j) := by
  intro e c n k r ha
  obtain ⟨v, hv⟩ := snapC_max false j k ha.isRead
  exact ⟨v, ⟨c, n, r, ha, fun h => by cases h⟩, c, n, r, ha, hv⟩

theorem outR_answersSticky (j : SInp reps lam) : AnswersSticky j (outR true j) := by
  intro e c n k r ha hst
  obtain ⟨v, hv⟩ := snapC_max true j k ha.isRead
  exact ⟨v, ⟨c, n, r, ha, fun _ => hst⟩, c, n, r, ha, hv⟩

/-- A monotone rule contained in the specification is consistent on its rows. -/
theorem ruleE_consistent (sp : Spec (SInp reps lam) (St Fact2)) (hP : ∀ j, sp.P j (outR s j)) :
    CAP.ConsistentOn sp (ruleE s) := by
  intro rows hrows j hj
  refine ⟨outR s j, hP j, fun r hr => ?_⟩
  rw [hrows r hr]; exact outR_mono (hj r hr)

/-! ## The classification -/

/-- The guarantees the rule `outR false` provides. -/
def HAGuar (lam : Bool) (g : Guar) : Prop :=
  g = .ICI ∨ g = .PCI ∨ g = .MR ∨ g = .MW ∨ g = .WFR ∨ (lam = true ∧ (g = .RC ∨ g = .MAV))

/-- The guarantees the sticky rule `outR true` provides. -/
def StickyGuar (g : Guar) : Prop :=
  g = .ICI ∨ g = .PCI ∨ g = .MR ∨ g = .MW ∨ g = .WFR ∨ g = .RYW ∨ g = .PRAM ∨ g = .Causal

theorem rule_clean_ha {g : Guar} (hg : HAGuar lam g) (j : SInp reps lam) :
    ¬ Phen g j (ruleHist false j) := by
  rcases hg with rfl | rfl | rfl | rfl | rfl | ⟨rfl, rfl | rfl⟩
  · exact rule_IMP
  · exact rule_PMP
  · exact rule_NMR
  · exact rule_NMW
  · exact rule_MRWD
  · exact fun h => h.elim (g0_false j) (rule_G1c j)
  · exact fun h => h.elim (g0_false j) fun h => h.elim (rule_G1c j) rule_OTV

theorem rule_clean_sticky {g : Guar} (hg : StickyGuar g) (j : SInp reps lam) :
    ¬ Phen g j (ruleHist true j) := by
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rule_IMP
  · exact rule_PMP
  · exact rule_NMR
  · exact rule_NMW
  · exact rule_MRWD
  · exact rule_MYR j
  · exact fun h => h.elim rule_NMR fun h => h.elim rule_NMW (rule_MYR j)
  · exact fun h => h.elim rule_NMR fun h => h.elim rule_NMW fun h => h.elim (rule_MYR j) rule_MRWD

theorem outR_tax {s : Bool} {g : Guar} (hclean : ∀ j : SInp reps lam, ¬ Phen g j (ruleHist s j))
    (j : SInp reps lam) : (tax g).P j (outR s j) :=
  ⟨outR_vis, ruleHist s j, outR_facts, hclean j⟩

/-- **Highly available** (Bailis et al., Table 3, "HA"): RC and MAV (under the
timestamp condition), I-CI, P-CI, MR, MW and WFR.  The rule is an explicit
relation contained in the specification that answers every read, and it is
consistent because it is monotone; Complete CAP for an explicit relation
(`CAP.complete_cap_for`, through `highlyAvailable_iff`) gives a system with
Availability for it and Partition Consistency. -/
theorem ha_of_rule {g : Guar} (hg : HAGuar lam g) (D : Type) :
    HighlyAvailable (reps := reps) (lam := lam) (tax g) D :=
  (highlyAvailable_iff _ D).2 ⟨ruleE false, fun i o h => h ▸ outR_tax (rule_clean_ha hg) i,
    fun i => ⟨_, rfl⟩, fun i o h => h ▸ outR_answers i,
    ruleE_consistent _ (outR_tax (rule_clean_ha hg))⟩

/-- **Sticky available** (Bailis et al., Table 3, "Sticky"): RYW, PRAM and causal
consistency (and the guarantees above).  The sticky rule answers every sticky
read, is contained in the specification, and is monotone; Complete CAP for an
explicit relation gives the system. -/
theorem sticky_of_rule {g : Guar} (hg : StickyGuar g) (D : Type) :
    StickyAvailable (reps := reps) (lam := lam) (tax g) D :=
  (stickyAvailable_iff _ D).2 ⟨ruleE true, fun i o h => h ▸ outR_tax (rule_clean_sticky hg) i,
    fun i => ⟨_, rfl⟩, fun i o h => h ▸ outR_answersSticky i,
    ruleE_consistent _ (outR_tax (rule_clean_sticky hg))⟩

end Rule

/-! ## Sticky availability as a deployment -/

section Deploy
open CC.Deploy

theorem tax_down {g : Guar} {j : SInp reps lam} {o o' : St Fact2} (h : (tax g).P j o)
    (hle : o' ≼ o) : (tax g).P j o' := by
  obtain ⟨hv, H, hF, hc⟩ := h
  exact ⟨fun e k v hx => hv e k v (hle _ hx), H, PO.trans hle hF, hc⟩

/-- The answers of `o` to reads of clients served by participant `p`. -/
def restrictTo {n : Nat} (srv : Nat → Fin n) (p : Fin n) (j : SInp reps lam) (o : St Fact2) :
    St Fact2
  | .rv e k v => o (.rv e k v) ∧ ∃ c m r, Acc j.1 e c m k r ∧ srv c = p

theorem restrictTo_le {n : Nat} (srv : Nat → Fin n) (p : Fin n) (j : SInp reps lam) (o : St Fact2) :
    restrictTo srv p j o ≼ o := by
  rintro ⟨e, k, v⟩ h; exact h.1

/-- The sticky deployment: each client `c` sticks to participant `srv c`, which
may emit the sticky rule's answers to `c`'s reads. -/
def stickyD {g : Guar} (hg : StickyGuar g) {n : Nat} (srv : Nat → Fin n) :
    Deployment (tax (reps := reps) (lam := lam) g) n where
  A p j o := o = restrictTo srv p j (outR true j)
  sub p j o h := h ▸ tax_down (outR_tax (rule_clean_sticky hg) j) (restrictTo_le srv p j _)

/-- The sticky deployment is monotone across partitions. -/
theorem stickyD_monoAcross {g : Guar} (hg : StickyGuar g) {n : Nat} (srv : Nat → Fin n) :
    MonoAcrossPartitions (stickyD (reps := reps) (lam := lam) hg srv) := by
  refine monoAcrossPartitions_of_consistentOn _ (fun j o => o ≼ outR true j)
    (fun p j o h => h ▸ restrictTo_le srv p j _) ?_
  intro rows hrows j hj
  refine ⟨outR true j, outR_tax (rule_clean_sticky hg) j, fun r hr => ?_⟩
  exact PO.trans (hrows r hr) (outR_mono (hj r hr))

/-- **Sticky availability as a deployment.**  With at least two participants,
some system has Deployment Availability for the sticky deployment and Partition
Consistency (the existence half of Prop. `thm:complete-cap-deployment`,
`Deploy.deployment_complete_cap_exists`). -/
theorem stickyD_available {g : Guar} (hg : StickyGuar g) {n : Nat} (hn : 2 ≤ n)
    (srv : Nat → Fin n) (D : Type) :
    ∃ Sys : CAP.System (tax (reps := reps) (lam := lam) g) D,
      DeploymentAvailability Sys (stickyD hg srv) ∧ PartitionConsistencyAt Sys n :=
  deployment_complete_cap_exists hn _ (stickyD_monoAcross hg srv)

/-- The sticky deployment authorizes each participant to answer every sticky read
of its clients. -/
theorem stickyD_answers {g : Guar} (hg : StickyGuar g) {n : Nat} (srv : Nat → Fin n)
    (j : SInp reps lam) {e c m k r : Nat} (ha : Acc j.1 e c m k r)
    (hst : Reflects (reps := reps) j.1 e c r) :
    ∃ o v, (stickyD (reps := reps) (lam := lam) hg srv).A (srv c) j o ∧ o (.rv e k v) := by
  obtain ⟨v, hv⟩ := outR_answersSticky j e c m k r ha hst
  exact ⟨_, v, rfl, hv, c, m, r, ha, rfl⟩

end Deploy

end HATTax
end CC
