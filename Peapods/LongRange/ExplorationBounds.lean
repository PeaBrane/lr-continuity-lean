import Peapods.LongRange.Exploration

/-!
# Probability bounds for the exploration (Lemmas 6.2–6.3 and the Peierls step)

Before a pending `v` is processed, every pair with an endpoint in `Q_v ∪ Q_x` (`x` an unvisited
neighbour) is fresh with law `edgeProb q`, so the relay lemma applies in `G(v) ∪ Q_x ∪ I_{vx}`
(`relay_failure`). With the promise and the tower property this gives the bad-mass bound
`δ + 4(d+10)η/δ < f` (`badMass_bound`, Lemma 6.2); OpenAI's adaptive-reveal scheme turns it into
`P(all of U bad) ≤ f^{|U|}` (Lemma 6.3), and the planar Peierls count bounds the probability that
the set of good coarse vertices is finite (`finite_good_bound`). Ported from OpenAI's
`ExplorationInvariant` and `ExplorationProbability`.
-/

namespace Peapods.LongRange.Coarse

open MeasureTheory ProbabilityTheory Classical OAI InfiniteConditioning

variable {d : ℕ}

namespace Exploration

variable {r : ℕ}

/-- The relay from the head `t` of the queue to an unvisited neighbour fails with probability at most
`(d + 10)η` under the current history. -/
theorem relay_failure (hd : 2 ≤ d) [NeZero d] {K : Kernel d} {β : ℝ} (sc : ScaleData K β)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0)) {s : Exploration d sc.r}
    (hs : s.Valid (K.edgeProb sc.q) sc.δ) {t : Packet d sc.r} {ts : List (Packet d sc.r)}
    (hq : s.queue = t :: ts) (dir : Direction)
    (hx : t.vertex + PlanarBoundary.outward dir ∉ s.visited) :
    (ProductCylinder.law (hparam (K.edgeProb sc.q) s.history)).real
      (s.frozenEvent t ∩ ((t.child (t.vertex + PlanarBoundary.outward dir)).event)ᶜ) ≤
        ((d : ℝ) + 10) * sc.η := by
  set x := t.vertex + PlanarBoundary.outward dir
  set p := hparam (K.edgeProb sc.q) s.history
  set u := t.child x
  have htq : t ∈ s.queue := by simp [hq]
  have hv := hs.unprocessed t htq
  have hxD : x ∉ s.processed := fun hh => hx (s.processed_visited hh)
  have hv0 : t.vertex ≠ (0, 0) := fun he => hv (he ▸ hs.root_processed)
  have hx0 : x ≠ (0, 0) := fun he => hxD (he ▸ hs.root_processed)
  have hfresh : ∀ e : Pair d, ∀ y ∈ e, y ∈ Qcube sc.r t.vertex ∪ Qcube sc.r x →
      p e = K.edgeProb sc.q e := by
    intro e y hy hyD
    apply hparam_fresh
    intro hk
    have hexp := hs.exposed hk
    rcases hyD with hyD | hyD
    · exact not_exposed hd hs.root_processed hv hy hyD hexp
    · exact not_exposed hd hs.root_processed hxD hy hyD hexp
  have huedges : u.graph.edges = t.graph.edges ∪ qBits sc.r x ∪ link sc.r t.vertex x := rfl
  have huvert : u.graph.vertices = t.graph.vertices ∪ qFinset sc.r x := rfl
  have hrelay := FinGraph.neighbor_relay hd sc hK hPos u.graph p t.vertex dir
    (fun y hy => by
      rw [huvert]
      rcases hy with hy | hy
      · exact Finset.mem_union_left _ (t.contains_vertices y hy)
      · exact Finset.mem_union_right _ (mem_qFinset.mpr hy))
    (fun y z hy hz hyz => by
      refine ⟨?_, hfresh _ y (Sym2.mem_mk_left y z) hy⟩
      rw [huedges]
      rcases hy with hy | hy <;> rcases hz with hz | hz
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (t.contains_edges (mk_mem_qBits.mpr ⟨hy, hz, hyz⟩)))
      · exact Finset.mem_union_right _ (mem_link.mpr ⟨y, hy, z, hz, rfl⟩)
      · exact Finset.mem_union_right _ (mem_link.mpr ⟨z, hz, y, hy, Sym2.eq_swap⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (mk_mem_qBits.mpr ⟨hy, hz, hyz⟩)))
    (fun y z _ hz _ => le_of_eq (congrArg Subtype.val (hfresh _ z (Sym2.mem_mk_right y z) hz)))
    u.root_mem
    (by
      rintro (h | h)
      · exact zero_not_mem_Qcube hd sc.r hv0 h
      · exact zero_not_mem_Qcube hd sc.r hx0 h)
  have hi : t.event ∩ u.eventᶜ ⊆ {ω | u.graph.Meets ω 0 (Bcube sc.r t.vertex) ∧
      ¬u.graph.Meets ω 0 (Bcube sc.r x)} := by
    intro ω hω
    exact ⟨meets_mono_edges (t.child_subgraph x) hω.1, hω.2⟩
  have heq : (ProductCylinder.law p).real (s.frozenEvent t ∩ u.eventᶜ) =
      (ProductCylinder.law p).real (t.event ∩ u.eventᶜ) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [ae_freeze (K.edgeProb sc.q) s.history] with ω hω
    change ((s.history.freeze ω ∈ t.event) ∧ _) = ((ω ∈ t.event) ∧ _)
    rw [hω]
  rw [heq]
  exact (measureReal_mono hi).trans hrelay

/-- Lemma 6.2: the head of the queue is declared bad with conditional probability less than `f`. -/
theorem badMass_bound (hd : 2 ≤ d) [NeZero d] {K : Kernel d} {β : ℝ} (sc : ScaleData K β)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0)) {s : Exploration d sc.r}
    (hs : s.Valid (K.edgeProb sc.q) sc.δ) :
    (scheme (r := sc.r) (K.edgeProb sc.q) sc.δ).badMass s ≤ CriticalScales.contourError := by
  rw [badMass_eq]
  cases hq : s.queue with
  | nil => simpa only [markedBad, hq, Bool.false_eq_true, Set.ofPred_false, measureReal_empty] using
      CriticalScales.contourError_pos.le
  | cons t ts =>
    let p₀ := K.edgeProb sc.q
    let μ := ProductCylinder.law (hparam p₀ s.history)
    let H := s.frozenEvent t
    let T (dir : Direction) : Set (Config d) :=
      {ω | ω ∈ H ∧ t.vertex + PlanarBoundary.outward dir ∉ s.visited ∧
        (ProductCylinder.law (hparam p₀ (s.after ω))).real
          ((t.child (t.vertex + PlanarBoundary.outward dir)).event) ≤ 1 - sc.δ}
    have hH := frozenEvent_determined hs hq
    have hHm : MeasurableSet H := ProductCylinder.measurableSet_determined _ _
      (fun ω ω' he => Eq.to_iff (hH ω ω' he))
    have hHprob : μ.real Hᶜ < sc.δ := by
      rw [measureReal_compl hHm, probReal_univ]
      have hh := hs.promise t (by simp [hq])
      have he := s.frozenEvent_probability p₀ t
      change μ.real H = μ.real t.event at he
      rw [he]
      linarith
    have hT (dir : Direction) : μ.real (T dir) ≤ (((d : ℝ) + 10) * sc.η) / sc.δ := by
      by_cases hx : t.vertex + PlanarBoundary.outward dir ∉ s.visited
      · have hh := conditional_failure_bound (hparam p₀ s.history) s.reveal H
          ((t.child (t.vertex + PlanarBoundary.outward dir)).event) hH
          ((t.child (t.vertex + PlanarBoundary.outward dir)).measurableSet_event) sc.δ_range.1
          (relay_failure hd sc hK hPos hs hq dir hx)
        have he : T dir = {ω | ω ∈ H ∧ conditionalProbability (hparam p₀ s.history)
            s.reveal ((t.child (t.vertex + PlanarBoundary.outward dir)).event) ω ≤ 1 - sc.δ} := by
          ext ω
          simp only [T, hx, not_false_eq_true, true_and, Set.mem_ofPred_eq, after, hparam_observe,
            conditionalProbability]
        rwa [he]
      · have he : T dir = ∅ := by
          ext ω
          simp only [T, hx, false_and, and_false, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
        rw [he, measureReal_empty]
        exact div_nonneg (mul_nonneg (by positivity) sc.η_range.1.le) sc.δ_range.1.le
    have hb : {ω | s.markedBad p₀ sc.δ ω = true} ⊆ Hᶜ ∪ ⋃ dir, T dir := by
      intro ω hω
      have hn : ¬s.Accept p₀ sc.δ t ω := by
        simpa only [Set.mem_ofPred_eq, markedBad, hq, decide_eq_true_eq] using hω
      by_cases hh : ω ∈ H
      · right
        have hcur := (accept_current_iff hs hq ω).mpr hh
        have hpred : ¬∀ u ∈ s.candidates t, 1 - sc.δ <
            (ProductCylinder.law (hparam p₀ (s.after ω))).real u.event :=
          fun hp => hn ⟨hcur, hp⟩
        push Not at hpred
        obtain ⟨u, hu, hfail⟩ := hpred
        obtain ⟨⟨dir, rfl⟩, hx⟩ := (mem_candidates s t u).mp hu
        exact Set.mem_iUnion.mpr ⟨dir, hh, hx, hfail⟩
      · exact Or.inl hh
    calc
      _ ≤ μ.real (Hᶜ ∪ ⋃ dir, T dir) := measureReal_mono hb
      _ ≤ μ.real Hᶜ + μ.real (⋃ dir, T dir) := measureReal_union_le _ _
      _ ≤ μ.real Hᶜ + ∑ dir, μ.real (T dir) := add_le_add le_rfl (measureReal_iUnion_fintype_le _)
      _ ≤ μ.real Hᶜ + ∑ _dir : Direction, (((d : ℝ) + 10) * sc.η) / sc.δ :=
        add_le_add le_rfl (Finset.sum_le_sum (fun dir _ => hT dir))
      _ = μ.real Hᶜ + 4 * ((d : ℝ) + 10) * sc.η / sc.δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ sc.δ + 4 * ((d : ℝ) + 10) * sc.η / sc.δ := add_le_add hHprob.le le_rfl
      _ ≤ CriticalScales.contourError := sc.failure_budget.le

/-- Lemma 6.3 through the adaptive-reveal scheme. -/
theorem everHit_bound (hd : 2 ≤ d) [NeZero d] {K : Kernel d} {β : ℝ} (sc : ScaleData K β)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0)) {s : Exploration d sc.r}
    (hs : s.Valid (K.edgeProb sc.q) sc.δ) (U : Finset Point) :
    (ProductCylinder.law (hparam (K.edgeProb sc.q) s.history)).real
      (⋃ n, (scheme (r := sc.r) (K.edgeProb sc.q) sc.δ).hit n s U) ≤
        CriticalScales.contourError ^ U.card := by
  apply AdaptiveReveals.Scheme.everHit_bound _ (Valid (K.edgeProb sc.q) sc.δ) _
    CriticalScales.contourError_pos.le (fun _ hs => badMass_bound hd sc hK hPos hs) _ s hs U
  intro s hs a _
  exact valid_advance hd hs _

/-! ### From bad vertices to the Peierls bound -/

theorem run_add (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) (a b : ℕ) (s : Exploration d r)
    (ω : Config d) : run p₀ δ (a + b) s ω = run p₀ δ b (run p₀ δ a s ω) ω := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add, run_zero]
  | succ a ih => rw [Nat.succ_add, run_succ, ih, run_succ]

theorem run_stable (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) (s : Exploration d r)
    (ω : Config d) {N k : ℕ} (hN : (run p₀ δ N s ω).queue = []) (hk : N ≤ k) :
    run p₀ δ k s ω = run p₀ δ N s ω := by
  rw [← Nat.add_sub_of_le hk, run_add]
  exact run_empty p₀ δ hN _ ω

theorem good_eq_of_empty (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) (s : Exploration d r)
    (ω : Config d) {N : ℕ} (hN : (run p₀ δ N s ω).queue = []) :
    Good p₀ δ s ω = ((run p₀ δ N s ω).good : Set Point) := by
  ext v
  constructor
  · rintro ⟨k, hk⟩
    have hh := run_good_mono p₀ δ s ω (show k ≤ N + k by omega) hk
    dsimp only at hh
    rwa [run_stable p₀ δ s ω hN (show N ≤ N + k by omega)] at hh
  · intro h; exact ⟨N, h⟩

theorem exists_empty_of_finite_good (hd : 2 ≤ d) {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ}
    {s : Exploration d r} (hs : s.Valid p₀ δ) (hc : s.Covered) (ω : Config d)
    (hfin : (Good p₀ δ s ω).Finite) : ∃ n, (run p₀ δ n s ω).queue = [] := by
  let X := Good p₀ δ s ω
  let F := X ∪ ⋃ dir : Direction, (fun v : Point => v + PlanarBoundary.outward dir) '' X
  have hF : F.Finite := hfin.union (Set.finite_iUnion (fun dir => hfin.image _))
  have hbound (n : ℕ) : (run p₀ δ n s ω).processed ⊆ hF.toFinset := by
    intro v hv
    apply hF.mem_toFinset.mpr
    have hh := run_covered p₀ δ hc n ω v ((run p₀ δ n s ω).processed_visited hv)
    rcases hh with hv | ⟨u, hu, dir, rfl⟩
    · exact Or.inl ⟨n, hv⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨dir, u, ⟨n, hu⟩, rfl⟩)
  by_contra! hn
  have hcard (n : ℕ) : s.processed.card + n ≤ (run p₀ δ n s ω).processed.card := by
    induction n with
    | zero => simp only [run_zero, Nat.add_zero, le_refl]
    | succ n ih =>
      have hvalid := run_valid hd hs n ω
      cases hq : (run p₀ δ n s ω).queue with
      | nil => exact False.elim (hn n hq)
      | cons t ts =>
        rw [run_succ_right, advance_processed _ p₀ δ ω hq,
          Finset.card_insert_of_notMem (hvalid.unprocessed t (by simp [hq]))]
        omega
  have hh := (hcard (hF.toFinset.card + 1)).trans (Finset.card_le_card (hbound _))
  omega

theorem outside_bad (hd : 2 ≤ d) {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ} {s : Exploration d r}
    (hs : s.Valid p₀ δ) (hc : s.Colored) (hclosed : s.Closed) (hcovered : s.Covered)
    (ω : Config d) (hfin : (Good p₀ δ s ω).Finite) {x : Point} (hx : x ∈ Good p₀ δ s ω)
    (dir : Direction) (hy : x + PlanarBoundary.outward dir ∉ Good p₀ δ s ω) :
    ω ∈ Bad p₀ δ s (x + PlanarBoundary.outward dir) := by
  obtain ⟨N, hN⟩ := exists_empty_of_finite_good hd hs hcovered ω hfin
  have he := good_eq_of_empty p₀ δ s ω hN
  have hxN : x ∈ (run p₀ δ N s ω).good := by
    change x ∈ ((run p₀ δ N s ω).good : Set Point)
    rwa [← he]
  have hv := run_closed p₀ δ hclosed N ω x hxN dir
  have hp : x + PlanarBoundary.outward dir ∈ (run p₀ δ N s ω).processed := by
    simpa only [visited, hN, List.map_nil, List.toFinset_nil, Finset.union_empty] using hv
  rw [(run_colored hd hs hc N ω).partition, Finset.mem_union] at hp
  rcases hp with hg | hb
  · exact False.elim (hy ⟨N, hg⟩)
  · exact ⟨N, hb⟩

theorem hit_of_bad_subset (hd : 2 ≤ d) {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ}
    {s : Exploration d r} (hs : s.Valid p₀ δ) (hc : s.Colored) (n : ℕ) (ω : Config d)
    (U : Finset Point) (hdis : Disjoint U s.processed) (hU : U ⊆ (run p₀ δ n s ω).bad) :
    ω ∈ (scheme (r := r) p₀ δ).hit n s U := by
  induction n generalizing s U with
  | zero =>
    have he : U = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact Finset.disjoint_left.mp hdis hv (hc.bad_processed (hU hv))
    rw [he, AdaptiveReveals.Scheme.hit_empty]
    trivial
  | succ n ih =>
    cases hq : s.queue with
    | nil =>
      have he : U = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        rw [run_empty p₀ δ hq] at hU
        exact Finset.disjoint_left.mp hdis hv (hc.bad_processed (hU hv))
      rw [he, AdaptiveReveals.Scheme.hit_empty]
      trivial
    | cons t ts =>
      have hchild : (scheme (r := r) p₀ δ).child s (s.reveal.restrict ω) = s.advance p₀ δ ω :=
        (ProductCylinder.determinedBy_eq_extend (s.advance_determined p₀ δ) ω).symm
      have hbad : (scheme (r := r) p₀ δ).bad s (s.reveal.restrict ω) = s.markedBad p₀ δ ω :=
        (ProductCylinder.determinedBy_eq_extend (s.markedBad_determined p₀ δ) ω).symm
      have hv : (scheme (r := r) p₀ δ).vertex s = some t.vertex := by
        simp only [scheme, hq, List.head?_cons, Option.map_some]
      rw [AdaptiveReveals.Scheme.hit, hv]
      change (t.vertex ∈ U → (scheme (r := r) p₀ δ).bad s (s.reveal.restrict ω) = true) ∧
        ω ∈ (scheme (r := r) p₀ δ).hit n
          ((scheme (r := r) p₀ δ).child s (s.reveal.restrict ω)) (U.erase t.vertex)
      rw [hchild, hbad]
      constructor
      · intro hv
        have hna : ¬s.Accept p₀ δ t ω := by
          intro ha
          have hg : t.vertex ∈ (s.advance p₀ δ ω).good := by
            simp only [advance, hq, ite_eq_left ha]; exact Finset.mem_insert_self _ _
          have hg' := run_good_mono p₀ δ (s.advance p₀ δ ω) ω (Nat.zero_le n) hg
          exact Finset.disjoint_left.mp (run_colored hd hs hc (n + 1) ω).disjoint hg' (hU hv)
        simpa only [markedBad, hq, decide_eq_true_eq] using hna
      · apply ih (valid_advance hd hs ω) (colored_advance hs hc ω) (U.erase t.vertex)
        · apply Finset.disjoint_left.mpr
          intro v hv hp
          rw [advance_processed s p₀ δ ω hq, Finset.mem_insert] at hp
          rcases hp with he | hp
          · exact (Finset.mem_erase.mp hv).1 he
          · exact Finset.disjoint_left.mp hdis (Finset.mem_of_mem_erase hv) hp
        · exact Finset.Subset.trans (Finset.erase_subset _ _) hU

theorem exists_bad_time (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) (s : Exploration d r)
    (ω : Config d) (U : Finset Point) (hU : ∀ v ∈ U, ω ∈ Bad p₀ δ s v) :
    ∃ n, U ⊆ (run p₀ δ n s ω).bad := by
  induction U using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert a U ha ih =>
    obtain ⟨k, hk⟩ := hU a (Finset.mem_insert_self _ _)
    obtain ⟨n, hn⟩ := ih (fun v hv => hU v (Finset.mem_insert_of_mem hv))
    refine ⟨max k n, ?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact run_bad_mono p₀ δ s ω (le_max_left _ _) hk
    · exact run_bad_mono p₀ δ s ω (le_max_right _ _) (hn hv)

theorem bad_set_subset (hd : 2 ≤ d) {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ}
    {s : Exploration d r} (hs : s.Valid p₀ δ) (hc : s.Colored) (hb : s.bad = ∅)
    (U : Finset Point) :
    {ω | ∀ v ∈ U, ω ∈ Bad p₀ δ s v} ⊆ ⋃ n, (scheme (r := r) p₀ δ).hit n s U := by
  intro ω hω
  obtain ⟨n, hn⟩ := exists_bad_time p₀ δ s ω U hω
  apply Set.mem_iUnion.mpr
  refine ⟨n, hit_of_bad_subset hd hs hc n ω U ?_ hn⟩
  apply Finset.disjoint_left.mpr
  intro v hv hp
  have hg : v ∈ s.good := by simpa only [hc.partition, hb, Finset.union_empty] using hp
  have hgn := run_good_mono p₀ δ s ω (Nat.zero_le n) hg
  exact Finset.disjoint_left.mp (run_colored hd hs hc n ω).disjoint hgn (hn hv)

/-- The proof of Theorem 1.1, Peierls step: the good set is finite with probability at most
`25/144` under the initial history. -/
theorem finite_good_bound (hd : 2 ≤ d) [NeZero d] {K : Kernel d} {β : ℝ} (sc : ScaleData K β)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0)) {s : Exploration d sc.r}
    (hs : s.Valid (K.edgeProb sc.q) sc.δ) (hc : s.Colored) (hb : s.bad = ∅)
    (hclosed : s.Closed) (hcovered : s.Covered) :
    (ProductCylinder.law (hparam (K.edgeProb sc.q) s.history)).real
      {ω | (Good (K.edgeProb sc.q) sc.δ s ω).Finite ∧ (0, 0) ∈ Good (K.edgeProb sc.q) sc.δ s ω} ≤
        25 / 144 := by
  apply PlanarBoundary.finite_good_bound _ (Good (K.edgeProb sc.q) sc.δ s)
    (Bad (K.edgeProb sc.q) sc.δ s)
    (fun ω hfin x hx dir hy => outside_bad hd hs hc hclosed hcovered ω hfin hx dir hy)
  intro U
  exact (measureReal_mono (bad_set_subset hd hs hc hb U)).trans (everHit_bound hd sc hK hPos hs U)

end Exploration

end Peapods.LongRange.Coarse
