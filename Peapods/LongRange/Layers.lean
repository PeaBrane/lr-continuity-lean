import Peapods.LongRange.FinGraph

/-!
# Step 1 of the extension lemma: a quiet layer

For a box `C`, the bits `ζ` are the edges of `G` off `C`, and `𝒞` is the open cluster of `o` in the
graph off `C`. The crossing weight `W = ∑ λ` runs over the edges of `G` from `𝒞` into `C`, with
`λ = -log (1 - p)`. Given `ζ`, every crossing edge is closed with probability exactly `e^{-W}`, and
then the cluster of `o` stays in `𝒞` (`blocked_conn`). Layers `B^{(j)}`, `j ∈ m + wℕ`, are blocked in
disjoint events, so some layer has a small probability of carrying a light cluster that reaches the
shell `B^{(j+w)} \ B^{(j)}` (`exists_quiet_layer`). A light cluster that misses the shell and still
reaches `B` uses an edge of length more than `w` into `B^{(R)}` (`meets_low_weight_subset`), which
is rare by the tail bound (`longEntry_le`). Ported in outline from OpenAI's `ShellProbability`
and `EntryLayers`, where the closing cost is `(1 - p)^{#entrants}`.
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical OAI InfiniteConditioning
open scoped ENNReal

variable {d : ℕ}

/-! ### Rates -/

/-- The rate `λ = -log (1 - p)` of a bit. -/
noncomputable def rate (t : Set.Icc (0 : ℝ) 1) : ℝ := -Real.log (1 - t)

theorem exp_neg_rate {t : Set.Icc (0 : ℝ) 1} (h : (t : ℝ) < 1) : Real.exp (-rate t) = 1 - t := by
  rw [rate, neg_neg, Real.exp_log (by linarith)]

theorem rate_nonneg (t : Set.Icc (0 : ℝ) 1) : 0 ≤ rate t := by
  rw [rate, neg_nonneg]
  exact Real.log_nonpos (by linarith [t.2.2]) (by linarith [t.2.1])

theorem rate_le {t : Set.Icc (0 : ℝ) 1} {a : ℝ} (h : (t : ℝ) ≤ 1 - Real.exp (-a)) : rate t ≤ a := by
  rw [rate, neg_le]
  have h1 : Real.exp (-a) ≤ 1 - t := by linarith
  calc -a = Real.log (Real.exp (-a)) := (Real.log_exp _).symm
    _ ≤ Real.log (1 - t) := Real.log_le_log (Real.exp_pos _) h1

namespace Kernel

variable (K : Kernel d)

theorem edgeProb_lt_one (q : ℝ) (e : Pair d) : (K.edgeProb q e : ℝ) < 1 := by
  simp only [edgeProb]
  linarith [Real.exp_pos (-(max q 0 * K.pairWeight e))]

/-- A bit dominated by `edgeProb q` has rate at most `q⁺ J`. -/
theorem rate_le_of_le {q : ℝ} {e : Pair d} {t : Set.Icc (0 : ℝ) 1}
    (h : (t : ℝ) ≤ K.edgeProb q e) : rate t ≤ max q 0 * K.pairWeight e :=
  rate_le h

/-- The tail union bound under any product law dominated by `edgeProb q` on the relevant pairs. -/
theorem tail_union_le (p : Pair d → Set.Icc (0 : ℝ) 1) (q : ℝ) (S : Finset (Vertex d)) (w : ℕ)
    (P : Pair d → Prop)
    (hp : ∀ z ∈ S, ∀ x, x ∉ cube z w → P s(z, x) → (p s(z, x) : ℝ) ≤ K.edgeProb q s(z, x)) :
    ProductCylinder.law p {ω | ∃ z ∈ S, ∃ x, x ∉ cube z w ∧ P s(z, x) ∧ ω s(z, x) = true} ≤
      ENNReal.ofReal (S.card * (max q 0 * K.tail w)) := by
  have hsub : {ω : Config d | ∃ z ∈ S, ∃ x, x ∉ cube z w ∧ P s(z, x) ∧ ω s(z, x) = true} ⊆
      ⋃ z ∈ S, ⋃ x : Vertex d,
        {ω : Config d | x ∉ cube z w ∧ P s(z, x) ∧ ω s(z, x) = true} := by
    rintro ω ⟨z, hz, x, hx⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨z, hz, x, hx⟩
  have hone (z x : Vertex d) (hz : z ∈ S) :
      ProductCylinder.law p {ω : Config d | x ∉ cube z w ∧ P s(z, x) ∧ ω s(z, x) = true} ≤
        (cube z w)ᶜ.indicator (fun x => K.stepWeight q (x - z)) x := by
    by_cases hx : x ∈ cube z w ∨ ¬P s(z, x)
    · have : {ω : Config d | x ∉ cube z w ∧ P s(z, x) ∧ ω s(z, x) = true} = ∅ := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; tauto
      rw [this, measure_empty]
      exact zero_le
    · push Not at hx
      rw [Set.indicator_of_mem (show x ∈ (cube z w)ᶜ from hx.1)]
      calc ProductCylinder.law p {ω : Config d | x ∉ cube z w ∧ P s(z, x) ∧ ω s(z, x) = true}
          ≤ ProductCylinder.law p {ω : Config d | ω s(z, x) = true} :=
            measure_mono (fun ω h => h.2.2)
        _ = ENNReal.ofReal (p s(z, x)) := by
            rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
            congr 1
            have h := InfiniteConditioning.single_probability p s(z, x) true
            simp only [InfiniteConditioning.bitProbability, ite_true] at h
            exact h
        _ ≤ K.stepWeight q (x - z) :=
            ENNReal.ofReal_le_ofReal ((hp z hz x hx.1 hx.2).trans (K.edgeProb_le q z x))
  have hrow (z : Vertex d) (hz : z ∈ S) : ∑' x, ProductCylinder.law p
      {ω : Config d | x ∉ cube z w ∧ P s(z, x) ∧ ω s(z, x) = true} ≤
      ENNReal.ofReal (max q 0 * K.tail w) := by
    refine (ENNReal.tsum_le_tsum (fun x => hone z x hz)).trans (le_of_eq ?_)
    have he (x : Vertex d) : (cube z w)ᶜ.indicator (fun x => K.stepWeight q (x - z)) x =
        (cube 0 w)ᶜ.indicator (K.stepWeight q) (x - z) := by
      by_cases h : x ∈ cube z w
      · have h' : x - z ∈ cube 0 w := mem_cube_iff_sub.mp h
        simp [h, h']
      · have h' : x - z ∉ cube 0 w := fun h' => h (mem_cube_iff_sub.mpr h')
        simp [h, h']
    simp_rw [he]
    rw [tsum_translate, K.tsum_stepWeight_tail]
  calc ProductCylinder.law p {ω : Config d | ∃ z ∈ S, ∃ x, x ∉ cube z w ∧ P s(z, x) ∧
        ω s(z, x) = true}
      ≤ ProductCylinder.law p (⋃ z ∈ S, ⋃ x : Vertex d,
          {ω : Config d | x ∉ cube z w ∧ P s(z, x) ∧ ω s(z, x) = true}) := measure_mono hsub
    _ ≤ ∑ z ∈ S, ProductCylinder.law p (⋃ x : Vertex d,
          {ω : Config d | x ∉ cube z w ∧ P s(z, x) ∧ ω s(z, x) = true}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ S, ENNReal.ofReal (max q 0 * K.tail w) :=
        Finset.sum_le_sum (fun z hz => (measure_iUnion_le _).trans (hrow z hz))
    _ = ENNReal.ofReal (S.card * (max q 0 * K.tail w)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

end Kernel

/-! ### Clusters off a box -/

namespace FinGraph

variable (G : FinGraph d)

/-- The edges of `G` with no endpoint in `C` (the bits `ζ`). -/
noncomputable def outsideBits (C : Box d) : Finset (Pair d) :=
  G.edges.filter (fun e => ∀ v ∈ e, ¬C.Contains v)

/-- The edges of `G` with both endpoints in `C` (the bits `ξ`). -/
noncomputable def insideBits (C : Box d) : Finset (Pair d) :=
  G.edges.filter (fun e => ∀ v ∈ e, C.Contains v)

/-- An open edge of `G` off `C`. -/
def OutAdj (C : Box d) (ω : Config d) (x y : Vertex d) : Prop :=
  G.Adj ω x y ∧ ¬C.Contains x ∧ ¬C.Contains y

/-- The open cluster `𝒞` of `o` in `G` off `C`. -/
noncomputable def outCluster (C : Box d) (ω : Config d) (o : Vertex d) : Finset (Vertex d) :=
  G.vertices.filter (fun x => Relation.ReflTransGen (G.OutAdj C ω) o x)

/-- Pairs `(x, z)` with `x ∈ 𝒞`, `z ∈ C` and `{x, z}` an edge of `G`. -/
noncomputable def crossPairs (C : Box d) (ω : Config d) (o : Vertex d) :
    Finset (Vertex d × Vertex d) :=
  (G.outCluster C ω o ×ˢ C.vertices).filter (fun xz => s(xz.1, xz.2) ∈ G.edges)

/-- The edges of `G` between `𝒞` and `C`. -/
noncomputable def crossing (C : Box d) (ω : Config d) (o : Vertex d) : Finset (Pair d) :=
  (G.crossPairs C ω o).image (fun xz => s(xz.1, xz.2))

/-- The crossing weight `W = ∑ λ` over the edges between `𝒞` and `C`. -/
noncomputable def weight (p : Pair d → Set.Icc (0 : ℝ) 1) (C : Box d) (ω : Config d)
    (o : Vertex d) : ℝ :=
  ∑ xz ∈ G.crossPairs C ω o, rate (p s(xz.1, xz.2))

/-- Every edge between `𝒞` and `C` is closed (the event `Cl`). -/
def Blocked (C : Box d) (ω : Config d) (o : Vertex d) : Prop :=
  ∀ e ∈ G.crossing C ω o, ω e = false

variable {G}

theorem mem_outCluster {C : Box d} {ω : Config d} {o x : Vertex d} :
    x ∈ G.outCluster C ω o ↔ x ∈ G.vertices ∧ Relation.ReflTransGen (G.OutAdj C ω) o x := by
  simp only [outCluster, Finset.mem_filter]

theorem outAdj_congr {C : Box d} {ω ω' : Config d} (h : ∀ e ∈ G.outsideBits C, ω' e = ω e)
    (x y : Vertex d) : G.OutAdj C ω' x y ↔ G.OutAdj C ω x y := by
  have hmem {x y : Vertex d} (he : s(x, y) ∈ G.edges) (hx : ¬C.Contains x)
      (hy : ¬C.Contains y) : s(x, y) ∈ G.outsideBits C := by
    refine Finset.mem_filter.mpr ⟨he, fun v hv => ?_⟩
    rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
  constructor <;> rintro ⟨⟨he, hne, ho⟩, hx, hy⟩
  · exact ⟨⟨he, hne, (h _ (hmem he hx hy)) ▸ ho⟩, hx, hy⟩
  · exact ⟨⟨he, hne, (h _ (hmem he hx hy)).symm ▸ ho⟩, hx, hy⟩

theorem outCluster_congr {C : Box d} {ω ω' : Config d} (h : ∀ e ∈ G.outsideBits C, ω' e = ω e)
    (o : Vertex d) : G.outCluster C ω' o = G.outCluster C ω o := by
  have he : G.OutAdj C ω' = G.OutAdj C ω := by
    funext a b; exact propext (outAdj_congr h a b)
  simp only [outCluster, he]

theorem crossPairs_congr {C : Box d} {ω ω' : Config d} (h : ∀ e ∈ G.outsideBits C, ω' e = ω e)
    (o : Vertex d) : G.crossPairs C ω' o = G.crossPairs C ω o := by
  simp only [crossPairs, outCluster_congr h o]

theorem crossing_congr {C : Box d} {ω ω' : Config d} (h : ∀ e ∈ G.outsideBits C, ω' e = ω e)
    (o : Vertex d) : G.crossing C ω' o = G.crossing C ω o := by
  simp only [crossing, crossPairs_congr h o]

theorem weight_congr (p : Pair d → Set.Icc (0 : ℝ) 1) {C : Box d} {ω ω' : Config d}
    (h : ∀ e ∈ G.outsideBits C, ω' e = ω e) (o : Vertex d) :
    G.weight p C ω' o = G.weight p C ω o := by
  simp only [weight, crossPairs_congr h o]

theorem outsideBits_subset (C : Box d) : G.outsideBits C ⊆ G.edges := Finset.filter_subset _ _

theorem insideBits_subset (C : Box d) : G.insideBits C ⊆ G.edges := Finset.filter_subset _ _

/-- Agreement on the edges of `G` is agreement on the bits `ζ`. -/
theorem agree_outside {C : Box d} {ω ω' : Config d} (h : ∀ e ∈ G.edges, ω' e = ω e) :
    ∀ e ∈ G.outsideBits C, ω' e = ω e := fun e he => h e (outsideBits_subset C he)

theorem outCluster_not_contains {C : Box d} {ω : Config d} {o x : Vertex d}
    (ho : ¬C.Contains o) (hx : x ∈ G.outCluster C ω o) : ¬C.Contains x := by
  have hp := (mem_outCluster.mp hx).2
  cases hp with
  | refl => exact ho
  | tail _ hab => exact hab.2.2

theorem outCluster_conn {C : Box d} {ω : Config d} {o x : Vertex d}
    (hx : x ∈ G.outCluster C ω o) : G.Conn ω o x :=
  Relation.ReflTransGen.mono (fun _ _ h => h.1) o x (mem_outCluster.mp hx).2

theorem self_mem_outCluster {C : Box d} {ω : Config d} {o : Vertex d} (hov : o ∈ G.vertices) :
    o ∈ G.outCluster C ω o := mem_outCluster.mpr ⟨hov, .refl⟩

theorem mem_crossPairs {C : Box d} {ω : Config d} {o x z : Vertex d} :
    (x, z) ∈ G.crossPairs C ω o ↔
      x ∈ G.outCluster C ω o ∧ C.Contains z ∧ s(x, z) ∈ G.edges := by
  simp only [crossPairs, Finset.mem_filter, Finset.mem_product, Box.mem_vertices, and_assoc]

theorem crossPairs_injOn {C : Box d} {ω : Config d} {o : Vertex d} (ho : ¬C.Contains o) :
    Set.InjOn (fun xz : Vertex d × Vertex d => s(xz.1, xz.2)) (G.crossPairs C ω o) := by
  rintro ⟨x, z⟩ h ⟨x', z'⟩ h' he
  have hx := outCluster_not_contains ho (mem_crossPairs.mp h).1
  have hz' := (mem_crossPairs.mp h').2.1
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, _⟩
  · rfl
  · exact absurd hz' hx

theorem mem_crossing {C : Box d} {ω : Config d} {o : Vertex d} {e : Pair d} :
    e ∈ G.crossing C ω o ↔ ∃ x z, (x, z) ∈ G.crossPairs C ω o ∧ e = s(x, z) := by
  simp only [crossing, Finset.mem_image, Prod.exists]
  exact ⟨fun ⟨x, z, h, he⟩ => ⟨x, z, h, he.symm⟩, fun ⟨x, z, h, he⟩ => ⟨x, z, h, he.symm⟩⟩

theorem crossing_subset_edges (C : Box d) (ω : Config d) (o : Vertex d) :
    G.crossing C ω o ⊆ G.edges := by
  intro e he
  obtain ⟨x, z, h, rfl⟩ := mem_crossing.mp he
  exact (mem_crossPairs.mp h).2.2

theorem crossing_disjoint_outside (C : Box d) (ω : Config d) (o : Vertex d) :
    Disjoint (G.outsideBits C) (G.crossing C ω o) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨x, z, h, rfl⟩ := mem_crossing.mp he'
  exact (Finset.mem_filter.mp he).2 z (Sym2.mem_mk_right x z) (mem_crossPairs.mp h).2.1

theorem crossing_disjoint_inside {C : Box d} {ω : Config d} {o : Vertex d} (ho : ¬C.Contains o) :
    Disjoint (G.insideBits C) (G.crossing C ω o) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨x, z, h, rfl⟩ := mem_crossing.mp he'
  exact outCluster_not_contains ho (mem_crossPairs.mp h).1
    ((Finset.mem_filter.mp he).2 x (Sym2.mem_mk_left x z))

/-- On `Cl`, the open cluster of `o` in `G` is `𝒞`. -/
theorem blocked_conn {C : Box d} {ω : Config d} {o y : Vertex d} (hb : G.Blocked C ω o)
    (ho : ¬C.Contains o) (hov : o ∈ G.vertices) (h : G.Conn ω o y) : y ∈ G.outCluster C ω o := by
  induction h with
  | refl => exact self_mem_outCluster hov
  | @tail a b _ hab ih =>
    have ha := outCluster_not_contains ho ih
    by_cases hb' : C.Contains b
    · have hc : s(a, b) ∈ G.crossing C ω o :=
        mem_crossing.mpr ⟨a, b, mem_crossPairs.mpr ⟨ih, hb', hab.1⟩, rfl⟩
      have := hb _ hc
      rw [hab.2.2] at this
      exact absurd this (by decide)
    · exact mem_outCluster.mpr ⟨(adj_mem hab).2, (mem_outCluster.mp ih).2.tail ⟨hab, ha, hb'⟩⟩

/-! ### The blocking probability -/

/-- Given the bits off `C`, the crossing edges are all closed with probability `e^{-W}`. -/
theorem blocked_probability (p : Pair d → Set.Icc (0 : ℝ) 1) {C : Box d} {o : Vertex d}
    (ho : ¬C.Contains o) (ξ : Config d)
    (hp1 : ∀ x z, s(x, z) ∈ G.edges → ¬C.Contains x → C.Contains z → (p s(x, z) : ℝ) < 1) :
    (ProductCylinder.law (fixedParameter p (G.outsideBits C) ξ)).real
      (allValue (G.crossing C ξ o) false) = Real.exp (-G.weight p C ξ o) := by
  rw [fixed_determined_probability p _ _ (crossing_disjoint_outside C ξ o) ξ _
    (allValue_determined _ _), allValue_probability, crossing,
    Finset.prod_image (fun a ha b hb h => crossPairs_injOn ho ha hb h)]
  simp only [bitProbability, Bool.false_eq_true, ite_false]
  rw [weight, ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  rintro ⟨x, z⟩ h
  obtain ⟨hx, hz, he⟩ := mem_crossPairs.mp h
  exact (exp_neg_rate (hp1 x z he (outCluster_not_contains ho hx) hz)).symm

/-! ### Layer events -/

/-- `𝒞` off `B^{(j)}` meets the shell `B^{(j+w)} \ B^{(j)}`. -/
def Shell (B : Box d) (j w : ℕ) (ω : Config d) (o : Vertex d) : Prop :=
  ∃ x ∈ G.outCluster (B.expand j) ω o, (B.expand (j + w)).Contains x

variable (G)

/-- The event `L_j = {W_j < L, 𝒞_j ∩ S_j ≠ ∅}`. -/
def LayerEvent (p : Pair d → Set.Icc (0 : ℝ) 1) (B : Box d) (j w : ℕ) (L : ℝ) (o : Vertex d) :
    Set (Config d) :=
  {ω | G.weight p (B.expand j) ω o < L ∧ G.Shell B j w ω o}

/-- An open edge of `G` of length more than `w` into `B^{(R)}`. -/
def LongEntry (B : Box d) (R w : ℕ) : Set (Config d) :=
  {ω | ∃ z ∈ (B.expand R).vertices, ∃ x, x ∉ cube z w ∧ s(z, x) ∈ G.edges ∧ ω s(z, x) = true}

variable {G}

theorem shell_congr {B : Box d} {j w : ℕ} {ω ω' : Config d}
    (h : ∀ e ∈ G.outsideBits (B.expand j), ω' e = ω e) (o : Vertex d) :
    G.Shell B j w ω' o ↔ G.Shell B j w ω o := by
  simp only [Shell, outCluster_congr h o]

theorem layerEvent_congr (p : Pair d → Set.Icc (0 : ℝ) 1) {B : Box d} {j w : ℕ} {L : ℝ}
    {o : Vertex d} {ω ω' : Config d} (h : ∀ e ∈ G.outsideBits (B.expand j), ω' e = ω e) :
    ω' ∈ G.LayerEvent p B j w L o ↔ ω ∈ G.LayerEvent p B j w L o := by
  simp only [LayerEvent, Set.mem_ofPred_eq, weight_congr p h o, shell_congr h o]

theorem measurableSet_layerEvent (p : Pair d → Set.Icc (0 : ℝ) 1) (B : Box d) (j w : ℕ) (L : ℝ)
    (o : Vertex d) : MeasurableSet (G.LayerEvent p B j w L o) :=
  ProductCylinder.measurableSet_determined _ _ (fun _ _ h => layerEvent_congr p h)

theorem measurableSet_layer_blocked (p : Pair d → Set.Icc (0 : ℝ) 1) (B : Box d) (j w : ℕ)
    (L : ℝ) (o : Vertex d) :
    MeasurableSet (G.LayerEvent p B j w L o ∩ {ω | G.Blocked (B.expand j) ω o}) := by
  apply ProductCylinder.measurableSet_determined G.edges
  intro ω ω' h
  have ho := agree_outside (C := B.expand j) h
  simp only [Set.mem_inter_iff, layerEvent_congr p ho, Set.mem_ofPred_eq, Blocked,
    crossing_congr ho o]
  apply and_congr_right
  intro _
  refine forall₂_congr (fun e he => ?_)
  rw [h e (crossing_subset_edges _ _ _ he)]

/-- `e^{-L} P(L_j) ≤ P(L_j ∩ Cl_j)`. -/
theorem layer_blocked_lower (p : Pair d → Set.Icc (0 : ℝ) 1) {B : Box d} {j w : ℕ} {L : ℝ}
    {o : Vertex d} (ho : ¬(B.expand j).Contains o)
    (hp1 : ∀ x z, s(x, z) ∈ G.edges → ¬(B.expand j).Contains x → (B.expand j).Contains z →
      (p s(x, z) : ℝ) < 1) :
    Real.exp (-L) * (ProductCylinder.law p).real (G.LayerEvent p B j w L o) ≤
      (ProductCylinder.law p).real (G.LayerEvent p B j w L o ∩ {ω | G.Blocked (B.expand j) ω o}) := by
  let J := G.outsideBits (B.expand j)
  let ξ (a : J → Bool) := ProductCylinder.extend J a
  let P (a : J → Bool) := ξ a ∈ G.LayerEvent p B j w L o
  let A (a : J → Bool) := allValue (G.crossing (B.expand j) (ξ a) o) false
  have h := select_probability_lower p J P A (fun a => measurableSet_allValue _ _)
    (b := Real.exp (-L)) ?_
  · have hext (ω : Config d) : ∀ e ∈ J, ξ (J.restrict ω) e = ω e := by
      intro e he
      simp [ξ, ProductCylinder.extend, he, Finset.restrict]
    have h1 (ω : Config d) : P (J.restrict ω) ↔ ω ∈ G.LayerEvent p B j w L o :=
      layerEvent_congr p (hext ω)
    have h2 (ω : Config d) : ω ∈ A (J.restrict ω) ↔ G.Blocked (B.expand j) ω o := by
      show (∀ e ∈ G.crossing (B.expand j) (ξ (J.restrict ω)) o, ω e = false) ↔ _
      rw [crossing_congr (hext ω) o]
      rfl
    have heP : {ω | P (J.restrict ω)} = G.LayerEvent p B j w L o :=
      Set.ext fun ω => h1 ω
    have heA : {ω | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} =
        G.LayerEvent p B j w L o ∩ {ω | G.Blocked (B.expand j) ω o} :=
      Set.ext fun ω => and_congr (h1 ω) (h2 ω)
    rwa [heP, heA] at h
  · intro a ha
    rw [blocked_probability p ho (ξ a) hp1]
    exact Real.exp_le_exp.mpr (neg_le_neg ha.1.le)

/-- A blocked later layer keeps the cluster away from an earlier shell. -/
theorem layer_blocked_disjoint {B : Box d} {j j' w : ℕ} (hjj : j + w ≤ j')
    (p : Pair d → Set.Icc (0 : ℝ) 1) (L : ℝ) {o : Vertex d} (ho : ¬(B.expand j').Contains o)
    (hov : o ∈ G.vertices) (ω : Config d) (h₁ : ω ∈ G.LayerEvent p B j w L o)
    (h₂ : G.Blocked (B.expand j') ω o) : False := by
  obtain ⟨x, hx, hxs⟩ := h₁.2
  have hx' := blocked_conn h₂ ho hov (outCluster_conn hx)
  exact outCluster_not_contains ho hx' (B.expand_mono hjj hxs)

/-- Step 1: some layer `j ∈ [m, R)` has `P(L_j) ≤ e^L w / (R - m)`. -/
theorem exists_quiet_layer (p : Pair d → Set.Icc (0 : ℝ) 1) (B : Box d) {o : Vertex d}
    (hov : o ∈ G.vertices) {m w R : ℕ} (hw : 0 < w) (hmR : m < R)
    (hoR : ¬(B.expand R).Contains o) (L : ℝ)
    (hp1 : ∀ j, j < R → ∀ x z, s(x, z) ∈ G.edges → ¬(B.expand j).Contains x →
      (B.expand j).Contains z → (p s(x, z) : ℝ) < 1) :
    ∃ j, m ≤ j ∧ j < R ∧
      (ProductCylinder.law p).real (G.LayerEvent p B j w L o) ≤ Real.exp L * w / (R - m) := by
  set N := (R - m - 1) / w + 1 with hN
  have hNpos : 0 < N := Nat.succ_pos _
  have hlayer (k : Fin N) : m + k.1 * w < R := by
    have hk : k.1 ≤ (R - m - 1) / w := Nat.lt_succ_iff.mp k.2
    have := Nat.mul_le_mul_right w hk
    have := Nat.div_mul_le_self (R - m - 1) w
    omega
  have hNw : R - m ≤ N * w := by
    have h := Nat.lt_div_mul_add (a := R - m - 1) hw
    have he : N * w = (R - m - 1) / w * w + w := by rw [hN]; ring
    omega
  have hoj (k : Fin N) : ¬(B.expand (m + k.1 * w)).Contains o :=
    fun h => hoR (B.expand_mono (hlayer k).le h)
  have : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  let Q (k : Fin N) := G.LayerEvent p B (m + k.1 * w) w L o
  let A (k : Fin N) := Q k ∩ {ω | G.Blocked (B.expand (m + k.1 * w)) ω o}
  have hAd : Pairwise (fun k k' : Fin N => Disjoint (A k) (A k')) := by
    intro k k' hkk
    apply Set.disjoint_left.mpr
    intro ω h h'
    rcases lt_or_gt_of_ne (fun h => hkk (Fin.ext h) : k.1 ≠ k'.1) with hlt | hlt
    · have hjj : m + k.1 * w + w ≤ m + k'.1 * w := by
        have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hlt)
        rw [Nat.succ_mul] at this
        omega
      exact layer_blocked_disjoint hjj p L (hoj k') hov ω h.1 h'.2
    · have hjj : m + k'.1 * w + w ≤ m + k.1 * w := by
        have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hlt)
        rw [Nat.succ_mul] at this
        omega
      exact layer_blocked_disjoint hjj p L (hoj k) hov ω h'.1 h.2
  obtain ⟨k, hk⟩ := ShellEstimates.exists_layer (ProductCylinder.law p) Q A
    (fun k => measurableSet_layer_blocked p B _ w L o) hAd (Real.exp_pos (-L))
    (fun k => layer_blocked_lower p (hoj k) (hp1 _ (hlayer k)))
  refine ⟨m + k.1 * w, Nat.le_add_right _ _, hlayer k, hk.trans ?_⟩
  rw [Fintype.card_fin]
  have hRm : (0 : ℝ) < R - m := by
    have : (m : ℝ) < R := by exact_mod_cast hmR
    linarith
  have hNw' : ((R : ℝ) - m) ≤ N * w := by
    have : ((R - m : ℕ) : ℝ) ≤ ((N * w : ℕ) : ℝ) := by exact_mod_cast hNw
    push_cast [Nat.cast_sub hmR.le] at this
    exact this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hlhs : 1 / (Real.exp (-L) * N) = Real.exp L / N := by
    rw [Real.exp_neg]; field_simp
  rw [hlhs, div_le_div_iff₀ hN0 hRm]
  have := mul_le_mul_of_nonneg_left hNw' (Real.exp_pos L).le
  nlinarith

/-! ### Light clusters that miss the shell -/

theorem rtg_out {C : Box d} {ω : Config d} {o a : Vertex d} (ho : ¬C.Contains o)
    (h : Relation.ReflTransGen (fun x y => y ∈ {v | ¬C.Contains v} ∧ G.Adj ω x y) o a) :
    Relation.ReflTransGen (G.OutAdj C ω) o a ∧ ¬C.Contains a := by
  induction h with
  | refl => exact ⟨.refl, ho⟩
  | tail _ hab ih => exact ⟨ih.1.tail ⟨hab.2, ih.2, hab.1⟩, hab.1⟩

theorem expand_of_cube {B : Box d} {j w : ℕ} {z a : Vertex d} (hz : (B.expand j).Contains z)
    (ha : a ∈ cube z w) : (B.expand (j + w)).Contains a := by
  intro i
  have h1 := hz i
  have h2 := (mem_cube.mp ha) i
  change B.lower i - j ≤ z i ∧ z i ≤ B.upper i + j at h1
  change B.lower i - ((j + w : ℕ) : ℤ) ≤ a i ∧ a i ≤ B.upper i + ((j + w : ℕ) : ℤ)
  push_cast
  omega

/-- Display (4.1): a light cluster reaching `B` either meets the shell or enters by a long edge. -/
theorem meets_low_weight_subset (p : Pair d → Set.Icc (0 : ℝ) 1) (B : Box d) {o : Vertex d}
    {j w R : ℕ} (hjR : j < R) (hoR : ¬(B.expand R).Contains o) (L : ℝ) :
    {ω | G.Meets ω o {x | B.Contains x} ∧ G.weight p (B.expand j) ω o < L} ⊆
      G.LayerEvent p B j w L o ∪ G.LongEntry B R w := by
  rintro ω ⟨⟨y, hy, hc⟩, hW⟩
  by_cases hs : G.Shell B j w ω o
  · exact Or.inl ⟨hW, hs⟩
  · right
    have ho : ¬(B.expand j).Contains o := fun h => hoR (B.expand_mono hjR.le h)
    rcases first_exit (D := {v | ¬(B.expand j).Contains v}) hc with hin | ⟨a, z, hpa, haz, hz⟩
    · exact absurd (B.contains_expand j hy) (rtg_out ho hin).2
    · obtain ⟨hpa', ha⟩ := rtg_out ho hpa
      simp only [Set.mem_ofPred_eq, not_not] at hz
      have hac : a ∈ G.outCluster (B.expand j) ω o := mem_outCluster.mpr ⟨(adj_mem haz).1, hpa'⟩
      have hfar : a ∉ cube z w := fun h => hs ⟨a, hac, expand_of_cube hz h⟩
      refine ⟨z, (Box.mem_vertices _ _).mpr (B.expand_mono hjR.le hz), a, hfar, ?_, ?_⟩
      · rw [Sym2.eq_swap]; exact haz.1
      · rw [Sym2.eq_swap]; exact haz.2.2

/-- The long-entry bound `P(E_long) ≤ |B^{(R)}| q⁺ T(w)`. -/
theorem longEntry_le (K : Kernel d) (p : Pair d → Set.Icc (0 : ℝ) 1) (q : ℝ) (B : Box d)
    (R w : ℕ)
    (hp : ∀ z x, (B.expand R).Contains z → x ≠ z → s(z, x) ∈ G.edges →
      (p s(z, x) : ℝ) ≤ K.edgeProb q s(z, x)) :
    (ProductCylinder.law p).real (G.LongEntry B R w) ≤
      (B.expand R).vertices.card * (max q 0 * K.tail w) := by
  apply ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (le_max_right _ _) (K.tail_nonneg w)))
  apply K.tail_union_le p q _ w (fun e => e ∈ G.edges)
  intro z hz x hx he
  have hxz : x ≠ z := by
    rintro rfl
    apply hx
    rw [mem_cube]
    intro i
    omega
  exact hp z x ((Box.mem_vertices _ _).mp hz) hxz he

end FinGraph

end Peapods.LongRange
