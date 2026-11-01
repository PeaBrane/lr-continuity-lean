import Peapods.LongRange.RelayQuality

/-!
# Step 3 of the extension lemma: entrances

Condition on the bits `ζ` off `C`. For `z ∈ C` let `a_z = ∑ λ` over the edges from `𝒞` into `z`, so
`W = ∑_z a_z`. A residue class `Z` of `C` modulo `4m + 3` carries at least `W / (4m+3)^d`, and the
clamped seed boxes `U(z)`, `z ∈ Z`, are disjoint. The trial at `z` is that some edge from `𝒞` into `z`
is open and `U(z)` is open; given `ζ` the trials are pairwise independent with probabilities
`c_z = ρ_z (1 - e^{-a_z})`. Chebyshev's inequality for non-identical trials
(`no_good_probability'`, a generalization of OpenAI's `TrialCounts.no_good_probability`) and
display (4.2) show that, when `W ≥ L`, the cluster of `o` reaches a good relay except with
probability `4 / (ρ₀ K) + 2γ/τ` (`heavy_failure`).
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical OAI InfiniteConditioning

variable {d : ℕ}

/-! ### Chebyshev for non-identical pairwise independent trials -/

section Counting

variable {Ω : Type} {I : Type} [MeasurableSpace Ω] [Fintype I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem count_variance_le' (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (c : I → ℝ)
    (hc : ∀ i, μ.real (A i) = c i)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ c i * c j) :
    variance (TrialCounts.count A) μ ≤ ∑ i, c i := by
  let X (i : I) : Ω → ℝ := (A i).indicator (fun _ => (1 : ℝ))
  have hX (i : I) : MemLp (X i) 2 μ := (memLp_const (1 : ℝ)).indicator (hA i)
  have hcov (i j : I) : covariance (X i) (X j) μ ≤ if i = j then c i else 0 := by
    have hprod : X i * X j = (A i ∩ A j).indicator (fun _ => (1 : ℝ)) :=
      TrialCounts.indicator_product (A i) (A j)
    rw [covariance_eq_sub (hX i) (hX j), hprod,
      TrialCounts.indicator_mean μ _ ((hA i).inter (hA j))]
    change μ.real (A i ∩ A j) -
      (∫ ω, (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ) *
      (∫ ω, (A j).indicator (fun _ => (1 : ℝ)) ω ∂μ) ≤ _
    rw [TrialCounts.indicator_mean μ _ (hA i), TrialCounts.indicator_mean μ _ (hA j), hc i, hc j]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, Set.inter_self, hc]
      nlinarith [sq_nonneg (c i)]
    · simp only [hij, ite_false]
      linarith [hpair i j hij]
  have he : TrialCounts.count A = ∑ i, X i := by ext ω; simp [TrialCounts.count, X]
  rw [he, variance_sum hX]
  calc
    _ ≤ ∑ i : I, ∑ j : I, if i = j then c i else 0 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov i j))
    _ = ∑ i, c i := by simp

/-- If no trial succeeds well, either few succeed or many succeed badly. -/
theorem no_good_probability' (A B : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hB : ∀ i, MeasurableSet (B i)) (c : I → ℝ) {γ τ : ℝ} (hcpos : 0 < ∑ i, c i) (hτ : 0 < τ)
    (hc : ∀ i, μ.real (A i) = c i)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ c i * c j)
    (hbad : ∀ i, μ.real (B i) ≤ c i * γ / τ) :
    μ.real {ω | ∀ i, ω ∈ A i → ω ∈ B i} ≤ 4 / (∑ i, c i) + 2 * γ / τ := by
  set a := ∑ i, c i
  have hm : (∫ ω, TrialCounts.count A ω ∂μ) = a := by
    rw [TrialCounts.count_mean μ A hA]
    simp only [hc, a]
  have hs := ShellEstimates.success_count_bound μ (TrialCounts.count A)
    (TrialCounts.count_memLp μ A hA) hcpos hm (count_variance_le' μ A hA c hc hpair)
  have hbmean : (∫ ω, TrialCounts.count B ω ∂μ) ≤ a * γ / τ := by
    rw [TrialCounts.count_mean μ B hB]
    calc
      _ ≤ ∑ i : I, c i * γ / τ := Finset.sum_le_sum (fun i _ => hbad i)
      _ = a * γ / τ := by simp only [a, Finset.sum_div, Finset.sum_mul]
  have hb := ShellEstimates.bad_count_bound μ (TrialCounts.count B)
    ((TrialCounts.count_memLp μ B hB).integrable (by norm_num)) (TrialCounts.count_nonneg B)
    hcpos hτ hbmean
  have hsub : {ω | ∀ i, ω ∈ A i → ω ∈ B i} ⊆
      {ω | TrialCounts.count A ω < a / 2} ∪ {ω | a / 2 ≤ TrialCounts.count B ω} := by
    intro ω hω
    by_cases hs : TrialCounts.count A ω < a / 2
    · exact Or.inl hs
    · apply Or.inr
      apply (le_of_not_gt hs).trans
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : ω ∈ A i
      · simp [Set.indicator, hi, hω i hi]
      · simp only [Set.indicator, hi, ite_false]
        split_ifs <;> norm_num
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add hs hb))

end Counting

/-- Concavity of `1 - e^{-a}`: `c_A a ≤ 1 - e^{-a}` for `0 ≤ a ≤ A`. -/
theorem one_sub_exp_ge {a A : ℝ} (ha : 0 ≤ a) (haA : a ≤ A) (hA : 0 < A) :
    (1 - Real.exp (-A)) / A * a ≤ 1 - Real.exp (-a) := by
  have h := convexOn_exp.2 (Set.mem_univ (-A)) (Set.mem_univ 0) (div_nonneg ha hA.le)
    (show 0 ≤ 1 - a / A by rw [sub_nonneg, div_le_one hA]; exact haA) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  have he : a / A * -A = -a := by field_simp
  rw [he] at h
  have : (1 - Real.exp (-A)) / A * a = a / A * (1 - Real.exp (-A)) := by ring
  rw [this]
  linarith

/-! ### Residue classes -/

/-- The residue class of `z` modulo `M`. -/
def residue (M : ℕ) (z : Vertex d) : Fin d → ℤ := fun i => z i % M

theorem residue_sep {M : ℕ} (hM : 0 < M) {z z' : Vertex d} (h : residue M z = residue M z')
    (hne : z ≠ z') : ∃ i, (M : ℤ) ≤ |z i - z' i| := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  refine ⟨i, ?_⟩
  have hmod : z i ≡ z' i [ZMOD M] := congrFun h i
  obtain ⟨k, hk⟩ := Int.ModEq.dvd hmod.symm
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hi
    linarith
  rw [hk, abs_mul, abs_of_pos (by exact_mod_cast hM : (0 : ℤ) < M)]
  have : 1 ≤ |k| := Int.one_le_abs hk0
  nlinarith

theorem residue_mem (M : ℕ) (hM : 0 < M) (z : Vertex d) :
    residue M z ∈ Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) M) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Ico]
  exact ⟨Int.emod_nonneg _ (by exact_mod_cast hM.ne'), Int.emod_lt_of_pos _ (by exact_mod_cast hM)⟩

theorem card_residues (M : ℕ) :
    (Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) M)).card = M ^ d := by
  rw [Fintype.card_piFinset]
  simp

/-- Some residue class carries at least the average. -/
theorem exists_heavy_class {M : ℕ} (hM : 0 < M) (S : Finset (Vertex d)) (a : Vertex d → ℝ) :
    ∃ κ, (∑ z ∈ S, a z) / M ^ d ≤ ∑ z ∈ S.filter (fun z => residue M z = κ), a z := by
  set P := Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) M)
  have hP : P.Nonempty := ⟨residue M 0, residue_mem M hM 0⟩
  have hsum : ∑ z ∈ S, a z = ∑ κ ∈ P, ∑ z ∈ S.filter (fun z => residue M z = κ), a z :=
    (Finset.sum_fiberwise_of_maps_to (fun z _ => residue_mem M hM z) a).symm
  have hcard : (P.card : ℝ) = (M : ℝ) ^ d := by rw [card_residues]; push_cast; ring
  have hle : ∑ _κ ∈ P, (∑ z ∈ S, a z) / M ^ d ≤
      ∑ κ ∈ P, ∑ z ∈ S.filter (fun z => residue M z = κ), a z := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard, ← hsum]
    have hM' : (0 : ℝ) < (M : ℝ) ^ d := by positivity
    rw [mul_div_cancel₀ _ hM'.ne']
  obtain ⟨κ, _, hκ⟩ := Finset.exists_le_of_sum_le hP hle
  exact ⟨κ, hκ⟩

/-! ### Entrances into `C` -/

namespace FinGraph

variable {G : FinGraph d}

variable (G) in
/-- The crossing pairs into a fixed `z ∈ C`. -/
noncomputable def entryPairs (C : Box d) (ω : Config d) (o z : Vertex d) :
    Finset (Vertex d × Vertex d) :=
  (G.crossPairs C ω o).filter (fun xz => xz.2 = z)

variable (G) in
noncomputable def entryEdges (C : Box d) (ω : Config d) (o z : Vertex d) : Finset (Pair d) :=
  (G.entryPairs C ω o z).image (fun xz => s(xz.1, xz.2))

variable (G) in
/-- `a_z = ∑ λ` over the edges from `𝒞` into `z`. -/
noncomputable def entryWeight (p : Pair d → Set.Icc (0 : ℝ) 1) (C : Box d) (ω : Config d)
    (o z : Vertex d) : ℝ :=
  ∑ xz ∈ G.entryPairs C ω o z, rate (p s(xz.1, xz.2))

theorem mem_entryPairs {C : Box d} {ω : Config d} {o z : Vertex d} {xz : Vertex d × Vertex d} :
    xz ∈ G.entryPairs C ω o z ↔ xz ∈ G.crossPairs C ω o ∧ xz.2 = z := by
  simp only [entryPairs, Finset.mem_filter]

theorem weight_eq_sum (p : Pair d → Set.Icc (0 : ℝ) 1) (C : Box d) (ω : Config d) (o : Vertex d) :
    G.weight p C ω o = ∑ z ∈ C.vertices, G.entryWeight p C ω o z := by
  rw [weight]
  exact (Finset.sum_fiberwise_of_maps_to (g := Prod.snd)
    (fun xz h => (Box.mem_vertices _ _).mpr (mem_crossPairs.mp h).2.1) _).symm

theorem entryWeight_nonneg (p : Pair d → Set.Icc (0 : ℝ) 1) (C : Box d) (ω : Config d)
    (o z : Vertex d) : 0 ≤ G.entryWeight p C ω o z :=
  Finset.sum_nonneg (fun _ _ => rate_nonneg _)

theorem mem_entryEdges {C : Box d} {ω : Config d} {o z : Vertex d} {e : Pair d} :
    e ∈ G.entryEdges C ω o z ↔ ∃ x, (x, z) ∈ G.crossPairs C ω o ∧ e = s(x, z) := by
  simp only [entryEdges, Finset.mem_image, mem_entryPairs, Prod.exists]
  constructor
  · rintro ⟨x, z', ⟨h, rfl⟩, rfl⟩; exact ⟨x, h, rfl⟩
  · rintro ⟨x, h, rfl⟩; exact ⟨x, z, ⟨h, rfl⟩, rfl⟩

theorem entryEdges_disjoint {C : Box d} {ω : Config d} {o : Vertex d} (ho : ¬C.Contains o)
    {z z' : Vertex d} (hzz : z ≠ z') :
    Disjoint (G.entryEdges C ω o z) (G.entryEdges C ω o z') := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨x, hx, rfl⟩ := mem_entryEdges.mp he
  obtain ⟨x', hx', he⟩ := mem_entryEdges.mp he'
  have hxC := outCluster_not_contains ho (mem_crossPairs.mp hx).1
  have hz'C := (mem_crossPairs.mp hx').2.1
  rcases Sym2.eq_iff.mp he with ⟨_, h⟩ | ⟨h, _⟩
  · exact hzz h
  · exact hxC (h ▸ hz'C)

theorem entryEdges_not_inside {C : Box d} {ω : Config d} {o z : Vertex d} (ho : ¬C.Contains o)
    {e : Pair d} (he : e ∈ G.entryEdges C ω o z) : ∃ x ∈ e, ¬C.Contains x := by
  obtain ⟨x, hx, rfl⟩ := mem_entryEdges.mp he
  exact ⟨x, Sym2.mem_mk_left x z, outCluster_not_contains ho (mem_crossPairs.mp hx).1⟩

theorem entryEdges_subset_crossing {C : Box d} {ω : Config d} {o z : Vertex d} :
    G.entryEdges C ω o z ⊆ G.crossing C ω o := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := mem_entryEdges.mp he
  exact mem_crossing.mpr ⟨x, z, hx, rfl⟩

theorem entryEdges_disjoint_outside (C : Box d) (ω : Config d) (o z : Vertex d) :
    Disjoint (G.outsideBits C) (G.entryEdges C ω o z) :=
  Finset.disjoint_of_subset_right entryEdges_subset_crossing (crossing_disjoint_outside C ω o)

theorem entryEdges_disjoint_inside {C : Box d} {ω : Config d} {o z : Vertex d}
    (ho : ¬C.Contains o) : Disjoint (G.insideBits C) (G.entryEdges C ω o z) :=
  Finset.disjoint_of_subset_right entryEdges_subset_crossing (crossing_disjoint_inside ho)

theorem entry_closed_probability (p : Pair d → Set.Icc (0 : ℝ) 1) {C : Box d} {o : Vertex d}
    (ho : ¬C.Contains o) (ξ : Config d) (z : Vertex d)
    (hp1 : ∀ x z, s(x, z) ∈ G.edges → ¬C.Contains x → C.Contains z → (p s(x, z) : ℝ) < 1) :
    (ProductCylinder.law (fixedParameter p (G.outsideBits C) ξ)).real
      (allValue (G.entryEdges C ξ o z) false) = Real.exp (-G.entryWeight p C ξ o z) := by
  have hinj : Set.InjOn (fun xz : Vertex d × Vertex d => s(xz.1, xz.2)) (G.entryPairs C ξ o z) :=
    (crossPairs_injOn ho).mono (fun xz h => (mem_entryPairs.mp h).1)
  rw [fixed_determined_probability p _ _ (entryEdges_disjoint_outside C ξ o z) ξ _
    (allValue_determined _ _), allValue_probability, entryEdges,
    Finset.prod_image (fun a ha b hb h => hinj ha hb h)]
  simp only [bitProbability, Bool.false_eq_true, ite_false]
  rw [entryWeight, ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  rintro ⟨x, z'⟩ h
  obtain ⟨hc, rfl⟩ := mem_entryPairs.mp h
  obtain ⟨hx, hz, he⟩ := mem_crossPairs.mp hc
  exact (exp_neg_rate (hp1 x z' he (outCluster_not_contains ho hx) hz)).symm

/-- `a_z ≤ q⁺ ‖J‖₁`. -/
theorem entryWeight_le {K : Kernel d} {p : Pair d → Set.Icc (0 : ℝ) 1} {q : ℝ} {C : Box d}
    {o : Vertex d} (ho : ¬C.Contains o) (ω : Config d) (z : Vertex d)
    (hcross : ∀ x z, s(x, z) ∈ G.edges → x ≠ z → C.Contains z →
      (p s(x, z) : ℝ) ≤ K.edgeProb q s(x, z)) :
    G.entryWeight p C ω o z ≤ max q 0 * ∑' y, K.J y := by
  have hinj : Set.InjOn (fun xz : Vertex d × Vertex d => xz.1 - z) (G.entryPairs C ω o z) := by
    rintro ⟨x, z1⟩ h ⟨x', z2⟩ h' he
    obtain ⟨_, rfl⟩ := mem_entryPairs.mp h
    obtain ⟨_, rfl⟩ := mem_entryPairs.mp h'
    simp only [sub_left_inj] at he
    rw [he]
  calc G.entryWeight p C ω o z
      ≤ ∑ xz ∈ G.entryPairs C ω o z, max q 0 * K.J (xz.1 - z) := by
        apply Finset.sum_le_sum
        rintro ⟨x, z'⟩ h
        obtain ⟨hc, rfl⟩ := mem_entryPairs.mp h
        obtain ⟨hx, hz, he⟩ := mem_crossPairs.mp hc
        have hxz : x ≠ z' := fun h' => outCluster_not_contains ho hx (h' ▸ hz)
        have := K.rate_le_of_le (hcross x z' he hxz hz)
        simpa only [Kernel.pairWeight_mk] using this
    _ = max q 0 * ∑ y ∈ (G.entryPairs C ω o z).image (fun xz => xz.1 - z), K.J y := by
        rw [Finset.sum_image (fun a ha b hb h => hinj ha hb h), Finset.mul_sum]
    _ ≤ max q 0 * ∑' y, K.J y :=
        mul_le_mul_of_nonneg_left (K.summable.sum_le_tsum _ (fun y _ => K.nonneg y))
          (le_max_right _ _)

theorem inside_disjoint_outside (C : Box d) : Disjoint (G.insideBits C) (G.outsideBits C) := by
  rw [Finset.disjoint_left]
  intro e he he'
  induction e using Sym2.ind with
  | _ a b =>
    exact (Finset.mem_filter.mp he').2 a (Sym2.mem_mk_left a b)
      ((Finset.mem_filter.mp he).2 a (Sym2.mem_mk_left a b))

theorem norm_pos_of_pos {K : Kernel d} (hPos : 0 < K.J (unitAt 0)) : 0 < ∑' y, K.J y :=
  hPos.trans_le (K.summable.le_tsum _ (fun y _ => K.nonneg y))

/-- Step 3 at a fixed pattern `ξ` of the bits off `C` with `W ≥ L`. -/
theorem fixed_heavy_failure [NeZero d] {K : Kernel d} {β : ℝ} (s : ScaleData K β)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0)) {p : Pair d → Set.Icc (0 : ℝ) 1}
    {D C : Box d} (hF : FqHolds K G p s.q D) (hDV : ∀ x, D.Contains x → x ∈ G.vertices)
    (hCD : ∀ x, C.Contains x → D.Contains x) (hw : ∀ i, C.lower i + s.m ≤ C.upper i - s.m)
    {o : Vertex d} (ho : ¬C.Contains o) (T : Set (Vertex d))
    (hE3 : ∀ u, C.Contains u → ∃ ℓ ∈ ({2 * s.r, 2 * s.r + 1, 10 * s.r - s.w} : Finset ℕ),
      ∃ f : FaceIndex d, (∀ x ∈ cube u (ℓ + s.w), D.Contains x) ∧ ThickFace u ℓ s.w f ⊆ T)
    (hcross : ∀ x z, s(x, z) ∈ G.edges → x ≠ z → C.Contains z →
      (p s(x, z) : ℝ) ≤ K.edgeProb s.q s(x, z))
    (ξ : Config d) (hW : K.extensionL β s.m s.trials ≤ G.weight p C ξ o) :
    (ProductCylinder.law (fixedParameter p (G.outsideBits C) ξ)).real
      {ω | ¬G.Meets ω o (G.goodRelays p (G.insideBits C) T s.τ ω)} ≤
      4 / (s.trials * K.seedRho β s.m) + 2 * s.γ / s.τ := by
  set J := G.outsideBits C
  set μ := ProductCylinder.law (fixedParameter p J ξ)
  set M := 4 * s.m + 3 with hMdef
  have hM : 0 < M := by omega
  have hβ : 0 < β := by linarith [s.q_half, s.q_lt]
  have hq0 : 0 < s.q := by linarith [s.q_half]
  have hτ := s.τ_range.1
  have hp1 : ∀ x z, s(x, z) ∈ G.edges → ¬C.Contains x → C.Contains z → (p s(x, z) : ℝ) < 1 :=
    fun x z he hx hz =>
      (hcross x z he (fun h => hx (h ▸ hz)) hz).trans_lt (K.edgeProb_lt_one _ _)
  set a : Vertex d → ℝ := fun z => G.entryWeight p C ξ o z
  obtain ⟨κ, hκ⟩ := exists_heavy_class hM C.vertices a
  set t := C.vertices.filter (fun z => residue M z = κ)
  have htC (z : t) : C.Contains z.1 := (Box.mem_vertices _ _).mp (Finset.mem_filter.mp z.2).1
  let v (z : Vertex d) := C.clamp s.m z
  have hvC (z : Vertex d) : ∀ x ∈ cube (v z) s.m, C.Contains x := fun x hx => cube_clamp_subset hw z hx
  have hvD (z : Vertex d) : ∀ x ∈ cube (v z) s.m, D.Contains x := fun x hx => hCD x (hvC z x hx)
  let O (z : Vertex d) := allValue (K.seedPairs (v z) s.m) true
  let Hit (z : Vertex d) : Set (Config d) := (allValue (G.entryEdges C ξ o z) false)ᶜ
  let Fz (z : Vertex d) : Set (Config d) :=
    {ω | conditionalProbability p (G.insideBits C) {ω | G.Meets ω (v z) T} ω ≤ 1 - s.τ}
  let A (z : t) : Set (Config d) := Hit z.1 ∩ O z.1
  let Bz (z : t) : Set (Config d) := A z ∩ Fz z.1
  let ρz (z : Vertex d) := (ProductCylinder.law p).real (O z)
  let c (z : t) : ℝ := (1 - Real.exp (-a z.1)) * ρz z.1
  have hseedIn (z : Vertex d) : K.seedPairs (v z) s.m ⊆ G.insideBits C :=
    seedPairs_subset_inside hF hCD (hvC z)
  have hseedJ (z : Vertex d) : Disjoint J (K.seedPairs (v z) s.m) :=
    Finset.disjoint_of_subset_right (hseedIn z) (inside_disjoint_outside C).symm
  have hentrySeed (z z' : Vertex d) :
      Disjoint (G.entryEdges C ξ o z) (K.seedPairs (v z') s.m) :=
    Finset.disjoint_of_subset_right (hseedIn z') (entryEdges_disjoint_inside ho).symm
  have hHitDet (z : Vertex d) :
      ProductCylinder.DeterminedBy (F := Prop) (G.entryEdges C ξ o z) (fun ω => ω ∈ Hit z) :=
    fun ω ω' h => propext (not_congr (eq_iff_iff.mp (allValue_determined _ _ ω ω' h)))
  have hODet (z : Vertex d) :
      ProductCylinder.DeterminedBy (F := Prop) (K.seedPairs (v z) s.m) (fun ω => ω ∈ O z) :=
    allValue_determined _ _
  have hmO (z : Vertex d) : μ.real (O z) = ρz z :=
    fixed_determined_probability p J _ (hseedJ z) ξ (O z) (hODet z)
  have hmHit (z : Vertex d) : μ.real (Hit z) = 1 - Real.exp (-a z) := by
    rw [measureReal_compl (measurableSet_allValue _ _), probReal_univ,
      entry_closed_probability p ho ξ z hp1]
  have hmA (z : t) : μ.real (A z) = c z := by
    have hind := indepSet_determined (fixedParameter p J ξ) _ _ (hentrySeed z.1 z.1)
      (Hit z.1) (O z.1) (hHitDet z.1) (hODet z.1)
    rw [Measure.real_def, hind.measure_inter_eq_mul, ENNReal.toReal_mul, ← Measure.real_def,
      ← Measure.real_def, hmHit, hmO]
  have hpair (z z' : t) (hzz : z ≠ z') : μ.real (A z ∩ A z') ≤ c z * c z' := by
    have hne : z.1 ≠ z'.1 := fun h => hzz (Subtype.ext h)
    obtain ⟨i, hi⟩ := residue_sep hM
      ((Finset.mem_filter.mp z.2).2.trans (Finset.mem_filter.mp z'.2).2.symm) hne
    have hseeds : Disjoint (K.seedPairs (v z.1) s.m) (K.seedPairs (v z'.1) s.m) := by
      rw [Finset.disjoint_left]
      intro e he he'
      induction e using Sym2.ind with
      | _ x y =>
        have hx := ((K.mk_mem_seedPairs).mp he).1
        have hx' := ((K.mk_mem_seedPairs).mp he').1
        have hi' : (4 * s.m + 3 : ℤ) ≤ |z.1 i - z'.1 i| := by
          have : ((M : ℕ) : ℤ) = 4 * s.m + 3 := by rw [hMdef]; push_cast; ring
          rw [← this]; exact hi
        exact cube_clamp_disjoint hw (htC z) (htC z') hi' hx hx'
    have hdis : Disjoint (G.entryEdges C ξ o z.1 ∪ K.seedPairs (v z.1) s.m)
        (G.entryEdges C ξ o z'.1 ∪ K.seedPairs (v z'.1) s.m) := by
      rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨entryEdges_disjoint ho hne, hentrySeed _ _⟩,
        ⟨(hentrySeed _ _).symm, hseeds⟩⟩
    have hdet (z : t) : ProductCylinder.DeterminedBy (F := Prop)
        (G.entryEdges C ξ o z.1 ∪ K.seedPairs (v z.1) s.m) (fun ω => ω ∈ A z) := by
      intro ω ω' h
      have h1 := hHitDet z.1 ω ω' (fun e he => h e (Finset.mem_union_left _ he))
      have h2 := hODet z.1 ω ω' (fun e he => h e (Finset.mem_union_right _ he))
      simp only [A, Set.mem_inter_iff] at h1 h2 ⊢
      rw [h1, h2]
    have hind := indepSet_determined (fixedParameter p J ξ) _ _ hdis (A z) (A z') (hdet z) (hdet z')
    rw [Measure.real_def, hind.measure_inter_eq_mul, ENNReal.toReal_mul, ← Measure.real_def,
      ← Measure.real_def, hmA, hmA]
  have hbad (z : t) : μ.real (Bz z) ≤ c z * s.γ / s.τ := by
    obtain ⟨ℓ, hℓ, f, hcube, hFT⟩ := hE3 (v z.1) (clamp_contains hw z.1)
    have hOF : ProductCylinder.DeterminedBy (F := Prop) (G.insideBits C)
        (fun ω => ω ∈ O z.1 ∩ Fz z.1) := by
      intro ω ω' h
      have h1 := ProductCylinder.determinedBy_mono (hseedIn z.1) (hODet z.1) ω ω' h
      have h2 := conditionalProbability_determined p (G.insideBits C)
        {ω | G.Meets ω (v z.1) T} ω ω' h
      simp only [Set.mem_inter_iff, Fz, Set.mem_ofPred_eq] at h1 ⊢
      rw [h1, h2]
    have hind := indepSet_determined (fixedParameter p J ξ) _ _
      (entryEdges_disjoint_inside ho).symm (Hit z.1) (O z.1 ∩ Fz z.1) (hHitDet z.1) hOF
    have hBz : Bz z = Hit z.1 ∩ (O z.1 ∩ Fz z.1) := Set.inter_assoc _ _ _
    have hq := relay_quality s hK hPos hF hCD (hvC z.1) T hℓ hcube hFT
    have hfix : μ.real (O z.1 ∩ Fz z.1) = (ProductCylinder.law p).real (O z.1 ∩ Fz z.1) :=
      fixed_determined_probability p J _ (inside_disjoint_outside C).symm ξ _ hOF
    rw [hBz, Measure.real_def, hind.measure_inter_eq_mul, ENNReal.toReal_mul, ← Measure.real_def,
      ← Measure.real_def, hmHit, hfix]
    have hexp : 0 ≤ 1 - Real.exp (-a z.1) := by
      have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (entryWeight_nonneg (G := G) p C ξ o z.1))
      linarith
    calc (1 - Real.exp (-a z.1)) * (ProductCylinder.law p).real (O z.1 ∩ Fz z.1)
        ≤ (1 - Real.exp (-a z.1)) * (ρz z.1 * s.γ / s.τ) := mul_le_mul_of_nonneg_left hq hexp
      _ = c z * s.γ / s.τ := by simp only [c]; ring
  -- the expected number of successes is at least `ρ₀ K`
  have hJ := norm_pos_of_pos hPos
  have hA : 0 < K.massA β := mul_pos hβ hJ
  have hcA : 0 < K.massC β := by
    have : Real.exp (-K.massA β) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact div_pos (by linarith) hA
  have hρ0 := K.seedRho_pos hβ s.m
  have hsum : (s.trials : ℝ) * K.seedRho β s.m ≤ ∑ z : t, c z := by
    have hc_ge (z : t) : K.seedRho β s.m * (K.massC β * a z.1) ≤ c z := by
      have h1 : K.seedRho β s.m ≤ ρz z.1 := by
        simp only [ρz, O]
        rw [seedOpen_probability hF (hvD z.1)]
        exact K.seedProd_ge s.q_half hβ _ _
      have hle : a z.1 ≤ K.massA β := by
        have h := entryWeight_le ho ξ z.1 hcross
        rw [max_eq_left hq0.le] at h
        exact h.trans (mul_le_mul_of_nonneg_right s.q_lt.le (tsum_nonneg K.nonneg))
      have h2 := one_sub_exp_ge (entryWeight_nonneg (G := G) p C ξ o z.1) hle hA
      have h0 : 0 ≤ K.massC β * a z.1 := mul_nonneg hcA.le (entryWeight_nonneg (G := G) p C ξ o z.1)
      calc K.seedRho β s.m * (K.massC β * a z.1)
          ≤ ρz z.1 * (1 - Real.exp (-a z.1)) := mul_le_mul h1 h2 h0 measureReal_nonneg
        _ = c z := by simp only [c]; ring
    have hW' : G.weight p C ξ o = ∑ z ∈ C.vertices, a z := weight_eq_sum p C ξ o
    have hMd : ((M : ℕ) : ℝ) ^ d = (4 * (s.m : ℝ) + 3) ^ d := by rw [hMdef]; push_cast; ring
    have hLeq : K.massC β * K.extensionL β s.m s.trials / (M : ℝ) ^ d = s.trials := by
      rw [Kernel.extensionL, hMd]
      field_simp
    calc (s.trials : ℝ) * K.seedRho β s.m
        = K.seedRho β s.m * (K.massC β * K.extensionL β s.m s.trials / (M : ℝ) ^ d) := by
          rw [hLeq]; ring
      _ ≤ K.seedRho β s.m * (K.massC β * (∑ z ∈ t, a z)) := by
          apply mul_le_mul_of_nonneg_left _ hρ0.le
          rw [mul_div_assoc]
          apply mul_le_mul_of_nonneg_left _ hcA.le
          calc K.extensionL β s.m s.trials / (M : ℝ) ^ d
              ≤ (∑ z ∈ C.vertices, a z) / (M : ℝ) ^ d := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                rw [← hW']; exact hW
            _ ≤ ∑ z ∈ t, a z := hκ
      _ = ∑ z : t, K.seedRho β s.m * (K.massC β * a z.1) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_coe_sort t]
      _ ≤ ∑ z : t, c z := Finset.sum_le_sum (fun z _ => hc_ge z)
  have hcpos : 0 < ∑ z : t, c z :=
    (mul_pos (by exact_mod_cast s.trials_pos) hρ0).trans_le hsum
  -- no good success: the cluster misses every good relay
  have hcount := no_good_probability' μ A Bz
    (fun z => (measurableSet_allValue _ _).compl.inter (measurableSet_allValue _ _))
    (fun z => ((measurableSet_allValue _ _).compl.inter (measurableSet_allValue _ _)).inter
      (measurableSet_conditional_test _ _ _ _))
    c hcpos hτ hmA hpair hbad
  have hae : {ω | ¬G.Meets ω o (G.goodRelays p (G.insideBits C) T s.τ ω)} ≤ᵐ[μ]
      {ω | ∀ z, ω ∈ A z → ω ∈ Bz z} := by
    filter_upwards [ae_fixed_determined p J ξ (fun ω => G.outCluster C ω o)
      (fun ω ω' h => outCluster_congr h o)] with ω hω
    intro hfail z hAz
    refine ⟨hAz, ?_⟩
    by_contra hnot
    have hgood : 1 - s.τ <
        conditionalProbability p (G.insideBits C) {ω | G.Meets ω (v z.1) T} ω :=
      lt_of_not_ge hnot
    obtain ⟨hHit, hO⟩ := hAz
    have hex : ∃ e ∈ G.entryEdges C ξ o z.1, ω e = true := by
      by_contra hh
      push Not at hh
      exact hHit (fun e he => Bool.eq_false_iff.mpr (hh e he))
    obtain ⟨e, he, heo⟩ := hex
    obtain ⟨x, hx, rfl⟩ := mem_entryEdges.mp he
    obtain ⟨hxc, hzC, hxe⟩ := mem_crossPairs.mp hx
    have hxc' : x ∈ G.outCluster C ω o := by rw [hω]; exact hxc
    have hxz : x ≠ z.1 := fun h => outCluster_not_contains ho hxc (h ▸ hzC)
    have hconn : G.Conn ω o (v z.1) :=
      conn_trans (conn_trans (outCluster_conn hxc') (conn_of_adj ⟨hxe, hxz, heo⟩))
        (box_conn_of_open hK hPos hF (hvD z.1) hO z.1 (mem_cube_clamp hw hzC) (v z.1)
          (by rw [mem_cube]; intro i; omega))
    exact hfail ⟨v z.1, ⟨hDV _ (hCD _ (clamp_contains hw z.1)), hgood⟩, hconn⟩
  calc μ.real {ω | ¬G.Meets ω o (G.goodRelays p (G.insideBits C) T s.τ ω)}
      ≤ μ.real {ω | ∀ z, ω ∈ A z → ω ∈ Bz z} := OAI.MeasureTheory.finite_measureReal_mono_ae hae
    _ ≤ 4 / (∑ z : t, c z) + 2 * s.γ / s.τ := hcount
    _ ≤ 4 / (s.trials * K.seedRho β s.m) + 2 * s.γ / s.τ := by
        gcongr
        exact mul_pos (by exact_mod_cast s.trials_pos) hρ0

/-- Step 3: when `W ≥ L`, the cluster of `o` reaches a good relay except with probability
`4 / (K ρ₀) + 2γ/τ`. -/
theorem heavy_failure [NeZero d] {K : Kernel d} {β : ℝ} (s : ScaleData K β)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0)) {p : Pair d → Set.Icc (0 : ℝ) 1}
    {D C : Box d} (hF : FqHolds K G p s.q D) (hDV : ∀ x, D.Contains x → x ∈ G.vertices)
    (hCD : ∀ x, C.Contains x → D.Contains x) (hw : ∀ i, C.lower i + s.m ≤ C.upper i - s.m)
    {o : Vertex d} (ho : ¬C.Contains o) (T : Set (Vertex d))
    (hE3 : ∀ u, C.Contains u → ∃ ℓ ∈ ({2 * s.r, 2 * s.r + 1, 10 * s.r - s.w} : Finset ℕ),
      ∃ f : FaceIndex d, (∀ x ∈ cube u (ℓ + s.w), D.Contains x) ∧ ThickFace u ℓ s.w f ⊆ T)
    (hcross : ∀ x z, s(x, z) ∈ G.edges → x ≠ z → C.Contains z →
      (p s(x, z) : ℝ) ≤ K.edgeProb s.q s(x, z)) :
    (ProductCylinder.law p).real
      {ω | K.extensionL β s.m s.trials ≤ G.weight p C ω o ∧
        ¬G.Meets ω o (G.goodRelays p (G.insideBits C) T s.τ ω)} ≤
      4 / (s.trials * K.seedRho β s.m) + 2 * s.γ / s.τ := by
  have hβ : 0 < β := by linarith [s.q_half, s.q_lt]
  set E : Set (Config d) := {ω | K.extensionL β s.m s.trials ≤ G.weight p C ω o ∧
    ¬G.Meets ω o (G.goodRelays p (G.insideBits C) T s.τ ω)}
  have hm : MeasurableSet E := by
    apply ProductCylinder.measurableSet_determined G.edges
    intro ω ω' h
    have hgood := goodRelays_determined (G := G) p (G.insideBits C) T s.τ ω ω'
      (fun e he => h e (insideBits_subset C he))
    simp only [E, Set.mem_ofPred_eq, weight_congr p (agree_outside h) o, hgood,
      meets_congr h]
  have hb0 : 0 ≤ 4 / (s.trials * K.seedRho β s.m) + 2 * s.γ / s.τ :=
    add_nonneg (div_nonneg (by norm_num)
      (mul_nonneg (Nat.cast_nonneg _) (K.seedRho_pos hβ _).le))
      (div_nonneg (by linarith [s.γ_range.1]) s.τ_range.1.le)
  have hr := select_probability_le p (G.outsideBits C) (fun _ => E) (fun _ => hm)
    (b := 4 / (s.trials * K.seedRho β s.m) + 2 * s.γ / s.τ) ?_
  · exact hr
  · intro a
    set ξ := ProductCylinder.extend (G.outsideBits C) a
    by_cases hL : K.extensionL β s.m s.trials ≤ G.weight p C ξ o
    · exact (measureReal_mono (fun _ h => h.2)).trans
        (fixed_heavy_failure s hK hPos hF hDV hCD hw ho T hE3 hcross ξ hL)
    · have hz : ProductCylinder.law (fixedParameter p (G.outsideBits C) ξ) E = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [ae_fixed_determined p (G.outsideBits C) ξ (fun ω => G.weight p C ω o)
          (fun ω ω' h => weight_congr p h o)] with ω hω
        intro h
        exact hL (hω ▸ h.1)
      simp only [Measure.real_def, hz, ENNReal.toReal_zero]
      exact hb0

end FinGraph

end Peapods.LongRange
