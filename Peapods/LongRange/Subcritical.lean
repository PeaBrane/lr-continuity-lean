import Peapods.LongRange.Model
import OAI.Probability.CriticalZ3.Conditioning

/-!
# No percolation at small `β` (`β_c > 0`)

The expected size of the cluster of the origin is at most `∑ₙ (β ‖J‖₁)ⁿ`: every vertex of the cluster is
the endpoint of an open self-avoiding vertex sequence from `0`, whose pairs are distinct bits, so the
sequence is open with probability at most `∏ β J (step)`; summing over sequences gives a geometric
series. Hence `θ(β) = 0` when `β ‖J‖₁ < 1`.
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical OAI
open scoped ENNReal

variable {d : ℕ}

/-- The open graph of a configuration. -/
def openGraph (ω : Config d) : SimpleGraph (Vertex d) where
  Adj := Adj ω
  symm := ⟨fun _ _ h => adj_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Every connection is witnessed by an injective vertex sequence of open pairs. -/
theorem exists_selfAvoiding {ω : Config d} {x y : Vertex d} (h : Connected ω x y) :
    ∃ n, ∃ γ : Fin (n + 1) → Vertex d, γ 0 = x ∧ γ (Fin.last n) = y ∧ Function.Injective γ ∧
      ∀ i : Fin n, Adj ω (γ i.castSucc) (γ i.succ) := by
  have hr : (openGraph ω).Reachable x y :=
    (SimpleGraph.reachable_iff_reflTransGen (G := openGraph ω) x y).mpr h
  obtain ⟨p⟩ := hr
  obtain ⟨q, hq⟩ := p.toPath
  have hlen : q.support.length = q.length + 1 := q.length_support
  have hget (i : Fin (q.length + 1)) :
      q.getVert i.val = q.support.get ⟨i.val, by rw [hlen]; exact i.is_lt⟩ := by
    have := congrFun q.getVert_comp_val_eq_get_support ⟨i.val, by rw [hlen]; exact i.is_lt⟩
    simp only [Function.comp_apply] at this
    exact this
  refine ⟨q.length, fun i => q.getVert i.val, q.getVert_zero, ?_, ?_, ?_⟩
  · show q.getVert (Fin.last q.length).val = y
    rw [Fin.val_last]
    exact q.getVert_length
  · intro i j hij
    have hij' : q.getVert i.val = q.getVert j.val := hij
    rw [hget, hget] at hij'
    have hinj := List.nodup_iff_injective_get.mp hq.support_nodup hij'
    exact Fin.ext (by simpa using congrArg Fin.val hinj)
  · intro i
    exact q.adj_getVert_succ i.is_lt

/-- Sum over vertex sequences of length `n` from `x` of the product of `f` over the steps. -/
noncomputable def walkSum (f : Vertex d → ℝ≥0∞) (n : ℕ) (x : Vertex d) : ℝ≥0∞ :=
  ∑' γ : Fin (n + 1) → Vertex d,
    if γ 0 = x then ∏ i : Fin n, f (γ i.succ - γ i.castSucc) else 0

theorem tsum_translate (f : Vertex d → ℝ≥0∞) (x : Vertex d) :
    ∑' b : Vertex d, f (b - x) = ∑' z, f z :=
  (Equiv.subRight x).tsum_eq f

theorem tsum_ite_eq_left {α : Type*} [DecidableEq α] (a : α) (F : α → ℝ≥0∞) :
    ∑' b : α, (if a = b then F b else 0) = F a := by
  rw [tsum_eq_single a (fun b hb => by simp only [Ne.symm hb, ite_false])]
  simp

theorem walkSum_eq (f : Vertex d → ℝ≥0∞) : ∀ n x, walkSum f n x = (∑' z, f z) ^ n := by
  intro n
  induction n with
  | zero =>
    intro x
    simp only [walkSum, Finset.univ_eq_empty, Finset.prod_empty, pow_zero]
    rw [← (Equiv.funUnique (Fin 1) (Vertex d)).symm.tsum_eq]
    simp [Equiv.funUnique]
  | succ n ih =>
    intro x
    unfold walkSum
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => Vertex d)).tsum_eq, ENNReal.tsum_prod']
    have hstep (a : Vertex d) (τ : Fin (n + 1) → Vertex d) :
        (if (Fin.consEquiv (fun _ : Fin (n + 2) => Vertex d) (a, τ)) 0 = x then
          ∏ i : Fin (n + 1), f ((Fin.consEquiv (fun _ : Fin (n + 2) => Vertex d) (a, τ)) i.succ -
            (Fin.consEquiv (fun _ : Fin (n + 2) => Vertex d) (a, τ)) i.castSucc) else 0) =
        if a = x then f (τ 0 - x) * ∏ i : Fin n, f (τ i.succ - τ i.castSucc) else 0 := by
      simp only [Fin.consEquiv_apply, Fin.cons_zero]
      split_ifs with ha
      · subst ha
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_succ, Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc]
      · rfl
    simp_rw [hstep]
    have hcol (a : Vertex d) : (∑' τ : Fin (n + 1) → Vertex d,
        if a = x then f (τ 0 - x) * ∏ i : Fin n, f (τ i.succ - τ i.castSucc) else 0) =
        if a = x then ∑' τ : Fin (n + 1) → Vertex d,
          f (τ 0 - x) * ∏ i : Fin n, f (τ i.succ - τ i.castSucc) else 0 := by
      split_ifs <;> simp
    simp_rw [hcol, tsum_ite_eq]
    calc ∑' τ : Fin (n + 1) → Vertex d, f (τ 0 - x) * ∏ i : Fin n, f (τ i.succ - τ i.castSucc)
        = ∑' b : Vertex d, ∑' τ : Fin (n + 1) → Vertex d,
            if τ 0 = b then f (b - x) * ∏ i : Fin n, f (τ i.succ - τ i.castSucc) else 0 := by
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun τ => ?_)
          exact (tsum_ite_eq_left (τ 0)
            (fun b => f (b - x) * ∏ i : Fin n, f (τ i.succ - τ i.castSucc))).symm
      _ = ∑' b : Vertex d, f (b - x) * walkSum f n b := by
          refine tsum_congr (fun b => ?_)
          unfold walkSum
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun τ => ?_)
          split_ifs <;> simp
      _ = (∑' z, f z) ^ (n + 1) := by
          simp_rw [ih, ENNReal.tsum_mul_right, tsum_translate, pow_succ']

/-- The pairs `{γ i, γ (i + 1)}` of an injective sequence are distinct bits. -/
theorem steps_injective {n : ℕ} {γ : Fin (n + 1) → Vertex d} (hγ : Function.Injective γ) :
    Function.Injective (fun i : Fin n => (s(γ i.castSucc, γ i.succ) : Pair d)) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact Fin.castSucc_injective _ (hγ h1)
  · have a := congrArg Fin.val (hγ h1)
    have b := congrArg Fin.val (hγ h2)
    simp only [Fin.val_castSucc, Fin.val_succ] at a b
    omega

/-- Sequences from `0` that are injective and open. -/
def GoodSeq (ω : Config d) (σ : Σ n : ℕ, Fin (n + 1) → Vertex d) : Prop :=
  σ.2 0 = 0 ∧ Function.Injective σ.2 ∧ ∀ i : Fin σ.1, Adj ω (σ.2 i.castSucc) (σ.2 i.succ)

theorem measurableSet_goodSeq (σ : Σ n : ℕ, Fin (n + 1) → Vertex d) :
    MeasurableSet {ω : Config d | GoodSeq ω σ} := by
  simp only [GoodSeq, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (MeasurableSet.iInter fun i => measurableSet_adj _ _))

/-- The number of vertices of the cluster of the origin. -/
noncomputable def clusterSize (ω : Config d) : ℝ≥0∞ := ∑' y : Vertex d, (cluster ω 0).indicator 1 y

theorem measurable_clusterSize : Measurable (clusterSize (d := d)) := by
  unfold clusterSize
  refine Measurable.tsum (fun y => ?_)
  have : (fun ω : Config d => (cluster ω 0).indicator (1 : Vertex d → ℝ≥0∞) y) =
      {ω : Config d | Connected ω 0 y}.indicator 1 := by
    funext ω
    by_cases h : Connected ω 0 y <;> simp [Set.indicator, cluster, h]
  rw [this]
  exact measurable_const.indicator (measurableSet_connected 0 y)

theorem clusterSize_eq_top {ω : Config d} (h : ω ∈ InfiniteAt 0) : clusterSize ω = ⊤ := by
  unfold clusterSize
  rw [← tsum_subtype (cluster ω 0) 1]
  simp only [Pi.one_apply]
  rw [ENNReal.tsum_set_one, Set.encard_eq_top h]
  rfl

/-- Each vertex of the cluster is the endpoint of a good sequence. -/
theorem clusterSize_le (ω : Config d) :
    clusterSize ω ≤ ∑' σ : (Σ n : ℕ, Fin (n + 1) → Vertex d), {σ | GoodSeq ω σ}.indicator 1 σ := by
  unfold clusterSize
  rw [← tsum_subtype (cluster ω 0) 1]
  have hex (y : cluster ω 0) := exists_selfAvoiding (ω := ω) (x := 0) (y := y.1) y.2
  choose n γ h0 hend hinj hopen using hex
  let G : cluster ω 0 → Σ n : ℕ, Fin (n + 1) → Vertex d := fun y => ⟨n y, γ y⟩
  have hG : Function.Injective G := by
    intro y y' h
    have : (G y).2 (Fin.last (G y).1) = (G y').2 (Fin.last (G y').1) := by rw [h]
    exact Subtype.ext (by simpa [G, hend] using this)
  have hgood (y : cluster ω 0) : {σ | GoodSeq ω σ}.indicator (1 : (Σ n : ℕ, Fin (n + 1) → Vertex d) → ℝ≥0∞) (G y) = 1 := by
    rw [Set.indicator_of_mem (show G y ∈ {σ | GoodSeq ω σ} from ⟨h0 y, hinj y, hopen y⟩)]
    rfl
  calc ∑' y : cluster ω 0, (1 : Vertex d → ℝ≥0∞) y
      = ∑' y : cluster ω 0, {σ | GoodSeq ω σ}.indicator 1 (G y) := by
        simp only [hgood, Pi.one_apply]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hG _

namespace Kernel

variable (K : Kernel d)

/-- The step weight `β⁺ J (z)` as an extended nonnegative real. -/
noncomputable def stepWeight (β : ℝ) (z : Vertex d) : ℝ≥0∞ := ENNReal.ofReal (max β 0 * K.J z)

theorem edgeProb_le (β : ℝ) (x y : Vertex d) :
    (K.edgeProb β s(x, y) : ℝ) ≤ max β 0 * K.J (y - x) := by
  simp only [edgeProb, pairWeight_mk]
  rw [← K.even (x - y), neg_sub]
  have := Real.add_one_le_exp (-(max β 0 * K.J (y - x)))
  linarith

/-- An injective open sequence has probability at most `∏ β⁺ J (step)`. -/
theorem openSeq_le (β : ℝ) {n : ℕ} (γ : Fin (n + 1) → Vertex d) (hγ : Function.Injective γ) :
    K.law β {ω | ∀ i : Fin n, Adj ω (γ i.castSucc) (γ i.succ)} ≤
      ∏ i : Fin n, K.stepWeight β (γ i.succ - γ i.castSucc) := by
  let steps : Finset (Pair d) := Finset.univ.image (fun i : Fin n => s(γ i.castSucc, γ i.succ))
  have hsub : {ω : Config d | ∀ i : Fin n, Adj ω (γ i.castSucc) (γ i.succ)} ⊆
      InfiniteConditioning.allValue steps true := by
    intro ω hω e he
    simp only [steps, Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨i, rfl⟩ := he
    exact (hω i).2
  have hall : K.law β (InfiniteConditioning.allValue steps true) =
      ENNReal.ofReal (∏ i : Fin n, (K.edgeProb β s(γ i.castSucc, γ i.succ) : ℝ)) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    congr 1
    have h := InfiniteConditioning.allValue_probability (K.edgeProb β) steps true
    simp only [InfiniteConditioning.bitProbability, ite_true] at h
    change (ProductCylinder.law (K.edgeProb β)).real _ = _
    rw [h]
    exact Finset.prod_image (fun i _ j _ hij => steps_injective hγ hij)
  calc K.law β _ ≤ K.law β (InfiniteConditioning.allValue steps true) := measure_mono hsub
    _ = ENNReal.ofReal (∏ i : Fin n, (K.edgeProb β s(γ i.castSucc, γ i.succ) : ℝ)) := hall
    _ ≤ ENNReal.ofReal (∏ i : Fin n, max β 0 * K.J (γ i.succ - γ i.castSucc)) := by
        apply ENNReal.ofReal_le_ofReal
        exact Finset.prod_le_prod₀ (fun i _ => (K.edgeProb β _).2.1) (fun i _ => K.edgeProb_le β _ _)
    _ = ∏ i : Fin n, K.stepWeight β (γ i.succ - γ i.castSucc) := by
        rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (le_max_right _ _) (K.nonneg _))]
        rfl

theorem goodSeq_le (β : ℝ) (σ : Σ n : ℕ, Fin (n + 1) → Vertex d) :
    K.law β {ω | GoodSeq ω σ} ≤
      if σ.2 0 = 0 then ∏ i : Fin σ.1, K.stepWeight β (σ.2 i.succ - σ.2 i.castSucc) else 0 := by
  by_cases h : σ.2 0 = 0 ∧ Function.Injective σ.2
  · simp only [h.1, ite_true]
    exact (measure_mono (fun ω hω => hω.2.2)).trans (K.openSeq_le β σ.2 h.2)
  · have : {ω : Config d | GoodSeq ω σ} = ∅ := by
      ext ω; simp only [GoodSeq, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h' => h ⟨h'.1, h'.2.1⟩
    rw [this, measure_empty]
    exact zero_le

/-- The expected cluster size is at most a geometric series in `∑ β⁺ J`. -/
theorem lintegral_clusterSize_le (β : ℝ) :
    ∫⁻ ω, clusterSize ω ∂(K.law β) ≤ ∑' n : ℕ, (∑' z, K.stepWeight β z) ^ n := by
  calc ∫⁻ ω, clusterSize ω ∂(K.law β)
      ≤ ∫⁻ ω, ∑' σ : (Σ n : ℕ, Fin (n + 1) → Vertex d), {σ | GoodSeq ω σ}.indicator 1 σ ∂(K.law β) :=
        lintegral_mono clusterSize_le
    _ = ∑' σ : (Σ n : ℕ, Fin (n + 1) → Vertex d), K.law β {ω | GoodSeq ω σ} := by
        rw [lintegral_tsum (fun σ => ?_)]
        · refine tsum_congr (fun σ => ?_)
          rw [← lintegral_indicator_one (measurableSet_goodSeq σ)]
          rfl
        · have : (fun ω : Config d => {σ | GoodSeq ω σ}.indicator (1 : (Σ n : ℕ, Fin (n + 1) → Vertex d) → ℝ≥0∞) σ) =
              {ω : Config d | GoodSeq ω σ}.indicator 1 := by
            funext ω
            by_cases h : GoodSeq ω σ <;> simp [Set.indicator, h]
          rw [this]
          exact (measurable_const.indicator (measurableSet_goodSeq σ)).aemeasurable
    _ ≤ ∑' σ : (Σ n : ℕ, Fin (n + 1) → Vertex d),
          if σ.2 0 = 0 then ∏ i : Fin σ.1, K.stepWeight β (σ.2 i.succ - σ.2 i.castSucc) else 0 :=
        ENNReal.tsum_le_tsum (fun σ => K.goodSeq_le β σ)
    _ = ∑' n : ℕ, walkSum (K.stepWeight β) n 0 := by
        rw [ENNReal.tsum_sigma']
        rfl
    _ = ∑' n : ℕ, (∑' z, K.stepWeight β z) ^ n := by
        simp_rw [walkSum_eq]

theorem tsum_stepWeight (β : ℝ) :
    ∑' z, K.stepWeight β z = ENNReal.ofReal (max β 0 * ∑' z, K.J z) := by
  unfold stepWeight
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (le_max_right _ _) (K.nonneg z))
    (K.summable.mul_left _), tsum_mul_left]

/-- Lemma 2.4, second half: no percolation when `β⁺ ‖J‖₁ < 1`. -/
theorem theta_eq_zero {β : ℝ} (h : max β 0 * ∑' z, K.J z < 1) : K.theta β = 0 := by
  have hr : ∑' z, K.stepWeight β z < 1 := by
    rw [K.tsum_stepWeight]
    exact (ENNReal.ofReal_lt_one).mpr h
  have hfin : ∫⁻ ω, clusterSize ω ∂(K.law β) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (K.lintegral_clusterSize_le β)
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hr).ne'
  have hzero := measure_eq_top_of_lintegral_ne_top measurable_clusterSize.aemeasurable hfin
  have hsub : InfiniteAt (d := d) 0 ⊆ {ω | clusterSize ω = ⊤} := fun ω h => clusterSize_eq_top h
  have : K.law β (InfiniteAt 0) = 0 := measure_mono_null hsub hzero
  simp [theta, Measure.real, this]

/-- Consequently `β_c ≥ 1 / ‖J‖₁ > 0` as soon as some `β` percolates. -/
theorem critical_pos (hne : ∃ β, 0 ≤ β ∧ 0 < K.theta β) (hJ : 0 < ∑' z, K.J z) :
    0 < K.critical := by
  have hlow : ∀ β ∈ {β : ℝ | 0 ≤ β ∧ 0 < K.theta β}, 1 / ∑' z, K.J z ≤ β := by
    rintro β ⟨hβ, hθ⟩
    by_contra hlt
    push Not at hlt
    have : max β 0 * ∑' z, K.J z < 1 := by
      rw [max_eq_left hβ]
      calc β * ∑' z, K.J z < 1 / (∑' z, K.J z) * ∑' z, K.J z :=
            mul_lt_mul_of_pos_right hlt hJ
        _ = 1 := by field_simp
    exact (ne_of_gt hθ) (K.theta_eq_zero this)
  exact lt_of_lt_of_le (by positivity) (le_csInf hne hlow)

end Kernel

end Peapods.LongRange
