import Peapods.LongRange.Model
import OAI.Probability.CriticalZ3.Subunit

/-!
# The long-range model percolates at large `β` (`β_c < ∞`)

The nearest-neighbour pairs of the plane spanned by the first two coordinates contain a planar
block percolation; OpenAI's Peierls survival bound (`OAI.BlockPercolation.survival`), extended here to
non-identical bit probabilities, shows that it has an infinite cluster with positive probability once
every planar pair is closed with probability at most `contourError / 2`.
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical OAI OAI.BlockPercolation OAI.PlanarBoundary

section Survival

variable {E : Type}

/-- `OAI.BlockPercolation.survival` for a product law with non-identical bit probabilities. -/
theorem survival_of_le (p : E → Set.Icc (0 : ℝ) 1) (J : Point → Finset E)
    (hJ : Pairwise (fun u v => Disjoint (J u) (J v))) (hcard : ∀ v, (J v).card ≤ 2)
    (hp : ∀ v, ∀ e ∈ J v, 2 * (1 - (p e : ℝ)) ≤ CriticalScales.contourError)
    (A : Set (E → Bool)) (hA : ∀ ω, (BlockPercolation.cluster J ω).Infinite → ω ∈ A) :
    0 < ProductCylinder.law p A := by
  let μ := ProductCylinder.law p
  have hε := CriticalScales.contourError_pos
  have hb (v : Point) : μ.real (Bad J v) ≤ CriticalScales.contourError := by
    have he : Bad J v = ⋃ e : J v, {ω | ω e.1 = false} := by
      ext ω
      simp only [Bad, active, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        push Not at h
        obtain ⟨e, he, hω⟩ := h
        exact ⟨⟨e, he⟩, Bool.eq_false_iff.mpr hω⟩
      · rintro ⟨e, he⟩ h
        have := h e.1 e.2
        simp_all
    rw [he]
    apply (measureReal_iUnion_fintype_le _).trans
    simp only [μ, InfiniteConditioning.single_probability, InfiniteConditioning.bitProbability,
      Bool.false_eq_true, ite_false]
    calc ∑ e : J v, (1 - (p e.1 : ℝ)) ≤ ∑ _e : J v, CriticalScales.contourError / 2 :=
          Finset.sum_le_sum (fun e _ => by have := hp v e.1 e.2; linarith)
      _ = (J v).card * (CriticalScales.contourError / 2) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (CriticalScales.contourError / 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard v) (by linarith)
      _ = CriticalScales.contourError := by ring
  have hbad (s : Finset Point) : μ.real {ω | ∀ v ∈ s, ω ∈ Bad J v} ≤
      CriticalScales.contourError ^ s.card := by
    rw [InfiniteConditioning.disjoint_blocks_probability p J hJ (Bad J) (bad_determined J) s]
    calc
      _ ≤ ∏ _v ∈ s, CriticalScales.contourError :=
        Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg) (fun v _ => hb v)
      _ = _ := by simp
  have hf := PlanarBoundary.finite_good_bound μ (BlockPercolation.cluster J) (Bad J)
    (fun ω _ x hx d hy => outside_bad J ω x hx d hy) hbad
  have hroot : 1 - CriticalScales.contourError ≤ μ.real {ω | active J ω (0, 0)} := by
    have he : {ω | active J ω (0, 0)} = (Bad J (0, 0))ᶜ := by ext ω; simp [Bad]
    rw [he, measureReal_compl (measurableSet_bad J (0, 0)), probReal_univ]
    linarith [hb (0, 0)]
  have hcover : {ω | active J ω (0, 0)} ⊆
      {ω | (BlockPercolation.cluster J ω).Finite ∧ (0, 0) ∈ BlockPercolation.cluster J ω} ∪ A := by
    intro ω hω
    by_cases hfinite : (BlockPercolation.cluster J ω).Finite
    · exact Or.inl ⟨hfinite, (root_mem_iff J ω).mpr hω⟩
    · exact Or.inr (hA ω hfinite)
  have hle := (measureReal_mono (μ := μ) hcover).trans (measureReal_union_le _ _)
  have hpos : 0 < μ.real A := by
    have hh := CriticalScales.contourError_lt_half
    linarith
  exact ENNReal.toReal_pos_iff.mp hpos |>.1

end Survival

variable {d : ℕ}

/-- The unit vector in coordinate `k` (the zero vector if `k ≥ d`). -/
def unitAt (k : ℕ) : Vertex d := fun i => if i.val = k then 1 else 0

/-- The plane spanned by the first two coordinates. -/
def planarEmbed (v : Point) : Vertex d := fun i => if i.val = 0 then v.1 else if i.val = 1 then v.2 else 0

@[simp] theorem planarEmbed_zero : planarEmbed (d := d) (0, 0) = 0 := by
  funext i; simp [planarEmbed]

theorem planarEmbed_injective (hd : 2 ≤ d) : Function.Injective (planarEmbed (d := d)) := by
  intro u v h
  have h0 := congrFun h ⟨0, by omega⟩
  have h1 := congrFun h ⟨1, by omega⟩
  simp [planarEmbed] at h0 h1
  exact Prod.ext h0 h1

/-- The two nearest-neighbour pairs from `v` in the positive planar directions. -/
noncomputable def planarBlock (v : Point) : Finset (Pair d) :=
  {s(planarEmbed v, planarEmbed v + unitAt 0), s(planarEmbed v, planarEmbed v + unitAt 1)}

theorem planarBlock_card (v : Point) : (planarBlock (d := d) v).card ≤ 2 := by
  unfold planarBlock
  exact (Finset.card_insert_le _ _).trans (by simp)

theorem planarEmbed_add_unit (v : Point) :
    planarEmbed (d := d) (v + (1, 0)) = planarEmbed v + unitAt 0 ∧
      planarEmbed (d := d) (v + (0, 1)) = planarEmbed v + unitAt 1 := by
  constructor <;> funext i <;> simp only [planarEmbed, unitAt, Prod.fst_add, Prod.snd_add,
    Pi.add_apply] <;> split_ifs <;> omega

theorem planarBlock_disjoint (hd : 2 ≤ d) :
    Pairwise (fun u v => Disjoint (planarBlock (d := d) u) (planarBlock (d := d) v)) := by
  intro u v huv
  rw [Finset.disjoint_left]
  have hne : planarEmbed (d := d) u ≠ planarEmbed v := fun h => huv (planarEmbed_injective hd h)
  have hsum (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) : unitAt (d := d) a + unitAt b ≠ 0 := by
    intro h
    have := congrFun h ⟨a, by omega⟩
    simp only [unitAt, Pi.add_apply, Pi.zero_apply, ite_true] at this
    split_ifs at this <;> omega
  have key (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1)
      (h : s(planarEmbed (d := d) u, planarEmbed u + unitAt a) =
        s(planarEmbed v, planarEmbed v + unitAt b)) : False := by
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact hne h1
    · apply hsum a b ha hb
      have h3 : planarEmbed (d := d) v + (unitAt a + unitAt b) = planarEmbed v + 0 := by
        calc planarEmbed (d := d) v + (unitAt a + unitAt b)
            = (planarEmbed v + unitAt b) + unitAt a := by abel
          _ = planarEmbed v + 0 := by rw [← h1, h2, add_zero]
      exact add_left_cancel h3
  intro e he he'
  simp only [planarBlock, Finset.mem_insert, Finset.mem_singleton] at he he'
  rcases he with rfl | rfl <;> rcases he' with h | h
  · exact key 0 0 (by omega) (by omega) h
  · exact key 0 1 (by omega) (by omega) h
  · exact key 1 0 (by omega) (by omega) h
  · exact key 1 1 (by omega) (by omega) h

theorem unitAt_ne_zero (hd : 2 ≤ d) {k : ℕ} (hk : k ≤ 1) : unitAt (d := d) k ≠ 0 := by
  intro h
  have := congrFun h ⟨k, by omega⟩
  simp [unitAt] at this

/-- An open planar block edge is an open long-range pair. -/
theorem planar_adj (hd : 2 ≤ d) {ω : Config d} {u v : Point}
    (h : BlockPercolation.Adj (planarBlock (d := d)) ω u v) :
    Adj ω (planarEmbed u) (planarEmbed v) := by
  obtain ⟨⟨dir, rfl⟩, hu, hv⟩ := h
  have hu0 := hu _ (Finset.mem_insert_self _ _)
  have hu1 := hu _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hv0 := hv _ (Finset.mem_insert_self _ _)
  have hv1 := hv _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have h10 := (planarEmbed_add_unit (d := d) u).1
  have h01 := (planarEmbed_add_unit (d := d) u).2
  have hm10 := (planarEmbed_add_unit (d := d) (u + outward dir)).1
  have hm01 := (planarEmbed_add_unit (d := d) (u + outward dir)).2
  have hz0 := unitAt_ne_zero (d := d) hd (k := 0) (by omega)
  have hz1 := unitAt_ne_zero (d := d) hd (k := 1) (by omega)
  fin_cases dir <;> simp only [outward, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.reduceFinMk] at hv0 hv1 hm10 hm01 ⊢
  · -- down: `u + (0,-1) + (0,1) = u`
    have hback : u + (0, -1) + (0, 1) = u := by ext <;> simp
    rw [hback] at hm01
    refine ⟨fun h => hz1 ?_, ?_⟩
    · have := congrArg (fun x => x - planarEmbed (d := d) (u + (0, -1))) hm01
      simp only [add_sub_cancel_left] at this
      rw [← this, h, sub_self]
    · rw [Sym2.eq_swap, hm01]; exact hv1
  · refine ⟨fun h => hz0 ?_, ?_⟩
    · have := congrArg (fun x => x - planarEmbed (d := d) u) h10
      simp only [add_sub_cancel_left] at this
      rw [← this, h, sub_self]
    · rw [h10]; exact hu0
  · refine ⟨fun h => hz1 ?_, ?_⟩
    · have := congrArg (fun x => x - planarEmbed (d := d) u) h01
      simp only [add_sub_cancel_left] at this
      rw [← this, h, sub_self]
    · rw [h01]; exact hu1
  · have hback : u + (-1, 0) + (1, 0) = u := by ext <;> simp
    rw [hback] at hm10
    refine ⟨fun h => hz0 ?_, ?_⟩
    · have := congrArg (fun x => x - planarEmbed (d := d) (u + (-1, 0))) hm10
      simp only [add_sub_cancel_left] at this
      rw [← this, h, sub_self]
    · rw [Sym2.eq_swap, hm10]; exact hv0

/-- An infinite planar block cluster gives an infinite long-range cluster of the origin. -/
theorem planar_infinite (hd : 2 ≤ d) {ω : Config d}
    (h : (BlockPercolation.cluster (planarBlock (d := d)) ω).Infinite) : ω ∈ InfiniteAt 0 := by
  have hsub : planarEmbed (d := d) '' BlockPercolation.cluster (planarBlock (d := d)) ω ⊆
      cluster ω 0 := by
    rintro _ ⟨v, ⟨_, hv⟩, rfl⟩
    change Connected ω 0 (planarEmbed v)
    rw [← planarEmbed_zero]
    induction hv with
    | refl => exact .refl
    | tail _ hab ih => exact ih.tail (planar_adj hd hab)
  exact (h.image (planarEmbed_injective hd).injOn).mono hsub

namespace Kernel

variable (K : Kernel d)

theorem pairWeight_planarBlock {v : Point} {e : Pair d} (he : e ∈ planarBlock v) :
    K.pairWeight e = K.J (unitAt 0) ∨ K.pairWeight e = K.J (unitAt 1) := by
  simp only [planarBlock, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · left; simp [← K.even (unitAt 0)]
  · right; simp [← K.even (unitAt 1)]

/-- Lemma 2.4, first half: if `J` charges both planar unit vectors, some `β ≥ 0` percolates. -/
theorem exists_supercritical (hd : 2 ≤ d) (h0 : 0 < K.J (unitAt 0)) (h1 : 0 < K.J (unitAt 1)) :
    ∃ β, 0 ≤ β ∧ 0 < K.theta β := by
  set ε := CriticalScales.contourError
  have hε0 : 0 < ε := CriticalScales.contourError_pos
  have hε1 : ε < 1 / 2 := CriticalScales.contourError_lt_half
  set m := min (K.J (unitAt 0)) (K.J (unitAt 1))
  have hm : 0 < m := lt_min h0 h1
  have hlog : 0 < Real.log (2 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε0]; linarith)
  refine ⟨Real.log (2 / ε) / m, (div_pos hlog hm).le, ?_⟩
  set β := Real.log (2 / ε) / m
  have hβ0 : 0 ≤ β := (div_pos hlog hm).le
  have hp : ∀ v, ∀ e ∈ planarBlock (d := d) v, 2 * (1 - (K.edgeProb β e : ℝ)) ≤ ε := by
    intro v e he
    have hw : m ≤ K.pairWeight e := by
      rcases K.pairWeight_planarBlock he with h | h <;> rw [h]
      · exact min_le_left _ _
      · exact min_le_right _ _
    have hβw : Real.log (2 / ε) ≤ β * K.pairWeight e := by
      calc Real.log (2 / ε) = β * m := by simp only [β]; rw [div_mul_cancel₀ _ hm.ne']
        _ ≤ β * K.pairWeight e := mul_le_mul_of_nonneg_left hw hβ0
    have hexp : Real.exp (-(max β 0 * K.pairWeight e)) ≤ ε / 2 := by
      rw [max_eq_left hβ0]
      calc Real.exp (-(β * K.pairWeight e)) ≤ Real.exp (-Real.log (2 / ε)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = ε / 2 := by
            rw [Real.exp_neg, Real.exp_log (by positivity)]
            field_simp
    simp only [edgeProb]
    linarith
  have hpos := survival_of_le (K.edgeProb β) (planarBlock (d := d)) (planarBlock_disjoint hd)
    planarBlock_card hp (InfiniteAt 0) (fun ω h => planar_infinite hd h)
  have hfin : (K.law β) (InfiniteAt 0) ≠ ⊤ := measure_ne_top _ _
  exact ENNReal.toReal_pos (ne_of_gt hpos) hfin

/-- Consequently `β_c` is finite: it is at most any percolating `β`. -/
theorem critical_le {β : ℝ} (hβ : 0 ≤ β) (h : 0 < K.theta β) : K.critical ≤ β :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hβ, h⟩

end Kernel

end Peapods.LongRange
