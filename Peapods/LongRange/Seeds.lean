import Peapods.LongRange.Model

/-!
# Infinite clusters at a percolating `β`

Lemma 2.4, last part: if `θ(β) > 0`, an infinite cluster exists almost surely (zero-one law for events
invariant under finitely many bit changes, `OAI.CriticalZ3.zero_one_of_finite_alteration`), and the
probability that the cube `Λ_m(c)` meets an infinite cluster tends to one. Ported from OpenAI's
`CriticalZ3.Basic` and `QuarterFaces`.
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical Filter Topology OAI

variable {d : ℕ}

def ExistsInfinite : Set (Config d) := {ω | ∃ x, (cluster ω x).Infinite}

theorem measurableSet_existsInfinite : MeasurableSet (ExistsInfinite (d := d)) := by
  simpa only [ExistsInfinite, InfiniteAt, Set.iUnion_ofPred] using
    (MeasurableSet.iUnion (fun x => measurableSet_infiniteAt (d := d) x))

theorem finite_mem_pair (e : Pair d) : {v | v ∈ e}.Finite := by
  induction e using Sym2.ind with
  | _ a b =>
    apply ((Set.finite_singleton b).insert a).subset
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl

theorem existsInfinite_of_finite_alteration {ω ω' : Config d}
    (J : Finset (Pair d)) (hagree : ∀ e ∉ J, ω' e = ω e) (hω : ω ∈ ExistsInfinite) :
    ω' ∈ ExistsInfinite := by
  let F : Set (Vertex d) := ⋃ e ∈ (J : Set (Pair d)), {v | v ∈ e}
  have hF : F.Finite := J.finite_toSet.biUnion (fun e _ => finite_mem_pair e)
  apply CriticalZ3.infinite_component_of_perturbation hF (r := Adj ω) (s := Adj ω') _ hω
  intro a b hab
  by_cases hj : s(a, b) ∈ J
  · exact Or.inr (Set.mem_iUnion₂.mpr ⟨s(a, b), hj, Sym2.mem_mk_right a b⟩)
  · exact Or.inl ⟨hab.1, (hagree _ hj).trans hab.2⟩

theorem existsInfinite_finite_alteration {ω ω' : Config d}
    (J : Finset (Pair d)) (hagree : ∀ e ∉ J, ω' e = ω e) :
    ω' ∈ ExistsInfinite ↔ ω ∈ ExistsInfinite :=
  ⟨existsInfinite_of_finite_alteration J (fun e he => (hagree e he).symm),
    existsInfinite_of_finite_alteration J hagree⟩

namespace Kernel

variable (K : Kernel d)

theorem existsInfinite_zero_one (β : ℝ) :
    K.law β ExistsInfinite = 0 ∨ K.law β ExistsInfinite = 1 := by
  apply CriticalZ3.zero_one_of_finite_alteration (K.law β)
    (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id))
    ExistsInfinite measurableSet_existsInfinite
  intro J ω ω' h
  exact existsInfinite_finite_alteration J h

theorem existsInfinite_one {β : ℝ} (hθ : 0 < K.theta β) : K.law β ExistsInfinite = 1 := by
  apply (K.existsInfinite_zero_one β).resolve_left
  have hpos : 0 < K.law β (InfiniteAt 0) := by
    by_contra h
    push Not at h
    have : K.law β (InfiniteAt 0) = 0 := le_antisymm h (zero_le)
    simp [theta, Measure.real, this] at hθ
  exact ne_of_gt (hpos.trans_le (measure_mono (fun _ h => ⟨0, h⟩)))

end Kernel

theorem exists_mem_cube (c x : Vertex d) : ∃ n, x ∈ cube c n := by
  let n := Finset.univ.sup (fun i : Fin d => (x i - c i).natAbs)
  refine ⟨n, mem_cube.mpr (fun i => ?_)⟩
  have hn : ((x i - c i).natAbs : ℤ) ≤ n := by
    exact_mod_cast (Finset.le_sup (f := fun i : Fin d => (x i - c i).natAbs) (Finset.mem_univ i))
  have hu := Int.le_natAbs (a := x i - c i)
  have hl := Int.le_natAbs (a := -(x i - c i))
  simp only [Int.natAbs_neg] at hl
  constructor <;> omega

/-- `Λ_n(c)` meets an infinite cluster. -/
def SeedInfinite (c : Vertex d) (n : ℕ) : Set (Config d) := {ω | ∃ x ∈ cube c n, ω ∈ InfiniteAt x}

theorem seedInfinite_mono (c : Vertex d) : Monotone (SeedInfinite c) := by
  intro m n h ω ⟨x, hx, hi⟩
  exact ⟨x, cube_mono c h hx, hi⟩

theorem measurableSet_seedInfinite (c : Vertex d) (n : ℕ) : MeasurableSet (SeedInfinite c n) := by
  simp only [SeedInfinite, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro x
  by_cases hx : x ∈ cube c n
  · simpa only [hx, Set.ofPred_true, Set.univ_inter, Set.ofPred_mem_eq] using
      measurableSet_infiniteAt (d := d) x
  · simp only [hx, Set.ofPred_false, Set.empty_inter, MeasurableSet.empty]

theorem iUnion_seedInfinite (c : Vertex d) : (⋃ n, SeedInfinite c n) = ExistsInfinite := by
  ext ω
  simp only [Set.mem_iUnion, SeedInfinite, ExistsInfinite, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, x, _, hx⟩; exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := exists_mem_cube c x
    exact ⟨n, x, hn, hx⟩

namespace Kernel

variable (K : Kernel d)

theorem seedInfinite_tendsto_one {β : ℝ} (hθ : 0 < K.theta β) (c : Vertex d) :
    Tendsto (fun n => K.law β (SeedInfinite c n)) atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := K.law β) (seedInfinite_mono c)
  simpa only [iUnion_seedInfinite, K.existsInfinite_one hθ, Function.comp_def] using h

theorem seedMiss_tendsto_zero {β : ℝ} (hθ : 0 < K.theta β) (c : Vertex d) :
    Tendsto (fun n => (K.law β).real (SeedInfinite c n)ᶜ) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal (by simp : (1 : ENNReal) ≠ ⊤)).comp
    (K.seedInfinite_tendsto_one hθ c)
  have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  simpa only [measureReal_compl (measurableSet_seedInfinite c _), probReal_univ,
    Measure.real_def, measure_univ, ENNReal.toReal_one, sub_self, Function.comp_def] using h'

/-- For every `ε > 0` and exponent `N` some seed cube misses infinite clusters with probability
less than `ε ^ N`. -/
theorem exists_seed {β : ℝ} (hθ : 0 < K.theta β) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, 0 < m ∧ (K.law β).real (SeedInfinite 0 m)ᶜ < ε ^ N := by
  have h := (K.seedMiss_tendsto_zero hθ 0).eventually (eventually_lt_nhds (pow_pos hε N))
  exact (h.and (eventually_gt_atTop 0)).exists.imp (fun _ h => h.symm)

end Kernel

end Peapods.LongRange
