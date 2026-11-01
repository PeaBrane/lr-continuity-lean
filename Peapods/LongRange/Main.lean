import Peapods.LongRange.Initial

/-!
# Theorem 1.1: no percolation at `β_c` for long-range percolation on `ℤ^d`, `d ≥ 2`

Let `J` satisfy (Sym) (`Kernel.SignInvariant`), (Pos) (`0 < J e₁`) and (Tail) (`Kernel.TailSmall`,
equivalently `liminf n^d T(n) = 0` taken in `[0, ∞]`, `tailSmall_iff_liminf`). Then `θ(β_c) = 0`
(`Kernel.theta_critical`), and `0 < β_c < ∞` (`Kernel.main`). If `θ(β_c) > 0`, the scales of Lemma 3.3
at `β = β_c` give `q < β_c` with `θ(q) > 0` (`Coarse.scales_percolate`), contradicting the definition
of `β_c`.
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical OAI Filter Topology
open scoped ENNReal

variable {d : ℕ}

namespace Kernel

variable (K : Kernel d)

theorem theta_nonneg (β : ℝ) : 0 ≤ K.theta β := measureReal_nonneg

/-- Theorem 1.1. -/
theorem theta_critical (hd : 2 ≤ d) (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0))
    (hT : K.TailSmall) : K.theta K.critical = 0 := by
  have : NeZero d := ⟨by omega⟩
  by_contra h
  have hθ : 0 < K.theta K.critical := lt_of_le_of_ne (K.theta_nonneg _) (Ne.symm h)
  obtain ⟨sc⟩ := exists_scales hK hT hθ
  have hq := Coarse.scales_percolate hd sc hK hPos
  have hq0 : 0 ≤ sc.q := by
    have := K.pos_of_theta hθ
    linarith [sc.q_half]
  have := K.critical_le hq0 hq
  linarith [sc.q_lt]

theorem J_unit_one [NeZero d] (hd : 2 ≤ d) (hK : K.SignInvariant) :
    K.J (unitAt 1) = K.J (unitAt 0) := by
  have h := K.J_axis hK ⟨1, by omega⟩ (t := 1) (Or.inl rfl)
  have he : (unitAt 1 : Vertex d) = fun j => if j = ⟨1, by omega⟩ then 1 else 0 := by
    funext j
    simp only [unitAt, Fin.ext_iff]
  rw [he, h]

/-- Theorem 1.1 with Lemma 2.4: `0 < β_c`, some `β` percolates (`β_c < ∞`), and `θ(β_c) = 0`. -/
theorem main (hd : 2 ≤ d) (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0))
    (hT : K.TailSmall) :
    0 < K.critical ∧ (∃ β, 0 ≤ β ∧ 0 < K.theta β) ∧ K.theta K.critical = 0 := by
  have : NeZero d := ⟨by omega⟩
  have hsup := K.exists_supercritical hd hPos (by rw [K.J_unit_one hd hK]; exact hPos)
  exact ⟨K.critical_pos hsup (FinGraph.norm_pos_of_pos hPos), hsup, K.theta_critical hd hK hPos hT⟩

/-- (Tail) in the paper's form: `liminf_{n → ∞} n^d T(n) = 0`, the liminf taken in `[0, ∞]`. -/
theorem tailSmall_iff_liminf :
    K.TailSmall ↔ liminf (fun n : ℕ => ENNReal.ofReal ((n : ℝ) ^ d * K.tail n)) atTop = 0 := by
  constructor
  · intro hT
    apply le_antisymm _ zero_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    rw [zero_add]
    apply liminf_le_of_frequently_le'
    apply (hT ε (by exact_mod_cast hε)).mono
    intro n hn
    rw [ENNReal.ofReal_le_iff_le_toReal (by simp)]
    simp only [ENNReal.coe_toReal]
    exact hn.le
  · intro hl ε hε
    have hlt : liminf (fun n : ℕ => ENNReal.ofReal ((n : ℝ) ^ d * K.tail n)) atTop <
        ENNReal.ofReal ε := by
      rw [hl]; exact ENNReal.ofReal_pos.mpr hε
    apply (frequently_lt_of_liminf_lt (by isBoundedDefault) hlt).mono
    intro n hn
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hn

end Kernel

end Peapods.LongRange
