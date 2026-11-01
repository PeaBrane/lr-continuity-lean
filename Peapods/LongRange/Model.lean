import Peapods.LongRange.Geometry
import OAI.Probability.CriticalZ3.ProductCylinder

/-!
# Long-range Bernoulli percolation on `ℤ^d`

Every unordered pair `{x, y}` of distinct vertices is open independently with probability
`1 - exp (-β J (x - y))`. The bits are indexed by `Sym2 (Vertex d)`; diagonal pairs carry the weight
`J 0` but never join anything. The law is OpenAI's product cylinder law (`OAI.ProductCylinder.law`).
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical

variable {d : ℕ}

/-- The bits of the long-range model: unordered pairs of vertices. -/
abbrev Pair (d : ℕ) := Sym2 (Vertex d)

abbrev Config (d : ℕ) := Pair d → Bool

/-- A nonnegative, even, summable interaction kernel. -/
structure Kernel (d : ℕ) where
  J : Vertex d → ℝ
  nonneg : ∀ x, 0 ≤ J x
  even : ∀ x, J (-x) = J x
  summable : Summable J

namespace Kernel

variable (K : Kernel d)

/-- The weight `J (x - y)` of the pair `{x, y}`. -/
def pairWeight : Pair d → ℝ :=
  Sym2.lift ⟨fun x y => K.J (x - y), fun x y => by dsimp only; rw [← K.even (x - y), neg_sub]⟩

@[simp] theorem pairWeight_mk (x y : Vertex d) : K.pairWeight s(x, y) = K.J (x - y) := rfl

theorem pairWeight_nonneg (e : Pair d) : 0 ≤ K.pairWeight e := by
  induction e using Sym2.ind with
  | _ x y => exact K.nonneg _

/-- The probability `1 - exp (-β⁺ J)` that a pair is open; `β⁺ = max β 0`. -/
noncomputable def edgeProb (β : ℝ) (e : Pair d) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - Real.exp (-(max β 0 * K.pairWeight e)), by
    have h0 : 0 ≤ max β 0 * K.pairWeight e := mul_nonneg (le_max_right _ _) (K.pairWeight_nonneg e)
    have h1 : Real.exp (-(max β 0 * K.pairWeight e)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : 0 < Real.exp (-(max β 0 * K.pairWeight e)) := Real.exp_pos _
    constructor <;> linarith⟩

theorem edgeProb_mono {β β' : ℝ} (h : β ≤ β') (e : Pair d) :
    (K.edgeProb β e : ℝ) ≤ K.edgeProb β' e := by
  simp only [edgeProb]
  have hw := K.pairWeight_nonneg e
  have : max β 0 * K.pairWeight e ≤ max β' 0 * K.pairWeight e :=
    mul_le_mul_of_nonneg_right (max_le_max h le_rfl) hw
  have := Real.exp_le_exp.mpr (neg_le_neg this)
  linarith

/-- The long-range percolation law at inverse temperature `β`. -/
noncomputable def law (β : ℝ) : Measure (Config d) := OAI.ProductCylinder.law (K.edgeProb β)

instance law_probability (β : ℝ) : IsProbabilityMeasure (K.law β) := by
  unfold law; infer_instance

end Kernel

/-- `x` and `y` are distinct and joined by an open pair. -/
def Adj (ω : Config d) (x y : Vertex d) : Prop := x ≠ y ∧ ω s(x, y) = true

theorem adj_symm {ω : Config d} {x y : Vertex d} (h : Adj ω x y) : Adj ω y x :=
  ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩

/-- Connection by a finite path of open pairs. -/
def Connected (ω : Config d) (x y : Vertex d) : Prop := Relation.ReflTransGen (Adj ω) x y

theorem connected_symm {ω : Config d} {x y : Vertex d} (h : Connected ω x y) : Connected ω y x := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (adj_symm hab) ih

def cluster (ω : Config d) (x : Vertex d) : Set (Vertex d) := {y | Connected ω x y}

def InfiniteAt (x : Vertex d) : Set (Config d) := {ω | (cluster ω x).Infinite}

theorem measurableSet_adj (x y : Vertex d) : MeasurableSet {ω : Config d | Adj ω x y} :=
  (MeasurableSet.const _).inter (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)

theorem measurableSet_connected (x y : Vertex d) :
    MeasurableSet {ω : Config d | Connected ω x y} :=
  OAI.CriticalZ3.measurableSet_rtg Adj measurableSet_adj x y

theorem measurableSet_infiniteAt (x : Vertex d) : MeasurableSet (InfiniteAt (d := d) x) :=
  OAI.CriticalZ3.measurableSet_infinite_fiber (fun ω y => Connected ω x y)
    (measurableSet_connected x)

namespace Kernel

variable (K : Kernel d)

/-- The percolation probability `θ(β)` of the origin. -/
noncomputable def theta (β : ℝ) : ℝ := (K.law β).real (InfiniteAt 0)

/-- The critical inverse temperature `β_c = inf {β ≥ 0 : θ(β) > 0}`. -/
noncomputable def critical : ℝ := sInf {β : ℝ | 0 ≤ β ∧ 0 < K.theta β}

end Kernel

end Peapods.LongRange
