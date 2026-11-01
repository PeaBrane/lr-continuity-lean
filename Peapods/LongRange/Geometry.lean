import Mathlib

/-!
# Lattice geometry of `ℤ^d`

Cubes, boxes, quarter-faces and signed coordinate symmetries of `ℤ^d`, used by the long-range
percolation proof. Ported from OpenAI's `OAI.Probability.CriticalZ3` (openai/math commit `4eaee87`,
Apache-2.0; `Basic`, `BoxGeometry`, `QuarterFaces`, `Symmetry`) with the dimension `3` replaced by `d`.
Only the configuration-free statements are ported here.
-/

namespace Peapods.LongRange

open Classical

/-- Vertices of `ℤ^d`. -/
abbrev Vertex (d : ℕ) := Fin d → ℤ

variable {d : ℕ}

/-- The closed sup-norm cube of radius `n` around `c`. -/
def cube (c : Vertex d) (n : ℕ) : Set (Vertex d) :=
  Set.Icc (fun i => c i - (n : ℤ)) (fun i => c i + (n : ℤ))

theorem mem_cube {c x : Vertex d} {n : ℕ} :
    x ∈ cube c n ↔ ∀ i, c i - (n : ℤ) ≤ x i ∧ x i ≤ c i + (n : ℤ) := by
  simp only [cube, Set.mem_Icc, Pi.le_def, forall_and]

theorem cube_finite (c : Vertex d) (n : ℕ) : (cube c n).Finite := Set.finite_Icc _ _

theorem cube_mono (c : Vertex d) : Monotone (cube c) := by
  intro m n h x hx
  rw [mem_cube] at hx ⊢
  intro i
  have hn : (m : ℤ) ≤ n := by exact_mod_cast h
  obtain ⟨h₁, h₂⟩ := hx i
  constructor <;> omega

/-- Points of the cube with at least one extreme coordinate. -/
def cubeBoundary (c : Vertex d) (n : ℕ) : Set (Vertex d) :=
  {x | x ∈ cube c n ∧ ∃ i, x i = c i - (n : ℤ) ∨ x i = c i + (n : ℤ)}

/-- A quarter-face is indexed by its normal coordinate and a sign for every coordinate. -/
abbrev FaceIndex (d : ℕ) := Fin d × (Fin d → Bool)

/-- The quarter-face of the cube of radius `n` around `c` with normal `f.1`: the normal coordinate
is extreme on the side `f.2 f.1`, and every other coordinate lies in the half given by its sign. -/
def QuarterFace (c : Vertex d) (n : ℕ) (f : FaceIndex d) : Set (Vertex d) :=
  {x | x f.1 = c f.1 + (if f.2 f.1 then (n : ℤ) else -(n : ℤ)) ∧
    ∀ i, i ≠ f.1 → if f.2 i then c i ≤ x i ∧ x i ≤ c i + (n : ℤ)
      else c i - (n : ℤ) ≤ x i ∧ x i ≤ c i}

/-- The quarter-face with normal `e₁` and all signs positive. -/
def canonicalFace [NeZero d] : FaceIndex d := (0, fun _ => true)

theorem quarterFace_subset_boundary (c : Vertex d) (n : ℕ) (f : FaceIndex d) :
    QuarterFace c n f ⊆ cubeBoundary c n := by
  intro x hx
  refine ⟨?_, f.1, ?_⟩
  · rw [mem_cube]
    intro i
    by_cases hi : i = f.1
    · subst i
      rw [hx.1]
      cases f.2 f.1 <;> simp
      omega
    · have h := hx.2 i hi
      cases hf : f.2 i <;> simp only [hf, Bool.false_eq_true, ite_false, ite_true] at h <;> omega
  · rw [hx.1]
    cases f.2 f.1 <;> simp [sub_eq_add_neg]

theorem boundary_eq_union_quarterFace (c : Vertex d) (n : ℕ) :
    cubeBoundary c n = ⋃ f : FaceIndex d, QuarterFace c n f := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, i, hi⟩
    rw [Set.mem_iUnion]
    let signs : Fin d → Bool := fun j => decide (c j ≤ x j)
    refine ⟨(i, signs), ?_, ?_⟩
    · change x i = c i + (if signs i then (n : ℤ) else -(n : ℤ))
      by_cases h : c i ≤ x i <;> simp [signs, h]
      all_goals rcases hi with hi | hi <;> omega
    · intro j _
      have hh := (mem_cube.mp hx) j
      change if signs j then c j ≤ x j ∧ x j ≤ c j + (n : ℤ)
        else c j - (n : ℤ) ≤ x j ∧ x j ≤ c j
      by_cases h : c j ≤ x j <;> simp [signs, h]
      all_goals omega
  · exact Set.iUnion_subset (quarterFace_subset_boundary c n)

/-- A signed coordinate permutation followed by a translation. -/
structure SignedSymmetry (d : ℕ) where
  perm : Equiv.Perm (Fin d)
  signs : Fin d → Bool
  shift : Vertex d

namespace SignedSymmetry

/-- The action on vertices: `x ↦ shift + (±x ∘ perm)`. -/
def vertex (S : SignedSymmetry d) : Vertex d ≃ Vertex d where
  toFun x := fun i => S.shift i + if S.signs i then x (S.perm i) else -x (S.perm i)
  invFun y := fun i => if S.signs (S.perm.symm i) then
    y (S.perm.symm i) - S.shift (S.perm.symm i)
    else -(y (S.perm.symm i) - S.shift (S.perm.symm i))
  left_inv x := by
    funext i
    simp only [Equiv.apply_symm_apply]
    cases S.signs (S.perm.symm i) <;> simp
  right_inv y := by
    funext i
    simp only [Equiv.symm_apply_apply]
    cases S.signs i <;> simp

end SignedSymmetry

/-- The symmetry carrying the canonical quarter-face around `0` onto the face `f` around `c`. -/
def faceSymmetry [NeZero d] (c : Vertex d) (f : FaceIndex d) : SignedSymmetry d :=
  ⟨Equiv.swap f.1 0, f.2, c⟩

@[simp] theorem faceSymmetry_zero [NeZero d] (c : Vertex d) (f : FaceIndex d) :
    (faceSymmetry c f).vertex 0 = c := by
  funext i
  simp [faceSymmetry, SignedSymmetry.vertex]

theorem quarterFace_preimage [NeZero d] (c : Vertex d) (n : ℕ) (f : FaceIndex d) :
    (faceSymmetry c f).vertex ⁻¹' QuarterFace c n f = QuarterFace 0 n canonicalFace := by
  ext x
  simp only [Set.mem_preimage, QuarterFace, Set.mem_ofPred_eq, canonicalFace,
    Pi.zero_apply, zero_add, ite_true]
  have hn : (faceSymmetry c f).vertex x f.1 =
      c f.1 + if f.2 f.1 then x 0 else -x 0 := by
    simp [faceSymmetry, SignedSymmetry.vertex]
  rw [hn]
  have hnormal : (c f.1 + (if f.2 f.1 then x 0 else -x 0) =
      c f.1 + (if f.2 f.1 then (n : ℤ) else -(n : ℤ))) ↔ x 0 = (n : ℤ) := by
    cases f.2 f.1 <;> simp
  rw [hnormal]
  apply and_congr_right
  intro _
  have hi (i : Fin d) :
      (if f.2 i then c i ≤ (faceSymmetry c f).vertex x i ∧
        (faceSymmetry c f).vertex x i ≤ c i + (n : ℤ)
      else c i - (n : ℤ) ≤ (faceSymmetry c f).vertex x i ∧
        (faceSymmetry c f).vertex x i ≤ c i) ↔
      (0 ≤ x (Equiv.swap f.1 0 i) ∧ x (Equiv.swap f.1 0 i) ≤ (n : ℤ)) := by
    change (if f.2 i then c i ≤ c i + (if f.2 i then x (Equiv.swap f.1 0 i)
        else -x (Equiv.swap f.1 0 i)) ∧
      c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ≤ c i + (n : ℤ)
      else c i - (n : ℤ) ≤ c i + (if f.2 i then x (Equiv.swap f.1 0 i)
        else -x (Equiv.swap f.1 0 i)) ∧
      c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ≤ c i) ↔ _
    cases f.2 i <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  simp_rw [hi]
  constructor
  · intro h i hi
    have hh := h (Equiv.swap f.1 0 i)
    simp only [Equiv.swap_apply_self] at hh
    apply hh
    intro he
    have := congrArg (Equiv.swap f.1 0) he
    simp only [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact hi this
  · intro h i hi
    apply h
    intro he
    have := congrArg (Equiv.swap f.1 0) he
    simp only [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    exact hi this

/-- A box `∏ᵢ [lower i, upper i]` in `ℤ^d`. -/
structure Box (d : ℕ) where
  lower : Vertex d
  upper : Vertex d
  ordered : lower ≤ upper

namespace Box

@[ext] theorem ext {B C : Box d} (hl : B.lower = C.lower) (hu : B.upper = C.upper) : B = C := by
  cases B; cases C; cases hl; cases hu; rfl

noncomputable def vertices (B : Box d) : Finset (Vertex d) := Finset.Icc B.lower B.upper

def Contains (B : Box d) (x : Vertex d) : Prop := ∀ i, B.lower i ≤ x i ∧ x i ≤ B.upper i

@[simp] theorem mem_vertices (B : Box d) (x : Vertex d) : x ∈ B.vertices ↔ B.Contains x := by
  simp only [vertices, Finset.mem_Icc, Pi.le_def, Contains]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- Enlarge every side by `j`. -/
def expand (B : Box d) (j : ℕ) : Box d where
  lower := fun i => B.lower i - j
  upper := fun i => B.upper i + j
  ordered := fun i => by
    have h : B.lower i ≤ B.upper i := B.ordered i
    dsimp
    omega

/-- The cube of radius `m` around `c`, as a box. -/
def cube (c : Vertex d) (m : ℕ) : Box d where
  lower := fun i => c i - m
  upper := fun i => c i + m
  ordered := fun i => by dsimp; omega

@[simp] theorem contains_cube (c x : Vertex d) (m : ℕ) :
    (cube c m).Contains x ↔ ∀ i, |x i - c i| ≤ (m : ℤ) := by
  simp only [Contains, cube, abs_le]
  constructor <;> intro h i <;> have hi := h i <;> omega

theorem contains_expand (B : Box d) (j : ℕ) {x : Vertex d} (h : B.Contains x) :
    (B.expand j).Contains x := by
  intro i
  have hi := h i
  change B.lower i - j ≤ x i ∧ x i ≤ B.upper i + j
  omega

theorem expand_mono (B : Box d) {j k : ℕ} (hjk : j ≤ k) {x : Vertex d}
    (h : (B.expand j).Contains x) : (B.expand k).Contains x := by
  intro i
  have hi := h i
  change B.lower i - j ≤ x i ∧ x i ≤ B.upper i + j at hi
  change B.lower i - k ≤ x i ∧ x i ≤ B.upper i + k
  omega

@[simp] theorem expand_expand (B : Box d) (j k : ℕ) :
    (B.expand j).expand k = B.expand (j + k) := by
  apply Box.ext <;> funext i <;> simp [expand] <;> omega

end Box

end Peapods.LongRange
