import Peapods.LongRange.RelayThick
import Peapods.LongRange.Supercritical

/-!
# Frames: transporting the relay to neighbouring coarse cubes

Signed symmetries permute thick faces (`thickFace_map`) and carry boxes to boxes (`framedBox`),
compatibly with expansion and cardinality. For `d ≥ 2`, the coarse cube `Q_v` is `Λ_{10r}(c_v)` with
`c_v = (20r+1)(v₁, v₂, 0, …, 0)`, and for each of the four planar directions a frame carries the
canonical prism onto `Q_v ∪ Q_{v+e}`, `0` onto `c_v` and `(20r+1)e₁` onto `c_{v+e}`. Ported from
OpenAI's `Coarse.frame` and `Box.framedRect`.
-/

namespace Peapods.LongRange

open Classical OAI

variable {d : ℕ}

/-! ### Faces under signed symmetries -/

/-- `±t` according to the sign `b`. -/
def sgn (b : Bool) (t : ℤ) : ℤ := if b then t else -t

theorem sgn_sgn (a b : Bool) (t : ℤ) : sgn (a == b) (sgn b t) = sgn a t := by
  cases a <;> cases b <;> simp [sgn]

theorem mem_thickFace_sgn {c x : Vertex d} {ℓ w : ℕ} {f : FaceIndex d} :
    x ∈ ThickFace c ℓ w f ↔
      ((ℓ : ℤ) < sgn (f.2 f.1) (x f.1 - c f.1) ∧ sgn (f.2 f.1) (x f.1 - c f.1) ≤ ℓ + w) ∧
      ∀ i, i ≠ f.1 → 0 ≤ sgn (f.2 i) (x i - c i) ∧ sgn (f.2 i) (x i - c i) ≤ ℓ + w := by
  simp only [ThickFace, Set.mem_ofPred_eq, sgn]
  apply and_congr
  · cases f.2 f.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  · refine forall₂_congr (fun i _ => ?_)
    cases f.2 i <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

namespace SignedSymmetry

/-- The face index carried by `S`. -/
def faceMap (S : SignedSymmetry d) (f : FaceIndex d) : FaceIndex d :=
  (S.perm.symm f.1, fun j => f.2 (S.perm j) == S.signs j)

theorem vertex_sub_apply (S : SignedSymmetry d) (x c : Vertex d) (j : Fin d) :
    S.vertex x j - S.vertex c j = sgn (S.signs j) (x (S.perm j) - c (S.perm j)) := by
  have h := congrFun (S.vertex_sub x c) j
  simp only [Pi.sub_apply, linear] at h
  rw [h, sgn]

theorem thickFace_map (S : SignedSymmetry d) (c x : Vertex d) (ℓ w : ℕ) (f : FaceIndex d) :
    S.vertex x ∈ ThickFace (S.vertex c) ℓ w (S.faceMap f) ↔ x ∈ ThickFace c ℓ w f := by
  rw [mem_thickFace_sgn, mem_thickFace_sgn]
  have hc (j : Fin d) : sgn (f.2 (S.perm j) == S.signs j) (S.vertex x j - S.vertex c j) =
      sgn (f.2 (S.perm j)) (x (S.perm j) - c (S.perm j)) := by
    rw [vertex_sub_apply]
    exact sgn_sgn _ _ _
  simp only [faceMap]
  simp only [hc]
  simp only [Equiv.apply_symm_apply]
  apply and_congr_right
  intro _
  constructor
  · intro h i hi
    have := h (S.perm.symm i) (fun he => hi (S.perm.symm.injective he))
    simpa using this
  · intro h j hj
    exact h (S.perm j) (fun he => hj (by rw [← he, Equiv.symm_apply_apply]))

end SignedSymmetry

/-! ### Framed boxes -/

/-- The image of a box under a signed symmetry. -/
def framedBox (S : SignedSymmetry d) (B : Box d) : Box d where
  lower i := S.shift i + if S.signs i then B.lower (S.perm i) else -B.upper (S.perm i)
  upper i := S.shift i + if S.signs i then B.upper (S.perm i) else -B.lower (S.perm i)
  ordered i := by
    have h : B.lower (S.perm i) ≤ B.upper (S.perm i) := B.ordered (S.perm i)
    dsimp
    split_ifs <;> omega

theorem contains_framedBox (S : SignedSymmetry d) (B : Box d) (x : Vertex d) :
    (framedBox S B).Contains (S.vertex x) ↔ B.Contains x := by
  have hcoord (i : Fin d) : ((framedBox S B).lower i ≤ S.vertex x i ∧
      S.vertex x i ≤ (framedBox S B).upper i) ↔
      (B.lower (S.perm i) ≤ x (S.perm i) ∧ x (S.perm i) ≤ B.upper (S.perm i)) := by
    simp only [framedBox, SignedSymmetry.vertex_apply]
    cases S.signs i <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  simp only [Box.Contains, hcoord]
  constructor
  · intro h k; simpa using h (S.perm.symm k)
  · intro h i; exact h _

theorem contains_framedBox' (S : SignedSymmetry d) (B : Box d) (y : Vertex d) :
    (framedBox S B).Contains y ↔ B.Contains (S.vertex.symm y) := by
  rw [← contains_framedBox S B, Equiv.apply_symm_apply]

theorem framedBox_expand (S : SignedSymmetry d) (B : Box d) (R : ℕ) :
    (framedBox S B).expand R = framedBox S (B.expand R) := by
  apply Box.ext <;> funext i <;> simp only [framedBox, Box.expand] <;>
    split_ifs <;> ring

theorem card_vertices (B : Box d) :
    B.vertices.card = ∏ i, (B.upper i + 1 - B.lower i).toNat := by
  simp only [Box.vertices, Pi.card_Icc, Int.card_Icc]

theorem card_framedBox (S : SignedSymmetry d) (B : Box d) :
    (framedBox S B).vertices.card = B.vertices.card := by
  rw [card_vertices, card_vertices]
  have h (i : Fin d) : ((framedBox S B).upper i + 1 - (framedBox S B).lower i).toNat =
      (B.upper (S.perm i) + 1 - B.lower (S.perm i)).toNat := by
    simp only [framedBox]
    split_ifs <;> congr 1 <;> ring
  simp_rw [h]
  exact Equiv.prod_comp S.perm (fun k => (B.upper k + 1 - B.lower k).toNat)

theorem image_cube (S : SignedSymmetry d) (c : Vertex d) (n : ℕ) (y : Vertex d) :
    y ∈ cube (S.vertex c) n ↔ S.vertex.symm y ∈ cube c n := by
  rw [← S.cube_map c, Equiv.apply_symm_apply]

/-- The canonical prism has at most `(41r + 1)^d` points. -/
theorem card_prism [NeZero d] {r : ℕ} (hr : 1 ≤ r) :
    (RelayThick.prism (d := d) r).vertices.card ≤ (41 * r + 1) ^ d := by
  rw [card_vertices]
  calc ∏ i, ((RelayThick.prism (d := d) r).upper i + 1 - (RelayThick.prism (d := d) r).lower i).toNat
      ≤ ∏ _i : Fin d, (41 * r + 1) := by
        apply Finset.prod_le_prod (fun i _ => ?_)
        simp only [RelayThick.prism]
        split_ifs <;> omega
    _ = (41 * r + 1) ^ d := by simp

/-! ### The coarse lattice -/

/-- The coarse centre `c_v = (20r + 1)(v₁, v₂, 0, …, 0)`. -/
def center (r : ℕ) (v : PlanarBoundary.Point) : Vertex d :=
  fun i => (20 * (r : ℤ) + 1) * planarEmbed v i

/-- The coarse cube `Q_v = Λ_{10r}(c_v)`. -/
def Qcube (r : ℕ) (v : PlanarBoundary.Point) : Set (Vertex d) := cube (center r v) (10 * r)

/-- The relay target `B_v = Λ_{4r}(c_v)`. -/
def Bcube (r : ℕ) (v : PlanarBoundary.Point) : Set (Vertex d) := cube (center r v) (4 * r)

@[simp] theorem center_zero (r : ℕ) : center (d := d) r (0, 0) = 0 := by
  funext i; simp [center, planarEmbed]

theorem Bcube_subset_Qcube (r : ℕ) (v : PlanarBoundary.Point) :
    Bcube (d := d) r v ⊆ Qcube r v := cube_mono _ (by omega)

/-- Coarse cubes are disjoint. -/
theorem Qcube_unique (hd : 2 ≤ d) (r : ℕ) {v w : PlanarBoundary.Point} {x : Vertex d}
    (hv : x ∈ Qcube r v) (hw : x ∈ Qcube r w) : v = w := by
  have hg (a b t : ℤ) (h0 : (20 * (r : ℤ) + 1) * a - (10 * r : ℕ) ≤ t)
      (h1 : t ≤ (20 * (r : ℤ) + 1) * a + (10 * r : ℕ))
      (h2 : (20 * (r : ℤ) + 1) * b - (10 * r : ℕ) ≤ t)
      (h3 : t ≤ (20 * (r : ℤ) + 1) * b + (10 * r : ℕ)) : a = b := by
    push_cast at h0 h1 h2 h3
    have hr : (0 : ℤ) ≤ r := Int.natCast_nonneg _
    by_contra h
    rcases lt_or_gt_of_ne h with hh | hh
    · have : a + 1 ≤ b := by omega
      nlinarith
    · have : b + 1 ≤ a := by omega
      nlinarith
  have hv0 := (mem_cube.mp hv) ⟨0, by omega⟩
  have hw0 := (mem_cube.mp hw) ⟨0, by omega⟩
  have hv1 := (mem_cube.mp hv) ⟨1, by omega⟩
  have hw1 := (mem_cube.mp hw) ⟨1, by omega⟩
  simp only [center, planarEmbed, ite_true, show (1 : ℕ) ≠ 0 by omega, ite_false] at hv0 hw0 hv1 hw1
  exact Prod.ext (hg _ _ _ hv0.1 hv0.2 hw0.1 hw0.2) (hg _ _ _ hv1.1 hv1.2 hw1.1 hw1.2)

section Frames

variable (hd : 2 ≤ d)
include hd

/-- The coordinate `i₁ = 1`. -/
def i1 : Fin d := ⟨1, by omega⟩

/-- The frame carrying the canonical relay onto the pair `(v, v + outward dir)`. -/
def frame (r : ℕ) (v : PlanarBoundary.Point) (dir : PlanarBoundary.Direction) :
    SignedSymmetry d where
  perm := if dir = 0 ∨ dir = 2 then Equiv.swap ⟨0, by omega⟩ (i1 hd) else Equiv.refl _
  signs := fun i => if dir = 0 then decide (i ≠ i1 hd) else
    if dir = 3 then decide (i.val ≠ 0) else true
  shift := center r v

theorem frame_zero (r : ℕ) (v : PlanarBoundary.Point) (dir : PlanarBoundary.Direction) :
    (frame hd r v dir).vertex 0 = center r v := by
  funext i
  simp [frame, SignedSymmetry.vertex_apply]

omit hd in
theorem planarEmbed_add (a b : PlanarBoundary.Point) (i : Fin d) :
    planarEmbed (d := d) (a + b) i = planarEmbed a i + planarEmbed b i := by
  simp only [planarEmbed, Prod.fst_add, Prod.snd_add]
  split_ifs <;> ring

theorem frame_axis [NeZero d] (r : ℕ) (v : PlanarBoundary.Point)
    (dir : PlanarBoundary.Direction) :
    (frame hd r v dir).vertex (RelayThick.axis (20 * (r : ℤ) + 1)) =
      center r (v + PlanarBoundary.outward dir) := by
  set A : ℤ := 20 * (r : ℤ) + 1
  have h0 : (⟨0, by omega⟩ : Fin d) = 0 := Fin.ext rfl
  have h01 : (0 : Fin d) ≠ i1 hd := fun h => by
    have := congrArg Fin.val h
    simp [i1] at this
  funext i
  rw [SignedSymmetry.vertex_apply]
  have hcen : center r (v + PlanarBoundary.outward dir) i =
      center r v i + A * planarEmbed (PlanarBoundary.outward dir) i := by
    rw [center, center, planarEmbed_add]; ring
  rw [hcen]
  change center r v i + _ = _
  congr 1
  obtain ⟨k, hk⟩ := i
  rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk2
  · rw [h0]
    have hpe : ∀ o : PlanarBoundary.Point, planarEmbed (d := d) o 0 = o.1 := fun o => by
      simp [planarEmbed]
    rw [hpe]
    fin_cases dir <;> simp [frame, h0, h01, h01.symm, RelayThick.axis, PlanarBoundary.outward, A]
  · have hi : (⟨1, hk⟩ : Fin d) = i1 hd := rfl
    rw [hi]
    have hpe : ∀ o : PlanarBoundary.Point, planarEmbed (d := d) o (i1 hd) = o.2 := fun o => by
      simp [planarEmbed, i1]
    rw [hpe]
    fin_cases dir <;> simp [frame, h0, h01.symm, RelayThick.axis, PlanarBoundary.outward, A]
  · set i : Fin d := ⟨k, hk⟩
    have hi0 : i ≠ 0 := fun h => by
      have := congrArg Fin.val h
      simp [i] at this; omega
    have hi1 : i ≠ i1 hd := fun h => by
      have := congrArg Fin.val h
      simp [i, i1] at this; omega
    have hpe : ∀ o : PlanarBoundary.Point, planarEmbed (d := d) o i = 0 := fun o => by
      simp only [planarEmbed, i]; split_ifs <;> first | rfl | omega
    rw [hpe, mul_zero]
    have hsw : Equiv.swap (0 : Fin d) (i1 hd) i = i := Equiv.swap_apply_of_ne_of_ne hi0 hi1
    fin_cases dir <;> simp [frame, h0, hsw, hi0, hi1, RelayThick.axis]

omit hd in
/-- The canonical prism is `Q_0 ∪ Q_{e₁}`. -/
theorem prism_eq_cubes [NeZero d] (r : ℕ) (x : Vertex d) :
    (RelayThick.prism r).Contains x ↔
      x ∈ cube 0 (10 * r) ∨ x ∈ cube (RelayThick.axis (20 * (r : ℤ) + 1)) (10 * r) := by
  rw [RelayThick.contains_prism, mem_cube_iff_abs, mem_cube_iff_abs]
  simp only [Pi.zero_apply, sub_zero, RelayThick.axis]
  constructor
  · rintro ⟨h0, h⟩
    by_cases hx : x 0 ≤ 10 * r
    · left
      intro i
      by_cases hi : i = 0
      · subst hi; rw [abs_le]; push_cast; omega
      · have := h i hi; push_cast; exact this
    · right
      intro i
      by_cases hi : i = 0
      · subst hi; simp only [ite_true]; rw [abs_le]; push_cast; omega
      · simp only [hi, ite_false, sub_zero]; have := h i hi; push_cast; exact this
  · rintro (h | h)
    · have h0 := h 0
      rw [abs_le] at h0
      push_cast at h0
      refine ⟨by omega, fun i _ => by have := h i; push_cast at this; exact this⟩
    · have h0 := h 0
      simp only [ite_true] at h0
      rw [abs_le] at h0
      push_cast at h0
      refine ⟨by omega, fun i hi => ?_⟩
      have := h i
      simp only [hi, ite_false, sub_zero] at this
      push_cast at this
      exact this

/-- The framed prism is `Q_v ∪ Q_{v+e}`. -/
theorem framedPrism_contains [NeZero d] (r : ℕ) (v : PlanarBoundary.Point)
    (dir : PlanarBoundary.Direction) (y : Vertex d) :
    (framedBox (frame hd r v dir) (RelayThick.prism r)).Contains y ↔
      y ∈ Qcube r v ∨ y ∈ Qcube r (v + PlanarBoundary.outward dir) := by
  rw [contains_framedBox', prism_eq_cubes, Qcube, Qcube, ← frame_zero hd r v dir,
    ← frame_axis hd r v dir, image_cube, image_cube]

end Frames

end Peapods.LongRange
