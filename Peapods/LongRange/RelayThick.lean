import Peapods.LongRange.Faces

/-!
# The relay route with thick faces

The geometry of Lemma 5.1 in the canonical frame `c_v = 0`, `c_x = (20r + 1) e₁`, with `R' = R + w`.
The rectangles are `P_t` (`t ≤ d`), centred at `0` with half-width `2r + tR'` in the directions
`h < t` and `4r + tR'` in the others, and `P_{d+i} = Λ_{w_i}(a_i e₁)` (`1 ≤ i ≤ 10`) with
`w_i = 2r + (d+i)R'`, `a_i = 2ri` for `i ≤ 9` and `a_10 = 20r + 1`. Every point `u` of `P_k^{(R)}`
has an outer thick quarter-face of radius `2r` (or `2r + 1` for the last step) inside `P_{k+1}`, and
`Λ_{ℓ+w}(u)` lies in the prism `[-10r, 30r+1] × [-10r, 10r]^{d-1}` (`route_thick_interface`).
Adapted from OpenAI's `LatticeRelay`, where the faces have no thickness and the widths grow by `R`.
-/

namespace Peapods.LongRange.RelayThick

open Classical

variable {d : ℕ}

/-- The box `∏ [c i - w i, c i + w i]`. -/
def rect (c w : Vertex d) (hw : ∀ i, 0 ≤ w i) : Box d :=
  ⟨fun i => c i - w i, fun i => c i + w i, fun i => by have := hw i; dsimp; omega⟩

theorem contains_rect {c w : Vertex d} {hw : ∀ i, 0 ≤ w i} {x : Vertex d} :
    (rect c w hw).Contains x ↔ ∀ i, |x i - c i| ≤ w i := by
  simp only [Box.Contains, rect, abs_le]
  exact forall_congr' (fun i => by constructor <;> intro h <;> constructor <;> omega)

/-- The canonical prism `[-10r, 30r+1] × [-10r, 10r]^{d-1}`. -/
def prism [NeZero d] (r : ℕ) : Box d :=
  ⟨fun _ => -10 * (r : ℤ), fun i => if i = 0 then 30 * (r : ℤ) + 1 else 10 * r, fun i => by
    dsimp; split_ifs <;> omega⟩

theorem contains_prism [NeZero d] {r : ℕ} {x : Vertex d} :
    (prism r).Contains x ↔
      (-10 * (r : ℤ) ≤ x 0 ∧ x 0 ≤ 30 * r + 1) ∧ ∀ i, i ≠ 0 → |x i| ≤ 10 * r := by
  simp only [Box.Contains, prism]
  constructor
  · intro h
    refine ⟨by simpa using h 0, fun i hi => ?_⟩
    have := h i
    simp only [hi, ite_false] at this
    rw [abs_le]; omega
  · rintro ⟨h0, h⟩ i
    by_cases hi : i = 0
    · subst hi; simpa using h0
    · have := h i hi
      simp only [hi, ite_false]
      rw [abs_le] at this; omega

/-- `e₁`-axis point `a e₁`. -/
def axis [NeZero d] (a : ℤ) : Vertex d := fun i => if i = 0 then a else 0

section Route

variable (r R w : ℕ)

/-- Half-widths of the contraction rectangle `P_t`. -/
def cWidth (t : ℕ) : Vertex d :=
  fun h => if h.val < t then 2 * (r : ℤ) + t * (R + w) else 4 * (r : ℤ) + t * (R + w)

theorem cWidth_nonneg (t : ℕ) (h : Fin d) : 0 ≤ cWidth (d := d) r R w t h := by
  unfold cWidth; split_ifs <;> positivity

/-- Centres `a_i` of the translation rectangles. -/
def tCenter (i : ℕ) : ℤ := if i ≤ 9 then 2 * (r : ℤ) * i else 20 * r + 1

/-- Half-width `w_i = 2r + (d+i)R'` of the translation rectangle `P_{d+i}`. -/
def tWidth (i : ℕ) : ℤ := 2 * (r : ℤ) + ((d : ℤ) + i) * (R + w)

/-- The route rectangles `P_0, …, P_{d+10}`. -/
def route [NeZero d] (k : ℕ) : Box d :=
  if k ≤ d then rect 0 (cWidth r R w k) (cWidth_nonneg r R w k)
  else rect (axis (tCenter r (k - d))) (fun _ => tWidth (d := d) r R w (k - d))
    (fun _ => by unfold tWidth; positivity)

/-- The relay budget `(d + 11)(R + w) + 1 ≤ 2r`. -/
def Budget : Prop := ((d : ℤ) + 11) * (R + w) + 1 ≤ 2 * r

end Route

/-! ### The thick faces -/

/-- The contraction face of `u` in direction `t`: inward in every coordinate. -/
def inwardFace (t : Fin d) (u : Vertex d) : FaceIndex d := (t, fun i => decide (u i < 0))

/-- The translation face of `u`: forward along `e₁`, inward elsewhere. -/
def forwardFace [NeZero d] (u : Vertex d) : FaceIndex d :=
  (0, fun i => if i = 0 then true else decide (u i < 0))

theorem mem_thickFace_coord {c x : Vertex d} {ℓ w : ℕ} {f : FaceIndex d}
    (hx : x ∈ ThickFace c ℓ w f) (i : Fin d) :
    (i = f.1 → if f.2 i then c i + ℓ < x i ∧ x i ≤ c i + (ℓ + w)
      else c i - (ℓ + w) ≤ x i ∧ x i < c i - ℓ) ∧
    (i ≠ f.1 → if f.2 i then c i ≤ x i ∧ x i ≤ c i + (ℓ + w)
      else c i - (ℓ + w) ≤ x i ∧ x i ≤ c i) := by
  refine ⟨fun h => ?_, fun h => hx.2 i h⟩
  subst h
  exact hx.1

/-- Inward faces stay in the box of radius `max |u_i| (ℓ + w)` around `0`. -/
theorem inward_coord_bound {a b : ℤ} {ℓ w : ℕ} {W : ℤ} (ha : |a| ≤ W) (hW : (ℓ : ℤ) + w ≤ W)
    (hb : if decide (a < 0) then a ≤ b ∧ b ≤ a + (ℓ + w) else a - (ℓ + w) ≤ b ∧ b ≤ a) :
    |b| ≤ W := by
  rw [abs_le] at ha ⊢
  by_cases h : a < 0 <;> simp only [h, decide_true, decide_false, ite_true, Bool.false_eq_true,
    ite_false] at hb <;> omega

section Interfaces

variable [NeZero d] {r R w : ℕ}

theorem cube_in_prism {u : Vertex d} {n : ℕ} {a W : ℤ} (ha0 : 0 ≤ a) (ha : a ≤ 18 * r + 1)
    (hu : ∀ i, |u i - axis a i| ≤ W) (hn : W + n ≤ 10 * r) :
    ∀ x ∈ cube u n, (prism r).Contains x := by
  intro x hx
  rw [contains_prism]
  have hb (i : Fin d) := (mem_cube.mp hx) i
  have h0 := hu 0
  simp only [axis, ite_true] at h0
  rw [abs_le] at h0
  have hb0 := hb 0
  refine ⟨by constructor <;> omega, fun i hi => ?_⟩
  have hi' := hu i
  simp only [axis, hi, ite_false, sub_zero] at hi'
  rw [abs_le] at hi' ⊢
  have := hb i
  constructor <;> omega

/-- Contraction steps `P_t → P_{t+1}` for `t < d`. -/
theorem contraction_interface (hR : 0 < R) (hb : Budget (d := d) r R w) {t : ℕ} (ht : t < d)
    {u : Vertex d} (hu : ((route (d := d) r R w t).expand R).Contains u) :
    (∀ x ∈ cube u (2 * r + w), (prism r).Contains x) ∧
      ThickFace u (2 * r) w (inwardFace ⟨t, ht⟩ u) ⊆
        {x | (route (d := d) r R w (t + 1)).Contains x} := by
  have hR' : (0 : ℤ) < R := by exact_mod_cast hR
  set a : ℤ := (t : ℤ) * (R + w) with ha
  have ha0 : 0 ≤ a := by positivity
  have hdt : (t : ℤ) + 1 ≤ d := by exact_mod_cast ht
  have hda : a + (R + w) ≤ (d : ℤ) * (R + w) := by
    have : ((t : ℤ) + 1) * (R + w) ≤ (d : ℤ) * (R + w) :=
      mul_le_mul_of_nonneg_right hdt (by positivity)
    nlinarith
  have hdb : (d : ℤ) * (R + w) + 11 * (R + w) + 1 ≤ 2 * r := by unfold Budget at hb; nlinarith
  have hw0 : (0 : ℤ) ≤ w := by positivity
  have hroute : route (d := d) r R w t = rect 0 (cWidth r R w t) (cWidth_nonneg r R w t) := by
    simp [route, ht.le]
  have hroute' : route (d := d) r R w (t + 1) =
      rect 0 (cWidth r R w (t + 1)) (cWidth_nonneg r R w (t + 1)) := by
    simp [route, Nat.succ_le_of_lt ht]
  have huu (i : Fin d) : |u i| ≤ (if i.val < t then 2 * (r : ℤ) + a else 4 * r + a) + R := by
    have h := hu i
    rw [hroute] at h
    change (0 : ℤ) - cWidth r R w t i - R ≤ u i ∧ u i ≤ 0 + cWidth r R w t i + R at h
    simp only [cWidth] at h
    rw [abs_le]
    split_ifs at h ⊢ <;> constructor <;> omega
  refine ⟨?_, ?_⟩
  · apply cube_in_prism (a := 0) le_rfl (by positivity) (W := 4 * r + a + R) _ (by push_cast; omega)
    intro i
    simp only [axis]
    split_ifs <;> simpa using (huu i).trans (by split_ifs <;> omega)
  · intro y hy
    rw [Set.mem_ofPred_eq, hroute', contains_rect]
    intro i
    simp only [Pi.zero_apply, sub_zero, cWidth]
    have hc := mem_thickFace_coord hy i
    by_cases hi : i = ⟨t, ht⟩
    · subst hi
      have h1 := hc.1 rfl
      have h2 := huu ⟨t, ht⟩
      simp only [inwardFace, lt_self_iff_false, ite_false] at h1 h2
      rw [abs_le] at h2 ⊢
      simp only [show t < t + 1 from Nat.lt_succ_self t, ite_true]
      have hexp : ((t : ℤ) + 1) * (R + w) = a + R + w := by rw [ha]; ring
      push_cast at h1 ⊢
      rw [hexp]
      by_cases hneg : u ⟨t, ht⟩ < 0 <;>
        simp only [hneg, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false] at h1 <;>
        constructor <;> omega
    · have h1 := hc.2 hi
      simp only [inwardFace] at h1
      have hiv : i.val ≠ t := fun h => hi (Fin.ext h)
      have h2 := huu i
      by_cases hlt : i.val < t
      · simp only [hlt, ite_true] at h2
        simp only [show i.val < t + 1 by omega, ite_true]
        push_cast
        exact inward_coord_bound (W := 2 * r + ((t : ℤ) + 1) * (R + w)) (h2.trans (by nlinarith))
          (by push_cast; nlinarith) h1
      · simp only [hlt, ite_false] at h2
        simp only [show ¬i.val < t + 1 by omega, ite_false]
        push_cast
        exact inward_coord_bound (W := 4 * r + ((t : ℤ) + 1) * (R + w)) (h2.trans (by nlinarith))
          (by push_cast; nlinarith) h1

theorem tCenter_succ {j : ℕ} (hj : j ≤ 9) :
    tCenter r (j + 1) = tCenter r j + (if j + 1 ≤ 9 then 2 * (r : ℤ) else 2 * r + 1) := by
  unfold tCenter
  by_cases h : j + 1 ≤ 9
  · simp only [h, show j ≤ 9 by omega, ite_true]; push_cast; ring
  · have : j = 9 := by omega
    subst this
    simp only [show ¬(9 + 1 ≤ 9) by omega, show (9 : ℕ) ≤ 9 from le_rfl, ite_true, ite_false]
    push_cast; ring

theorem tCenter_bounds {j : ℕ} (hj : j ≤ 9) : 0 ≤ tCenter r j ∧ tCenter r j ≤ 18 * r := by
  unfold tCenter
  simp only [hj, ite_true]
  have : (j : ℤ) ≤ 9 := by exact_mod_cast hj
  constructor <;> nlinarith

/-- `P_{d+j}` is the cube of radius `w_j` around `a_j e₁`, also for `j = 0`. -/
theorem contains_route_translation {j : ℕ} (hj : j ≤ 10) {x : Vertex d} :
    (route (d := d) r R w (d + j)).Contains x ↔
      ∀ k, |x k - axis (tCenter r j) k| ≤ tWidth (d := d) r R w j := by
  by_cases h0 : j = 0
  · subst h0
    simp only [route, le_refl, ite_true, contains_rect, Pi.zero_apply, tCenter,
      Nat.zero_le, Nat.cast_zero, mul_zero, cWidth, tWidth, add_zero]
    have hax : axis (d := d) (0 : ℤ) = 0 := by funext i; simp [axis]
    rw [hax]
    exact forall_congr' (fun k => by simp [k.isLt])
  · simp only [route, show ¬(d + j ≤ d) by omega, ite_false, contains_rect,
      show d + j - d = j by omega]

/-- Translation steps `P_{d+j} → P_{d+j+1}` for `j ≤ 9`. -/
theorem translation_interface (hR : 0 < R) (hb : Budget (d := d) r R w) {j : ℕ} (hj : j ≤ 9)
    {u : Vertex d} (hu : ((route (d := d) r R w (d + j)).expand R).Contains u) {s : ℕ}
    (hs : (s : ℤ) = if j + 1 ≤ 9 then 2 * (r : ℤ) else 2 * r + 1) :
    (∀ x ∈ cube u (s + w), (prism r).Contains x) ∧
      ThickFace u s w (forwardFace u) ⊆ {x | (route (d := d) r R w (d + (j + 1))).Contains x} := by
  have hR' : (0 : ℤ) < R := by exact_mod_cast hR
  have hw0 : (0 : ℤ) ≤ w := by positivity
  obtain ⟨ha0, ha18⟩ := tCenter_bounds (r := r) hj
  have hsle : (s : ℤ) ≤ 2 * r + 1 := by rw [hs]; split_ifs <;> omega
  have hj' : (j : ℤ) ≤ 9 := by exact_mod_cast hj
  have hdb : ((d : ℤ) + 11) * (R + w) + 1 ≤ 2 * r := hb
  have hwj : tWidth (d := d) r R w j + R + s + w ≤ 10 * r := by
    unfold tWidth
    have : ((d : ℤ) + j) * (R + w) ≤ ((d : ℤ) + 9) * (R + w) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have hstep : tWidth (d := d) r R w (j + 1) = tWidth (d := d) r R w j + R + w := by
    unfold tWidth; push_cast; ring
  have hsw : (s : ℤ) + w ≤ tWidth (d := d) r R w (j + 1) := by
    unfold tWidth
    have : (R : ℤ) + w ≤ ((d : ℤ) + (j + 1 : ℕ)) * (R + w) := by
      have h1 : (1 : ℤ) ≤ (d : ℤ) + (j + 1 : ℕ) := by
        have : (0 : ℤ) ≤ d := by positivity
        push_cast; linarith
      nlinarith
    omega
  have huu (k : Fin d) : |u k - axis (tCenter r j) k| ≤ tWidth (d := d) r R w j + R := by
    have h := hu k
    by_cases h0 : j = 0
    · subst h0
      simp only [route, Nat.add_zero, le_refl, ite_true] at h
      change (0 : ℤ) - cWidth r R w d k - R ≤ u k ∧ u k ≤ 0 + cWidth r R w d k + R at h
      have hax : axis (d := d) (tCenter r 0) k = 0 := by simp [axis, tCenter]
      rw [hax, abs_le]
      simp only [cWidth, k.isLt, ite_true, tWidth, Nat.cast_zero, add_zero] at h ⊢
      constructor <;> omega
    · simp only [route, show ¬(d + j ≤ d) by omega, ite_false, show d + j - d = j by omega] at h
      change axis (tCenter r j) k - tWidth (d := d) r R w j - R ≤ u k ∧
        u k ≤ axis (tCenter r j) k + tWidth (d := d) r R w j + R at h
      rw [abs_le]; constructor <;> omega
  refine ⟨cube_in_prism ha0 (by omega) huu (by push_cast; omega), ?_⟩
  intro y hy
  rw [Set.mem_ofPred_eq, contains_route_translation (by omega)]
  intro k
  have hc := mem_thickFace_coord hy k
  by_cases hk : k = 0
  · subst hk
    have h1 := hc.1 rfl
    simp only [forwardFace, ite_true] at h1
    have h2 := huu 0
    have hsucc := tCenter_succ (r := r) hj
    simp only [axis, ite_true] at h2 ⊢
    rw [abs_le] at h2 ⊢
    rw [hstep, hsucc]
    constructor <;> split_ifs at hs ⊢ <;> omega
  · have h1 := hc.2 hk
    simp only [forwardFace, hk, ite_false] at h1
    have h2 := huu k
    simp only [axis, hk, ite_false, sub_zero] at h2 ⊢
    exact inward_coord_bound (W := tWidth (d := d) r R w (j + 1)) (by rw [hstep]; linarith)
      (by linarith) h1

theorem route_zero (x : Vertex d) :
    (route (d := d) r R w 0).Contains x ↔ ∀ k, |x k| ≤ 4 * r := by
  simp only [route, Nat.zero_le, ite_true, contains_rect, Pi.zero_apply, sub_zero, cWidth,
    Nat.not_lt_zero, ite_false, Nat.cast_zero, zero_mul, add_zero]

theorem route_last (hb : Budget (d := d) r R w) {x : Vertex d}
    (hx : (route (d := d) r R w (d + 10)).Contains x) :
    ∀ k, |x k - axis (20 * (r : ℤ) + 1) k| ≤ 4 * r := by
  intro k
  have h := (contains_route_translation (r := r) (R := R) (w := w) le_rfl).mp hx k
  have hc : tCenter r 10 = 20 * r + 1 := by simp [tCenter]
  rw [hc] at h
  have : tWidth (d := d) r R w 10 ≤ 4 * r := by
    unfold tWidth
    have hdb : ((d : ℤ) + 11) * (R + w) + 1 ≤ 2 * r := hb
    push_cast
    nlinarith [show (0 : ℤ) ≤ R + w by positivity]
  linarith

/-- Every relay step has a thick face of radius `2r` or `2r + 1` into the next rectangle. -/
theorem route_thick_interface (hR : 0 < R) (hb : Budget (d := d) r R w) {k : ℕ}
    (hk : k < d + 10) {u : Vertex d} (hu : ((route (d := d) r R w k).expand R).Contains u) :
    ∃ ℓ, (ℓ = 2 * r ∨ ℓ = 2 * r + 1) ∧ ∃ f, (∀ x ∈ cube u (ℓ + w), (prism r).Contains x) ∧
      ThickFace u ℓ w f ⊆ {x | (route (d := d) r R w (k + 1)).Contains x} := by
  by_cases hkd : k < d
  · exact ⟨2 * r, Or.inl rfl, _, contraction_interface hR hb hkd hu⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = d + j := ⟨k - d, by omega⟩
    have hj : j ≤ 9 := by omega
    by_cases h9 : j + 1 ≤ 9
    · refine ⟨2 * r, Or.inl rfl, _, translation_interface hR hb hj hu (s := 2 * r) ?_⟩
      simp [h9]
    · refine ⟨2 * r + 1, Or.inr rfl, _, translation_interface hR hb hj hu (s := 2 * r + 1) ?_⟩
      simp [h9]

end Interfaces

end Peapods.LongRange.RelayThick
