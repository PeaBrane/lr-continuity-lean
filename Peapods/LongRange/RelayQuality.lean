import Peapods.LongRange.Layers
import Peapods.LongRange.Supercritical

/-!
# Step 2 of the extension lemma: relay quality

For `z ∈ C`, `v(z)` clamps `z` to `C` shrunk by `m`, so that the seed box `U(z) = Λ_m(v(z))` lies in
`C` and contains `z`. `O(v)` is the event that every pair of `Λ_m(v)` with `J > 0` is open; under
(Pos) and (Sym) an open seed box is connected (`box_conn_of_open`), and under `(F_q(D))` its
probability is at least `ρ₀` (`seedOpen_ge`). Display (4.2), `relay_quality`: the open seed boxes
from which `T` is reached with conditional probability at most `1 - τ` given the bits inside `C`
have mass at most `P(O) γ / τ`. The face event of (S7) is transferred from the infinite-volume law
to `G` through `(F_q(D))`, since it only sees pairs of distinct points of `Λ_{ℓ+w}(v) ⊆ D`.
Ported from OpenAI's `SeedQuality.seed_conditional_quality`.
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical OAI InfiniteConditioning

variable {d : ℕ}

/-- `(F_q(U))`: every pair of distinct points of `U` is an edge of `G` with law `edgeProb q`. Pairs
with `J = 0` then have probability `0`, as in the paper, where they are not edges. -/
def FqHolds (K : Kernel d) (G : FinGraph d) (p : Pair d → Set.Icc (0 : ℝ) 1) (q : ℝ)
    (U : Box d) : Prop :=
  ∀ x y, U.Contains x → U.Contains y → x ≠ y → s(x, y) ∈ G.edges ∧ p s(x, y) = K.edgeProb q s(x, y)

/-! ### Clamping into a box -/

/-- Clamp each coordinate of `z` to the corresponding side of `C` shrunk by `m`. -/
def Box.clamp (C : Box d) (m : ℕ) (z : Vertex d) : Vertex d :=
  fun i => max (C.lower i + m) (min (C.upper i - m) (z i))

section Clamp

variable {C : Box d} {m : ℕ}

theorem clamp_near (hw : ∀ i, C.lower i + m ≤ C.upper i - m) {z : Vertex d} (hz : C.Contains z)
    (i : Fin d) : z i - m ≤ C.clamp m z i ∧ C.clamp m z i ≤ z i + m := by
  have := hw i
  have := hz i
  simp only [Box.clamp]
  constructor
  · rcases le_total (C.upper i - m) (z i) with h | h
    · rw [min_eq_left h]; exact le_max_of_le_right (by omega)
    · rw [min_eq_right h]; exact le_max_of_le_right (by omega)
  · apply max_le (by omega)
    exact (min_le_right _ _).trans (by omega)

theorem cube_clamp_subset (hw : ∀ i, C.lower i + m ≤ C.upper i - m) (z : Vertex d)
    {x : Vertex d} (hx : x ∈ cube (C.clamp m z) m) : C.Contains x := by
  intro i
  have h := (mem_cube.mp hx) i
  have := hw i
  simp only [Box.clamp] at h
  constructor
  · have := le_max_left (C.lower i + m) (min (C.upper i - m) (z i))
    omega
  · have h1 : max (C.lower i + m) (min (C.upper i - m) (z i)) ≤ C.upper i - m :=
      max_le (hw i) (min_le_left _ _)
    omega

theorem mem_cube_clamp (hw : ∀ i, C.lower i + m ≤ C.upper i - m) {z : Vertex d}
    (hz : C.Contains z) : z ∈ cube (C.clamp m z) m := by
  rw [mem_cube]
  intro i
  have := clamp_near hw hz i
  constructor <;> omega

theorem clamp_contains (hw : ∀ i, C.lower i + m ≤ C.upper i - m) (z : Vertex d) :
    C.Contains (C.clamp m z) :=
  cube_clamp_subset hw z (by rw [mem_cube]; intro i; constructor <;> omega)

/-- Boxes of points `4m + 3` apart in some coordinate are disjoint after clamping. -/
theorem cube_clamp_disjoint (hw : ∀ i, C.lower i + m ≤ C.upper i - m) {z z' : Vertex d}
    (hz : C.Contains z) (hz' : C.Contains z') {i : Fin d}
    (hi : (4 * m + 3 : ℤ) ≤ |z i - z' i|) {x : Vertex d} (hx : x ∈ cube (C.clamp m z) m) :
    x ∉ cube (C.clamp m z') m := by
  intro hx'
  have h1 := clamp_near hw hz i
  have h2 := clamp_near hw hz' i
  have h3 := (mem_cube.mp hx) i
  have h4 := (mem_cube.mp hx') i
  rw [le_abs'] at hi
  omega

end Clamp

/-! ### Translations and the seed product -/

namespace SignedSymmetry

/-- Translation by `v`. -/
def translation (v : Vertex d) : SignedSymmetry d := ⟨Equiv.refl _, fun _ => true, v⟩

@[simp] theorem translation_vertex (v x : Vertex d) : (translation v).vertex x = v + x := by
  funext i
  simp [vertex_apply, translation]

theorem translation_zero (v : Vertex d) : (translation v).vertex 0 = v := by simp

end SignedSymmetry

namespace Kernel

variable (K : Kernel d)

theorem mem_seedPairs {c : Vertex d} {m : ℕ} {e : Pair d} :
    e ∈ K.seedPairs c m ↔ (∀ x ∈ e, x ∈ cube c m) ∧ ¬e.IsDiag ∧ 0 < K.pairWeight e := by
  simp only [seedPairs, Finset.mem_filter, Finset.mem_sym2_iff, mem_cubeFinset]

theorem mk_mem_seedPairs {c : Vertex d} {m : ℕ} {x y : Vertex d} :
    s(x, y) ∈ K.seedPairs c m ↔ x ∈ cube c m ∧ y ∈ cube c m ∧ x ≠ y ∧ 0 < K.J (x - y) := by
  rw [mem_seedPairs]
  simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, Sym2.mk_isDiag_iff, pairWeight_mk,
    and_assoc]

theorem translate_mem_seedPairs (v : Vertex d) (m : ℕ) (e : Pair d) :
    (SignedSymmetry.translation v).pair e ∈ K.seedPairs v m ↔ e ∈ K.seedPairs 0 m := by
  induction e using Sym2.ind with
  | _ a b =>
    set S := SignedSymmetry.translation v
    rw [SignedSymmetry.pair_mk, mk_mem_seedPairs, mk_mem_seedPairs, S.vertex_sub]
    have hl : S.linear (a - b) = a - b := by
      funext i; simp [SignedSymmetry.linear, S, SignedSymmetry.translation]
    rw [hl]
    have hc (x : Vertex d) : S.vertex x ∈ cube v m ↔ x ∈ cube 0 m := by
      have h := S.cube_map 0 x m
      rwa [SignedSymmetry.translation_zero] at h
    rw [hc, hc, S.vertex.injective.ne_iff]

theorem seedPairs_translate (v : Vertex d) (m : ℕ) :
    (K.seedPairs 0 m).map (SignedSymmetry.translation v).pair.toEmbedding = K.seedPairs v m := by
  ext e
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨e0, he0, rfl⟩
    exact (K.translate_mem_seedPairs v m e0).mpr he0
  · intro he
    refine ⟨(SignedSymmetry.translation v).pair.symm e, ?_, by simp⟩
    rw [← K.translate_mem_seedPairs v m]
    simpa using he

theorem pairWeight_translate (v : Vertex d) (e : Pair d) :
    K.pairWeight ((SignedSymmetry.translation v).pair e) = K.pairWeight e := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SignedSymmetry.pair_mk, pairWeight_mk, SignedSymmetry.translation_vertex]
    congr 1
    abel

/-- `(S4)`: `ρ₀` lower-bounds the probability that a seed box is open at any `q > β/2`. -/
theorem seedProd_ge {β q : ℝ} (hq : β / 2 < q) (hβ : 0 < β) (v : Vertex d) (m : ℕ) :
    K.seedRho β m ≤ ∏ e ∈ K.seedPairs v m, (K.edgeProb q e : ℝ) := by
  rw [← K.seedPairs_translate v m, Finset.prod_map, seedRho]
  apply Finset.prod_le_prod₀
  · intro e he
    have hw := ((K.mem_seedPairs).mp he).2.2
    have : Real.exp (-(β / 2 * K.pairWeight e)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  · intro e _
    simp only [Equiv.coe_toEmbedding, edgeProb, K.pairWeight_translate]
    have hw := K.pairWeight_nonneg e
    have hm : β / 2 ≤ max q 0 := (le_max_left q 0).trans' hq.le
    have := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hm hw))
    linarith

/-- Under (Sym), every unit vector `±eᵢ` has the weight of `e₁`. -/
theorem J_axis [NeZero d] (hK : K.SignInvariant) (i : Fin d) {t : ℤ} (ht : t = 1 ∨ t = -1) :
    K.J (fun j => if j = i then t else 0) = K.J (unitAt 0) := by
  let S : SignedSymmetry d := ⟨Equiv.swap 0 i, fun _ => decide (t = 1), 0⟩
  rw [← hK S (unitAt 0)]
  congr 1
  funext j
  simp only [SignedSymmetry.linear, S, unitAt]
  by_cases hj : j = i
  · subst hj
    simp only [Equiv.swap_apply_right, Fin.val_zero, ite_true]
    rcases ht with rfl | rfl <;> simp
  · have h0 : (Equiv.swap 0 i j).val ≠ 0 := by
      intro h
      have h' : Equiv.swap 0 i j = 0 := Fin.ext (by simpa using h)
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h'
      exact hj h'
    simp only [hj, h0, ite_false]
    split_ifs <;> simp

end Kernel

/-! ### Open seed boxes -/

namespace FinGraph

variable {G : FinGraph d}

theorem stepIn_conn {U : Set (Vertex d)} (hU : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → s(a, b) ∈ G.edges)
    {ω : Config d} {x y : Vertex d} (hx : x ∈ U) (h : Relation.ReflTransGen (StepIn U ω) x y) :
    G.Conn ω x y := by
  induction h with
  | refl => exact .refl
  | @tail a b hp hs ih =>
    exact ih.tail ⟨hU a (stepIn_mem hx hp) b hs.1 hs.2.1, hs.2.1, hs.2.2⟩

theorem conn_of_adj {ω : Config d} {x y : Vertex d} (h : G.Adj ω x y) : G.Conn ω x y :=
  Relation.ReflTransGen.single h

/-- Under (Pos) and (Sym), an open seed box is connected through its unit steps. -/
theorem box_conn_of_open [NeZero d] {K : Kernel d} (hK : K.SignInvariant)
    (hPos : 0 < K.J (unitAt 0)) {p : Pair d → Set.Icc (0 : ℝ) 1} {q : ℝ} {D : Box d}
    (hF : FqHolds K G p q D) {v : Vertex d} {m : ℕ} (hsub : ∀ x ∈ cube v m, D.Contains x)
    {ω : Config d} (hO : ω ∈ allValue (K.seedPairs v m) true) :
    ∀ a ∈ cube v m, ∀ b ∈ cube v m, G.Conn ω a b := by
  apply conn_of_box v m
  intro x hx i t ht hy
  set y := Function.update x i (x i + t)
  have hne : x ≠ y := by
    intro h
    have := congrFun h i
    simp only [y, Function.update_self] at this
    rcases ht with rfl | rfl <;> omega
  have hdiff : x - y = fun j => if j = i then -t else 0 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [y]
    · simp [y, hj]
  have hJ : 0 < K.J (x - y) := by
    rw [hdiff, K.J_axis hK i (by rcases ht with rfl | rfl <;> simp)]
    exact hPos
  refine ⟨(hF x y (hsub x hx) (hsub y hy) hne).1, hne, ?_⟩
  exact hO _ ((K.mk_mem_seedPairs).mpr ⟨hx, hy, hne, hJ⟩)

theorem seedPairs_subset_inside {K : Kernel d} {p : Pair d → Set.Icc (0 : ℝ) 1} {q : ℝ}
    {D C : Box d} (hF : FqHolds K G p q D) (hCD : ∀ x, C.Contains x → D.Contains x)
    {v : Vertex d} {m : ℕ} (hvC : ∀ x ∈ cube v m, C.Contains x) :
    K.seedPairs v m ⊆ G.insideBits C := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb, hne, _⟩ := (K.mk_mem_seedPairs).mp he
    refine Finset.mem_filter.mpr ⟨(hF a b (hCD a (hvC a ha)) (hCD b (hvC b hb)) hne).1, ?_⟩
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact hvC _ ha
    · exact hvC _ hb

/-- Under `(F_q(D))`, the probability that `Λ_m(v) ⊆ D` is open is `∏ edgeProb q ≥ ρ₀`. -/
theorem seedOpen_probability {K : Kernel d} {p : Pair d → Set.Icc (0 : ℝ) 1} {q : ℝ} {D : Box d}
    (hF : FqHolds K G p q D) {v : Vertex d} {m : ℕ} (hsub : ∀ x ∈ cube v m, D.Contains x) :
    (ProductCylinder.law p).real (allValue (K.seedPairs v m) true) =
      ∏ e ∈ K.seedPairs v m, (K.edgeProb q e : ℝ) := by
  rw [allValue_probability]
  apply Finset.prod_congr rfl
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb, hne, _⟩ := (K.mk_mem_seedPairs).mp he
    simp only [bitProbability, ite_true, (hF a b (hsub a ha) (hsub b hb) hne).2]

/-- The pairs of distinct points of a finite set. -/
noncomputable def offDiag (S : Finset (Vertex d)) : Finset (Pair d) :=
  S.sym2.filter (fun e => ¬e.IsDiag)

theorem mk_mem_offDiag {S : Finset (Vertex d)} {a b : Vertex d} :
    s(a, b) ∈ offDiag S ↔ a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  simp only [offDiag, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff, and_assoc]

/-- Display (4.2): open seed boxes of low relay quality are rare. -/
theorem relay_quality [NeZero d] {K : Kernel d} {β : ℝ} (s : ScaleData K β)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0)) {p : Pair d → Set.Icc (0 : ℝ) 1}
    {D C : Box d} (hF : FqHolds K G p s.q D) (hCD : ∀ x, C.Contains x → D.Contains x)
    {v : Vertex d} (hvC : ∀ x ∈ cube v s.m, C.Contains x) (T : Set (Vertex d)) {ℓ : ℕ}
    (hℓ : ℓ ∈ ({2 * s.r, 2 * s.r + 1, 10 * s.r - s.w} : Finset ℕ)) {f : FaceIndex d}
    (hcube : ∀ x ∈ cube v (ℓ + s.w), D.Contains x) (hFT : ThickFace v ℓ s.w f ⊆ T) :
    (ProductCylinder.law p).real
      {ω | ω ∈ allValue (K.seedPairs v s.m) true ∧
        conditionalProbability p (G.insideBits C) {ω | G.Meets ω v T} ω ≤ 1 - s.τ} ≤
      (ProductCylinder.law p).real (allValue (K.seedPairs v s.m) true) * s.γ / s.τ := by
  have hmℓ : s.m ≤ ℓ := (faceRadius_bounds s.r_mw hℓ).1
  set O := allValue (K.seedPairs v s.m) true
  set X := Reaches v s.m ℓ s.w (ThickFace v ℓ s.w f)
  set J := offDiag (cubeFinset v (ℓ + s.w))
  have hvD : ∀ x ∈ cube v s.m, D.Contains x := fun x hx => hCD x (hvC x hx)
  have hmJ : K.seedPairs v s.m ⊆ J := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hne, _⟩ := (K.mk_mem_seedPairs).mp he
      have hle : s.m ≤ ℓ + s.w := hmℓ.trans (Nat.le_add_right _ _)
      exact mk_mem_offDiag.mpr ⟨mem_cubeFinset.mpr (cube_mono v hle ha),
        mem_cubeFinset.mpr (cube_mono v hle hb), hne⟩
  have hO : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ O) :=
    ProductCylinder.determinedBy_mono hmJ (allValue_determined _ _)
  have hX : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ X) := by
    intro ω ω' h
    apply propext
    have hag (ω ω' : Config d) (h : ∀ e ∈ J, ω' e = ω e) : ∀ a ∈ cube v (ℓ + s.w),
        ∀ b ∈ cube v (ℓ + s.w), a ≠ b → ω' s(a, b) = ω s(a, b) := fun a ha b hb hab =>
      h _ (mk_mem_offDiag.mpr ⟨mem_cubeFinset.mpr ha, mem_cubeFinset.mpr hb, hab⟩)
    exact ⟨reaches_of_agree_pairs hmℓ (thickFace_subset _ _ _ _)
        (hag ω' ω (fun e he => (h e he).symm)),
      reaches_of_agree_pairs hmℓ (thickFace_subset _ _ _ _) (hag ω ω' h)⟩
  have hpq : ∀ e ∈ J, p e = K.edgeProb s.q e := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hne⟩ := mk_mem_offDiag.mp he
      exact (hF a b (hcube a (mem_cubeFinset.mp ha)) (hcube b (mem_cubeFinset.mp hb)) hne).2
  have hprob : 1 - s.γ ≤ (ProductCylinder.law p).real X := by
    rw [ProductCylinder.probability_congr_parameters J p (K.edgeProb s.q) hpq X hX]
    exact (s.faces ℓ hℓ v f).le
  have hsub : O ∩ X ⊆ {ω | G.Meets ω v T} := by
    rintro ω ⟨hOω, x0, hx0, y, hy, z, hz, hpath, hyz, _⟩
    have hbig (a : Vertex d) (h : a ∈ cube v ℓ) : a ∈ cube v (ℓ + s.w) :=
      cube_mono v (Nat.le_add_right ℓ s.w) h
    have hv : G.Conn ω v x0 :=
      box_conn_of_open hK hPos hF hvD hOω v (by rw [mem_cube]; intro i; omega) x0 hx0
    have hxy : G.Conn ω x0 y :=
      stepIn_conn (fun a ha b hb hab => (hF a b (hcube a (hbig a ha)) (hcube b (hbig b hb)) hab).1)
        (cube_mono v hmℓ hx0) hpath
    have hzD : D.Contains z := hcube z (thickFace_subset _ _ _ _ hz)
    have hyz' : G.Adj ω y z := ⟨(hF y z (hcube y (hbig y hy)) hzD hyz.1).1, hyz.1, hyz.2⟩
    exact ⟨z, hFT hz, conn_trans (conn_trans hv hxy) (conn_of_adj hyz')⟩
  have hfail := ProductCylinder.seed_failure_bound J p O X {ω | G.Meets ω v T} hO hX
    (allValue_true_monotone _) (fun _ _ h hω => reaches_mono h hω) hsub hprob
  exact conditional_failure_bound p (G.insideBits C) O {ω | G.Meets ω v T}
    (ProductCylinder.determinedBy_mono (seedPairs_subset_inside hF hCD hvC)
      (allValue_determined _ _))
    (measurableSet_meets v T) s.τ_range.1 hfail

end FinGraph

end Peapods.LongRange
