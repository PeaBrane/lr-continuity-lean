import Peapods.LongRange.Seeds
import Peapods.LongRange.Subcritical
import OAI.Probability.CriticalZ3.QuarterFaces

/-!
# Faces at a percolating parameter (Lemma 3.2)

The outer thick quarter-faces of `Λ_ℓ(u)` (Definition 3.1) and the event `X(u, ℓ, F)`: an open path
from `Λ_m(u)` inside `Λ_ℓ(u)` that leaves it by an open pair of sup-norm length at most `w` landing in
`F`. Off the event that some open pair from `Λ_ℓ` is longer than `w`, a seed with an infinite cluster
reaches one of the `d 2^d` faces; signed coordinate symmetries give all faces the same probability
and Harris's inequality gives the root bound. Ported from OpenAI's `CriticalZ3.QuarterFaces`, where
the last edge is a nearest-neighbour bond and there is no long-edge term.
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical OAI
open scoped ENNReal

variable {d : ℕ}

/-! ### Cubes as finite sets -/

/-- The cube `Λ_n(c)` as a `Finset`. -/
noncomputable def cubeFinset (c : Vertex d) (n : ℕ) : Finset (Vertex d) :=
  Finset.Icc (fun i => c i - (n : ℤ)) (fun i => c i + (n : ℤ))

@[simp] theorem mem_cubeFinset {c x : Vertex d} {n : ℕ} : x ∈ cubeFinset c n ↔ x ∈ cube c n := by
  simp only [cubeFinset, cube, Finset.mem_Icc, Set.mem_Icc]

theorem card_cubeFinset (c : Vertex d) (n : ℕ) : (cubeFinset c n).card = (2 * n + 1) ^ d := by
  rw [cubeFinset, Pi.card_Icc]
  have h (i : Fin d) : (Finset.Icc (c i - (n : ℤ)) (c i + (n : ℤ))).card = 2 * n + 1 := by
    rw [Int.card_Icc]
    omega
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem mem_cube_iff_abs {c x : Vertex d} {n : ℕ} : x ∈ cube c n ↔ ∀ i, |x i - c i| ≤ n := by
  rw [mem_cube]
  exact forall_congr' (fun i => by rw [abs_le]; omega)

theorem mem_cube_iff_sub {c x : Vertex d} {n : ℕ} : x ∈ cube c n ↔ x - c ∈ cube 0 n := by
  simp only [mem_cube_iff_abs, Pi.sub_apply, Pi.zero_apply, sub_zero]

theorem mem_cube_add {u a b : Vertex d} {ℓ w : ℕ} (ha : a ∈ cube u ℓ) (hb : b ∈ cube a w) :
    b ∈ cube u (ℓ + w) := by
  rw [mem_cube] at ha hb ⊢
  intro i
  have := ha i
  have := hb i
  push_cast
  omega

/-! ### Signed symmetries of the kernel and of the law -/

namespace SignedSymmetry

/-- The linear part `z ↦ ±z ∘ perm` of a signed symmetry. -/
def linear (S : SignedSymmetry d) (z : Vertex d) : Vertex d :=
  fun i => if S.signs i then z (S.perm i) else -z (S.perm i)

theorem vertex_apply (S : SignedSymmetry d) (x : Vertex d) (i : Fin d) :
    S.vertex x i = S.shift i + if S.signs i then x (S.perm i) else -x (S.perm i) := rfl

theorem vertex_sub (S : SignedSymmetry d) (x y : Vertex d) :
    S.vertex x - S.vertex y = S.linear (x - y) := by
  funext i
  simp only [Pi.sub_apply, vertex_apply, linear]
  cases S.signs i
  · simp only [Bool.false_eq_true, ite_false]; ring
  · simp only [ite_true]; ring

theorem linear_mem_cube (S : SignedSymmetry d) (z : Vertex d) (n : ℕ) :
    S.linear z ∈ cube 0 n ↔ z ∈ cube 0 n := by
  simp only [mem_cube_iff_abs, Pi.zero_apply, sub_zero]
  have habs (i : Fin d) : |S.linear z i| = |z (S.perm i)| := by
    simp only [linear]
    cases S.signs i <;> simp
  simp_rw [habs]
  exact ⟨fun h i => by simpa using h (S.perm.symm i), fun h i => h _⟩

theorem cube_map (S : SignedSymmetry d) (c x : Vertex d) (n : ℕ) :
    S.vertex x ∈ cube (S.vertex c) n ↔ x ∈ cube c n := by
  rw [mem_cube_iff_sub, vertex_sub, linear_mem_cube, ← mem_cube_iff_sub]

/-- The induced permutation of the bits. -/
def pair (S : SignedSymmetry d) : Pair d ≃ Pair d where
  toFun := Sym2.map S.vertex
  invFun := Sym2.map S.vertex.symm
  left_inv z := by
    induction z using Sym2.ind with
    | _ a b => simp [Sym2.map_mk]
  right_inv z := by
    induction z using Sym2.ind with
    | _ a b => simp [Sym2.map_mk]

@[simp] theorem pair_mk (S : SignedSymmetry d) (x y : Vertex d) :
    S.pair s(x, y) = s(S.vertex x, S.vertex y) := rfl

theorem adj_map (S : SignedSymmetry d) (ω : Config d) (x y : Vertex d) :
    Adj (fun e => ω (S.pair e)) x y ↔ Adj ω (S.vertex x) (S.vertex y) := by
  simp only [Adj, pair_mk, ne_eq, EmbeddingLike.apply_eq_iff_eq]

end SignedSymmetry

namespace Kernel

variable (K : Kernel d)

/-- (Sym): `J` is invariant under coordinate permutations and sign changes of coordinates. -/
def SignInvariant : Prop := ∀ (S : SignedSymmetry d) (z : Vertex d), K.J (S.linear z) = K.J z

theorem edgeProb_pair {K : Kernel d} (hK : K.SignInvariant) (β : ℝ) (S : SignedSymmetry d)
    (e : Pair d) : K.edgeProb β (S.pair e) = K.edgeProb β e := by
  induction e using Sym2.ind with
  | _ x y =>
    apply Subtype.ext
    simp only [edgeProb, SignedSymmetry.pair_mk, pairWeight_mk, S.vertex_sub, hK S]

/-- Under (Sym) the law is invariant under every signed symmetry of `ℤ^d`. -/
theorem law_reindex {K : Kernel d} (hK : K.SignInvariant) (β : ℝ) (S : SignedSymmetry d)
    {A : Set (Config d)} (hA : MeasurableSet A) :
    K.law β ((fun ω e => ω (S.pair e)) ⁻¹' A) = K.law β A := by
  unfold law
  rw [← Measure.map_apply (Measurable.of_eval (fun e => measurable_pi_apply (S.pair e))) hA,
    ProductCylinder.map_reindex]
  simp only [edgeProb_pair hK]

end Kernel

/-! ### Outer thick quarter-faces -/

/-- The outer thick quarter-face of `Λ_ℓ(c)` of thickness `w` (Definition 3.1): the normal
coordinate `f.1` lies in `(ℓ, ℓ + w]` on the side `f.2 f.1`, and every other coordinate `i` lies
in `[0, ℓ + w]` on the side `f.2 i`. -/
def ThickFace (c : Vertex d) (ℓ w : ℕ) (f : FaceIndex d) : Set (Vertex d) :=
  {x | (if f.2 f.1 then c f.1 + ℓ < x f.1 ∧ x f.1 ≤ c f.1 + (ℓ + w)
      else c f.1 - (ℓ + w) ≤ x f.1 ∧ x f.1 < c f.1 - ℓ) ∧
    ∀ i, i ≠ f.1 → if f.2 i then c i ≤ x i ∧ x i ≤ c i + (ℓ + w)
      else c i - (ℓ + w) ≤ x i ∧ x i ≤ c i}

theorem card_faceIndex : Fintype.card (FaceIndex d) = d * 2 ^ d := by
  simp [FaceIndex, Fintype.card_prod]

theorem thickFace_subset (c : Vertex d) (ℓ w : ℕ) (f : FaceIndex d) :
    ThickFace c ℓ w f ⊆ cube c (ℓ + w) := by
  intro x hx
  rw [mem_cube]
  intro i
  push_cast
  by_cases hi : i = f.1
  · subst i
    have h := hx.1
    cases hf : f.2 f.1 <;> simp only [hf, Bool.false_eq_true, ite_false, ite_true] at h <;> omega
  · have h := hx.2 i hi
    cases hf : f.2 i <;> simp only [hf, Bool.false_eq_true, ite_false, ite_true] at h <;> omega

/-- The faces cover the shell `Λ_{ℓ+w}(c) \ Λ_ℓ(c)`. -/
theorem exists_thickFace {c y : Vertex d} {ℓ w : ℕ} (hy : y ∈ cube c (ℓ + w))
    (hout : y ∉ cube c ℓ) : ∃ f, y ∈ ThickFace c ℓ w f := by
  rw [mem_cube] at hy hout
  push_cast at hy
  push Not at hout
  obtain ⟨i, hi⟩ := hout
  refine ⟨(i, fun j => decide (c j ≤ y j)), ?_, ?_⟩
  · have h := hy i
    by_cases hc : c i ≤ y i <;> simp only [hc, decide_true, decide_false, ite_true,
      Bool.false_eq_true, ite_false] <;> omega
  · intro j _
    have h := hy j
    by_cases hc : c j ≤ y j <;> simp only [hc, decide_true, decide_false, ite_true,
      Bool.false_eq_true, ite_false, true_and] <;> omega

theorem thickFace_preimage [NeZero d] (c : Vertex d) (ℓ w : ℕ) (f : FaceIndex d) :
    (faceSymmetry c f).vertex ⁻¹' ThickFace c ℓ w f = ThickFace 0 ℓ w canonicalFace := by
  ext x
  have hv (i : Fin d) : (faceSymmetry c f).vertex x i =
      c i + if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i) := rfl
  have hnormal : (if f.2 f.1 then c f.1 + ℓ < (faceSymmetry c f).vertex x f.1 ∧
        (faceSymmetry c f).vertex x f.1 ≤ c f.1 + (ℓ + w)
      else c f.1 - (ℓ + w) ≤ (faceSymmetry c f).vertex x f.1 ∧
        (faceSymmetry c f).vertex x f.1 < c f.1 - ℓ) ↔ ((ℓ : ℤ) < x 0 ∧ x 0 ≤ ℓ + w) := by
    rw [hv, Equiv.swap_apply_left]
    cases f.2 f.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hside (i : Fin d) : (if f.2 i then c i ≤ (faceSymmetry c f).vertex x i ∧
        (faceSymmetry c f).vertex x i ≤ c i + (ℓ + w)
      else c i - (ℓ + w) ≤ (faceSymmetry c f).vertex x i ∧
        (faceSymmetry c f).vertex x i ≤ c i) ↔
      (0 ≤ x (Equiv.swap f.1 0 i) ∧ x (Equiv.swap f.1 0 i) ≤ ℓ + w) := by
    rw [hv]
    cases f.2 i <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  simp only [Set.mem_preimage, ThickFace, Set.mem_ofPred_eq]
  rw [hnormal]
  simp_rw [hside]
  simp only [canonicalFace, ite_true, Pi.zero_apply, zero_add]
  apply and_congr_right
  intro _
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

/-! ### The face event `X(u, ℓ, T)` -/

/-- An open step into `D`. -/
def StepIn (D : Set (Vertex d)) (ω : Config d) (x y : Vertex d) : Prop := y ∈ D ∧ Adj ω x y

/-- The event `X(u, ℓ, T)` of Definition 3.1 with seed radius `m` and last-edge bound `w`: an open
path from `Λ_m(u)` that stays in `Λ_ℓ(u)`, followed by an open pair of sup-norm length at most `w`
into `T`. -/
def Reaches (u : Vertex d) (m ℓ w : ℕ) (T : Set (Vertex d)) : Set (Config d) :=
  {ω | ∃ x ∈ cube u m, ∃ y ∈ cube u ℓ, ∃ z ∈ T,
    Relation.ReflTransGen (StepIn (cube u ℓ) ω) x y ∧ Adj ω y z ∧ z ∈ cube y w}

theorem stepIn_mem {D : Set (Vertex d)} {ω : Config d} {x y : Vertex d} (hx : x ∈ D)
    (h : Relation.ReflTransGen (StepIn D ω) x y) : y ∈ D := by
  cases h with
  | refl => exact hx
  | tail _ hs => exact hs.1

theorem stepIn_congr {D : Set (Vertex d)} {ω ω' : Config d}
    (hagree : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → ω' s(a, b) = ω s(a, b)) {x y : Vertex d} (hx : x ∈ D)
    (h : Relation.ReflTransGen (StepIn D ω) x y) : Relation.ReflTransGen (StepIn D ω') x y := by
  induction h with
  | refl => exact .refl
  | tail hp hs ih =>
    exact ih.tail ⟨hs.1, hs.2.1, (hagree _ (stepIn_mem hx hp) _ hs.1 hs.2.1).trans hs.2.2⟩

/-- First exit: a path from `a` either stays in `D` or has a last vertex in `D` followed by a step
out of `D`. -/
theorem first_exit {α : Type*} {r : α → α → Prop} {D : Set α} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen (fun x y => y ∈ D ∧ r x y) a b ∨
      ∃ c e, Relation.ReflTransGen (fun x y => y ∈ D ∧ r x y) a c ∧ r c e ∧ e ∉ D := by
  induction h with
  | refl => exact Or.inl .refl
  | @tail b' c _ hbc ih =>
    rcases ih with hin | hexit
    · by_cases hc : c ∈ D
      · exact Or.inl (hin.tail ⟨hc, hbc⟩)
      · exact Or.inr ⟨b', c, hin, hbc, hc⟩
    · exact Or.inr hexit

theorem adj_mono {ω ω' : Config d} (h : ω ≤ ω') {x y : Vertex d} (hxy : Adj ω x y) :
    Adj ω' x y :=
  ⟨hxy.1, Bool.eq_true_of_true_le (hxy.2 ▸ h s(x, y))⟩

theorem reaches_mono {u : Vertex d} {m ℓ w : ℕ} {T : Set (Vertex d)} {ω ω' : Config d}
    (h : ω ≤ ω') (hω : ω ∈ Reaches u m ℓ w T) : ω' ∈ Reaches u m ℓ w T := by
  obtain ⟨x, hx, y, hy, z, hz, hp, ha, hw⟩ := hω
  exact ⟨x, hx, y, hy, z, hz,
    Relation.ReflTransGen.mono (fun a b hs => ⟨hs.1, adj_mono h hs.2⟩) x y hp, adj_mono h ha, hw⟩

/-- `X(u, ℓ, T)` only sees the pairs of distinct vertices of `Λ_{ℓ+w}(u)`. -/
theorem reaches_of_agree_pairs {u : Vertex d} {m ℓ w : ℕ} {T : Set (Vertex d)} (hmℓ : m ≤ ℓ)
    (hT : T ⊆ cube u (ℓ + w)) {ω ω' : Config d}
    (hagree : ∀ a ∈ cube u (ℓ + w), ∀ b ∈ cube u (ℓ + w), a ≠ b → ω' s(a, b) = ω s(a, b))
    (hω : ω ∈ Reaches u m ℓ w T) : ω' ∈ Reaches u m ℓ w T := by
  obtain ⟨x, hx, y, hy, z, hz, hp, ha, hw⟩ := hω
  have hbig (a : Vertex d) (h : a ∈ cube u ℓ) : a ∈ cube u (ℓ + w) :=
    cube_mono u (Nat.le_add_right ℓ w) h
  have hxℓ : x ∈ cube u ℓ := cube_mono u hmℓ hx
  refine ⟨x, hx, y, hy, z, hz,
    stepIn_congr (fun a ha b hb => hagree a (hbig a ha) b (hbig b hb)) hxℓ hp, ⟨ha.1, ?_⟩, hw⟩
  exact (hagree y (hbig y hy) z (hT hz) ha.1).trans ha.2

theorem reaches_of_agree {u : Vertex d} {m ℓ w : ℕ} {T : Set (Vertex d)} (hmℓ : m ≤ ℓ)
    (hT : T ⊆ cube u (ℓ + w)) {ω ω' : Config d}
    (hagree : ∀ e ∈ (cubeFinset u (ℓ + w)).sym2, ω' e = ω e) (hω : ω ∈ Reaches u m ℓ w T) :
    ω' ∈ Reaches u m ℓ w T :=
  reaches_of_agree_pairs hmℓ hT (fun _ ha _ hb _ =>
    hagree _ (Finset.mk_mem_sym2_iff.mpr ⟨mem_cubeFinset.mpr ha, mem_cubeFinset.mpr hb⟩)) hω

theorem reaches_determined {u : Vertex d} {m ℓ w : ℕ} {T : Set (Vertex d)} (hmℓ : m ≤ ℓ)
    (hT : T ⊆ cube u (ℓ + w)) (ω ω' : Config d)
    (hagree : ∀ e ∈ (cubeFinset u (ℓ + w)).sym2, ω' e = ω e) :
    ω' ∈ Reaches u m ℓ w T ↔ ω ∈ Reaches u m ℓ w T :=
  ⟨reaches_of_agree hmℓ hT (fun e he => (hagree e he).symm), reaches_of_agree hmℓ hT hagree⟩

theorem measurableSet_reaches {u : Vertex d} {m ℓ w : ℕ} {T : Set (Vertex d)} (hmℓ : m ≤ ℓ)
    (hT : T ⊆ cube u (ℓ + w)) : MeasurableSet (Reaches u m ℓ w T) :=
  ProductCylinder.measurableSet_determined _ _ (reaches_determined hmℓ hT)

theorem SignedSymmetry.reaches_map (S : SignedSymmetry d) (ω : Config d) (c : Vertex d)
    (m ℓ w : ℕ) (T : Set (Vertex d)) :
    (fun e => ω (S.pair e)) ∈ Reaches c m ℓ w (S.vertex ⁻¹' T) ↔
      ω ∈ Reaches (S.vertex c) m ℓ w T := by
  have hstep (a b : Vertex d) : StepIn (cube c ℓ) (fun e => ω (S.pair e)) a b ↔
      StepIn (cube (S.vertex c) ℓ) ω (S.vertex a) (S.vertex b) := by
    simp only [StepIn, S.cube_map, S.adj_map]
  have hrtg := CriticalZ3.rtg_equiv_iff S.vertex hstep
  constructor
  · rintro ⟨x, hx, y, hy, z, hz, hp, ha, hw⟩
    exact ⟨S.vertex x, (S.cube_map c x m).mpr hx, S.vertex y, (S.cube_map c y ℓ).mpr hy,
      S.vertex z, hz, (hrtg x y).mp hp, (S.adj_map ω y z).mp ha, (S.cube_map y z w).mpr hw⟩
  · rintro ⟨x, hx, y, hy, z, hz, hp, ha, hw⟩
    obtain ⟨x, rfl⟩ := S.vertex.surjective x
    obtain ⟨y, rfl⟩ := S.vertex.surjective y
    obtain ⟨z, rfl⟩ := S.vertex.surjective z
    exact ⟨x, (S.cube_map c x m).mp hx, y, (S.cube_map c y ℓ).mp hy, z, hz, (hrtg x y).mpr hp,
      (S.adj_map ω y z).mpr ha, (S.cube_map y z w).mp hw⟩

/-! ### Long edges -/

/-- Some open pair from `Λ_ℓ(u)` has sup-norm length more than `w`. -/
def LongEdge (u : Vertex d) (ℓ w : ℕ) : Set (Config d) :=
  {ω | ∃ x ∈ cube u ℓ, ∃ y, y ∉ cube x w ∧ ω s(x, y) = true}

/-- A seed cube that meets an infinite cluster, off long edges, reaches one of the faces. -/
theorem seed_subset_faces {u : Vertex d} {m ℓ w : ℕ} (hmℓ : m ≤ ℓ) :
    SeedInfinite u m ∩ (LongEdge u ℓ w)ᶜ ⊆ ⋃ f : FaceIndex d, Reaches u m ℓ w (ThickFace u ℓ w f) := by
  rintro ω ⟨⟨x, hx, hinf⟩, hlong⟩
  have hxℓ : x ∈ cube u ℓ := cube_mono u hmℓ hx
  obtain ⟨y, hy, hyout⟩ := (Set.Infinite.sdiff hinf (cube_finite u ℓ)).nonempty
  rcases first_exit (D := cube u ℓ) hy with hin | ⟨a, b, hpa, hab, hb⟩
  · exact absurd (stepIn_mem (ω := ω) hxℓ hin) hyout
  · have ha : a ∈ cube u ℓ := stepIn_mem (ω := ω) hxℓ hpa
    have hshort : b ∈ cube a w := by
      by_contra h
      exact hlong ⟨a, ha, b, h, hab.2⟩
    obtain ⟨f, hf⟩ := exists_thickFace (mem_cube_add ha hshort) hb
    exact Set.mem_iUnion.mpr ⟨f, x, hx, a, ha, b, hf, hpa, hab, hshort⟩

namespace Kernel

variable (K : Kernel d)

/-- The tail `T(w) = ∑_{‖z‖ > w} J(z)`. -/
noncomputable def tail (w : ℕ) : ℝ := ∑' z, (cube 0 w)ᶜ.indicator K.J z

theorem tail_nonneg (w : ℕ) : 0 ≤ K.tail w :=
  tsum_nonneg (fun z => Set.indicator_nonneg (fun z _ => K.nonneg z) z)

theorem tsum_stepWeight_tail (β : ℝ) (w : ℕ) :
    ∑' z, (cube 0 w)ᶜ.indicator (K.stepWeight β) z = ENNReal.ofReal (max β 0 * K.tail w) := by
  have he (z : Vertex d) : (cube 0 w)ᶜ.indicator (K.stepWeight β) z =
      ENNReal.ofReal (max β 0 * (cube 0 w)ᶜ.indicator K.J z) := by
    by_cases h : z ∈ (cube 0 w)ᶜ <;> simp [Set.indicator, h, stepWeight]
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun z => mul_nonneg (le_max_right _ _) (Set.indicator_nonneg (fun z _ => K.nonneg z) z))
    ((K.summable.indicator _).mul_left _), tsum_mul_left, tail]

/-- `P(E_long) ≤ β⁺ (2ℓ + 1)^d T(w)`. -/
theorem longEdge_le (β : ℝ) (u : Vertex d) (ℓ w : ℕ) :
    K.law β (LongEdge u ℓ w) ≤ ENNReal.ofReal ((2 * ℓ + 1) ^ d * (max β 0 * K.tail w)) := by
  have hsub : LongEdge u ℓ w ⊆ ⋃ x ∈ cubeFinset u ℓ, ⋃ y : Vertex d,
      {ω : Config d | y ∉ cube x w ∧ ω s(x, y) = true} := by
    rintro ω ⟨x, hx, y, hy, hω⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨x, mem_cubeFinset.mpr hx, y, hy, hω⟩
  have hone (x y : Vertex d) : K.law β {ω : Config d | y ∉ cube x w ∧ ω s(x, y) = true} ≤
      (cube x w)ᶜ.indicator (fun y => K.stepWeight β (y - x)) y := by
    by_cases hy : y ∈ cube x w
    · have : {ω : Config d | y ∉ cube x w ∧ ω s(x, y) = true} = ∅ := by
        ext ω; simp [hy]
      rw [this, measure_empty]
      exact zero_le
    · rw [Set.indicator_of_mem (show y ∈ (cube x w)ᶜ from hy)]
      calc K.law β {ω : Config d | y ∉ cube x w ∧ ω s(x, y) = true}
          ≤ K.law β {ω : Config d | ω s(x, y) = true} := measure_mono (fun ω h => h.2)
        _ = ENNReal.ofReal (K.edgeProb β s(x, y)) := by
            rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
            congr 1
            have h := InfiniteConditioning.single_probability (K.edgeProb β) s(x, y) true
            simp only [InfiniteConditioning.bitProbability, ite_true] at h
            exact h
        _ ≤ K.stepWeight β (y - x) := ENNReal.ofReal_le_ofReal (K.edgeProb_le β x y)
  have hrow (x : Vertex d) : ∑' y, K.law β {ω : Config d | y ∉ cube x w ∧ ω s(x, y) = true} ≤
      ENNReal.ofReal (max β 0 * K.tail w) := by
    refine (ENNReal.tsum_le_tsum (hone x)).trans (le_of_eq ?_)
    have he (y : Vertex d) : (cube x w)ᶜ.indicator (fun y => K.stepWeight β (y - x)) y =
        (cube 0 w)ᶜ.indicator (K.stepWeight β) (y - x) := by
      by_cases h : y ∈ cube x w
      · have h' : y - x ∈ cube 0 w := mem_cube_iff_sub.mp h
        simp [h, h']
      · have h' : y - x ∉ cube 0 w := fun h' => h (mem_cube_iff_sub.mpr h')
        simp [h, h']
    simp_rw [he]
    rw [tsum_translate, K.tsum_stepWeight_tail]
  calc K.law β (LongEdge u ℓ w)
      ≤ K.law β (⋃ x ∈ cubeFinset u ℓ, ⋃ y : Vertex d,
          {ω : Config d | y ∉ cube x w ∧ ω s(x, y) = true}) := measure_mono hsub
    _ ≤ ∑ x ∈ cubeFinset u ℓ, K.law β (⋃ y : Vertex d,
          {ω : Config d | y ∉ cube x w ∧ ω s(x, y) = true}) := measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ cubeFinset u ℓ, ENNReal.ofReal (max β 0 * K.tail w) :=
        Finset.sum_le_sum (fun x _ => (measure_iUnion_le _).trans (hrow x))
    _ = ENNReal.ofReal ((2 * ℓ + 1) ^ d * (max β 0 * K.tail w)) := by
        rw [Finset.sum_const, card_cubeFinset, nsmul_eq_mul,
          show ((2 * (ℓ : ℝ) + 1) ^ d) = (((2 * ℓ + 1) ^ d : ℕ) : ℝ) by push_cast; ring,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem longEdge_real_le (β : ℝ) (u : Vertex d) (ℓ w : ℕ) :
    (K.law β).real (LongEdge u ℓ w) ≤ (2 * ℓ + 1) ^ d * (max β 0 * K.tail w) :=
  ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (by positivity) (mul_nonneg (le_max_right _ _) (K.tail_nonneg w)))
    (K.longEdge_le β u ℓ w)

/-! ### Symmetry and Harris -/

theorem reaches_face_probability [NeZero d] {K : Kernel d} (hK : K.SignInvariant) (β : ℝ)
    {m ℓ w : ℕ} (hmℓ : m ≤ ℓ) (c : Vertex d) (f : FaceIndex d) :
    K.law β (Reaches c m ℓ w (ThickFace c ℓ w f)) =
      K.law β (Reaches 0 m ℓ w (ThickFace 0 ℓ w canonicalFace)) := by
  let S := faceSymmetry c f
  have h := law_reindex hK β S
    (measurableSet_reaches hmℓ (thickFace_subset 0 ℓ w canonicalFace))
  rw [← h]
  congr 1
  ext ω
  have hm := S.reaches_map ω 0 m ℓ w (ThickFace c ℓ w f)
  simpa only [S, faceSymmetry_zero, thickFace_preimage, Set.mem_preimage] using hm.symm

theorem reaches_face_compl [NeZero d] {K : Kernel d} (hK : K.SignInvariant) (β : ℝ)
    {m ℓ w : ℕ} (hmℓ : m ≤ ℓ) (c : Vertex d) (f : FaceIndex d) :
    (K.law β).real (Reaches c m ℓ w (ThickFace c ℓ w f))ᶜ =
      (K.law β).real (Reaches 0 m ℓ w (ThickFace 0 ℓ w canonicalFace))ᶜ := by
  rw [measureReal_compl (measurableSet_reaches hmℓ (thickFace_subset _ _ _ _)),
    measureReal_compl (measurableSet_reaches hmℓ (thickFace_subset _ _ _ _))]
  simp only [Measure.real_def, reaches_face_probability hK β hmℓ c f]

/-- Harris's inequality over the `d 2^d` faces. -/
theorem faces_harris [NeZero d] {K : Kernel d} (hK : K.SignInvariant) (β : ℝ) {m ℓ w : ℕ}
    (hmℓ : m ≤ ℓ) :
    ((K.law β).real (Reaches 0 m ℓ w (ThickFace 0 ℓ w canonicalFace))ᶜ) ^ (d * 2 ^ d) ≤
      (K.law β).real (⋂ f : FaceIndex d, (Reaches 0 m ℓ w (ThickFace 0 ℓ w f))ᶜ) := by
  have h := ProductCylinder.decreasing_forall ((cubeFinset 0 (ℓ + w)).sym2) (K.edgeProb β)
    (fun f : FaceIndex d => (Reaches 0 m ℓ w (ThickFace 0 ℓ w f))ᶜ)
    (fun f ω ω' hω => not_congr (reaches_determined hmℓ (thickFace_subset _ _ _ f) ω ω' hω))
    (fun f ω ω' hω h' h => h' (reaches_mono hω h))
  change (∏ f : FaceIndex d, (K.law β).real _) ≤ (K.law β).real _ at h
  simp_rw [reaches_face_compl hK β hmℓ 0] at h
  simpa only [Finset.prod_const, Finset.card_univ, card_faceIndex] using h

/-- Lemma 3.2 in power form: for `m ≤ ℓ`, every centre `c` and every face `f`,
`P(X(c, ℓ, F_f)ᶜ)^{d 2^d} ≤ P(Λ_m meets no infinite cluster) + β⁺ (2ℓ + 1)^d T(w)`. -/
theorem faces_bound [NeZero d] {K : Kernel d} (hK : K.SignInvariant) (β : ℝ) {m ℓ w : ℕ}
    (hmℓ : m ≤ ℓ) (c : Vertex d) (f : FaceIndex d) :
    ((K.law β).real (Reaches c m ℓ w (ThickFace c ℓ w f))ᶜ) ^ (d * 2 ^ d) ≤
      (K.law β).real (SeedInfinite 0 m)ᶜ + (2 * ℓ + 1) ^ d * (max β 0 * K.tail w) := by
  rw [reaches_face_compl hK β hmℓ c f]
  refine (faces_harris hK β hmℓ).trans ?_
  have hsub : (⋂ f : FaceIndex d, (Reaches 0 m ℓ w (ThickFace 0 ℓ w f))ᶜ) ⊆
      (SeedInfinite 0 m)ᶜ ∪ LongEdge 0 ℓ w := by
    intro ω hω
    by_contra h
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at h
    obtain ⟨f, hf⟩ := Set.mem_iUnion.mp (seed_subset_faces hmℓ ⟨h.1, h.2⟩)
    exact Set.mem_iInter.mp hω f hf
  calc (K.law β).real (⋂ f : FaceIndex d, (Reaches 0 m ℓ w (ThickFace 0 ℓ w f))ᶜ)
      ≤ (K.law β).real ((SeedInfinite 0 m)ᶜ ∪ LongEdge 0 ℓ w) := measureReal_mono hsub
    _ ≤ (K.law β).real (SeedInfinite 0 m)ᶜ + (K.law β).real (LongEdge 0 ℓ w) :=
        measureReal_union_le _ _
    _ ≤ _ := by
        gcongr
        exact K.longEdge_real_le β 0 ℓ w

/-- Lemma 3.2 as a root bound: `P(X(c, ℓ, F)ᶜ) < ε` once the right side is below `ε^{d 2^d}`. -/
theorem faces_root_bound [NeZero d] {K : Kernel d} (hK : K.SignInvariant) (β : ℝ) {m ℓ w : ℕ}
    (hmℓ : m ≤ ℓ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : (K.law β).real (SeedInfinite 0 m)ᶜ + (2 * ℓ + 1) ^ d * (max β 0 * K.tail w) <
      ε ^ (d * 2 ^ d))
    (c : Vertex d) (f : FaceIndex d) :
    (K.law β).real (Reaches c m ℓ w (ThickFace c ℓ w f))ᶜ < ε := by
  have hN : d * 2 ^ d ≠ 0 := Nat.mul_ne_zero (NeZero.ne d) (by positivity)
  exact (pow_lt_pow_iff_left₀ measureReal_nonneg hε hN).mp
    ((faces_bound hK β hmℓ c f).trans_lt h)

end Kernel

end Peapods.LongRange
