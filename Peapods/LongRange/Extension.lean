import Peapods.LongRange.Trials

/-!
# The extension lemma (Lemma 4.1)

Let `G` be a finite graph with a product law `p`, `D` a rectangle of at most `(41r+1)^d` points with
`(F_q(D))`, `B` a rectangle with `B^{(R)} ⊆ D`, `o ∉ B^{(R)}`, and `T` a vertex set, such that
(E2) every edge `{x, z}` of `G` with `z ∈ B^{(R)}` and `x ∉ D` is dominated by `edgeProb q`, and
(E3) every `u ∈ B^{(R)}` has a face radius `ℓ` and a face `F ⊆ T` with `Λ_{ℓ+w}(u) ⊆ D`. Then
`P(o ↔ B, o ↮ T) < η`. Steps 1–4 are `exists_quiet_layer`, `meets_low_weight_subset`,
`longEntry_le` (budget `η/8 + η/8`), `heavy_failure` (`η/4 + η/4`) and `random_relay_failure`
(`τ < η/4`). Ported from OpenAI's `LatticeGraph.extension_bound`.
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical OAI InfiniteConditioning

variable {d : ℕ}

namespace FinGraph

/-- Lemma 4.1. -/
theorem extension [NeZero d] {K : Kernel d} {β : ℝ} (s : ScaleData K β)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0))
    (G : FinGraph d) (p : Pair d → Set.Icc (0 : ℝ) 1) (D B : Box d)
    (hDcard : D.vertices.card ≤ (41 * s.r + 1) ^ d)
    (hDV : ∀ x, D.Contains x → x ∈ G.vertices) (hF : FqHolds K G p s.q D)
    (hBR : ∀ x, (B.expand s.R).Contains x → D.Contains x)
    {o : Vertex d} (hov : o ∈ G.vertices) (hoR : ¬(B.expand s.R).Contains o)
    (T : Set (Vertex d))
    (hE2 : ∀ x z, s(x, z) ∈ G.edges → (B.expand s.R).Contains z → ¬D.Contains x →
      (p s(x, z) : ℝ) ≤ K.edgeProb s.q s(x, z))
    (hE3 : ∀ u, (B.expand s.R).Contains u →
      ∃ ℓ ∈ ({2 * s.r, 2 * s.r + 1, 10 * s.r - s.w} : Finset ℕ),
        ∃ f : FaceIndex d, (∀ x ∈ cube u (ℓ + s.w), D.Contains x) ∧ ThickFace u ℓ s.w f ⊆ T) :
    (ProductCylinder.law p).real {ω | G.Meets ω o {x | B.Contains x} ∧ ¬G.Meets ω o T} <
      s.η := by
  have hβ : 0 < β := by linarith [s.q_half, s.q_lt]
  have hq0 : 0 < s.q := by linarith [s.q_half]
  have hη := s.η_range.1
  have hτ := s.τ_range.1
  set L := K.extensionL β s.m s.trials
  -- (E2) and `(F_q(D))`: every edge into `B^{(R)}` is dominated by `edgeProb q`
  have hcrossR : ∀ x z, s(x, z) ∈ G.edges → x ≠ z → (B.expand s.R).Contains z →
      (p s(x, z) : ℝ) ≤ K.edgeProb s.q s(x, z) := by
    intro x z he hxz hz
    by_cases hx : D.Contains x
    · exact le_of_eq (congrArg Subtype.val (hF x z hx (hBR z hz) hxz).2)
    · exact hE2 x z he hz hx
  have hw0 : 0 < s.w := lt_of_lt_of_le s.m_pos s.m_le_w
  have hwR : (0 : ℝ) < s.w := by exact_mod_cast hw0
  have hRm : (s.m : ℝ) + 8 * Real.exp L * s.w / s.η ≤ s.R := by
    have := s.R_large
    linarith
  have hgap : 0 < 8 * Real.exp L * s.w / s.η := by positivity
  have hmR : s.m < s.R := by
    have : (s.m : ℝ) < s.R := by linarith
    exact_mod_cast this
  -- Step 1: a quiet layer
  obtain ⟨j, hmj, hjR, hlayer⟩ := exists_quiet_layer (G := G) p B hov hw0 hmR hoR L
    (fun j hj x z he hx hz => (hcrossR x z he (fun h => hx (h ▸ hz))
      (B.expand_mono hj.le hz)).trans_lt (K.edgeProb_lt_one _ _))
  have hlayer' : (ProductCylinder.law p).real (G.LayerEvent p B j s.w L o) ≤ s.η / 8 := by
    refine hlayer.trans ?_
    have hpos : (0 : ℝ) < s.R - s.m := by linarith
    rw [div_le_iff₀ hpos]
    have h8 : 8 * Real.exp L * s.w / s.η * (s.η / 8) = Real.exp L * s.w := by field_simp
    nlinarith
  have hlong : (ProductCylinder.law p).real (G.LongEntry B s.R s.w) ≤ s.η / 8 := by
    refine (longEntry_le K p s.q B s.R s.w (fun z x hz hxz he => by
      rw [Sym2.eq_swap] at he ⊢; exact hcrossR x z he hxz hz)).trans ?_
    have hcard : ((B.expand s.R).vertices.card : ℝ) ≤ (41 * s.r + 1 : ℝ) ^ d := by
      have h1 : (B.expand s.R).vertices ⊆ D.vertices := by
        intro x hx
        exact (Box.mem_vertices _ _).mpr (hBR x ((Box.mem_vertices _ _).mp hx))
      have h2 := (Finset.card_le_card h1).trans hDcard
      exact_mod_cast h2
    rw [max_eq_left hq0.le]
    have hT := K.tail_nonneg s.w
    calc ((B.expand s.R).vertices.card : ℝ) * (s.q * K.tail s.w)
        ≤ (41 * s.r + 1 : ℝ) ^ d * (β * K.tail s.w) :=
          mul_le_mul hcard (mul_le_mul_of_nonneg_right s.q_lt.le hT)
            (mul_nonneg hq0.le hT) (by positivity)
      _ = β * (41 * s.r + 1) ^ d * K.tail s.w := by ring
      _ ≤ s.η / 8 := s.tail_relay
  have hlow : (ProductCylinder.law p).real
      {ω | G.Meets ω o {x | B.Contains x} ∧ G.weight p (B.expand j) ω o < L} ≤ s.η / 4 := by
    calc _ ≤ (ProductCylinder.law p).real (G.LayerEvent p B j s.w L o ∪ G.LongEntry B s.R s.w) :=
          measureReal_mono (meets_low_weight_subset p B hjR hoR L)
      _ ≤ (ProductCylinder.law p).real (G.LayerEvent p B j s.w L o) +
          (ProductCylinder.law p).real (G.LongEntry B s.R s.w) := measureReal_union_le _ _
      _ ≤ s.η / 4 := by linarith
  -- Steps 2–3: heavy layers reach a good relay
  set C := B.expand j
  have hCR : ∀ x, C.Contains x → (B.expand s.R).Contains x := fun x h => B.expand_mono hjR.le h
  have hwC : ∀ i, C.lower i + s.m ≤ C.upper i - s.m := by
    intro i
    have h : B.lower i ≤ B.upper i := B.ordered i
    change B.lower i - j + s.m ≤ B.upper i + j - s.m
    have : (s.m : ℤ) ≤ j := by exact_mod_cast hmj
    omega
  have hoC : ¬C.Contains o := fun h => hoR (hCR o h)
  have hheavy := heavy_failure s hK hPos hF hDV (fun x h => hBR x (hCR x h)) hwC hoC T
    (fun u hu => hE3 u (hCR u hu)) (fun x z he hxz hz => hcrossR x z he hxz (hCR z hz))
  -- Step 4: good relays reach `T`
  have hrelay := random_relay_failure (G := G) p (G.insideBits C) hov T hτ.le
  have hcontain : {ω | G.Meets ω o {x | B.Contains x} ∧ ¬G.Meets ω o T} ⊆
      ({ω | G.Meets ω o {x | B.Contains x} ∧ G.weight p C ω o < L} ∪
        {ω | L ≤ G.weight p C ω o ∧ ¬G.Meets ω o (G.goodRelays p (G.insideBits C) T s.τ ω)}) ∪
      {ω | G.Meets ω o (G.goodRelays p (G.insideBits C) T s.τ ω) ∧ ¬G.Meets ω o T} := by
    intro ω hω
    by_cases hW : G.weight p C ω o < L
    · exact Or.inl (Or.inl ⟨hω.1, hW⟩)
    · by_cases hg : G.Meets ω o (G.goodRelays p (G.insideBits C) T s.τ ω)
      · exact Or.inr ⟨hg, hω.2⟩
      · exact Or.inl (Or.inr ⟨le_of_not_gt hW, hg⟩)
  have hsum := (measureReal_mono (μ := ProductCylinder.law p) hcontain).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
  have hb1 := s.trials_budget
  have hb2 := s.trial_budget
  have hb3 := s.relay_budget
  calc _ ≤ _ := hsum
    _ ≤ s.η / 4 + (4 / (s.trials * K.seedRho β s.m) + 2 * s.γ / s.τ) + s.τ :=
        add_le_add (add_le_add hlow hheavy) hrelay
    _ < s.η := by linarith

end FinGraph

end Peapods.LongRange
