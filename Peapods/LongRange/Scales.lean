import Peapods.LongRange.Faces
import OAI.Probability.CriticalZ3.Scales

/-!
# The choice of scales (Lemma 3.3)

At a percolating `β > 0`, under (Sym) and (Tail), the constants (S1)–(S7) of the paper exist. The
order of choices is that of the paper: the error budgets, then the seed radius `m`, then the trial
count, then the thickness `w` from the tail condition, then `R` and `r`, and finally a parameter
`q ∈ (β/2, β)` at which every face event of the three radii `2r`, `2r + 1`, `10r - w` has probability
more than `1 - γ`. Ported from OpenAI's `CriticalZ3.Scales` (`ScaleData`, `exists_scales`), with the
failure-budget constant `52` replaced by `4 (d + 10)` and the face estimate taken from Lemma 3.2;
(S1) is fixed by taking `f = contourError`, for which OpenAI proves the contour budget.
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical OAI Filter Topology

variable {d : ℕ}

/-- (S2) for any constant `C ≥ 1`; OpenAI's `CriticalScales.error_budgets` is the case `C = 52`. -/
theorem error_budgets {f C : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hC : 1 ≤ C) :
    ∃ δ η τ γ : ℝ, δ ∈ Set.Ioo 0 1 ∧ η ∈ Set.Ioo 0 1 ∧ τ ∈ Set.Ioo 0 1 ∧ γ ∈ Set.Ioo 0 1 ∧
      δ + C * η / δ < f ∧ τ < η / 4 ∧ γ < δ ∧ 2 * γ / τ < η / 4 := by
  have hC0 : 0 < C := by linarith
  let δ := f / 2
  let η := δ * f / (4 * C)
  let τ := η / 8
  let γ := min (δ / 2) (τ * η / 16)
  have hd0 : 0 < δ := by positivity
  have hd1 : δ < 1 := by dsimp [δ]; linarith
  have he0 : 0 < η := by positivity
  have he1 : η < 1 := by
    have h1 : δ * f < 1 := by nlinarith
    have h2 : δ * f < 4 * C := by linarith
    exact (div_lt_one (by positivity)).mpr h2
  have ht0 : 0 < τ := by positivity
  have ht1 : τ < 1 := by dsimp [τ]; linarith
  have hg0 : 0 < γ := lt_min (by positivity) (by positivity)
  have hgd : γ ≤ δ / 2 := min_le_left _ _
  have hge : γ ≤ τ * η / 16 := min_le_right _ _
  refine ⟨δ, η, τ, γ, ⟨hd0, hd1⟩, ⟨he0, he1⟩, ⟨ht0, ht1⟩, ⟨hg0, by linarith⟩, ?_, ?_, ?_, ?_⟩
  · have heq : C * η / δ = f / 4 := by dsimp [η]; field_simp
    rw [heq]
    dsimp [δ]
    linarith
  · dsimp [τ]; linarith
  · linarith
  · apply (div_lt_iff₀ ht0).mpr
    nlinarith

namespace Kernel

variable (K : Kernel d)

/-- (Tail): `liminf_{n → ∞} n^d T(n) = 0`, stated as: `n^d T(n)` is frequently below every
`ε > 0`. The two forms are equivalent because `n^d T(n) ≥ 0`. -/
def TailSmall : Prop := ∀ ε > 0, ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ d * K.tail n < ε

/-- The pairs internal to `Λ_m(c)` with `J > 0`. -/
noncomputable def seedPairs (c : Vertex d) (m : ℕ) : Finset (Pair d) :=
  (cubeFinset c m).sym2.filter (fun e => ¬ e.IsDiag ∧ 0 < K.pairWeight e)

/-- `ρ₀ = ∏ (1 - e^{-(β/2) J(e)})` over the pairs internal to `Λ_m` with `J > 0` (S4). -/
noncomputable def seedRho (β : ℝ) (m : ℕ) : ℝ :=
  ∏ e ∈ K.seedPairs 0 m, (1 - Real.exp (-(β / 2 * K.pairWeight e)))

theorem seedRho_pos {β : ℝ} (hβ : 0 < β) (m : ℕ) : 0 < K.seedRho β m := by
  apply Finset.prod_pos
  intro e he
  have hw := (Finset.mem_filter.mp he).2.2
  have : Real.exp (-(β / 2 * K.pairWeight e)) < 1 :=
    Real.exp_lt_one_iff.mpr (by have := mul_pos (half_pos hβ) hw; linarith)
  linarith

/-- `A = β ‖J‖₁` (S4). -/
noncomputable def massA (β : ℝ) : ℝ := β * ∑' z, K.J z

/-- `c_A = (1 - e^{-A}) / A` (S4). -/
noncomputable def massC (β : ℝ) : ℝ := (1 - Real.exp (-K.massA β)) / K.massA β

/-- `L = K (4m + 3)^d / c_A` (S4), where `K` is the number of trials. -/
noncomputable def extensionL (β : ℝ) (m trials : ℕ) : ℝ :=
  trials * (4 * m + 3 : ℝ) ^ d / K.massC β

theorem norm_pos_of_theta {β : ℝ} (hθ : 0 < K.theta β) : 0 < ∑' z, K.J z := by
  rcases (tsum_nonneg K.nonneg).lt_or_eq with h | h
  · exact h
  · exact absurd (K.theta_eq_zero (by rw [← h, mul_zero]; exact one_pos)) (ne_of_gt hθ)

/-- A percolating `β` is positive: for `β ≤ 0` every pair is closed. -/
theorem pos_of_theta {β : ℝ} (hθ : 0 < K.theta β) : 0 < β := by
  by_contra h
  push Not at h
  exact absurd (K.theta_eq_zero (by rw [max_eq_right h, zero_mul]; exact one_pos)) (ne_of_gt hθ)

theorem massA_pos {β : ℝ} (hβ : 0 < β) (hθ : 0 < K.theta β) : 0 < K.massA β :=
  mul_pos hβ (K.norm_pos_of_theta hθ)

theorem massC_pos {β : ℝ} (hβ : 0 < β) (hθ : 0 < K.theta β) : 0 < K.massC β := by
  have hA := K.massA_pos hβ hθ
  have : Real.exp (-K.massA β) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact div_pos (by linarith) hA

theorem continuous_edgeProb : Continuous (fun β : ℝ => K.edgeProb β) := by
  apply continuous_pi
  intro e
  apply continuous_induced_rng.mpr
  change Continuous (fun β : ℝ => 1 - Real.exp (-(max β 0 * K.pairWeight e)))
  fun_prop

/-- Probabilities of events determined by finitely many bits are continuous in `β`. -/
theorem continuous_probability (J : Finset (Pair d)) (A : Set (Config d))
    (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    Continuous (fun β : ℝ => (K.law β).real A) :=
  (ProductCylinder.continuous_probability J A hA).comp K.continuous_edgeProb

end Kernel

/-- The constants of Lemma 3.3 at a percolating `β`. The thickness `w` is a field; the radii of
the face events are `2r`, `2r + 1` and `10r - w`. -/
structure ScaleData (K : Kernel d) (β : ℝ) where
  δ : ℝ
  η : ℝ
  τ : ℝ
  γ : ℝ
  δ_range : δ ∈ Set.Ioo 0 1
  η_range : η ∈ Set.Ioo 0 1
  τ_range : τ ∈ Set.Ioo 0 1
  γ_range : γ ∈ Set.Ioo 0 1
  /-- (S1) and (S2), with `f = contourError`. -/
  failure_budget : δ + 4 * ((d : ℝ) + 10) * η / δ < CriticalScales.contourError
  relay_budget : τ < η / 4
  γδ : γ < δ
  trial_budget : 2 * γ / τ < η / 4
  m : ℕ
  trials : ℕ
  w : ℕ
  R : ℕ
  r : ℕ
  m_pos : 0 < m
  trials_pos : 0 < trials
  /-- (S3) -/
  seed : (K.law β).real (SeedInfinite 0 m)ᶜ < (γ / 2) ^ (d * 2 ^ d) / 2
  /-- (S4) -/
  trials_budget : 4 / (trials * K.seedRho β m) < η / 4
  /-- (S5) -/
  tail_faces : β * (41 * r + 1) ^ d * K.tail w ≤ (γ / 2) ^ (d * 2 ^ d) / 2
  tail_relay : β * (41 * r + 1) ^ d * K.tail w ≤ η / 8
  /-- (S6) -/
  m_le_w : m ≤ w
  R_large : (m : ℝ) + w + 8 * Real.exp (K.extensionL β m trials) * w / η ≤ R
  r_large : 4 * (d + 12) * (R + w + 1) < r
  r_mw : m + w < r
  /-- (S7) -/
  q : ℝ
  q_half : β / 2 < q
  q_lt : q < β
  faces : ∀ ℓ ∈ ({2 * r, 2 * r + 1, 10 * r - w} : Finset ℕ), ∀ c f,
    1 - γ < (K.law q).real (Reaches c m ℓ w (ThickFace c ℓ w f))

/-- The three face radii exceed `m` and satisfy `2ℓ + 1 ≤ 41r + 1`. -/
theorem faceRadius_bounds {m w r ℓ : ℕ} (hr : m + w < r)
    (hℓ : ℓ ∈ ({2 * r, 2 * r + 1, 10 * r - w} : Finset ℕ)) :
    m ≤ ℓ ∧ 2 * ℓ + 1 ≤ 41 * r + 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
  rcases hℓ with rfl | rfl | rfl <;> omega

/-- Lemma 3.3: under (Sym) and (Tail), the scales exist at every percolating `β`. -/
theorem exists_scales [NeZero d] {K : Kernel d} (hK : K.SignInvariant) (hT : K.TailSmall)
    {β : ℝ} (hθ : 0 < K.theta β) : Nonempty (ScaleData K β) := by
  have hβ : 0 < β := K.pos_of_theta hθ
  set N := d * 2 ^ d
  -- (S1), (S2)
  obtain ⟨δ, η, τ, γ, hδ, hη, hτ, hγ, hb, hτb, hγδ, hγb⟩ :=
    error_budgets (C := 4 * ((d : ℝ) + 10)) CriticalScales.contourError_pos
      (CriticalScales.contourError_lt_half.trans (by norm_num))
      (by have : (0 : ℝ) ≤ d := d.cast_nonneg; linarith)
  have hγ2 : 0 < (γ / 2) ^ N / 2 := by have := hγ.1; positivity
  -- (S3)
  obtain ⟨m, hseed, hm⟩ := ((K.seedMiss_tendsto_zero hθ 0).eventually
    (eventually_lt_nhds hγ2)).and (eventually_gt_atTop 0) |>.exists
  -- (S4)
  set ρ := K.seedRho β m
  have hρ : 0 < ρ := K.seedRho_pos hβ m
  obtain ⟨trials, htrials⟩ := exists_nat_gt (16 / (ρ * η))
  have htrials0 : 0 < trials := by
    have : 0 < (trials : ℝ) := (div_pos (by norm_num) (mul_pos hρ hη.1)).trans htrials
    exact_mod_cast this
  have htb : 4 / ((trials : ℝ) * ρ) < η / 4 := by
    have hh := (div_lt_iff₀ (mul_pos hρ hη.1)).mp htrials
    apply (div_lt_iff₀ (mul_pos (by exact_mod_cast htrials0) hρ)).mpr
    nlinarith
  -- (S5), (S6): the thickness `w` from the tail condition
  set L := K.extensionL β m trials
  set a : ℝ := 8 * Real.exp L / η
  have ha : 0 < a := div_pos (by positivity) hη.1
  set C0 : ℝ := 4 * ((d : ℝ) + 12) * (m + a + 5)
  have hC0 : 1 ≤ C0 := by
    have : (1 : ℝ) ≤ 4 * ((d : ℝ) + 12) := by have : (0 : ℝ) ≤ d := d.cast_nonneg; linarith
    have h5 : (1 : ℝ) ≤ m + a + 5 := by have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith
    nlinarith
  set C1 : ℝ := 42 * C0
  have hC1 : 0 < C1 := by positivity
  set ε0 : ℝ := min ((γ / 2) ^ N / 2) (η / 8)
  have hε0 : 0 < ε0 := lt_min hγ2 (by linarith [hη.1])
  obtain ⟨w, hwT, hw⟩ := ((hT (ε0 / (β * C1 ^ d)) (by positivity)).and_eventually
    (eventually_ge_atTop (max m 1))).exists
  have hw1 : 1 ≤ w := le_of_max_le_right hw
  have hmw : m ≤ w := le_of_max_le_left hw
  set R : ℕ := m + w + ⌈a * w⌉₊
  set r : ℕ := 4 * (d + 12) * (R + w + 2)
  have hRw : m + w ≤ R := Nat.le_add_right _ _
  have hr_large : 4 * (d + 12) * (R + w + 1) < r :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
  have hr_mw : m + w < r := by
    have : R + w + 2 ≤ r := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  -- `41 r + 1 ≤ C1 w`
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw1
  have hr_le : (41 * (r : ℝ) + 1) ≤ C1 * w := by
    have hceil : (⌈a * w⌉₊ : ℝ) < a * w + 1 := Nat.ceil_lt_add_one (by positivity)
    have hR : (R : ℝ) ≤ (m + a + 2) * w := by
      have : (R : ℝ) = m + w + ⌈a * w⌉₊ := by simp [R]
      have hm' : (m : ℝ) ≤ m * w := le_mul_of_one_le_right m.cast_nonneg hwR
      nlinarith
    have hr' : (r : ℝ) ≤ C0 * w := by
      have : (r : ℝ) = 4 * ((d : ℝ) + 12) * (R + w + 2) := by simp [r]
      rw [this]
      have h4 : (0 : ℝ) ≤ 4 * ((d : ℝ) + 12) := by positivity
      have : (R : ℝ) + w + 2 ≤ (m + a + 5) * w := by nlinarith
      calc 4 * ((d : ℝ) + 12) * (R + w + 2) ≤ 4 * ((d : ℝ) + 12) * ((m + a + 5) * w) :=
            mul_le_mul_of_nonneg_left this h4
        _ = C0 * w := by ring
    have : (1 : ℝ) ≤ C0 * w := by nlinarith
    calc 41 * (r : ℝ) + 1 ≤ 41 * (C0 * w) + C0 * w := by linarith
      _ = C1 * w := by ring
  have htail : β * (41 * (r : ℝ) + 1) ^ d * K.tail w ≤ ε0 := by
    have hT0 := K.tail_nonneg w
    calc β * (41 * (r : ℝ) + 1) ^ d * K.tail w ≤ β * (C1 * w) ^ d * K.tail w := by
          gcongr
      _ = β * C1 ^ d * ((w : ℝ) ^ d * K.tail w) := by rw [mul_pow]; ring
      _ ≤ β * C1 ^ d * (ε0 / (β * C1 ^ d)) := by gcongr
      _ = ε0 := by field_simp
  have hRlarge : (m : ℝ) + w + 8 * Real.exp L * w / η ≤ R := by
    have : (R : ℝ) = m + w + ⌈a * w⌉₊ := by simp [R]
    rw [this]
    have hc := Nat.le_ceil (a * w)
    have : 8 * Real.exp L * w / η = a * w := by simp only [a]; ring
    linarith
  -- (S7)
  let s : Finset ℕ := {2 * r, 2 * r + 1, 10 * r - w}
  let g : s → ℝ → ℝ := fun ℓ t =>
    (K.law t).real (Reaches 0 m ℓ.1 w (ThickFace 0 ℓ.1 w canonicalFace))ᶜ
  have hg : ∀ ℓ, Continuous (g ℓ) := by
    intro ℓ
    have hmℓ := (faceRadius_bounds hr_mw ℓ.2).1
    exact K.continuous_probability _ _
      (fun ω ω' h => not_congr (reaches_determined hmℓ (thickFace_subset _ _ _ _) ω ω' h))
  have hgβ : ∀ ℓ, g ℓ β < γ := by
    intro ℓ
    obtain ⟨hmℓ, hℓr⟩ := faceRadius_bounds hr_mw ℓ.2
    have hpow : (2 * (ℓ.1 : ℝ) + 1) ^ d ≤ (41 * (r : ℝ) + 1) ^ d :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hℓr) d
    have hsum : (K.law β).real (SeedInfinite 0 m)ᶜ +
        (2 * (ℓ.1 : ℝ) + 1) ^ d * (max β 0 * K.tail w) < (γ / 2) ^ N := by
      have hT0 := K.tail_nonneg w
      have h1 : (2 * (ℓ.1 : ℝ) + 1) ^ d * (max β 0 * K.tail w) ≤ (γ / 2) ^ N / 2 := by
        rw [max_eq_left hβ.le]
        calc (2 * (ℓ.1 : ℝ) + 1) ^ d * (β * K.tail w)
            ≤ (41 * (r : ℝ) + 1) ^ d * (β * K.tail w) := by gcongr
          _ = β * (41 * (r : ℝ) + 1) ^ d * K.tail w := by ring
          _ ≤ (γ / 2) ^ N / 2 := htail.trans (min_le_left _ _)
      linarith
    exact (Kernel.faces_root_bound hK β hmℓ (by linarith [hγ.1]) hsum 0 canonicalFace).trans
      (by linarith [hγ.1])
  obtain ⟨q, hq, hgq⟩ := CriticalZ3.exists_lower_forall hβ g hg hgβ
  refine ⟨⟨δ, η, τ, γ, hδ, hη, hτ, hγ, hb, hτb, hγδ, hγb, m, trials, w, R, r, hm, htrials0,
    hseed, htb, htail.trans (min_le_left _ _), htail.trans (min_le_right _ _), hmw, hRlarge,
    hr_large, hr_mw, q, hq.1, hq.2, ?_⟩⟩
  intro ℓ hℓ c f
  have hmℓ := (faceRadius_bounds hr_mw hℓ).1
  have h := hgq ⟨ℓ, hℓ⟩
  simp only [g] at h
  rw [← Kernel.reaches_face_compl hK q hmℓ c f,
    measureReal_compl (measurableSet_reaches hmℓ (thickFace_subset _ _ _ _)), probReal_univ] at h
  linarith

end Peapods.LongRange
