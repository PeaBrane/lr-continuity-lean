import Peapods.LongRange.Extension
import Peapods.LongRange.Frames

/-!
# The relay lemma (Lemma 5.1)

In any frame `S`, `d + 10` applications of the extension lemma along the thick route carry the
cluster of `o` from `S(Λ_{4r}(0))` to `S(Λ_{4r}((20r+1)e₁))` except with probability `(d + 10)η`
(`FinGraph.relay`). In the coarse frames this is the relay between neighbouring cubes `Q_v`, `Q_x`
(`FinGraph.neighbor_relay`). The hypothesis on the edges leaving `D = Q_v ∪ Q_x` is that they are
dominated by `edgeProb q` at every point of `D`; the paper's (E2°) needs this only on `D°`, and the
exploration supplies the stronger form. Ported from OpenAI's `ScaleData.relay_in_frame`.
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical OAI

variable {d : ℕ}

namespace ScaleData

variable {K : Kernel d} {β : ℝ} (s : ScaleData K β)

theorem R_pos : 0 < s.R := by
  have h := s.R_large
  have hw : (0 : ℝ) < s.w := by exact_mod_cast lt_of_lt_of_le s.m_pos s.m_le_w
  have : 0 ≤ 8 * Real.exp (K.extensionL β s.m s.trials) * s.w / s.η :=
    div_nonneg (by positivity) s.η_range.1.le
  have : (0 : ℝ) < s.R := by linarith [(Nat.cast_nonneg s.m : (0 : ℝ) ≤ s.m)]
  exact_mod_cast this

theorem r_pos : 1 ≤ s.r := by have := s.r_mw; omega

theorem budget : RelayThick.Budget (d := d) s.r s.R s.w := by
  have h := s.r_large
  unfold RelayThick.Budget
  have h' : ((4 * (d + 12) * (s.R + s.w + 1) : ℕ) : ℤ) < s.r := by exact_mod_cast h
  push_cast at h'
  have : (0 : ℤ) ≤ (s.R : ℤ) + s.w := by positivity
  have : (0 : ℤ) ≤ (d : ℤ) := by positivity
  nlinarith

end ScaleData

/-- `(F_q(D))` for a vertex set. -/
def FqOn (K : Kernel d) (G : FinGraph d) (p : Pair d → Set.Icc (0 : ℝ) 1) (q : ℝ)
    (D : Set (Vertex d)) : Prop :=
  ∀ x y, x ∈ D → y ∈ D → x ≠ y → s(x, y) ∈ G.edges ∧ p s(x, y) = K.edgeProb q s(x, y)

namespace FinGraph

/-- Lemma 5.1 in a frame `S`. -/
theorem relay [NeZero d] {K : Kernel d} {β : ℝ} (s : ScaleData K β) (hK : K.SignInvariant)
    (hPos : 0 < K.J (unitAt 0)) (G : FinGraph d) (p : Pair d → Set.Icc (0 : ℝ) 1)
    (S : SignedSymmetry d)
    (hDV : ∀ x, (framedBox S (RelayThick.prism s.r)).Contains x → x ∈ G.vertices)
    (hF : FqHolds K G p s.q (framedBox S (RelayThick.prism s.r)))
    (hE2 : ∀ x z, s(x, z) ∈ G.edges → (framedBox S (RelayThick.prism s.r)).Contains z →
      ¬(framedBox S (RelayThick.prism s.r)).Contains x → (p s(x, z) : ℝ) ≤ K.edgeProb s.q s(x, z))
    {o : Vertex d} (hov : o ∈ G.vertices) (ho : ¬(framedBox S (RelayThick.prism s.r)).Contains o) :
    (ProductCylinder.law p).real
      {ω | G.Meets ω o (cube (S.vertex 0) (4 * s.r)) ∧
        ¬G.Meets ω o (cube (S.vertex (RelayThick.axis (20 * (s.r : ℤ) + 1))) (4 * s.r))} ≤
      ((d : ℝ) + 10) * s.η := by
  set D := framedBox S (RelayThick.prism s.r)
  set Bk : ℕ → Box d := fun k => framedBox S (RelayThick.route s.r s.R s.w k)
  have hR := s.R_pos
  have hb := s.budget
  have hDcard : D.vertices.card ≤ (41 * s.r + 1) ^ d := by
    rw [card_framedBox]; exact card_prism s.r_pos
  -- every expanded route box lies in `D`, with its interfaces
  have hiface (k : ℕ) (hk : k < d + 10) (u : Vertex d) (hu : ((Bk k).expand s.R).Contains u) :
      ∃ ℓ, (ℓ = 2 * s.r ∨ ℓ = 2 * s.r + 1) ∧ ∃ f,
        (∀ x ∈ cube (S.vertex.symm u) (ℓ + s.w), (RelayThick.prism s.r).Contains x) ∧
        ThickFace (S.vertex.symm u) ℓ s.w f ⊆
          {x | (RelayThick.route (d := d) s.r s.R s.w (k + 1)).Contains x} := by
    rw [framedBox_expand, contains_framedBox'] at hu
    exact RelayThick.route_thick_interface hR hb hk hu
  have hBR (k : ℕ) (hk : k < d + 10) : ∀ x, ((Bk k).expand s.R).Contains x → D.Contains x := by
    intro x hx
    obtain ⟨ℓ, _, f, hcube, _⟩ := hiface k hk x hx
    rw [contains_framedBox']
    exact hcube _ (by rw [mem_cube]; intro i; omega)
  let A (k : ℕ) : Set (Config d) := {ω | G.Meets ω o {x | (Bk k).Contains x}}
  have hstep (k : ℕ) (hk : k < d + 10) : (ProductCylinder.law p).real (A k \ A (k + 1)) ≤ s.η := by
    apply le_of_lt
    apply extension s hK hPos G p D (Bk k) hDcard hDV hF (hBR k hk) hov
      (fun h => ho (hBR k hk o h)) {x | (Bk (k + 1)).Contains x}
      (fun x z he hz hx => hE2 x z he (hBR k hk z hz) hx)
    intro u hu
    obtain ⟨ℓ, hℓ, f, hcube, hface⟩ := hiface k hk u hu
    refine ⟨ℓ, ?_, S.faceMap f, ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    · intro x hx
      rw [contains_framedBox']
      apply hcube
      rw [← image_cube, Equiv.apply_symm_apply]
      exact hx
    · intro x hx
      rw [Set.mem_ofPred_eq, contains_framedBox']
      apply hface
      rw [← S.thickFace_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hx
  have hrel := OAI.MeasureTheory.finite_relay_bound (ProductCylinder.law p) A s.η (d + 10) hstep
  push_cast at hrel
  refine le_trans (measureReal_mono ?_) hrel
  rintro ω ⟨⟨y, hy, hc⟩, hn⟩
  refine ⟨⟨y, ?_, hc⟩, fun ⟨z, hz, hcz⟩ => hn ⟨z, ?_, hcz⟩⟩
  · change (Bk 0).Contains y
    rw [contains_framedBox', RelayThick.route_zero]
    have := (image_cube S 0 (4 * s.r) y).mp hy
    rw [mem_cube_iff_abs] at this
    simpa using this
  · have hz' := RelayThick.route_last hb ((contains_framedBox' S _ z).mp hz)
    rw [image_cube, mem_cube_iff_abs]
    push_cast
    exact hz'

/-- Lemma 5.1 between neighbouring coarse cubes `Q_v` and `Q_{v+e}`. -/
theorem neighbor_relay (hd : 2 ≤ d) [NeZero d] {K : Kernel d} {β : ℝ} (s : ScaleData K β)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0)) (G : FinGraph d)
    (p : Pair d → Set.Icc (0 : ℝ) 1) (v : PlanarBoundary.Point) (dir : PlanarBoundary.Direction)
    (hDV : ∀ x, x ∈ Qcube s.r v ∪ Qcube s.r (v + PlanarBoundary.outward dir) → x ∈ G.vertices)
    (hF : FqOn K G p s.q (Qcube s.r v ∪ Qcube s.r (v + PlanarBoundary.outward dir)))
    (hE2 : ∀ x z, s(x, z) ∈ G.edges →
      z ∈ Qcube s.r v ∪ Qcube s.r (v + PlanarBoundary.outward dir) →
      x ∉ Qcube s.r v ∪ Qcube s.r (v + PlanarBoundary.outward dir) →
      (p s(x, z) : ℝ) ≤ K.edgeProb s.q s(x, z))
    {o : Vertex d} (hov : o ∈ G.vertices)
    (ho : o ∉ Qcube s.r v ∪ Qcube s.r (v + PlanarBoundary.outward dir)) :
    (ProductCylinder.law p).real
      {ω | G.Meets ω o (Bcube s.r v) ∧ ¬G.Meets ω o (Bcube s.r (v + PlanarBoundary.outward dir))} ≤
      ((d : ℝ) + 10) * s.η := by
  have hc (y : Vertex d) : (framedBox (frame hd s.r v dir) (RelayThick.prism s.r)).Contains y ↔
      y ∈ Qcube s.r v ∪ Qcube s.r (v + PlanarBoundary.outward dir) :=
    framedPrism_contains hd s.r v dir y
  have h := relay s hK hPos G p (frame hd s.r v dir) (fun x hx => hDV x ((hc x).mp hx))
    (fun x y hx hy hxy => hF x y ((hc x).mp hx) ((hc y).mp hy) hxy)
    (fun x z he hz hx => hE2 x z he ((hc z).mp hz) (fun h => hx ((hc x).mpr h))) hov
    (fun h => ho ((hc o).mp h))
  rwa [frame_zero, frame_axis] at h

end FinGraph

end Peapods.LongRange
