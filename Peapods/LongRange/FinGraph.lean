import Peapods.LongRange.Scales
import OAI.Probability.CriticalZ3.ShellProbability

/-!
# Finite graphs on `ℤ^d` with independent long-range bits

The finite graphs of Section 2: a finite vertex set and a finite set of edges among its pairs. As in
OpenAI's `LatticeGraph`, the bits are all pairs of `ℤ^d` under an arbitrary product law, and
connections in `G` use only the edges of `G`. The failure comparison (Corollary 2.2) is OpenAI's
`HyperedgeComparison.failure_comparison` through the two-point hypergraph of `G`.
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical OAI InfiniteConditioning

variable {d : ℕ}

/-- A finite graph: vertices, and edges whose endpoints are vertices. -/
structure FinGraph (d : ℕ) where
  vertices : Finset (Vertex d)
  edges : Finset (Pair d)
  mem : ∀ e ∈ edges, ∀ v ∈ e, v ∈ vertices

namespace FinGraph

variable (G : FinGraph d)

/-- An open edge of `G` between distinct vertices. -/
def Adj (ω : Config d) (x y : Vertex d) : Prop := s(x, y) ∈ G.edges ∧ x ≠ y ∧ ω s(x, y) = true

def Conn (ω : Config d) (x y : Vertex d) : Prop := Relation.ReflTransGen (G.Adj ω) x y

def Meets (ω : Config d) (o : Vertex d) (T : Set (Vertex d)) : Prop := ∃ y ∈ T, G.Conn ω o y

variable {G}

theorem adj_symm {ω : Config d} {x y : Vertex d} (h : G.Adj ω x y) : G.Adj ω y x := by
  obtain ⟨he, hne, ho⟩ := h
  refine ⟨?_, hne.symm, ?_⟩
  · rw [Sym2.eq_swap]; exact he
  · rw [Sym2.eq_swap]; exact ho

theorem adj_mem {ω : Config d} {x y : Vertex d} (h : G.Adj ω x y) :
    x ∈ G.vertices ∧ y ∈ G.vertices :=
  ⟨G.mem _ h.1 x (Sym2.mem_mk_left x y), G.mem _ h.1 y (Sym2.mem_mk_right x y)⟩

theorem conn_symm {ω : Config d} {x y : Vertex d} (h : G.Conn ω x y) : G.Conn ω y x := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (adj_symm hab) ih

theorem conn_trans {ω : Config d} {x y z : Vertex d} (h₁ : G.Conn ω x y) (h₂ : G.Conn ω y z) :
    G.Conn ω x z := Relation.ReflTransGen.trans h₁ h₂

theorem conn_mem {ω : Config d} {x y : Vertex d} (h : G.Conn ω x y) (hx : x ∈ G.vertices) :
    y ∈ G.vertices := by
  cases h with
  | refl => exact hx
  | tail _ hab => exact (adj_mem hab).2

theorem adj_mono {ω ω' : Config d} (h : ω ≤ ω') {x y : Vertex d} (hxy : G.Adj ω x y) :
    G.Adj ω' x y :=
  ⟨hxy.1, hxy.2.1, Bool.eq_true_of_true_le (hxy.2.2 ▸ h s(x, y))⟩

theorem conn_mono {ω ω' : Config d} (h : ω ≤ ω') {x y : Vertex d} (hxy : G.Conn ω x y) :
    G.Conn ω' x y :=
  Relation.ReflTransGen.mono (fun _ _ hab => adj_mono h hab) x y hxy

theorem meets_mono (o : Vertex d) (T : Set (Vertex d)) :
    Monotone (fun ω => G.Meets ω o T) := by
  intro ω ω' h ⟨y, hy, hc⟩
  exact ⟨y, hy, conn_mono h hc⟩

theorem adj_congr {ω ω' : Config d} (h : ∀ e ∈ G.edges, ω' e = ω e) (x y : Vertex d) :
    G.Adj ω' x y ↔ G.Adj ω x y := by
  constructor <;> rintro ⟨he, hne, ho⟩
  · exact ⟨he, hne, (h _ he) ▸ ho⟩
  · exact ⟨he, hne, (h _ he).symm ▸ ho⟩

theorem conn_congr {ω ω' : Config d} (h : ∀ e ∈ G.edges, ω' e = ω e) (x y : Vertex d) :
    G.Conn ω' x y ↔ G.Conn ω x y := by
  have he : G.Adj ω' = G.Adj ω := by
    funext a b; exact propext (adj_congr h a b)
  simp only [Conn, he]

theorem meets_congr {ω ω' : Config d} (h : ∀ e ∈ G.edges, ω' e = ω e) (o : Vertex d)
    (T : Set (Vertex d)) : G.Meets ω' o T ↔ G.Meets ω o T :=
  exists_congr (fun y => and_congr_right (fun _ => conn_congr h o y))

theorem measurableSet_meets (o : Vertex d) (T : Set (Vertex d)) :
    MeasurableSet {ω : Config d | G.Meets ω o T} :=
  ProductCylinder.measurableSet_determined G.edges _ (fun _ _ h => meets_congr h o T)

/-! ### The two-point hypergraph and the failure comparison -/

variable (G)

/-- The hypergraph of `G` on its vertex subtype: each edge is the set of its endpoints. -/
def hyper : HyperedgeComparison.Hypergraph G.vertices G.edges := fun e => {x | x.1 ∈ e.1}

variable {G}

theorem conn_lift {ω : Config d} (x : G.vertices) {c : Vertex d}
    (h : G.Conn ω x.1 c) (hc : c ∈ G.vertices) :
    HyperedgeComparison.Connected G.hyper (fun e => ω e.1) ∅ x ⟨c, hc⟩ := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    exact (ih (adj_mem hbc).1).tail
      ⟨⟨s(b, c), hbc.1⟩, hbc.2.2, Set.disjoint_empty _, Sym2.mem_mk_left b c, Sym2.mem_mk_right b c⟩

theorem conn_iff_hyper (ω : Config d) (x y : G.vertices) :
    G.Conn ω x.1 y.1 ↔ HyperedgeComparison.Connected G.hyper (fun e => ω e.1) ∅ x y := by
  constructor
  · intro h
    exact conn_lift x h y.2
  · intro h
    induction h with
    | refl => exact .refl
    | @tail a b _ hab ih =>
      obtain ⟨e, ho, _, ha, hb⟩ := hab
      by_cases hne : a.1 = b.1
      · rw [← hne]; exact ih
      · have he : e.1 = s(a.1, b.1) := (Sym2.mem_and_mem_iff hne).mp ⟨ha, hb⟩
        exact ih.tail ⟨he ▸ e.2, hne, he ▸ ho⟩

theorem meets_iff_hyper (ω : Config d) (o : G.vertices) (T : Set (Vertex d)) :
    G.Meets ω o.1 T ↔
      HyperedgeComparison.Meets G.hyper (fun e => ω e.1) ∅ o {y | y.1 ∈ T} := by
  constructor
  · rintro ⟨y, hy, hc⟩
    have hyv := conn_mem hc o.2
    exact ⟨⟨y, hyv⟩, hy, (conn_iff_hyper ω o ⟨y, hyv⟩).mp hc⟩
  · rintro ⟨y, hy, hc⟩
    exact ⟨y.1, hy, (conn_iff_hyper ω o y).mpr hc⟩

/-- Any observable of the connections of `G` is a finite cylinder on the edges of `G`. -/
theorem observable_probability (p : Pair d → Set.Icc (0 : ℝ) 1)
    (φ : (G.vertices → Set (Vertex d) → Prop) → Prop) :
    (ProductCylinder.law p).real {ω | φ (fun o T => G.Meets ω o.1 T)} =
      HyperedgeComparison.eventProb (fun e : G.edges => p e.1)
        (fun ω => φ (fun o T => HyperedgeComparison.Meets G.hyper ω ∅ o {y | y.1 ∈ T})) := by
  have hd : ∀ ω ω' : Config d, (∀ e ∈ G.edges, ω' e = ω e) →
      (φ (fun o T => G.Meets ω' o.1 T) ↔ φ (fun o T => G.Meets ω o.1 T)) := by
    intro ω ω' he
    have hm : (fun (o : G.vertices) T => G.Meets ω' o.1 T) = fun o T => G.Meets ω o.1 T := by
      funext o T; exact propext (meets_congr he o.1 T)
    rw [hm]
  rw [Measure.real_def, ProductCylinder.probability_determined G.edges p
    {ω : Config d | φ (fun o T => G.Meets ω o.1 T)} hd,
    HyperedgeComparison.eventProb_eq_real]
  congr 1
  congr 1
  ext ξ
  have he : (fun e : G.edges => ProductCylinder.extend G.edges ξ e.1) = ξ := by
    funext e; simp [ProductCylinder.extend, e.2]
  have hm : (fun (o : G.vertices) T => G.Meets (ProductCylinder.extend G.edges ξ) o.1 T) =
      fun o T => HyperedgeComparison.Meets G.hyper ξ ∅ o {y | y.1 ∈ T} := by
    funext o T
    apply propext
    rw [meets_iff_hyper, he]
  simp only [Set.mem_ofPred_eq, hm]

theorem meets_probability (p : Pair d → Set.Icc (0 : ℝ) 1) (o : G.vertices) (T : Set (Vertex d)) :
    (ProductCylinder.law p).real {ω | G.Meets ω o.1 T} =
      HyperedgeComparison.eventProb (fun e : G.edges => p e.1)
        (fun ω => HyperedgeComparison.Meets G.hyper ω ∅ o {y | y.1 ∈ T}) :=
  observable_probability p (fun M => M o T)

/-- Corollary 2.2 in `G` under any product law. -/
theorem failure_comparison (p : Pair d → Set.Icc (0 : ℝ) 1) {o : Vertex d} (ho : o ∈ G.vertices)
    (A T : Set (Vertex d)) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ a ∈ A, a ∈ G.vertices →
      1 - b ≤ (ProductCylinder.law p).real {ω | G.Meets ω a T}) :
    (ProductCylinder.law p).real {ω | G.Meets ω o A ∧ ¬G.Meets ω o T} ≤ b := by
  have h := observable_probability p (fun M => M ⟨o, ho⟩ A ∧ ¬M ⟨o, ho⟩ T)
  simp only at h
  rw [h]
  apply HyperedgeComparison.failure_comparison _ _ _ _ _ b hb0
  intro a ha
  rw [← meets_probability]
  exact hb a.1 ha a.2

/-! ### Good relays (Step 4 of Lemma 4.1) -/

variable (G)

/-- Vertices from which `T` is reached with conditional probability more than `1 - τ`, given the
bits of `J`. -/
noncomputable def goodRelays (p : Pair d → Set.Icc (0 : ℝ) 1) (J : Finset (Pair d))
    (T : Set (Vertex d)) (τ : ℝ) (ω : Config d) : Set (Vertex d) :=
  {v | v ∈ G.vertices ∧ 1 - τ < conditionalProbability p J {ω | G.Meets ω v T} ω}

variable {G}

theorem goodRelays_determined (p : Pair d → Set.Icc (0 : ℝ) 1) (J : Finset (Pair d))
    (T : Set (Vertex d)) (τ : ℝ) : ProductCylinder.DeterminedBy J (G.goodRelays p J T τ) := by
  intro ω ω' h
  ext v
  simp only [goodRelays, Set.mem_ofPred_eq, conditionalProbability_determined p J _ ω ω' h]

/-- Conditionally on `J`, the good relays reach `T` except with probability `τ`. -/
theorem random_relay_failure (p : Pair d → Set.Icc (0 : ℝ) 1) (J : Finset (Pair d))
    {o : Vertex d} (ho : o ∈ G.vertices) (T : Set (Vertex d)) {τ : ℝ} (hτ : 0 ≤ τ) :
    (ProductCylinder.law p).real
      {ω | G.Meets ω o (G.goodRelays p J T τ ω) ∧ ¬G.Meets ω o T} ≤ τ := by
  let A (a : J → Bool) : Set (Config d) :=
    {ω | G.Meets ω o (G.goodRelays p J T τ (ProductCylinder.extend J a)) ∧ ¬G.Meets ω o T}
  have he : {ω | G.Meets ω o (G.goodRelays p J T τ ω) ∧ ¬G.Meets ω o T} =
      {ω | ω ∈ A (J.restrict ω)} := by
    ext ω
    simp only [A, Set.mem_ofPred_eq,
      ProductCylinder.determinedBy_eq_extend (goodRelays_determined p J T τ) ω]
  rw [he]
  apply select_probability_le p J A
  · intro a
    exact (measurableSet_meets _ _).inter (measurableSet_meets _ _).compl
  · intro a
    apply failure_comparison _ ho _ T hτ
    intro v hv _
    exact hv.2.le

/-! ### Open boxes are connected -/

theorem dist_update_lt {a b : Vertex d} {i : Fin d} (hi : a i ≠ b i) :
    ∑ j, (Function.update a i (a i + if a i < b i then 1 else -1) j - b j).natAbs <
      ∑ j, (a j - b j).natAbs := by
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      split_ifs <;> omega
    · simp [Function.update_of_ne hj]
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    simp only [Function.update_self]
    split_ifs <;> omega

/-- A cube is connected when every unit step between two of its points is an open edge. -/
theorem conn_of_box (c : Vertex d) (m : ℕ) {ω : Config d}
    (hstep : ∀ x ∈ cube c m, ∀ (i : Fin d) (t : ℤ), (t = 1 ∨ t = -1) →
      Function.update x i (x i + t) ∈ cube c m → G.Adj ω x (Function.update x i (x i + t))) :
    ∀ a ∈ cube c m, ∀ b ∈ cube c m, G.Conn ω a b := by
  intro a ha b hb
  induction hn : ∑ j, (a j - b j).natAbs using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    by_cases hab : a = b
    · subst hab; exact .refl
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    set t : ℤ := if a i < b i then 1 else -1 with ht
    set a' := Function.update a i (a i + t)
    have ha' : a' ∈ cube c m := by
      rw [mem_cube] at ha hb ⊢
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [a', Function.update_self, ht]
        have := ha j
        have := hb j
        split_ifs <;> omega
      · simp only [a', Function.update_of_ne hj]
        exact ha j
    have ht1 : t = 1 ∨ t = -1 := by simp only [ht]; split_ifs <;> simp
    exact Relation.ReflTransGen.head (hstep a ha i t ht1 ha')
      (ih _ (hn ▸ dist_update_lt hi) a' ha' rfl)

end FinGraph

end Peapods.LongRange
