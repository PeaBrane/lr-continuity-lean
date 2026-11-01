import Peapods.LongRange.ExplorationBounds

/-!
# The initial exploration and survival (Lemma 6.1, proof of Theorem 1.1)

The initial history `𝓘` fixes the pairs internal to `Q_0`: open if `J > 0`, closed otherwise; this has
positive probability under `edgeProb q`. The root is good and processed, and its four neighbours are
queued. The promise for a neighbour `v` (Lemma 6.1) uses the face event of (S7) at `u = c_v - w e`,
radius `10r - w`, facing `Q_0`, transported from the canonical frame: on `𝓘` it implies
`0 ↔ B_v` in `Q_0 ∪ Q_v ∪ I_{0v}`, and it only sees pairs with an endpoint in `Q_v`, which `𝓘` does not
prescribe. Every good vertex has `B_v` joined to `0`, so a finite cluster of `0` gives a finite good set,
and the Peierls bound gives `θ(q) > 0` (`scales_percolate`). Ported from OpenAI's
`ExplorationConnectivity` and `ExplorationSurvival`.
-/

namespace Peapods.LongRange

open MeasureTheory ProbabilityTheory Classical OAI InfiniteConditioning

variable {d : ℕ}

/-- `X(u, ℓ, T)` sees only the pairs with an endpoint in `Λ_ℓ(u)` and the other in `Λ_{ℓ+w}(u)`. -/
theorem reaches_of_agree_inner {u : Vertex d} {m ℓ w : ℕ} {T : Set (Vertex d)} (hmℓ : m ≤ ℓ)
    (hT : T ⊆ cube u (ℓ + w)) {ω ω' : Config d}
    (hagree : ∀ a ∈ cube u ℓ, ∀ b ∈ cube u (ℓ + w), a ≠ b → ω' s(a, b) = ω s(a, b))
    (hω : ω ∈ Reaches u m ℓ w T) : ω' ∈ Reaches u m ℓ w T := by
  obtain ⟨x, hx, y, hy, z, hz, hp, ha, hw⟩ := hω
  have hbig (a : Vertex d) (h : a ∈ cube u ℓ) : a ∈ cube u (ℓ + w) :=
    cube_mono u (Nat.le_add_right ℓ w) h
  have hxℓ : x ∈ cube u ℓ := cube_mono u hmℓ hx
  refine ⟨x, hx, y, hy, z, hz,
    stepIn_congr (fun a ha b hb => hagree a ha b (hbig b hb)) hxℓ hp, ⟨ha.1, ?_⟩, hw⟩
  exact (hagree y hy z (hT hz) ha.1).trans ha.2

/-- The pairs with an endpoint in `Λ_ℓ(u)` and the other in `Λ_{ℓ+w}(u)`. -/
noncomputable def innerPairs (u : Vertex d) (ℓ w : ℕ) : Finset (Pair d) :=
  ((cubeFinset u ℓ ×ˢ cubeFinset u (ℓ + w)).filter (fun ab => ab.1 ≠ ab.2)).image
    (fun ab => s(ab.1, ab.2))

theorem mem_innerPairs {u : Vertex d} {ℓ w : ℕ} {e : Pair d} :
    e ∈ innerPairs u ℓ w ↔ ∃ a ∈ cube u ℓ, ∃ b ∈ cube u (ℓ + w), a ≠ b ∧ e = s(a, b) := by
  simp only [innerPairs, Finset.mem_image, Finset.mem_filter, Finset.mem_product, mem_cubeFinset,
    Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl⟩; exact ⟨a, ha, b, hb, hab, rfl⟩
  · rintro ⟨a, ha, b, hb, hab, rfl⟩; exact ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl⟩

theorem reaches_determined_inner {u : Vertex d} {m ℓ w : ℕ} {T : Set (Vertex d)} (hmℓ : m ≤ ℓ)
    (hT : T ⊆ cube u (ℓ + w)) :
    ProductCylinder.DeterminedBy (F := Prop) (innerPairs u ℓ w) (fun ω => ω ∈ Reaches u m ℓ w T) := by
  intro ω ω' h
  have hag (ω ω' : Config d) (h : ∀ e ∈ innerPairs u ℓ w, ω' e = ω e) : ∀ a ∈ cube u ℓ,
      ∀ b ∈ cube u (ℓ + w), a ≠ b → ω' s(a, b) = ω s(a, b) := fun a ha b hb hab =>
    h _ (mem_innerPairs.mpr ⟨a, ha, b, hb, hab, rfl⟩)
  exact propext ⟨reaches_of_agree_inner hmℓ hT (hag ω' ω (fun e he => (h e he).symm)),
    reaches_of_agree_inner hmℓ hT (hag ω ω' h)⟩

namespace FinGraph

/-- An open box is connected when its pairs of distinct points are edges of `G`. -/
theorem box_conn_of_open' [NeZero d] {K : Kernel d} (hK : K.SignInvariant)
    (hPos : 0 < K.J (unitAt 0)) {G : FinGraph d} {v : Vertex d} {m : ℕ}
    (hE : ∀ x ∈ cube v m, ∀ y ∈ cube v m, x ≠ y → s(x, y) ∈ G.edges)
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
  exact ⟨hE x hx y hy hne, hne, hO _ ((K.mk_mem_seedPairs).mpr ⟨hx, hy, hne, hJ⟩)⟩

theorem adj_global {G : FinGraph d} {ω : Config d} {x y : Vertex d} (h : G.Adj ω x y) :
    Peapods.LongRange.Adj ω x y := ⟨h.2.1, h.2.2⟩

theorem conn_global {G : FinGraph d} {ω : Config d} {x y : Vertex d} (h : G.Conn ω x y) :
    Connected ω x y :=
  Relation.ReflTransGen.mono (fun _ _ hab => adj_global hab) x y h

end FinGraph

namespace Coarse

/-- The values of `𝓘`: pairs of `Q_0` with `J > 0` open, the others closed. -/
noncomputable def rootValues (K : Kernel d) : Config d := fun e => decide (0 < K.pairWeight e)

noncomputable def initial (K : Kernel d) (r : ℕ) : Exploration d r where
  history := ⟨rootBits r, rootValues K⟩
  processed := {(0, 0)}
  queue := List.ofFn (fun dir : Direction => (rootPacket r).child (PlanarBoundary.outward dir))
  good := {(0, 0)}
  bad := ∅

@[simp] theorem mem_initial_queue (K : Kernel d) (r : ℕ) (t : Packet d r) :
    t ∈ (initial K r).queue ↔
      ∃ dir : Direction, (rootPacket r).child (PlanarBoundary.outward dir) = t := by
  simp only [initial, List.mem_ofFn]

theorem zero_point_add (x : Point) : ((0, 0) : Point) + x = x := zero_add x

theorem outward_ne_zero (dir : Direction) : PlanarBoundary.outward dir ≠ (0, 0) := by
  have := CriticalZ3.Coarse.neighbor_ne 0 dir
  intro h
  apply this
  rw [zero_add]
  exact h

/-- On `𝓘`, the face event toward `Q_0` joins `0` to `B_v` in `Q_0 ∪ Q_v ∪ I_{0v}`. -/
theorem initial_promise (hd : 2 ≤ d) [NeZero d] {K : Kernel d} {β : ℝ} (sc : ScaleData K β)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0)) (dir : Direction) :
    1 - sc.δ < (ProductCylinder.law (hparam (K.edgeProb sc.q) (initial K sc.r).history)).real
      ((rootPacket sc.r).child (PlanarBoundary.outward dir)).event := by
  set r := sc.r
  set w := sc.w
  set m := sc.m
  set p₀ := K.edgeProb sc.q
  set v := PlanarBoundary.outward dir
  set S := frame hd r (0, 0) dir
  set A : ℤ := 20 * (r : ℤ) + 1
  set u0 : Vertex d := RelayThick.axis (A - w)
  set ℓ' : ℕ := 10 * r - w
  set f : FaceIndex d := (0, fun i => decide (i ≠ 0))
  set u := S.vertex u0
  set F := ThickFace u ℓ' w (S.faceMap f)
  set X := Reaches u m ℓ' w F
  have hrmw := sc.r_mw
  have hw10 : w ≤ 10 * r := by omega
  have hmℓ : m ≤ ℓ' := by omega
  have hℓcast : ((ℓ' : ℕ) : ℤ) = 10 * (r : ℤ) - w := by
    simp only [ℓ']; push_cast [Nat.cast_sub hw10]; ring
  have hS0 : S.vertex 0 = 0 := by rw [frame_zero, center_zero]
  have hSA : S.vertex (RelayThick.axis A) = center r v := by
    rw [frame_axis, zero_point_add]
  have hv0 : v ≠ (0, 0) := outward_ne_zero dir
  -- canonical facts
  have ha : ∀ y ∈ cube u0 ℓ', y ∈ cube (RelayThick.axis A) (10 * r) := by
    intro y hy
    rw [mem_cube] at hy ⊢
    intro i
    have h := hy i
    rw [hℓcast] at h
    simp only [u0, RelayThick.axis] at h ⊢
    push_cast
    split_ifs at h ⊢ <;> constructor <;> omega
  have hb : ∀ y ∈ cube u0 m, y ∈ cube (RelayThick.axis A) (4 * r) := by
    intro y hy
    rw [mem_cube] at hy ⊢
    intro i
    have h := hy i
    simp only [u0, RelayThick.axis] at h ⊢
    push_cast
    split_ifs at h ⊢ <;> constructor <;> omega
  have hc : ∀ y ∈ ThickFace u0 ℓ' w f, y ∈ cube 0 (10 * r) := by
    intro y hy
    rw [mem_cube]
    intro i
    have h := RelayThick.mem_thickFace_coord hy i
    simp only [Pi.zero_apply, zero_sub, zero_add]
    push_cast
    by_cases hi : i = 0
    · subst hi
      have h1 := h.1 rfl
      simp only [f, u0, RelayThick.axis, ite_true, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false] at h1
      rw [hℓcast] at h1
      constructor <;> omega
    · have h1 := h.2 hi
      simp only [f, u0, RelayThick.axis, hi, ite_false, ne_eq, not_false_eq_true, decide_true,
        ite_true] at h1
      rw [hℓcast] at h1
      constructor <;> omega
  -- transported facts
  have ha' : ∀ y ∈ cube u ℓ', y ∈ Qcube r v := by
    intro y hy
    have := ha _ ((image_cube S u0 ℓ' y).mp hy)
    rw [Qcube, ← hSA, image_cube]
    exact this
  have hb' : ∀ y ∈ cube u m, y ∈ Bcube r v := by
    intro y hy
    have := hb _ ((image_cube S u0 m y).mp hy)
    rw [Bcube, ← hSA, image_cube]
    exact this
  have hc' : ∀ y ∈ F, y ∈ Qcube r (0, 0) := by
    intro y hy
    have h1 : S.vertex (S.vertex.symm y) ∈ ThickFace (S.vertex u0) ℓ' w (S.faceMap f) := by
      rwa [Equiv.apply_symm_apply]
    have := hc _ ((S.thickFace_map u0 _ ℓ' w f).mp h1)
    rw [Qcube, center_zero, ← hS0, image_cube]
    exact this
  -- `X` only sees fresh pairs
  have hXdet := reaches_determined_inner (u := u) (m := m) (ℓ := ℓ') (w := w) (T := F) hmℓ
    (thickFace_subset _ _ _ _)
  have hfresh : ∀ e ∈ innerPairs u ℓ' w,
      hparam p₀ (initial K r).history e = p₀ e := by
    intro e he
    apply hparam_fresh
    obtain ⟨a, haℓ, b, _, _, rfl⟩ := mem_innerPairs.mp he
    intro hk
    have hk' : s(a, b) ∈ qBits r (0, 0) := hk
    exact hv0 (Qcube_unique hd r (ha' a haℓ) ((mk_mem_qBits.mp hk').1))
  have hprob : (ProductCylinder.law (hparam p₀ (initial K r).history)).real X =
      (ProductCylinder.law p₀).real X :=
    ProductCylinder.probability_congr_parameters _ _ _ hfresh X hXdet
  have hface : 1 - sc.γ < (ProductCylinder.law p₀).real X :=
    sc.faces ℓ' (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Or.inr rfl))
      u (S.faceMap f)
  -- on `𝓘`, `X` gives the event
  set t := (rootPacket (d := d) r).child v
  have hedges : t.graph.edges = qBits r (0, 0) ∪ qBits r v ∪ link r (0, 0) v := rfl
  have hincl : ∀ ω ∈ pattern (rootBits (d := d) r) (rootValues K), ω ∈ X → ω ∈ t.event := by
    intro ω hω hX
    obtain ⟨x0, hx0, y, hy, z, hz, hpath, hyz, _⟩ := hX
    have hx0y : t.graph.Conn ω x0 y := by
      apply FinGraph.stepIn_conn _ (cube_mono u hmℓ hx0) hpath
      intro a ha2 b hb2 hab
      rw [hedges]
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (mk_mem_qBits.mpr ⟨ha' a ha2, ha' b hb2, hab⟩))
    have hzQ := hc' z hz
    have hyzG : t.graph.Adj ω y z := by
      refine ⟨?_, hyz.1, hyz.2⟩
      rw [hedges]
      exact Finset.mem_union_right _ (mem_link.mpr ⟨z, hzQ, y, ha' y hy, Sym2.eq_swap⟩)
    have hQ0 : Qcube (d := d) r (0, 0) = cube 0 (10 * r) := by rw [Qcube, center_zero]
    have h0z : t.graph.Conn ω 0 z := by
      apply FinGraph.box_conn_of_open' hK hPos (v := 0) (m := 10 * r) _ _ 0
        (by rw [mem_cube]; intro i; simp) z (hQ0 ▸ hzQ)
      · intro a ha2 b hb2 hab
        rw [hedges]
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (mk_mem_qBits.mpr ⟨hQ0 ▸ ha2, hQ0 ▸ hb2, hab⟩))
      · intro e he
        have heroot : e ∈ rootBits (d := d) r := by
          induction e using Sym2.ind with
          | _ a b =>
            obtain ⟨ha2, hb2, hab, _⟩ := (K.mk_mem_seedPairs).mp he
            exact mk_mem_qBits.mpr ⟨hQ0 ▸ ha2, hQ0 ▸ hb2, hab⟩
        rw [hω e heroot]
        simp only [rootValues, decide_eq_true_eq]
        exact ((K.mem_seedPairs).mp he).2.2
    exact ⟨x0, hb' x0 hx0, FinGraph.conn_trans (FinGraph.conn_trans h0z
      (FinGraph.conn_of_adj (FinGraph.adj_symm hyzG))) (FinGraph.conn_symm hx0y)⟩
  have hle : (ProductCylinder.law (hparam p₀ (initial K r).history)).real X ≤
      (ProductCylinder.law (hparam p₀ (initial K r).history)).real t.event := by
    apply OAI.MeasureTheory.finite_measureReal_mono_ae
    filter_upwards [ae_fixed_pattern p₀ (rootBits (d := d) r) (rootValues K)] with ω hω
    exact hincl ω hω
  have hγδ := sc.γδ
  rw [hprob] at hle
  linarith

namespace Exploration

theorem initial_valid (hd : 2 ≤ d) [NeZero d] {K : Kernel d} {β : ℝ} (sc : ScaleData K β)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0)) :
    (initial K sc.r).Valid (K.edgeProb sc.q) sc.δ := by
  constructor
  · exact Finset.mem_singleton_self _
  · change ((List.ofFn (fun dir : Direction =>
      (rootPacket (d := d) sc.r).child (PlanarBoundary.outward dir))).map Packet.vertex).Nodup
    rw [List.map_ofFn]
    exact List.nodup_ofFn.mpr CriticalZ3.Coarse.outward_injective
  · intro t ht
    obtain ⟨dir, rfl⟩ := (mem_initial_queue _ _ _).mp ht
    simpa only [initial, Packet.child, Finset.mem_singleton] using outward_ne_zero dir
  · intro t ht
    obtain ⟨dir, rfl⟩ := (mem_initial_queue _ _ _).mp ht
    exact Finset.mem_singleton_self _
  · intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  · intro t ht
    obtain ⟨dir, rfl⟩ := (mem_initial_queue _ _ _).mp ht
    rw [Packet.child_edges]
    exact Finset.union_subset_union (fun e he => he) (Finset.Subset.refl _)
  · intro t ht
    obtain ⟨dir, rfl⟩ := (mem_initial_queue _ _ _).mp ht
    exact initial_promise hd sc hK hPos dir

theorem initial_colored (K : Kernel d) (r : ℕ) : (initial K r).Colored := by
  constructor
  · simp only [initial, Finset.union_empty]
  · exact Finset.disjoint_empty_right _

theorem initial_closed (K : Kernel d) (r : ℕ) : (initial K r).Closed := by
  intro v hv dir
  have hv0 : v = (0, 0) := Finset.mem_singleton.mp hv
  subst v
  rw [zero_point_add]
  apply Exploration.queue_visited (initial K r)
    (t := (rootPacket r).child (PlanarBoundary.outward dir))
  exact (mem_initial_queue _ _ _).mpr ⟨dir, rfl⟩

theorem initial_covered (K : Kernel d) (r : ℕ) : (initial K r).Covered := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact Or.inl hv
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    obtain ⟨dir, rfl⟩ := (mem_initial_queue _ _ _).mp ht
    exact Or.inr ⟨(0, 0), Finset.mem_singleton_self _, dir, (zero_point_add _).symm⟩

/-! ### Soundness: good vertices are joined to `0` -/

variable {r : ℕ}

def Sound (s : Exploration d r) (ω : Config d) : Prop :=
  ∀ v ∈ s.good, ∃ y ∈ Bcube r v, Connected ω 0 y

theorem accepted_event {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ} {s : Exploration d r}
    (hs : s.Valid p₀ δ) {t : Packet d r} {ts : List (Packet d r)} (hq : s.queue = t :: ts)
    {ω : Config d} (hω : ω ∈ pattern s.history.known s.history.values)
    (ha : s.Accept p₀ δ t ω) : ω ∈ t.event := by
  have hh := (accept_current_iff hs hq ω).mp ha.1
  change s.history.freeze ω ∈ t.event at hh
  simpa only [History.freeze, replace_eq_of_pattern hω] using hh

theorem sound_advance {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ} {s : Exploration d r}
    (hs : s.Valid p₀ δ) {ω : Config d}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω) :
    (s.advance p₀ δ ω).Sound ω := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s p₀ δ ω hq]
  | cons t ts =>
    intro v hv
    simp only [advance, hq] at hv
    split_ifs at hv with ha
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · obtain ⟨y, hy, hpath⟩ := accepted_event hs hq hω ha
        exact ⟨y, hy, FinGraph.conn_global hpath⟩
      · exact hS v hv
    · exact hS v hv

theorem run_pattern (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) {s : Exploration d r}
    {ω : Config d} (hω : ω ∈ pattern s.history.known s.history.values) (n : ℕ) :
    ω ∈ pattern (run p₀ δ n s ω).history.known (run p₀ δ n s ω).history.values := by
  induction n generalizing s with
  | zero => exact hω
  | succ n ih => exact ih (s.history.observe_pattern s.reveal hω)

theorem run_sound (hd : 2 ≤ d) {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ} {s : Exploration d r}
    (hs : s.Valid p₀ δ) {ω : Config d}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω) (n : ℕ) :
    (run p₀ δ n s ω).Sound ω := by
  induction n generalizing s with
  | zero => exact hS
  | succ n ih =>
    exact ih (valid_advance hd hs ω) (s.history.observe_pattern s.reveal hω)
      (sound_advance hs hω hS)

theorem good_finite_of_cluster_finite (hd : 2 ≤ d) {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ}
    {s : Exploration d r} (hs : s.Valid p₀ δ) {ω : Config d}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω)
    (hfin : (cluster ω 0).Finite) : (Good p₀ δ s ω).Finite := by
  have hf (y : Vertex d) : ({v | y ∈ Bcube (d := d) r v} : Set Point).Finite := by
    apply Set.Subsingleton.finite
    intro v hv w hw
    exact Qcube_unique hd r (Bcube_subset_Qcube r v hv) (Bcube_subset_Qcube r w hw)
  apply (hfin.biUnion (fun y _ => hf y)).subset
  intro v hv
  obtain ⟨n, hn⟩ := hv
  obtain ⟨y, hy, hc⟩ := run_sound hd hs hω hS n v hn
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hc, hy⟩⟩

theorem initial_sound (K : Kernel d) (r : ℕ) (ω : Config d) : (initial K r).Sound ω := by
  intro v hv
  have hv0 : v = (0, 0) := Finset.mem_singleton.mp hv
  subst v
  refine ⟨0, ?_, .refl⟩
  rw [Bcube, center_zero, mem_cube]
  intro i; simp

end Exploration

/-- The exploration percolates at the parameter `q < β` of the scales. -/
theorem scales_percolate (hd : 2 ≤ d) [NeZero d] {K : Kernel d} {β : ℝ} (sc : ScaleData K β)
    (hK : K.SignInvariant) (hPos : 0 < K.J (unitAt 0)) : 0 < K.theta sc.q := by
  set p₀ := K.edgeProb sc.q
  set s := initial K sc.r
  set μ := ProductCylinder.law (hparam p₀ s.history)
  set ν := ProductCylinder.law p₀
  have hs : s.Valid p₀ sc.δ := Exploration.initial_valid hd sc hK hPos
  have hb := Exploration.finite_good_bound hd sc hK hPos hs (Exploration.initial_colored K sc.r) rfl
    (Exploration.initial_closed K sc.r) (Exploration.initial_covered K sc.r)
  have hle : μ.real (InfiniteAt 0)ᶜ ≤ μ.real
      {ω | (Exploration.Good p₀ sc.δ s ω).Finite ∧ (0, 0) ∈ Exploration.Good p₀ sc.δ s ω} := by
    apply OAI.MeasureTheory.finite_measureReal_mono_ae
    filter_upwards [ae_fixed_pattern p₀ (rootBits (d := d) sc.r) (rootValues K)] with ω hω
    intro hn
    have hfin : (cluster ω 0).Finite := by
      by_contra hnf
      exact hn hnf
    exact ⟨Exploration.good_finite_of_cluster_finite hd hs hω (Exploration.initial_sound K sc.r ω)
      hfin, ⟨0, Finset.mem_singleton_self _⟩⟩
  have hpos : 0 < μ.real (InfiniteAt 0) := by
    rw [measureReal_compl (measurableSet_infiniteAt 0), probReal_univ] at hle
    linarith
  set H := pattern (rootBits (d := d) sc.r) (rootValues K)
  have hH : 0 < ν.real H := by
    rw [finite_pattern_probability]
    apply Finset.prod_pos
    intro e _
    simp only [bitProbability]
    split_ifs with h
    · simp only [rootValues, decide_eq_true_eq] at h
      have hq : 0 < max sc.q 0 := lt_max_of_lt_left (by linarith [sc.q_half, sc.q_lt])
      simp only [p₀, Kernel.edgeProb]
      have : Real.exp (-(max sc.q 0 * K.pairWeight e)) < 1 :=
        Real.exp_lt_one_iff.mpr (by have := mul_pos hq h; linarith)
      linarith
    · simp only [p₀, Kernel.edgeProb]
      linarith [Real.exp_pos (-(max sc.q 0 * K.pairWeight e))]
  have he : ν.real (H ∩ InfiniteAt 0) = ν.real H * μ.real (InfiniteAt 0) :=
    pattern_inter_real _ _ _ _ (measurableSet_infiniteAt 0)
  have hinf : 0 < ν.real (InfiniteAt 0) :=
    (he ▸ mul_pos hH hpos).trans_le (measureReal_mono Set.inter_subset_right)
  exact hinf

end Coarse

end Peapods.LongRange
