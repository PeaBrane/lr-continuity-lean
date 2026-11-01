import Peapods.LongRange.Coarse
import OAI.Probability.CriticalZ3.ExplorationSurvival

/-!
# The exploration of Section 6

A port of OpenAI's `CriticalZ3.Coarse.Exploration` (`Exploration`, `ExplorationInvariant`) to the
long-range bits. The base law of the fresh bits is an arbitrary product law `p₀` (in the application,
`edgeProb q`), so histories are frozen into `fixedParameter p₀ known values` instead of OpenAI's
constant parameter. Processing the head `t` of the queue reveals the bits of `Q_t` and of the
parent interface `I_{t, parent}` not yet known; `t` is good if `H_t` holds and every unvisited
neighbour `x` has conditional probability more than `1 - δ` of `o ↔ B_x` in `G(t) ∪ Q_x ∪ I_{tx}`.
-/

namespace Peapods.LongRange.Coarse

open MeasureTheory ProbabilityTheory Classical OAI InfiniteConditioning

variable {d : ℕ}

/-- The law of the fresh bits given a history. -/
noncomputable def hparam (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (h : History (Pair d)) :
    Pair d → Set.Icc (0 : ℝ) 1 :=
  fixedParameter p₀ h.known h.values

theorem hparam_observe (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (h : History (Pair d)) (R : Finset (Pair d))
    (ω : Config d) : hparam p₀ (h.observe R ω) = fixedParameter (hparam p₀ h) R ω :=
  (fixedParameter_merge p₀ h.known R h.values ω).symm

theorem hparam_fresh (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (h : History (Pair d)) {e : Pair d}
    (he : e ∉ h.known) : hparam p₀ h e = p₀ e := by
  simp only [hparam, fixedParameter, he, ite_false]

theorem ae_freeze (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (h : History (Pair d)) :
    ∀ᵐ ω ∂ProductCylinder.law (hparam p₀ h), h.freeze ω = ω := by
  filter_upwards [ae_fixed_pattern p₀ h.known h.values] with ω hω
  exact replace_eq_of_pattern hω

structure Exploration (d r : ℕ) where
  history : History (Pair d)
  processed : Finset Point
  queue : List (Packet d r)
  good : Finset Point
  bad : Finset Point

namespace Exploration

variable {r : ℕ}

noncomputable def visited (s : Exploration d r) : Finset Point :=
  s.processed ∪ (s.queue.map Packet.vertex).toFinset

noncomputable def reveal (s : Exploration d r) : Finset (Pair d) :=
  match s.queue with
  | [] => ∅
  | t :: _ => block r t.vertex t.parent \ s.history.known

noncomputable def after (s : Exploration d r) (ω : Config d) : History (Pair d) :=
  s.history.observe s.reveal ω

noncomputable def candidates (s : Exploration d r) (t : Packet d r) : List (Packet d r) :=
  (List.ofFn (fun dir : Direction => t.child (t.vertex + PlanarBoundary.outward dir))).filter
    (fun u => u.vertex ∉ s.visited)

noncomputable def Accept (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (t : Packet d r) (ω : Config d) : Prop :=
  (s.after ω).values ∈ t.event ∧ ∀ u ∈ s.candidates t,
    1 - δ < (ProductCylinder.law (hparam p₀ (s.after ω))).real u.event

noncomputable def markedBad (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (ω : Config d) : Bool :=
  match s.queue with
  | [] => false
  | t :: _ => decide (¬s.Accept p₀ δ t ω)

noncomputable def advance (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (ω : Config d) : Exploration d r where
  history := s.after ω
  processed := match s.queue with | [] => s.processed | t :: _ => insert t.vertex s.processed
  queue := match s.queue with
    | [] => []
    | t :: ts => ts ++ if s.Accept p₀ δ t ω then s.candidates t else []
  good := match s.queue with
    | [] => s.good
    | t :: _ => if s.Accept p₀ δ t ω then insert t.vertex s.good else s.good
  bad := match s.queue with
    | [] => s.bad
    | t :: _ => if s.Accept p₀ δ t ω then s.bad else insert t.vertex s.bad

theorem reveal_disjoint (s : Exploration d r) : Disjoint s.reveal s.history.known := by
  cases h : s.queue with
  | nil => simp only [reveal, h]; exact Finset.disjoint_empty_left _
  | cons t ts => simp only [reveal, h]; exact Finset.sdiff_disjoint

noncomputable def scheme (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) :
    AdaptiveReveals.Scheme (Pair d) Point (Exploration d r) where
  reveal := reveal
  parameter := fun s => hparam p₀ s.history
  vertex := fun s => (s.queue.head?).map Packet.vertex
  bad := fun s a => s.markedBad p₀ δ (ProductCylinder.extend s.reveal a)
  child := fun s a => s.advance p₀ δ (ProductCylinder.extend s.reveal a)
  parameter_child := fun s _a => hparam_observe p₀ s.history s.reveal _

structure Valid (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) (s : Exploration d r) : Prop where
  root_processed : (0, 0) ∈ s.processed
  distinct : (s.queue.map Packet.vertex).Nodup
  unprocessed : ∀ t ∈ s.queue, t.vertex ∉ s.processed
  parents : ∀ t ∈ s.queue, t.parent ∈ s.processed
  exposed : s.history.known ⊆ Coarse.exposed r s.processed
  support : ∀ t ∈ s.queue, t.graph.edges ⊆ s.history.known ∪ block r t.vertex t.parent
  promise : ∀ t ∈ s.queue, 1 - δ < (ProductCylinder.law (hparam p₀ s.history)).real t.event

@[simp] theorem mem_candidates (s : Exploration d r) (t u : Packet d r) :
    u ∈ s.candidates t ↔
      (∃ dir : Direction, t.child (t.vertex + PlanarBoundary.outward dir) = u) ∧
        u.vertex ∉ s.visited := by
  simp only [candidates, List.mem_filter, List.mem_ofFn, decide_eq_true_eq]

theorem queue_visited (s : Exploration d r) {t : Packet d r} (ht : t ∈ s.queue) :
    t.vertex ∈ s.visited :=
  Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, ht, rfl⟩))

theorem processed_visited (s : Exploration d r) : s.processed ⊆ s.visited :=
  Finset.subset_union_left

theorem candidates_distinct (s : Exploration d r) (t : Packet d r) :
    ((s.candidates t).map Packet.vertex).Nodup := by
  have hh : ((List.ofFn (fun dir : Direction =>
      t.child (t.vertex + PlanarBoundary.outward dir))).map Packet.vertex).Nodup := by
    rw [List.map_ofFn]
    apply List.nodup_ofFn.mpr
    intro a b hab
    exact CriticalZ3.Coarse.outward_injective (add_left_cancel hab)
  exact (List.filter_sublist.map Packet.vertex).nodup hh

theorem advance_empty (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (ω : Config d) (h : s.queue = []) : s.advance p₀ δ ω = s := by
  cases s with
  | mk history processed queue good bad =>
    cases history
    simp_all only [advance, after, reveal, History.observe, Finset.union_empty,
      Exploration.mk.injEq, History.mk.injEq, true_and, and_true]
    funext e
    exact ite_eq_right (Finset.notMem_empty e)

theorem current_support {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ} {s : Exploration d r}
    (hs : s.Valid p₀ δ) {t : Packet d r} {ts : List (Packet d r)} (hq : s.queue = t :: ts) :
    t.graph.edges ⊆ s.history.known ∪ s.reveal := by
  intro e he
  have hh := hs.support t (by simp [hq]) he
  rcases Finset.mem_union.mp hh with hh | hh
  · exact Finset.mem_union_left _ hh
  · by_cases hk : e ∈ s.history.known
    · exact Finset.mem_union_left _ hk
    · exact Finset.mem_union_right _ (by simpa only [reveal, hq, Finset.mem_sdiff] using ⟨hh, hk⟩)

theorem later_disjoint (hd : 2 ≤ d) {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ}
    {s : Exploration d r} (hs : s.Valid p₀ δ) {t : Packet d r} {ts : List (Packet d r)}
    (hq : s.queue = t :: ts) {u : Packet d r} (hu : u ∈ ts) : Disjoint s.reveal u.graph.edges := by
  have htq : t ∈ s.queue := by simp [hq]
  have huq : u ∈ s.queue := by simp [hq, hu]
  have htu : t.vertex ≠ u.vertex := by
    have hn := hs.distinct
    rw [hq, List.map_cons, List.nodup_cons] at hn
    intro he
    exact hn.1 (he ▸ List.mem_map.mpr ⟨u, hu, rfl⟩)
  have hdis := block_disjoint (d := d) (r := r) hd (hs.unprocessed t htq) (hs.unprocessed u huq)
    (hs.parents t htq) (hs.parents u huq) htu
  apply Finset.disjoint_left.mpr
  intro e he hu'
  have hr : e ∈ block r t.vertex t.parent ∧ e ∉ s.history.known := by
    simpa only [reveal, hq, Finset.mem_sdiff] using he
  rcases Finset.mem_union.mp (hs.support u huq hu') with hu' | hu'
  · exact hr.2 hu'
  · exact Finset.disjoint_left.mp hdis hr.1 hu'

theorem later_probability (hd : 2 ≤ d) {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ}
    {s : Exploration d r} (hs : s.Valid p₀ δ) {t : Packet d r} {ts : List (Packet d r)}
    (hq : s.queue = t :: ts) {u : Packet d r} (hu : u ∈ ts) (ω : Config d) :
    (ProductCylinder.law (hparam p₀ (s.after ω))).real u.event =
      (ProductCylinder.law (hparam p₀ s.history)).real u.event := by
  apply ProductCylinder.probability_congr_parameters u.graph.edges _ _ _ _ u.event_determined
  intro e he
  rw [after, hparam_observe]
  exact ite_eq_right (fun hh => Finset.disjoint_left.mp (later_disjoint hd hs hq hu) hh he)

theorem valid_advance (hd : 2 ≤ d) {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ}
    {s : Exploration d r} (hs : s.Valid p₀ δ) (ω : Config d) : (s.advance p₀ δ ω).Valid p₀ δ := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s p₀ δ ω hq]
  | cons t ts =>
    have htq : t ∈ s.queue := by simp [hq]
    have hnot : t.vertex ∉ ts.map Packet.vertex := by
      have hh := hs.distinct
      rw [hq, List.map_cons, List.nodup_cons] at hh
      exact hh.1
    have htail : (ts.map Packet.vertex).Nodup := by
      have hh := hs.distinct
      rw [hq, List.map_cons, List.nodup_cons] at hh
      exact hh.2
    have hp : (s.advance p₀ δ ω).processed = insert t.vertex s.processed := by simp [advance, hq]
    have hn : (s.advance p₀ δ ω).queue =
        ts ++ if s.Accept p₀ δ t ω then s.candidates t else [] := by
      simp [advance, hq]
    have hvu {u : Packet d r} (hu : u ∈ s.candidates t) :
        u.vertex ≠ t.vertex ∧ u.vertex ∉ s.processed := by
      have hh := (mem_candidates s t u).mp hu |>.2
      exact ⟨fun he => hh (he ▸ s.queue_visited htq), fun he => hh (s.processed_visited he)⟩
    have hold {u : Packet d r} (hu : u ∈ ts) : u.vertex ≠ t.vertex ∧ u.vertex ∉ s.processed := by
      exact ⟨fun he => hnot (he ▸ List.mem_map.mpr ⟨u, hu, rfl⟩),
        hs.unprocessed u (by simp [hq, hu])⟩
    have hmembers {u : Packet d r} (hu : u ∈ (s.advance p₀ δ ω).queue) :
        u ∈ ts ∨ (s.Accept p₀ δ t ω ∧ u ∈ s.candidates t) := by
      rw [hn, List.mem_append] at hu
      rcases hu with hu | hu
      · exact Or.inl hu
      · split_ifs at hu with ha
        · exact Or.inr ⟨ha, hu⟩
        · exact False.elim (List.not_mem_nil hu)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hp]; exact Finset.mem_insert_of_mem hs.root_processed
    · rw [hn, List.map_append]
      split_ifs with ha
      · apply htail.append (s.candidates_distinct t)
        apply List.disjoint_left.mpr
        intro v hv hu
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
        have hh := (mem_candidates s t z).mp hz |>.2
        exact hh (Finset.mem_union_right _ (List.mem_toFinset.mpr (by
          rw [hq, List.map_cons]; exact List.mem_cons_of_mem _ hv)))
      · simpa only [List.map_nil, List.append_nil] using htail
    · intro u hu
      rw [hp, Finset.mem_insert]
      rcases hmembers hu with hu | ⟨_, hu⟩
      · exact not_or.mpr (hold hu)
      · exact not_or.mpr (hvu hu)
    · intro u hu
      rw [hp]
      rcases hmembers hu with hu | ⟨_, hu⟩
      · exact Finset.mem_insert_of_mem (hs.parents u (by simp [hq, hu]))
      · obtain ⟨⟨dir, rfl⟩, _⟩ := (mem_candidates s t u).mp hu
        exact Finset.mem_insert_self _ _
    · rw [hp]
      dsimp only [advance, after, History.observe]
      simp only [Finset.subset_iff, Finset.mem_union]
      intro e he
      rcases he with hk | hr
      · exact exposed_mono (Finset.subset_insert _ _) (hs.exposed hk)
      · apply block_subset_exposed_insert (hs.parents t htq)
        exact (Finset.mem_sdiff.mp (by simpa only [reveal, hq] using hr)).1
    · intro u hu
      dsimp only [advance, after, History.observe]
      simp only [Finset.subset_iff, Finset.mem_union]
      rcases hmembers hu with hu | ⟨_, hu⟩
      · intro e he
        rcases Finset.mem_union.mp (hs.support u (by simp [hq, hu]) he) with he | he
        · exact Or.inl (Or.inl he)
        · exact Or.inr he
      · obtain ⟨⟨dir, rfl⟩, _⟩ := (mem_candidates s t u).mp hu
        intro e he
        rw [Packet.child_edges, Finset.mem_union] at he
        rcases he with he | he
        · exact Or.inl (Finset.mem_union.mp (current_support hs hq he))
        · exact Or.inr he
    · intro u hu
      rcases hmembers hu with hu | ⟨ha, hu⟩
      · change 1 - δ < (ProductCylinder.law (hparam p₀ (s.after ω))).real u.event
        rw [later_probability hd hs hq hu ω]
        exact hs.promise u (by simp [hq, hu])
      · exact ha.2 u hu

/-! ### Determination by the reveal -/

theorem after_determined (s : Exploration d r) :
    ProductCylinder.DeterminedBy s.reveal (s.after) := by
  intro ω ω' he
  unfold after History.observe
  congr 1
  funext e
  by_cases hr : e ∈ s.reveal
  · simp only [replace, ite_eq_left hr, he e hr]
  · simp only [replace, ite_eq_right hr]

theorem markedBad_determined (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) :
    ProductCylinder.DeterminedBy s.reveal (s.markedBad p₀ δ) := by
  intro ω ω' he
  have h := s.after_determined ω ω' he
  have ha (t : Packet d r) : s.Accept p₀ δ t ω' ↔ s.Accept p₀ δ t ω := by simp only [Accept, h]
  cases hq : s.queue <;> simp only [markedBad, hq, ha]

theorem advance_determined (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) :
    ProductCylinder.DeterminedBy s.reveal (s.advance p₀ δ) := by
  intro ω ω' he
  have h := s.after_determined ω ω' he
  have ha (t : Packet d r) : s.Accept p₀ δ t ω' ↔ s.Accept p₀ δ t ω := by simp only [Accept, h]
  cases hq : s.queue <;> simp only [advance, hq, h, ha]

theorem badMass_eq (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) :
    (scheme (r := r) p₀ δ).badMass s =
      (ProductCylinder.law (hparam p₀ s.history)).real {ω | s.markedBad p₀ δ ω = true} := by
  rw [AdaptiveReveals.Scheme.badMass_eq_probability]
  congr 2
  ext ω
  change (s.markedBad p₀ δ (ProductCylinder.extend s.reveal (s.reveal.restrict ω)) = true) ↔ _
  rw [← ProductCylinder.determinedBy_eq_extend (s.markedBad_determined p₀ δ) ω]

noncomputable def frozenEvent (s : Exploration d r) (t : Packet d r) : Set (Config d) :=
  {ω | s.history.freeze ω ∈ t.event}

theorem frozenEvent_determined {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ} {s : Exploration d r}
    (hs : s.Valid p₀ δ) {t : Packet d r} {ts : List (Packet d r)} (hq : s.queue = t :: ts) :
    ProductCylinder.DeterminedBy (F := Prop) s.reveal (fun ω => ω ∈ s.frozenEvent t) :=
  s.history.freeze_determined _ t.event_determined (by
    simpa only [Finset.subset_iff, Finset.mem_union] using current_support hs hq)

theorem frozenEvent_probability (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1)
    (t : Packet d r) :
    (ProductCylinder.law (hparam p₀ s.history)).real (s.frozenEvent t) =
      (ProductCylinder.law (hparam p₀ s.history)).real t.event := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ae_freeze p₀ s.history] with ω hω
  change (s.history.freeze ω ∈ t.event) = (ω ∈ t.event)
  rw [hω]

theorem accept_current_iff {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ} {s : Exploration d r}
    (hs : s.Valid p₀ δ) {t : Packet d r} {ts : List (Packet d r)} (hq : s.queue = t :: ts)
    (ω : Config d) : (s.after ω).values ∈ t.event ↔ ω ∈ s.frozenEvent t := by
  exact Eq.to_iff (s.history.observe_outcome _ t.event_determined
    (by simpa only [Finset.subset_iff, Finset.mem_union] using current_support hs hq)
    s.reveal_disjoint ω)

/-! ### Colouring and runs -/

theorem advance_processed (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (ω : Config d) {t : Packet d r} {ts : List (Packet d r)} (hq : s.queue = t :: ts) :
    (s.advance p₀ δ ω).processed = insert t.vertex s.processed := by simp only [advance, hq]

theorem advance_queue (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (ω : Config d) {t : Packet d r} {ts : List (Packet d r)} (hq : s.queue = t :: ts) :
    (s.advance p₀ δ ω).queue = ts ++ if s.Accept p₀ δ t ω then s.candidates t else [] := by
  simp only [advance, hq]

theorem mem_advance_queue (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (ω : Config d) {t u : Packet d r} {ts : List (Packet d r)} (hq : s.queue = t :: ts) :
    u ∈ (s.advance p₀ δ ω).queue ↔ u ∈ ts ∨ (s.Accept p₀ δ t ω ∧ u ∈ s.candidates t) := by
  rw [s.advance_queue p₀ δ ω hq, List.mem_append]
  by_cases h : s.Accept p₀ δ t ω <;> simp [h]

theorem processed_advance_mono (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (ω : Config d) : s.processed ⊆ (s.advance p₀ δ ω).processed := by
  cases hq : s.queue
  · rw [advance_empty s p₀ δ ω hq]
  · rw [s.advance_processed p₀ δ ω hq]; exact Finset.subset_insert _ _

theorem good_advance_mono (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (ω : Config d) : s.good ⊆ (s.advance p₀ δ ω).good := by
  cases hq : s.queue
  · rw [advance_empty s p₀ δ ω hq]
  · simp only [advance, hq]
    split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _

theorem bad_advance_mono (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (ω : Config d) : s.bad ⊆ (s.advance p₀ δ ω).bad := by
  cases hq : s.queue
  · rw [advance_empty s p₀ δ ω hq]
  · simp only [advance, hq]
    split_ifs
    · exact Finset.Subset.refl _
    · exact Finset.subset_insert _ _

theorem visited_advance_mono (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (ω : Config d) : s.visited ⊆ (s.advance p₀ δ ω).visited := by
  cases hq : s.queue with
  | nil => rw [advance_empty s p₀ δ ω hq]
  | cons t ts =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (s.advance p₀ δ ω).processed_visited (s.processed_advance_mono p₀ δ ω hv)
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      rw [hq, List.mem_cons] at hu
      rcases hu with rfl | hu
      · apply (s.advance p₀ δ ω).processed_visited
        rw [s.advance_processed p₀ δ ω hq]
        exact Finset.mem_insert_self _ _
      · apply (s.advance p₀ δ ω).queue_visited
        exact (s.mem_advance_queue p₀ δ ω hq).mpr (Or.inl hu)

theorem new_visited (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (ω : Config d) {t : Packet d r} {ts : List (Packet d r)} (hq : s.queue = t :: ts)
    {v : Point} (hv : v ∈ (s.advance p₀ δ ω).visited) :
    v ∈ s.visited ∨
      (s.Accept p₀ δ t ω ∧ ∃ dir : Direction, v = t.vertex + PlanarBoundary.outward dir) := by
  rcases Finset.mem_union.mp hv with hv | hv
  · rw [s.advance_processed p₀ δ ω hq, Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact Or.inl (s.queue_visited (by simp [hq]))
    · exact Or.inl (s.processed_visited hv)
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    rcases (s.mem_advance_queue p₀ δ ω hq).mp hu with hu | ⟨ha, hu⟩
    · exact Or.inl (s.queue_visited (by simp [hq, hu]))
    · obtain ⟨⟨dir, rfl⟩, _⟩ := (mem_candidates s t u).mp hu
      exact Or.inr ⟨ha, dir, rfl⟩

theorem accepted_neighbors (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (ω : Config d) {t : Packet d r} {ts : List (Packet d r)} (hq : s.queue = t :: ts)
    (ha : s.Accept p₀ δ t ω) (dir : Direction) :
    t.vertex + PlanarBoundary.outward dir ∈ (s.advance p₀ δ ω).visited := by
  by_cases hv : t.vertex + PlanarBoundary.outward dir ∈ s.visited
  · exact s.visited_advance_mono p₀ δ ω hv
  · apply (s.advance p₀ δ ω).queue_visited (t := t.child (t.vertex + PlanarBoundary.outward dir))
    apply (s.mem_advance_queue p₀ δ ω hq).mpr
    exact Or.inr ⟨ha, (mem_candidates _ _ _).mpr ⟨⟨dir, rfl⟩, hv⟩⟩

structure Colored (s : Exploration d r) : Prop where
  partition : s.processed = s.good ∪ s.bad
  disjoint : Disjoint s.good s.bad

def Closed (s : Exploration d r) : Prop :=
  ∀ v ∈ s.good, ∀ dir : Direction, v + PlanarBoundary.outward dir ∈ s.visited

def Covered (s : Exploration d r) : Prop :=
  ∀ v ∈ s.visited, v ∈ s.good ∨ ∃ u ∈ s.good, ∃ dir : Direction, v = u + PlanarBoundary.outward dir

theorem Colored.good_processed {s : Exploration d r} (h : s.Colored) : s.good ⊆ s.processed := by
  rw [h.partition]; exact Finset.subset_union_left

theorem Colored.bad_processed {s : Exploration d r} (h : s.Colored) : s.bad ⊆ s.processed := by
  rw [h.partition]; exact Finset.subset_union_right

theorem colored_advance {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ} {s : Exploration d r}
    (hs : s.Valid p₀ δ) (hc : s.Colored) (ω : Config d) : (s.advance p₀ δ ω).Colored := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s p₀ δ ω hq]
  | cons t ts =>
    have hn := hs.unprocessed t (by simp [hq])
    have hng : t.vertex ∉ s.good := fun h => hn (hc.good_processed h)
    have hnb : t.vertex ∉ s.bad := fun h => hn (hc.bad_processed h)
    constructor
    · simp only [advance, hq]
      split_ifs <;> simp only [hc.partition, Finset.insert_union, Finset.union_insert]
    · simp only [advance, hq]
      split_ifs
      · exact Finset.disjoint_insert_left.mpr ⟨hnb, hc.disjoint⟩
      · exact Finset.disjoint_insert_right.mpr ⟨hng, hc.disjoint⟩

theorem closed_advance (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (hc : s.Closed) (ω : Config d) : (s.advance p₀ δ ω).Closed := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s p₀ δ ω hq]
  | cons t ts =>
    intro v hv dir
    simp only [advance, hq] at hv
    split_ifs at hv with ha
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact s.accepted_neighbors p₀ δ ω hq ha dir
      · exact s.visited_advance_mono p₀ δ ω (hc _ hv dir)
    · exact s.visited_advance_mono p₀ δ ω (hc _ hv dir)

theorem covered_advance (s : Exploration d r) (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ)
    (hc : s.Covered) (ω : Config d) : (s.advance p₀ δ ω).Covered := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s p₀ δ ω hq]
  | cons t ts =>
    intro v hv
    rcases s.new_visited p₀ δ ω hq hv with hv | ⟨ha, dir, rfl⟩
    · rcases hc _ hv with hv | ⟨u, hu, dir, he⟩
      · exact Or.inl (s.good_advance_mono p₀ δ ω hv)
      · exact Or.inr ⟨u, s.good_advance_mono p₀ δ ω hu, dir, he⟩
    · right
      refine ⟨t.vertex, ?_, dir, rfl⟩
      simp only [advance, hq, ite_eq_left ha]
      exact Finset.mem_insert_self _ _

noncomputable def run (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) :
    ℕ → Exploration d r → Config d → Exploration d r
  | 0, s, _ => s
  | n + 1, s, ω => run p₀ δ n (s.advance p₀ δ ω) ω

@[simp] theorem run_zero (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) (s : Exploration d r)
    (ω : Config d) : run p₀ δ 0 s ω = s := rfl

@[simp] theorem run_succ (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) (n : ℕ) (s : Exploration d r)
    (ω : Config d) : run p₀ δ (n + 1) s ω = run p₀ δ n (s.advance p₀ δ ω) ω := rfl

theorem run_succ_right (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) (n : ℕ) (s : Exploration d r)
    (ω : Config d) : run p₀ δ (n + 1) s ω = (run p₀ δ n s ω).advance p₀ δ ω := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [run_succ, ih, run_succ]

theorem run_valid (hd : 2 ≤ d) {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ} {s : Exploration d r}
    (hs : s.Valid p₀ δ) (n : ℕ) (ω : Config d) : (run p₀ δ n s ω).Valid p₀ δ := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => exact ih (valid_advance hd hs ω)

theorem run_colored (hd : 2 ≤ d) {p₀ : Pair d → Set.Icc (0 : ℝ) 1} {δ : ℝ} {s : Exploration d r}
    (hs : s.Valid p₀ δ) (hc : s.Colored) (n : ℕ) (ω : Config d) : (run p₀ δ n s ω).Colored := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (valid_advance hd hs ω) (colored_advance hs hc ω)

theorem run_closed (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) {s : Exploration d r}
    (hc : s.Closed) (n : ℕ) (ω : Config d) : (run p₀ δ n s ω).Closed := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (closed_advance s p₀ δ hc ω)

theorem run_covered (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) {s : Exploration d r}
    (hc : s.Covered) (n : ℕ) (ω : Config d) : (run p₀ δ n s ω).Covered := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (covered_advance s p₀ δ hc ω)

theorem run_good_mono (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) (s : Exploration d r)
    (ω : Config d) : Monotone (fun n => (run p₀ δ n s ω).good) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [run_succ_right]
  exact good_advance_mono _ _ _ _

theorem run_bad_mono (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) (s : Exploration d r)
    (ω : Config d) : Monotone (fun n => (run p₀ δ n s ω).bad) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [run_succ_right]
  exact bad_advance_mono _ _ _ _

theorem run_empty (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) {s : Exploration d r}
    (hs : s.queue = []) (n : ℕ) (ω : Config d) : run p₀ δ n s ω = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, advance_empty s p₀ δ ω hs, ih]

noncomputable def Good (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) (s : Exploration d r)
    (ω : Config d) : Set Point :=
  {v | ∃ n, v ∈ (run p₀ δ n s ω).good}

noncomputable def Bad (p₀ : Pair d → Set.Icc (0 : ℝ) 1) (δ : ℝ) (s : Exploration d r)
    (v : Point) : Set (Config d) :=
  {ω | ∃ n, v ∈ (run p₀ δ n s ω).bad}

end Exploration

end Peapods.LongRange.Coarse
