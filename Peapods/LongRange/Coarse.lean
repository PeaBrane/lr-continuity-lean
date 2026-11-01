import Peapods.LongRange.RelayLemma

/-!
# Coarse cubes, interfaces and parent-chain packets

The bits of the exploration of Section 6: the pairs internal to a coarse cube `Q_v` (`qBits`), the
interface `I_{vw}` of all pairs between `Q_v` and `Q_w` (`link`), the block revealed when `v` is
processed with parent `p` (`qBits v ∪ I_{vp}`), and the bits `exposed` by a set of processed cubes.
A packet stores the parent-chain graph `G(v)` of a pending coarse vertex. Ported from OpenAI's
`CriticalZ3.Coarse` and `Exploration.Packet`, where interfaces are nearest-neighbour bonds.
-/

namespace Peapods.LongRange.Coarse

open MeasureTheory ProbabilityTheory Classical OAI

abbrev Point := PlanarBoundary.Point
abbrev Direction := PlanarBoundary.Direction

variable {d : ℕ}

noncomputable def qFinset (r : ℕ) (v : Point) : Finset (Vertex d) := cubeFinset (center r v) (10 * r)

@[simp] theorem mem_qFinset {r : ℕ} {v : Point} {x : Vertex d} : x ∈ qFinset r v ↔ x ∈ Qcube r v :=
  mem_cubeFinset

/-- All pairs of distinct points of `Q_v`. -/
noncomputable def qBits (r : ℕ) (v : Point) : Finset (Pair d) := FinGraph.offDiag (qFinset r v)

/-- The interface `I_{vw}`: all pairs between `Q_v` and `Q_w`. -/
noncomputable def link (r : ℕ) (v w : Point) : Finset (Pair d) :=
  (qFinset r v ×ˢ qFinset r w).image (fun yz => s(yz.1, yz.2))

/-- The bits revealed when `v` is processed with parent `p`. -/
noncomputable def block (r : ℕ) (v p : Point) : Finset (Pair d) := qBits r v ∪ link r v p

/-- The bits prescribed at the start: the pairs internal to `Q_0`. -/
noncomputable def rootBits (r : ℕ) : Finset (Pair d) := qBits r 0

/-- The bits exposed by a set `D` of processed coarse vertices. -/
noncomputable def exposed (r : ℕ) (D : Finset Point) : Finset (Pair d) :=
  rootBits r ∪ D.biUnion (qBits r) ∪ (D ×ˢ D).biUnion (fun e => link r e.1 e.2)

theorem mem_qBits {r : ℕ} {v : Point} {e : Pair d} :
    e ∈ qBits r v ↔ (∀ y ∈ e, y ∈ Qcube r v) ∧ ¬e.IsDiag := by
  simp only [qBits, FinGraph.offDiag, Finset.mem_filter, Finset.mem_sym2_iff, mem_qFinset]

theorem mk_mem_qBits {r : ℕ} {v : Point} {x y : Vertex d} :
    s(x, y) ∈ qBits r v ↔ x ∈ Qcube r v ∧ y ∈ Qcube r v ∧ x ≠ y := by
  simp only [qBits, FinGraph.mk_mem_offDiag, mem_qFinset]

theorem mem_link {r : ℕ} {v w : Point} {e : Pair d} :
    e ∈ link r v w ↔ ∃ y ∈ Qcube r v, ∃ z ∈ Qcube r w, e = s(y, z) := by
  simp only [link, Finset.mem_image, Finset.mem_product, mem_qFinset, Prod.exists]
  constructor
  · rintro ⟨y, z, ⟨hy, hz⟩, rfl⟩; exact ⟨y, hy, z, hz, rfl⟩
  · rintro ⟨y, hy, z, hz, rfl⟩; exact ⟨y, z, ⟨hy, hz⟩, rfl⟩

theorem link_comm (r : ℕ) (v w : Point) : link (d := d) r v w = link r w v := by
  ext e
  simp only [mem_link]
  constructor <;> rintro ⟨y, hy, z, hz, rfl⟩ <;> exact ⟨z, hz, y, hy, Sym2.eq_swap⟩

/-- Every pair of a block has an endpoint in `Q_v` and all its endpoints in `Q_v ∪ Q_p`. -/
theorem block_endpoints {r : ℕ} {v p : Point} {e : Pair d} (he : e ∈ block r v p) :
    (∃ y ∈ e, y ∈ Qcube r v) ∧ ∀ y ∈ e, y ∈ Qcube r v ∨ y ∈ Qcube r p := by
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨hy, _⟩ := mem_qBits.mp he
    induction e using Sym2.ind with
    | _ a b => exact ⟨⟨a, Sym2.mem_mk_left a b, hy a (Sym2.mem_mk_left a b)⟩,
        fun y h => Or.inl (hy y h)⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := mem_link.mp he
    refine ⟨⟨y, Sym2.mem_mk_left y z, hy⟩, fun x hx => ?_⟩
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact Or.inl hy
    · exact Or.inr hz

/-- Every endpoint of an exposed pair lies in a cube of `D`. -/
theorem exposed_endpoints {r : ℕ} {D : Finset Point} (h0 : (0, 0) ∈ D) {e : Pair d}
    (he : e ∈ exposed r D) : ∀ y ∈ e, ∃ a ∈ D, y ∈ Qcube r a := by
  intro y hy
  simp only [exposed, rootBits, Finset.mem_union, Finset.mem_biUnion, Finset.mem_product] at he
  rcases he with (he | ⟨a, ha, he⟩) | ⟨⟨a, b⟩, ⟨ha, hb⟩, he⟩
  · exact ⟨(0, 0), h0, (mem_qBits.mp he).1 y hy⟩
  · exact ⟨a, ha, (mem_qBits.mp he).1 y hy⟩
  · obtain ⟨y', hy', z', hz', rfl⟩ := mem_link.mp he
    rcases Sym2.mem_iff.mp hy with rfl | rfl
    · exact ⟨a, ha, hy'⟩
    · exact ⟨b, hb, hz'⟩

/-- A pair with an endpoint in an unprocessed cube is not exposed. -/
theorem not_exposed (hd : 2 ≤ d) {r : ℕ} {D : Finset Point} (h0 : (0, 0) ∈ D) {v : Point}
    (hv : v ∉ D) {e : Pair d} {y : Vertex d} (hy : y ∈ e) (hyv : y ∈ Qcube r v) :
    e ∉ exposed r D := by
  intro he
  obtain ⟨a, ha, hya⟩ := exposed_endpoints h0 he y hy
  exact hv (Qcube_unique hd r hya hyv ▸ ha)

theorem block_disjoint (hd : 2 ≤ d) {r : ℕ} {D : Finset Point} {v w a b : Point}
    (hv : v ∉ D) (_hw : w ∉ D) (_ha : a ∈ D) (hb : b ∈ D) (hvw : v ≠ w) :
    Disjoint (block (d := d) r v a) (block r w b) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨⟨y, hy, hyv⟩, _⟩ := block_endpoints he
  rcases (block_endpoints he').2 y hy with h | h
  · exact hvw (Qcube_unique hd r hyv h)
  · exact hv (Qcube_unique hd r hyv h ▸ hb)

theorem block_subset_exposed_insert {r : ℕ} {D : Finset Point} {v a : Point} (ha : a ∈ D) :
    block (d := d) r v a ⊆ exposed r (insert v D) := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self _ _, he⟩))
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨(v, a), Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ha⟩, he⟩)

theorem exposed_mono {r : ℕ} {D D' : Finset Point} (h : D ⊆ D') :
    exposed (d := d) r D ⊆ exposed r D' := by
  intro e he
  simp only [exposed, Finset.mem_union, Finset.mem_biUnion, Finset.mem_product] at he ⊢
  rcases he with (he | ⟨v, hv, he⟩) | ⟨⟨v, w⟩, ⟨hv, hw⟩, he⟩
  · exact Or.inl (Or.inl he)
  · exact Or.inl (Or.inr ⟨v, h hv, he⟩)
  · exact Or.inr ⟨(v, w), ⟨h hv, h hw⟩, he⟩

theorem zero_mem_Qcube (r : ℕ) : (0 : Vertex d) ∈ Qcube r (0, 0) := by
  rw [Qcube, center_zero, mem_cube]; intro i; simp

theorem zero_not_mem_Qcube (hd : 2 ≤ d) (r : ℕ) {v : Point} (hv : v ≠ (0, 0)) :
    (0 : Vertex d) ∉ Qcube r v := fun h => hv (Qcube_unique hd r h (zero_mem_Qcube r))

/-! ### Packets -/

/-- A pending coarse vertex with its parent-chain graph `G(v)`. -/
structure Packet (d r : ℕ) where
  vertex : Point
  parent : Point
  graph : FinGraph d
  contains_vertices : ∀ x ∈ Qcube r vertex, x ∈ graph.vertices
  contains_edges : qBits r vertex ⊆ graph.edges
  root_mem : (0 : Vertex d) ∈ graph.vertices

/-- `G' = G ∪ Q_x ∪ I_{vx}`. -/
noncomputable def extendGraph (r : ℕ) (G : FinGraph d) (v x : Point)
    (hv : ∀ y ∈ Qcube r v, y ∈ G.vertices) : FinGraph d where
  vertices := G.vertices ∪ qFinset r x
  edges := G.edges ∪ qBits r x ∪ link r v x
  mem := by
    intro e he y hy
    rcases Finset.mem_union.mp he with he | he
    · rcases Finset.mem_union.mp he with he | he
      · exact Finset.mem_union_left _ (G.mem e he y hy)
      · exact Finset.mem_union_right _ (mem_qFinset.mpr ((mem_qBits.mp he).1 y hy))
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_link.mp he
      rcases Sym2.mem_iff.mp hy with rfl | rfl
      · exact Finset.mem_union_left _ (hv _ ha)
      · exact Finset.mem_union_right _ (mem_qFinset.mpr hb)

namespace Packet

variable {r : ℕ}

/-- `H_v = {o ↔ B_v in G(v)}` with `o = 0`. -/
def event (t : Packet d r) : Set (Config d) := {ω | t.graph.Meets ω 0 (Bcube r t.vertex)}

theorem measurableSet_event (t : Packet d r) : MeasurableSet t.event :=
  FinGraph.measurableSet_meets _ _

theorem event_determined (t : Packet d r) :
    ProductCylinder.DeterminedBy (F := Prop) t.graph.edges (fun ω => ω ∈ t.event) :=
  fun _ _ h => propext (FinGraph.meets_congr h _ _)

noncomputable def child (t : Packet d r) (x : Point) : Packet d r where
  vertex := x
  parent := t.vertex
  graph := extendGraph r t.graph t.vertex x t.contains_vertices
  contains_vertices := fun _ hy => Finset.mem_union_right _ (mem_qFinset.mpr hy)
  contains_edges := fun _ he => Finset.mem_union_left _ (Finset.mem_union_right _ he)
  root_mem := Finset.mem_union_left _ t.root_mem

theorem child_edges (t : Packet d r) (x : Point) :
    (t.child x).graph.edges = t.graph.edges ∪ block r x t.vertex := by
  simp only [child, extendGraph, block, link_comm r t.vertex x, Finset.union_assoc]

theorem child_subgraph (t : Packet d r) (x : Point) :
    t.graph.edges ⊆ (t.child x).graph.edges :=
  fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)

end Packet

/-- The root packet: `Q_0` with all its internal pairs. -/
noncomputable def rootPacket (r : ℕ) : Packet d r where
  vertex := (0, 0)
  parent := (0, 0)
  graph := ⟨qFinset r (0, 0), qBits r (0, 0), fun _ he y hy =>
    mem_qFinset.mpr ((mem_qBits.mp he).1 y hy)⟩
  contains_vertices := fun _ hy => mem_qFinset.mpr hy
  contains_edges := fun _ h => h
  root_mem := mem_qFinset.mpr (zero_mem_Qcube r)

/-! ### Connectivity in a larger graph -/

theorem conn_mono_edges {G H : FinGraph d} (h : G.edges ⊆ H.edges) {ω : Config d}
    {x y : Vertex d} (hc : G.Conn ω x y) : H.Conn ω x y :=
  Relation.ReflTransGen.mono (fun _ _ hab => ⟨h hab.1, hab.2⟩) x y hc

theorem meets_mono_edges {G H : FinGraph d} (h : G.edges ⊆ H.edges) {ω : Config d}
    {o : Vertex d} {T : Set (Vertex d)} (hm : G.Meets ω o T) : H.Meets ω o T := by
  obtain ⟨y, hy, hc⟩ := hm
  exact ⟨y, hy, conn_mono_edges h hc⟩

end Peapods.LongRange.Coarse
