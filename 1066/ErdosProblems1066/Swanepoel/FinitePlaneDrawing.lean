import Mathlib.Tactic
import Mathlib.Analysis.Convex.Side
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.Compact
import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete

set_option autoImplicit false

/-!
# Finite plane drawing rows for S2

This file starts the honest S2 outer-component theorem at the drawing level.
It defines the subset of the plane occupied by canonical unit-distance edges
and proves the endpoint membership facts needed before an exterior component
can be selected.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FinitePlaneDrawing

open JordanTopologyFactsConcrete
open JordanTopologyFactsConcrete.MinimalFailureTopology

noncomputable section

variable {n : Nat}

/-- The closed affine segment from `a` to `b`, expressed using the project-local
straight-line parametrization. -/
def closedSegment (a b : PlanarInterface.Point) : Set PlanarInterface.Point :=
  {p | Exists fun t : Real =>
    0 <= t /\ t <= 1 /\ p = PlanarInterface.segmentPoint a b t}

/-- Membership in a project-local closed segment, unfolded to the segment
parameter. -/
theorem mem_closedSegment_iff_exists_segmentPoint
    {p a b : PlanarInterface.Point} :
    p ∈ closedSegment a b <->
      Exists fun t : Real =>
        0 <= t /\ t <= 1 /\ p = PlanarInterface.segmentPoint a b t :=
  Iff.rfl

/-- Closed-segment membership, with the parameter bundled as membership in the
closed interval `[0, 1]`. -/
theorem mem_closedSegment_iff_exists_Icc
    {p a b : PlanarInterface.Point} :
    p ∈ closedSegment a b <->
      Exists fun t : Real =>
        t ∈ Set.Icc (0 : Real) 1 /\
          p = PlanarInterface.segmentPoint a b t := by
  constructor
  · rintro ⟨t, ht0, ht1, hpt⟩
    exact ⟨t, ⟨ht0, ht1⟩, hpt⟩
  · rintro ⟨t, ht, hpt⟩
    exact ⟨t, ht.1, ht.2, hpt⟩

/-- The project-local closed segment is the image of the compact interval
`[0, 1]` under the affine segment parametrization. -/
theorem closedSegment_eq_image_Icc (a b : PlanarInterface.Point) :
    closedSegment a b =
      (fun t : Real => PlanarInterface.segmentPoint a b t) ''
        Set.Icc (0 : Real) 1 := by
  ext p
  constructor
  · rintro ⟨t, ht0, ht1, hpt⟩
    exact ⟨t, ⟨ht0, ht1⟩, hpt.symm⟩
  · rintro ⟨t, ht, hpt⟩
    exact ⟨t, ht.1, ht.2, hpt.symm⟩

/-- The affine segment parametrization is continuous. -/
theorem continuous_segmentPoint (a b : PlanarInterface.Point) :
    Continuous fun t : Real => PlanarInterface.segmentPoint a b t := by
  unfold PlanarInterface.segmentPoint
  continuity

/-- The project-local segment parametrization is Mathlib's affine `lineMap`
on the Euclidean plane.  This bridge lets the local drawing lemmas use
Mathlib's affine-line and side-of-line API without changing the project-facing
`PlanarInterface.segmentPoint` statements. -/
theorem segmentPoint_eq_affineLineMap
    (a b : PlanarInterface.Point) (t : Real) :
    PlanarInterface.segmentPoint a b t = AffineMap.lineMap a b t := by
  ext <;> simp [PlanarInterface.segmentPoint, AffineMap.lineMap_apply_module]

/-- Every project-local segment point lies on the Mathlib affine line through
the two segment endpoints. -/
theorem segmentPoint_mem_affineSpan_pair
    (a b : PlanarInterface.Point) (t : Real) :
    PlanarInterface.segmentPoint a b t ∈
      (line[ℝ, a, b] : AffineSubspace ℝ PlanarInterface.Point) := by
  rw [segmentPoint_eq_affineLineMap]
  exact AffineMap.lineMap_mem_affineSpan_pair t a b

/-- The project-local closed segment is contained in the Mathlib affine line
through its endpoints. -/
theorem closedSegment_subset_affineSpan_pair
    (a b : PlanarInterface.Point) :
    closedSegment a b ⊆
      (line[ℝ, a, b] : AffineSubspace ℝ PlanarInterface.Point) := by
  intro p hp
  rcases hp with ⟨t, _ht0, _ht1, hpt⟩
  rw [hpt]
  exact segmentPoint_mem_affineSpan_pair a b t

/-- The project-local open segment is contained in the Mathlib affine line
through its endpoints. -/
theorem inOpenSegment_mem_affineSpan_pair
    {p a b : PlanarInterface.Point}
    (hp : PlanarInterface.InOpenSegment p a b) :
    p ∈ (line[ℝ, a, b] : AffineSubspace ℝ PlanarInterface.Point) := by
  rcases hp with ⟨t, _ht0, _ht1, hpt⟩
  rw [hpt]
  exact segmentPoint_mem_affineSpan_pair a b t

/-- The linear signed-area functional normal to the directed line from `a` to
`b`.  Subtracting its value at `a` gives the usual signed distance surrogate
from the affine line through `a` and `b`. -/
def edgeNormalLinearMap
    (a b : PlanarInterface.Point) : PlanarInterface.Point →ₗ[ℝ] Real where
  toFun p := - (b.2 - a.2) * p.1 + (b.1 - a.1) * p.2
  map_add' := by
    intro p q
    simp
    ring
  map_smul' := by
    intro c p
    simp
    ring

/-- Signed affine normal coordinate for the directed line through `a` and
`b`.  It vanishes on the whole affine line. -/
def edgeNormalCoord
    (a b p : PlanarInterface.Point) : Real :=
  edgeNormalLinearMap a b p - edgeNormalLinearMap a b a

/-- Segment points have zero signed affine normal coordinate. -/
theorem edgeNormalCoord_segmentPoint_eq_zero
    (a b : PlanarInterface.Point) (t : Real) :
    edgeNormalCoord a b (PlanarInterface.segmentPoint a b t) = 0 := by
  unfold edgeNormalCoord edgeNormalLinearMap PlanarInterface.segmentPoint
  simp
  ring

/-- Reversing the directed edge reverses the signed normal coordinate. -/
theorem edgeNormalCoord_swap
    (a b p : PlanarInterface.Point) :
    edgeNormalCoord b a p = - edgeNormalCoord a b p := by
  unfold edgeNormalCoord edgeNormalLinearMap
  simp
  ring

/-- Move from `z` in the positive normal direction to the directed line
through `a` and `b`. -/
def normalOffsetPoint
    (a b z : PlanarInterface.Point) (δ : Real) :
    PlanarInterface.Point :=
  (z.1 - δ * (b.2 - a.2), z.2 + δ * (b.1 - a.1))

/-- The normal offset changes the signed normal coordinate by a positive
multiple of the squared edge length. -/
theorem edgeNormalCoord_normalOffsetPoint
    (a b z : PlanarInterface.Point) (δ : Real) :
    edgeNormalCoord a b (normalOffsetPoint a b z δ) =
      edgeNormalCoord a b z +
        δ * ((b.2 - a.2) ^ 2 + (b.1 - a.1) ^ 2) := by
  unfold edgeNormalCoord edgeNormalLinearMap normalOffsetPoint
  simp
  ring

/-- A nondegenerate edge has positive squared direction length. -/
theorem edge_direction_sq_sum_pos
    {a b : PlanarInterface.Point} (hab : a ≠ b) :
    0 < (b.2 - a.2) ^ 2 + (b.1 - a.1) ^ 2 := by
  have hnonneg :
      0 <= (b.2 - a.2) ^ 2 + (b.1 - a.1) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hne :
      (b.2 - a.2) ^ 2 + (b.1 - a.1) ^ 2 ≠ 0 := by
    intro hzero
    have hdy_sq : (b.2 - a.2) ^ 2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1)]
    have hdx_sq : (b.1 - a.1) ^ 2 = 0 := by nlinarith [sq_nonneg (b.2 - a.2)]
    have hdy : b.2 - a.2 = 0 := sq_eq_zero_iff.mp hdy_sq
    have hdx : b.1 - a.1 = 0 := sq_eq_zero_iff.mp hdx_sq
    exact hab (Prod.ext (by linarith) (by linarith))
  exact lt_of_le_of_ne' hnonneg hne

/-- Positive normal offsets from a point on the affine edge-line lie in the
positive strict side. -/
theorem edgeNormalCoord_normalOffsetPoint_pos_of_zero_of_pos_of_ne
    {a b z : PlanarInterface.Point} {δ : Real}
    (hz : edgeNormalCoord a b z = 0)
    (hδ : 0 < δ)
    (hab : a ≠ b) :
    0 < edgeNormalCoord a b (normalOffsetPoint a b z δ) := by
  rw [edgeNormalCoord_normalOffsetPoint, hz, zero_add]
  exact mul_pos hδ (edge_direction_sq_sum_pos hab)

/-- The normal offset map is continuous. -/
theorem continuous_normalOffsetPoint
    (a b z : PlanarInterface.Point) :
    Continuous fun δ : Real => normalOffsetPoint a b z δ := by
  unfold normalOffsetPoint
  continuity

/-- Zero normal offset is the original point. -/
theorem normalOffsetPoint_zero
    (a b z : PlanarInterface.Point) :
    normalOffsetPoint a b z 0 = z := by
  ext <;> simp [normalOffsetPoint]

/-- Closed-segment points have zero signed affine normal coordinate. -/
theorem edgeNormalCoord_eq_zero_of_mem_closedSegment
    {p a b : PlanarInterface.Point}
    (hp : p ∈ closedSegment a b) :
    edgeNormalCoord a b p = 0 := by
  rcases hp with ⟨t, _ht0, _ht1, hpt⟩
  rw [hpt]
  exact edgeNormalCoord_segmentPoint_eq_zero a b t

/-- Zero signed normal coordinate means membership in the affine line through
the directed edge endpoints. -/
theorem mem_affineSpan_pair_of_edgeNormalCoord_eq_zero_of_ne
    {p a b : PlanarInterface.Point}
    (hab : a ≠ b)
    (hp : edgeNormalCoord a b p = 0) :
    p ∈ (line[ℝ, a, b] : AffineSubspace ℝ PlanarInterface.Point) := by
  have hcross :
      (b.1 - a.1) * (p.2 - a.2) =
        (b.2 - a.2) * (p.1 - a.1) := by
    unfold edgeNormalCoord edgeNormalLinearMap at hp
    simp at hp
    nlinarith
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  by_cases hdx : b.1 - a.1 = 0
  · have hdy : b.2 - a.2 ≠ 0 := by
      intro hdy
      exact hab (Prod.ext (by linarith) (by linarith))
    refine ⟨(p.2 - a.2) / (b.2 - a.2), ?_⟩
    ext <;> simp [AffineMap.lineMap_apply_module]
    · have hb1 : b.1 = a.1 := sub_eq_zero.mp hdx
      have hp1 : p.1 = a.1 := by
        have hmul : (b.2 - a.2) * (p.1 - a.1) = 0 := by
          rw [← hcross, hdx, zero_mul]
        have hp1zero : p.1 - a.1 = 0 := (mul_eq_zero.mp hmul).resolve_left hdy
        linarith
      rw [hb1, hp1]
      ring
    · field_simp [hdy]
      ring
  · refine ⟨(p.1 - a.1) / (b.1 - a.1), ?_⟩
    ext <;> simp [AffineMap.lineMap_apply_module]
    · field_simp [hdx]
      ring
    · field_simp [hdx]
      nlinarith

/-- Near an open-segment point of a nondegenerate edge, the local residual of
the affine edge-line is contained in the closed segment.  This is the
finite-drawing input needed to turn frontier closure into a strict same-side
exterior patch. -/
theorem exists_ball_inter_edgeNormalCoord_zero_subset_closedSegment_of_inOpenSegment_of_ne
    {p a b : PlanarInterface.Point}
    (hab : a ≠ b)
    (hp : PlanarInterface.InOpenSegment p a b) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball p ε ∩
            {q : PlanarInterface.Point | edgeNormalCoord a b q = 0} ⊆
          closedSegment a b := by
  rcases hp with ⟨t, ht0, ht1, hpt⟩
  let D : Real := dist a b
  have hDpos : 0 < D := by
    simpa [D] using dist_pos.2 hab
  have ht1pos : 0 < 1 - t := by linarith
  let ε : Real := min (t * D) ((1 - t) * D)
  have hεpos : 0 < ε := by
    exact lt_min (mul_pos ht0 hDpos) (mul_pos ht1pos hDpos)
  refine ⟨ε, hεpos, ?_⟩
  intro q hq
  rcases
      (mem_affineSpan_pair_iff_exists_lineMap_eq.1
        (mem_affineSpan_pair_of_edgeNormalCoord_eq_zero_of_ne
          (p := q) (a := a) (b := b) hab hq.2)) with
    ⟨s, hsq⟩
  have hp_line : AffineMap.lineMap a b t = p := by
    rw [← segmentPoint_eq_affineLineMap, hpt]
  have hdist_eq : dist p q = dist t s * D := by
    rw [← hp_line, ← hsq]
    simpa [D] using dist_lineMap_lineMap a b t s
  have hdist_pq_lt : dist p q < ε := by
    simpa [dist_comm, Metric.mem_ball] using hq.1
  have hdist_lt : dist t s * D < ε := by
    simpa [hdist_eq] using hdist_pq_lt
  have hdist_lt_left : dist t s * D < t * D :=
    lt_of_lt_of_le hdist_lt (min_le_left _ _)
  have hdist_lt_right : dist t s * D < (1 - t) * D :=
    lt_of_lt_of_le hdist_lt (min_le_right _ _)
  have hparam_left : dist t s < t := by
    exact lt_of_mul_lt_mul_right hdist_lt_left hDpos.le
  have hparam_right : dist t s < 1 - t := by
    exact lt_of_mul_lt_mul_right hdist_lt_right hDpos.le
  have hs0 : 0 ≤ s := by
    by_contra hsneg
    have hslt : s < 0 := lt_of_not_ge hsneg
    have hge : t ≤ dist t s := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    linarith
  have hs1 : s ≤ 1 := by
    by_contra hsgt_not
    have hsgt : 1 < s := lt_of_not_ge hsgt_not
    have hge : 1 - t ≤ dist t s := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    linarith
  exact
    ⟨s, hs0, hs1,
      calc
        q = AffineMap.lineMap a b s := hsq.symm
        _ = PlanarInterface.segmentPoint a b s :=
          (segmentPoint_eq_affineLineMap a b s).symm⟩

/-- The positive strict side of the directed edge, restricted to a metric
ball. -/
def edgePositiveSideBall
    (a b z : PlanarInterface.Point) (r : Real) :
    Set PlanarInterface.Point :=
  {p | 0 < edgeNormalCoord a b p} ∩ Metric.ball z r

/-- The positive side-ball is convex. -/
theorem convex_edgePositiveSideBall
    (a b z : PlanarInterface.Point) (r : Real) :
    Convex ℝ (edgePositiveSideBall a b z r) := by
  have hhalf :
      Convex ℝ
        {p : PlanarInterface.Point |
          edgeNormalLinearMap a b a < edgeNormalLinearMap a b p} :=
    convex_halfSpace_gt (edgeNormalLinearMap a b).isLinear
      (edgeNormalLinearMap a b a)
  simpa [edgePositiveSideBall, edgeNormalCoord, sub_pos] using
    hhalf.inter (convex_ball z r)

/-- The positive side-ball is preconnected. -/
theorem isPreconnected_edgePositiveSideBall
    (a b z : PlanarInterface.Point) (r : Real) :
    IsPreconnected (edgePositiveSideBall a b z r) :=
  (convex_edgePositiveSideBall a b z r).isPreconnected

/-- A point on a nondegenerate edge-line is accumulated by the positive
side-ball at every positive radius. -/
theorem mem_closure_edgePositiveSideBall_of_edgeNormalCoord_eq_zero
    {a b z : PlanarInterface.Point} {r : Real}
    (hz : edgeNormalCoord a b z = 0)
    (hab : a ≠ b)
    (hr : 0 < r) :
    z ∈ closure (edgePositiveSideBall a b z r) := by
  rw [Metric.mem_closure_iff]
  intro eps heps
  have hmin_pos : 0 < min r eps := lt_min hr heps
  have hcont :
      Filter.Tendsto (fun δ : Real => normalOffsetPoint a b z δ)
        (nhds 0) (nhds z) := by
    have hcontinuous := continuous_normalOffsetPoint a b z
    have ht := hcontinuous.continuousAt (x := (0 : Real))
    change
      Filter.Tendsto (fun δ : Real => normalOffsetPoint a b z δ)
        (nhds 0) (nhds (normalOffsetPoint a b z 0)) at ht
    simpa [normalOffsetPoint_zero a b z] using ht
  have hpreimage :
      {δ : Real | normalOffsetPoint a b z δ ∈ Metric.ball z (min r eps)}
        ∈ nhds (0 : Real) :=
    hcont (Metric.ball_mem_nhds z hmin_pos)
  rcases Metric.mem_nhds_iff.1 hpreimage with
    ⟨η, hηpos, hηsubset⟩
  let δ : Real := min (η / 2) 1
  have hδpos : 0 < δ := lt_min (half_pos hηpos) (by norm_num)
  have hδball : δ ∈ Metric.ball (0 : Real) η := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hδnonneg : 0 <= δ := le_of_lt hδpos
    rw [sub_zero, abs_of_nonneg hδnonneg]
    exact lt_of_le_of_lt (min_le_left (η / 2) 1) (half_lt_self hηpos)
  let y : PlanarInterface.Point := normalOffsetPoint a b z δ
  have hyball_min : y ∈ Metric.ball z (min r eps) := hηsubset hδball
  have hyball_r : y ∈ Metric.ball z r :=
    Metric.ball_subset_ball (min_le_left r eps) hyball_min
  have hydist_yz : dist y z < eps :=
    (Metric.ball_subset_ball (min_le_right r eps) hyball_min)
  have hydist : dist z y < eps := by
    simpa [dist_comm] using hydist_yz
  refine ⟨y, ?_, hydist⟩
  exact
    ⟨edgeNormalCoord_normalOffsetPoint_pos_of_zero_of_pos_of_ne
        hz hδpos hab,
      hyball_r⟩

/-- Any point on the affine edge-line inside the metric part of a side-ball is
accumulated by that side-ball.  This is the translated-center version used to
propagate exterior closure along a locally isolated open edge. -/
theorem mem_closure_edgePositiveSideBall_of_edgeNormalCoord_eq_zero_of_mem_ball
    {a b c z : PlanarInterface.Point} {r : Real}
    (hz : edgeNormalCoord a b z = 0)
    (hab : a ≠ b)
    (hzball : z ∈ Metric.ball c r) :
    z ∈ closure (edgePositiveSideBall a b c r) := by
  rw [Metric.mem_closure_iff]
  intro eps heps
  have hcont :
      Filter.Tendsto (fun δ : Real => normalOffsetPoint a b z δ)
        (nhds 0) (nhds z) := by
    have hcontinuous := continuous_normalOffsetPoint a b z
    have ht := hcontinuous.continuousAt (x := (0 : Real))
    change
      Filter.Tendsto (fun δ : Real => normalOffsetPoint a b z δ)
        (nhds 0) (nhds (normalOffsetPoint a b z 0)) at ht
    simpa [normalOffsetPoint_zero a b z] using ht
  have hpreimage_c :
      {δ : Real | normalOffsetPoint a b z δ ∈ Metric.ball c r}
        ∈ nhds (0 : Real) :=
    hcont (Metric.isOpen_ball.mem_nhds hzball)
  have hpreimage_eps :
      {δ : Real | normalOffsetPoint a b z δ ∈ Metric.ball z eps}
        ∈ nhds (0 : Real) :=
    hcont (Metric.ball_mem_nhds z heps)
  have hpreimage :
      {δ : Real |
        normalOffsetPoint a b z δ ∈ Metric.ball c r ∧
          normalOffsetPoint a b z δ ∈ Metric.ball z eps}
        ∈ nhds (0 : Real) := by
    simpa [Set.inter_def] using Filter.inter_mem hpreimage_c hpreimage_eps
  rcases Metric.mem_nhds_iff.1 hpreimage with
    ⟨η, hηpos, hηsubset⟩
  let δ : Real := min (η / 2) 1
  have hδpos : 0 < δ := lt_min (half_pos hηpos) (by norm_num)
  have hδball : δ ∈ Metric.ball (0 : Real) η := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hδnonneg : 0 <= δ := le_of_lt hδpos
    rw [sub_zero, abs_of_nonneg hδnonneg]
    exact lt_of_le_of_lt (min_le_left (η / 2) 1) (half_lt_self hηpos)
  let y : PlanarInterface.Point := normalOffsetPoint a b z δ
  have hydata := hηsubset hδball
  have hydist_yz : dist y z < eps := by
    simpa [y, Metric.mem_ball] using hydata.2
  have hydist : dist z y < eps := by
    simpa [dist_comm] using hydist_yz
  refine ⟨y, ?_, hydist⟩
  exact
    ⟨edgeNormalCoord_normalOffsetPoint_pos_of_zero_of_pos_of_ne
        hz hδpos hab,
      by simpa [y] using hydata.1⟩

/-- A point strictly on one side of the affine line through a closed segment
cannot lie on that closed segment. -/
theorem sSameSide_line_not_mem_closedSegment
    {q y a b : PlanarInterface.Point}
    (hqside :
      (line[ℝ, a, b] : AffineSubspace ℝ PlanarInterface.Point).SSameSide
        y q) :
    q ∉ closedSegment a b := by
  intro hqseg
  exact hqside.right_notMem
    (closedSegment_subset_affineSpan_pair a b hqseg)

/-- Closed straight segments are compact. -/
theorem isCompact_closedSegment (a b : PlanarInterface.Point) :
    IsCompact (closedSegment a b) := by
  rw [closedSegment_eq_image_Icc]
  exact isCompact_Icc.image (continuous_segmentPoint a b)

/-- Closed straight segments are topologically closed in the plane. -/
theorem isClosed_closedSegment (a b : PlanarInterface.Point) :
    IsClosed (closedSegment a b) :=
  (isCompact_closedSegment a b).isClosed

/-- The left endpoint lies on its closed segment. -/
theorem left_mem_closedSegment (a b : PlanarInterface.Point) :
    a ∈ closedSegment a b := by
  refine ⟨0, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · ext <;> norm_num [PlanarInterface.segmentPoint]

/-- The right endpoint lies on its closed segment. -/
theorem right_mem_closedSegment (a b : PlanarInterface.Point) :
    b ∈ closedSegment a b := by
  refine ⟨1, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · ext <;> norm_num [PlanarInterface.segmentPoint]

theorem segmentPoint_mem_closedSegment
    (a b : PlanarInterface.Point) {t : Real}
    (ht0 : 0 <= t) (ht1 : t <= 1) :
    PlanarInterface.segmentPoint a b t ∈ closedSegment a b :=
  ⟨t, ht0, ht1, rfl⟩

theorem inOpenSegment_mem_closedSegment
    {x a b : PlanarInterface.Point}
    (hx : PlanarInterface.InOpenSegment x a b) :
    x ∈ closedSegment a b := by
  rcases hx with ⟨t, ht0, ht1, hxt⟩
  exact ⟨t, le_of_lt ht0, le_of_lt ht1, hxt⟩

theorem mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment
    {x a b : PlanarInterface.Point}
    (hx : x ∈ closedSegment a b) :
    x = a ∨ x = b ∨ PlanarInterface.InOpenSegment x a b := by
  rcases hx with ⟨t, ht0, ht1, hxt⟩
  rcases lt_trichotomy t 0 with htneg | rfl | htpos
  · exact False.elim ((not_lt_of_ge ht0) htneg)
  · left
    simpa [PlanarInterface.segmentPoint] using hxt
  · rcases lt_trichotomy t 1 with htlt | htEq | htgt
    · exact Or.inr (Or.inr ⟨t, htpos, htlt, hxt⟩)
    · subst t
      right
      left
      simpa [PlanarInterface.segmentPoint] using hxt
    · exact False.elim ((not_lt_of_ge ht1) htgt)

theorem closedSegment_symm
    (a b : PlanarInterface.Point) :
    closedSegment a b = closedSegment b a := by
  ext x
  constructor
  · rintro ⟨t, ht0, ht1, hxt⟩
    refine ⟨1 - t, sub_nonneg.mpr ht1, by linarith, ?_⟩
    rw [hxt]
    ext <;> simp [PlanarInterface.segmentPoint] <;> ring
  · rintro ⟨t, ht0, ht1, hxt⟩
    refine ⟨1 - t, sub_nonneg.mpr ht1, by linarith, ?_⟩
    rw [hxt]
    ext <;> simp [PlanarInterface.segmentPoint] <;> ring

/-- Closed-segment membership is symmetric in the two endpoints. -/
theorem mem_closedSegment_symm
    {p a b : PlanarInterface.Point} :
    p ∈ closedSegment a b <-> p ∈ closedSegment b a := by
  rw [closedSegment_symm]

/-- Reversing endpoints corresponds to replacing the segment parameter `t` by
`1 - t`. -/
theorem segmentPoint_symm
    (a b : PlanarInterface.Point) (t : Real) :
    PlanarInterface.segmentPoint a b t =
      PlanarInterface.segmentPoint b a (1 - t) := by
  ext <;> simp [PlanarInterface.segmentPoint] <;> ring

/-- Open-segment membership is symmetric in the two endpoints. -/
theorem inOpenSegment_symm
    {p a b : PlanarInterface.Point}
    (hp : PlanarInterface.InOpenSegment p a b) :
    PlanarInterface.InOpenSegment p b a := by
  rcases hp with ⟨t, ht0, ht1, hpt⟩
  refine ⟨1 - t, by linarith, by linarith, ?_⟩
  rw [hpt, segmentPoint_symm]

/-- The project-local open straight segment is preconnected. -/
theorem isPreconnected_inOpenSegment
    (a b : PlanarInterface.Point) :
    IsPreconnected
      ({p : PlanarInterface.Point |
        PlanarInterface.InOpenSegment p a b} :
        Set PlanarInterface.Point) := by
  have hset :
      ({p : PlanarInterface.Point |
        PlanarInterface.InOpenSegment p a b} :
        Set PlanarInterface.Point) =
        (fun t : Real => PlanarInterface.segmentPoint a b t) ''
          Set.Ioo (0 : Real) 1 := by
    ext p
    constructor
    · rintro ⟨t, ht0, ht1, hpt⟩
      exact ⟨t, ⟨ht0, ht1⟩, hpt.symm⟩
    · rintro ⟨t, ht, hpt⟩
      exact ⟨t, ht.1, ht.2, hpt.symm⟩
  rw [hset]
  exact isPreconnected_Ioo.image _
    (continuous_segmentPoint a b).continuousOn

/-- The affine midpoint lies in the project-local open segment. -/
theorem midpoint_inOpenSegment
    (a b : PlanarInterface.Point) :
    PlanarInterface.InOpenSegment
      (PlanarInterface.segmentPoint a b (1 / 2 : Real)) a b := by
  refine ⟨1 / 2, by norm_num, by norm_num, rfl⟩

/-- The left endpoint is in the closure of the corresponding open segment.
This is used later to put endpoints of a whole-frontier open edge segment onto
the closed frontier. -/
theorem left_mem_closure_inOpenSegment
    (a b : PlanarInterface.Point) :
    Set.Mem
      (closure
        ({p | PlanarInterface.InOpenSegment p a b} :
          Set PlanarInterface.Point))
      a := by
  change a ∈
    closure
      ({p | PlanarInterface.InOpenSegment p a b} :
        Set PlanarInterface.Point)
  rw [Metric.mem_closure_iff]
  intro eps heps
  have hseg0 : PlanarInterface.segmentPoint a b 0 = a := by
    ext <;> simp [PlanarInterface.segmentPoint]
  have htend :
      Filter.Tendsto (fun t : Real => PlanarInterface.segmentPoint a b t)
        (nhds (0 : Real)) (nhds a) := by
    simpa [hseg0] using
      ((continuous_segmentPoint a b).continuousAt
        (x := (0 : Real))).tendsto
  have hball_mem :
      Set.preimage (fun t : Real => PlanarInterface.segmentPoint a b t)
          (Metric.ball a eps) ∈ nhds (0 : Real) :=
    htend (Metric.ball_mem_nhds a heps)
  rcases Metric.mem_nhds_iff.1 hball_mem with ⟨delta, hdelta, hdeltasub⟩
  let t : Real := min (delta / 2) (1 / 2)
  have ht0 : 0 < t :=
    lt_min (half_pos hdelta) (by norm_num)
  have ht1 : t < 1 :=
    lt_of_le_of_lt (min_le_right (delta / 2) (1 / 2)) (by norm_num)
  have htdelta : t ∈ Metric.ball (0 : Real) delta := by
    rw [Metric.mem_ball, Real.dist_eq]
    have ht_nonneg : 0 <= t := le_of_lt ht0
    rw [sub_zero, abs_of_nonneg ht_nonneg]
    exact lt_of_le_of_lt
      (min_le_left (delta / 2) (1 / 2)) (half_lt_self hdelta)
  refine ⟨PlanarInterface.segmentPoint a b t, ?_, ?_⟩
  · exact ⟨t, ht0, ht1, rfl⟩
  · simpa [Metric.mem_ball, dist_comm] using hdeltasub htdelta

/-- The right endpoint is in the closure of the corresponding open segment. -/
theorem right_mem_closure_inOpenSegment
    (a b : PlanarInterface.Point) :
    Set.Mem
      (closure
        ({p | PlanarInterface.InOpenSegment p a b} :
          Set PlanarInterface.Point))
      b := by
  change b ∈
    closure
      ({p | PlanarInterface.InOpenSegment p a b} :
        Set PlanarInterface.Point)
  have hset :
      ({p | PlanarInterface.InOpenSegment p b a} :
        Set PlanarInterface.Point) =
        ({p | PlanarInterface.InOpenSegment p a b} :
          Set PlanarInterface.Point) := by
    ext p
    constructor <;> intro hp <;> exact inOpenSegment_symm hp
  simpa [hset] using left_mem_closure_inOpenSegment b a

/-- If two segment parametrizations start at the same point, use the same
nonzero parameter, and name the same point, then they have the same endpoint. -/
theorem segmentPoint_eq_same_left_of_pos
    {a b c : PlanarInterface.Point} {t : Real}
    (ht : 0 < t)
    (h :
      PlanarInterface.segmentPoint a b t =
        PlanarInterface.segmentPoint a c t) :
    b = c := by
  apply Prod.ext
  · have hcoord :
        (1 - t) * a.1 + t * b.1 =
          (1 - t) * a.1 + t * c.1 := by
      simpa [PlanarInterface.segmentPoint] using congrArg Prod.fst h
    have hmul : t * (b.1 - c.1) = 0 := by
      linarith
    have htne : t ≠ 0 := ne_of_gt ht
    rcases mul_eq_zero.mp hmul with htzero | hdiff
    · exact False.elim (htne htzero)
    · exact sub_eq_zero.mp hdiff
  · have hcoord :
        (1 - t) * a.2 + t * b.2 =
          (1 - t) * a.2 + t * c.2 := by
      simpa [PlanarInterface.segmentPoint] using congrArg Prod.snd h
    have hmul : t * (b.2 - c.2) = 0 := by
      linarith
    have htne : t ≠ 0 := ne_of_gt ht
    rcases mul_eq_zero.mp hmul with htzero | hdiff
    · exact False.elim (htne htzero)
    · exact sub_eq_zero.mp hdiff

/-- In a nondegenerate segment, an open-segment point is not the left
endpoint. -/
theorem left_ne_of_inOpenSegment
    {p a b : PlanarInterface.Point}
    (hab : a ≠ b)
    (hp : PlanarInterface.InOpenSegment p a b) :
    p ≠ a := by
  rintro rfl
  rcases hp with ⟨t, ht0, _ht1, hpt⟩
  have hseg :
    PlanarInterface.segmentPoint p b t =
        PlanarInterface.segmentPoint p p t := by
    rw [← hpt]
    ext <;> simp [PlanarInterface.segmentPoint] <;> ring
  exact hab (segmentPoint_eq_same_left_of_pos ht0 hseg).symm

/-- In a nondegenerate segment, an open-segment point is not the right
endpoint. -/
theorem right_ne_of_inOpenSegment
    {p a b : PlanarInterface.Point}
    (hab : a ≠ b)
    (hp : PlanarInterface.InOpenSegment p a b) :
    p ≠ b := by
  exact
    left_ne_of_inOpenSegment
      (p := p) (a := b) (b := a)
      (fun hba => hab hba.symm) (inOpenSegment_symm hp)

/-- Around an open-segment point of a nondegenerate segment, the closed segment
has no endpoint: a small ball meets the closed segment only in its open
subsegment. -/
theorem exists_ball_inter_closedSegment_subset_inOpenSegment_of_ne
    {p a b : PlanarInterface.Point}
    (hab : a ≠ b)
    (hp : PlanarInterface.InOpenSegment p a b) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball p ε ∩ closedSegment a b ⊆
          {q | PlanarInterface.InOpenSegment q a b} := by
  have hpa : p ≠ a := left_ne_of_inOpenSegment hab hp
  have hpb : p ≠ b := right_ne_of_inOpenSegment hab hp
  refine ⟨min (dist p a) (dist p b), ?_, ?_⟩
  · exact lt_min (dist_pos.2 hpa) (dist_pos.2 hpb)
  · intro q hq
    rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hq.2 with
        hqa | hqb | hqopen
    · have hdist : dist p a < min (dist p a) (dist p b) := by
        simpa [hqa, dist_comm, Metric.mem_ball] using hq.1
      exact False.elim ((not_lt_of_ge (min_le_left _ _)) hdist)
    · have hdist : dist p b < min (dist p a) (dist p b) := by
        simpa [hqb, dist_comm, Metric.mem_ball] using hq.1
      exact False.elim ((not_lt_of_ge (min_le_right _ _)) hdist)
    · exact hqopen

/-- Around an open-segment point, a small ball meets the closed segment only
in its open subsegment.  The degenerate case is harmless because then the
closed and open segment carriers are both the singleton endpoint. -/
theorem exists_ball_inter_closedSegment_subset_inOpenSegment
    {p a b : PlanarInterface.Point}
    (hp : PlanarInterface.InOpenSegment p a b) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball p ε ∩ closedSegment a b ⊆
          {q | PlanarInterface.InOpenSegment q a b} := by
  by_cases hab : a = b
  · subst b
    refine ⟨1, by norm_num, ?_⟩
    intro q hq
    rcases hq.2 with ⟨t, _ht0, _ht1, hqt⟩
    rw [hqt]
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    ext <;> simp [PlanarInterface.segmentPoint] <;> ring
  · exact exists_ball_inter_closedSegment_subset_inOpenSegment_of_ne hab hp

/-- Pointwise form of
`exists_ball_inter_closedSegment_subset_inOpenSegment_of_ne`. -/
theorem exists_ball_forall_mem_inOpenSegment_of_mem_closedSegment_of_ne
    {p a b : PlanarInterface.Point}
    (hab : a ≠ b)
    (hp : PlanarInterface.InOpenSegment p a b) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball p ε ->
            q ∈ closedSegment a b ->
              PlanarInterface.InOpenSegment q a b := by
  rcases exists_ball_inter_closedSegment_subset_inOpenSegment_of_ne hab hp with
    ⟨ε, hεpos, hsubset⟩
  exact ⟨ε, hεpos, fun q hqball hqseg => hsubset ⟨hqball, hqseg⟩⟩

/-- Pointwise form of
`exists_ball_inter_closedSegment_subset_inOpenSegment`. -/
theorem exists_ball_forall_mem_inOpenSegment_of_mem_closedSegment
    {p a b : PlanarInterface.Point}
    (hp : PlanarInterface.InOpenSegment p a b) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball p ε ->
            q ∈ closedSegment a b ->
              PlanarInterface.InOpenSegment q a b := by
  rcases exists_ball_inter_closedSegment_subset_inOpenSegment hp with
    ⟨ε, hεpos, hsubset⟩
  exact ⟨ε, hεpos, fun q hqball hqseg => hsubset ⟨hqball, hqseg⟩⟩

theorem eucDist_left_segmentPoint
    (a b : PlanarInterface.Point) (t : Real) (ht : 0 <= t) :
    _root_.eucDist a (PlanarInterface.segmentPoint a b t) =
      t * _root_.eucDist a b := by
  unfold _root_.eucDist PlanarInterface.segmentPoint
  have hs :
      (a.1 - ((1 - t) * a.1 + t * b.1)) ^ 2 +
        (a.2 - ((1 - t) * a.2 + t * b.2)) ^ 2 =
      t ^ 2 * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by
    ring
  rw [hs]
  rw [Real.sqrt_mul (sq_nonneg t)]
  rw [Real.sqrt_sq ht]

theorem eucDist_segmentPoint_right
    (a b : PlanarInterface.Point) (t : Real) (ht : t <= 1) :
    _root_.eucDist (PlanarInterface.segmentPoint a b t) b =
      (1 - t) * _root_.eucDist a b := by
  unfold _root_.eucDist PlanarInterface.segmentPoint
  have hs :
      (((1 - t) * a.1 + t * b.1) - b.1) ^ 2 +
        (((1 - t) * a.2 + t * b.2) - b.2) ^ 2 =
      (1 - t) ^ 2 * ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := by
    ring
  rw [hs]
  rw [Real.sqrt_mul (sq_nonneg (1 - t))]
  rw [Real.sqrt_sq (sub_nonneg.mpr ht)]

/-- The geometric drawing of the canonical unit-distance graph, as the union of
all closed straight segments carried by graph adjacencies. -/
def embeddedEdgeSet (C : _root_.UDConfig n) : Set PlanarInterface.Point :=
  {p | Exists fun i : Fin n =>
    Exists fun j : Fin n =>
      (canonicalGraph C).Adj i j /\
        p ∈ closedSegment
          ((canonicalGraph C).point i)
          ((canonicalGraph C).point j)}

/-- Membership in the embedded drawing, unfolded to an adjacent ordered
carrier and closed-segment membership. -/
theorem mem_embeddedEdgeSet_iff
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} :
    p ∈ embeddedEdgeSet C <->
      Exists fun i : Fin n =>
        Exists fun j : Fin n =>
          (canonicalGraph C).Adj i j /\
            p ∈ closedSegment
              ((canonicalGraph C).point i)
              ((canonicalGraph C).point j) :=
  Iff.rfl

/-- Membership in the embedded drawing can be witnessed by one of the stored
ordered canonical edges.  Reversed adjacency witnesses are normalized by
reversing the closed segment. -/
theorem mem_embeddedEdgeSet_iff_exists_edge_mem_closedSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} :
    p ∈ embeddedEdgeSet C <->
      Exists fun e : PlanarInterface.Edge n =>
        e ∈ (canonicalGraph C).edgeSet /\
          p ∈ closedSegment
            ((canonicalGraph C).point e.1)
            ((canonicalGraph C).point e.2) := by
  constructor
  · rintro ⟨i, j, hAdj, hpseg⟩
    rcases hAdj with he | he
    · exact ⟨(i, j), he, hpseg⟩
    · exact ⟨(j, i), he, (mem_closedSegment_symm.1 hpseg)⟩
  · rintro ⟨e, he, hpseg⟩
    exact ⟨e.1, e.2, Or.inl he, hpseg⟩

/-- The finite set of ordered canonical graph edges used to present the
embedded drawing as a finite union of closed segments. -/
def embeddedEdgePairs (C : _root_.UDConfig n) :
    Finset (Prod (Fin n) (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).product
      (Finset.univ : Finset (Fin n))).filter
    (fun e : Prod (Fin n) (Fin n) => (canonicalGraph C).Adj e.1 e.2)

theorem mem_embeddedEdgePairs_iff
    {C : _root_.UDConfig n} {e : Prod (Fin n) (Fin n)} :
    e ∈ embeddedEdgePairs C <-> (canonicalGraph C).Adj e.1 e.2 := by
  classical
  simp [embeddedEdgePairs]

/-- The existential drawing definition is equivalent to the finite ordered-edge
presentation. -/
theorem mem_embeddedEdgeSet_iff_exists_embeddedEdgePairs
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} :
    p ∈ embeddedEdgeSet C <->
      Exists fun e : Prod (Fin n) (Fin n) =>
        e ∈ embeddedEdgePairs C /\
          p ∈ closedSegment
            ((canonicalGraph C).point e.1)
            ((canonicalGraph C).point e.2) := by
  classical
  constructor
  · intro hp
    rcases hp with ⟨i, j, hAdj, hpseg⟩
    refine ⟨(i, j), ?_, hpseg⟩
    exact mem_embeddedEdgePairs_iff.2 hAdj
  · intro hp
    rcases hp with ⟨e, he, hpseg⟩
    refine ⟨e.1, e.2, ?_, hpseg⟩
    exact mem_embeddedEdgePairs_iff.1 he

/-- The embedded drawing as a finite double union over all ordered vertex
pairs, retaining only adjacent pairs. -/
theorem embeddedEdgeSet_eq_iUnion_edges
    (C : _root_.UDConfig n) :
    embeddedEdgeSet C =
      ⋃ i : Fin n, ⋃ j : Fin n,
        {p | (canonicalGraph C).Adj i j /\
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} := by
  ext p
  simp [embeddedEdgeSet]

/-- The embedded drawing is closed: it is a finite union of compact straight
segments. -/
theorem embeddedEdgeSet_closed
    (C : _root_.UDConfig n) :
    IsClosed (embeddedEdgeSet C) := by
  rw [embeddedEdgeSet_eq_iUnion_edges]
  apply isClosed_iUnion_of_finite
  intro i
  apply isClosed_iUnion_of_finite
  intro j
  by_cases hAdj : (canonicalGraph C).Adj i j
  · rw [show {p | (canonicalGraph C).Adj i j /\
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} =
          closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) by
        ext p
        simp [hAdj]]
    exact isClosed_closedSegment _ _
  · rw [show {p | (canonicalGraph C).Adj i j /\
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} =
          (∅ : Set PlanarInterface.Point) by
        ext p
        simp [hAdj]]
    exact isClosed_empty

/-- The embedded drawing is compact: it is a finite union of compact straight
segments. -/
theorem embeddedEdgeSet_compact
    (C : _root_.UDConfig n) :
    IsCompact (embeddedEdgeSet C) := by
  rw [embeddedEdgeSet_eq_iUnion_edges]
  simpa only [Set.mem_univ, Set.iUnion_true] using
    (Set.finite_univ.isCompact_biUnion (s := (Set.univ : Set (Fin n)))
      (f := fun i : Fin n =>
        ⋃ j : Fin n,
          {p | (canonicalGraph C).Adj i j /\
            p ∈ closedSegment
              ((canonicalGraph C).point i)
              ((canonicalGraph C).point j)})
      (by
        intro i _hi
        simpa only [Set.mem_univ, Set.iUnion_true] using
          (Set.finite_univ.isCompact_biUnion (s := (Set.univ : Set (Fin n)))
            (f := fun j : Fin n =>
              {p | (canonicalGraph C).Adj i j /\
                p ∈ closedSegment
                  ((canonicalGraph C).point i)
                  ((canonicalGraph C).point j)})
            (by
              intro j _hj
              by_cases hAdj : (canonicalGraph C).Adj i j
              · simpa [hAdj] using
                  isCompact_closedSegment
                    ((canonicalGraph C).point i)
                    ((canonicalGraph C).point j)
              · simp [hAdj]))))

/-- The tail endpoint of any canonical graph edge lies in the embedded drawing. -/
theorem left_vertex_mem_embeddedEdgeSet_of_adj
    {C : _root_.UDConfig n} {i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j) :
    (canonicalGraph C).point i ∈ embeddedEdgeSet C := by
  exact
    ⟨i, j, hAdj,
      left_mem_closedSegment
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)⟩

/-- The head endpoint of any canonical graph edge lies in the embedded drawing. -/
theorem right_vertex_mem_embeddedEdgeSet_of_adj
    {C : _root_.UDConfig n} {i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j) :
    (canonicalGraph C).point j ∈ embeddedEdgeSet C := by
  exact
    ⟨i, j, hAdj,
      right_mem_closedSegment
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)⟩

/-- A canonical graph edge contributes its whole closed segment to the embedded
drawing. -/
theorem closedSegment_subset_embeddedEdgeSet_of_adj
    {C : _root_.UDConfig n} {i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j) :
    closedSegment
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) ⊆
      embeddedEdgeSet C := by
  intro p hp
  exact ⟨i, j, hAdj, hp⟩

theorem segmentPoint_mem_embeddedEdgeSet_of_adj
    {C : _root_.UDConfig n} {i j : Fin n} {t : Real}
    (hAdj : (canonicalGraph C).Adj i j)
    (ht0 : 0 <= t) (ht1 : t <= 1) :
    PlanarInterface.segmentPoint
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) t ∈
      embeddedEdgeSet C :=
  closedSegment_subset_embeddedEdgeSet_of_adj hAdj
    (segmentPoint_mem_closedSegment _ _ ht0 ht1)

theorem mem_embeddedEdgeSet_of_mem_embeddedEdgePairs
    {C : _root_.UDConfig n} {e : Prod (Fin n) (Fin n)}
    (he : e ∈ embeddedEdgePairs C) :
    closedSegment
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2) ⊆
      embeddedEdgeSet C :=
  closedSegment_subset_embeddedEdgeSet_of_adj
    (mem_embeddedEdgePairs_iff.1 he)

theorem left_vertex_mem_embeddedEdgeSet_of_mem_embeddedEdgePairs
    {C : _root_.UDConfig n} {e : Prod (Fin n) (Fin n)}
    (he : e ∈ embeddedEdgePairs C) :
    (canonicalGraph C).point e.1 ∈ embeddedEdgeSet C :=
  mem_embeddedEdgeSet_of_mem_embeddedEdgePairs he
    (left_mem_closedSegment _ _)

theorem right_vertex_mem_embeddedEdgeSet_of_mem_embeddedEdgePairs
    {C : _root_.UDConfig n} {e : Prod (Fin n) (Fin n)}
    (he : e ∈ embeddedEdgePairs C) :
    (canonicalGraph C).point e.2 ∈ embeddedEdgeSet C :=
  mem_embeddedEdgeSet_of_mem_embeddedEdgePairs he
    (right_mem_closedSegment _ _)

theorem inOpenSegment_subset_embeddedEdgeSet_of_adj
    {C : _root_.UDConfig n} {i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j) :
    {p | PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)} ⊆
      embeddedEdgeSet C := by
  intro p hp
  exact closedSegment_subset_embeddedEdgeSet_of_adj hAdj
    (inOpenSegment_mem_closedSegment hp)

theorem inOpenSegment_mem_embeddedEdgeSet_of_adj
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} {i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j)
    (hp :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)) :
    p ∈ embeddedEdgeSet C :=
  inOpenSegment_subset_embeddedEdgeSet_of_adj hAdj hp

theorem graph_vertex_on_unit_edge_segment_is_endpoint
    {C : _root_.UDConfig n} {v i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j)
    (hmem :
      (canonicalGraph C).point v ∈
        closedSegment
          ((canonicalGraph C).point i)
          ((canonicalGraph C).point j)) :
    v = i ∨ v = j := by
  by_cases hvi : v = i
  · exact Or.inl hvi
  by_cases hvj : v = j
  · exact Or.inr hvj
  exfalso
  rcases hmem with ⟨t, ht0, ht1, hpoint⟩
  have hij :
      _root_.eucDist ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) = 1 := by
    simpa [PlanarInterface.geometry_eucDist_eq_root] using
      ((canonicalGraph C).adj_geometry_dist_eq_one hAdj)
  have hleft :
      _root_.eucDist ((canonicalGraph C).point i)
        ((canonicalGraph C).point v) = t := by
    rw [hpoint]
    rw [eucDist_left_segmentPoint _ _ t ht0]
    rw [hij]
    ring
  have hright :
      _root_.eucDist ((canonicalGraph C).point v)
        ((canonicalGraph C).point j) = 1 - t := by
    rw [hpoint]
    rw [eucDist_segmentPoint_right _ _ t ht1]
    rw [hij]
    ring
  have hsep_left :
      1 <= _root_.eucDist ((canonicalGraph C).point i)
        ((canonicalGraph C).point v) := by
    simpa [_root_.eucDist_comm] using C.sep v i hvi
  have ht_ge_one : 1 <= t := by
    simpa [hleft] using hsep_left
  have ht_eq_one : t = 1 := le_antisymm ht1 ht_ge_one
  have hsep_right :
      1 <= _root_.eucDist ((canonicalGraph C).point v)
        ((canonicalGraph C).point j) := by
    simpa using C.sep v j hvj
  have hzero : _root_.eucDist ((canonicalGraph C).point v)
        ((canonicalGraph C).point j) = 0 := by
    rw [hright, ht_eq_one]
    ring
  linarith

theorem graph_vertex_not_inOpenSegment_of_adj
    {C : _root_.UDConfig n} {v i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j) :
    ¬ PlanarInterface.InOpenSegment
        ((canonicalGraph C).point v)
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) := by
  intro hmem
  rcases hmem with ⟨t, ht0, ht1, hpoint⟩
  have hclosed :
      (canonicalGraph C).point v ∈
        closedSegment
          ((canonicalGraph C).point i)
          ((canonicalGraph C).point j) :=
    ⟨t, le_of_lt ht0, le_of_lt ht1, hpoint⟩
  rcases graph_vertex_on_unit_edge_segment_is_endpoint hAdj hclosed with hvi | hvj
  · subst v
    have hij :
        _root_.eucDist ((canonicalGraph C).point i)
          ((canonicalGraph C).point j) = 1 := by
      simpa [PlanarInterface.geometry_eucDist_eq_root] using
        ((canonicalGraph C).adj_geometry_dist_eq_one hAdj)
    have hdist :
        _root_.eucDist ((canonicalGraph C).point i)
          (PlanarInterface.segmentPoint
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) t) = t := by
      rw [eucDist_left_segmentPoint _ _ t (le_of_lt ht0), hij]
      ring
    have hzero :
        _root_.eucDist ((canonicalGraph C).point i)
          (PlanarInterface.segmentPoint
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) t) = 0 := by
      rw [← hpoint]
      exact _root_.eucDist_self _
    linarith
  · subst v
    have hij :
        _root_.eucDist ((canonicalGraph C).point i)
          ((canonicalGraph C).point j) = 1 := by
      simpa [PlanarInterface.geometry_eucDist_eq_root] using
        ((canonicalGraph C).adj_geometry_dist_eq_one hAdj)
    have hdist :
        _root_.eucDist
          (PlanarInterface.segmentPoint
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) t)
          ((canonicalGraph C).point j) = 1 - t := by
      rw [eucDist_segmentPoint_right _ _ t (le_of_lt ht1), hij]
      ring
    have hzero :
        _root_.eucDist
          (PlanarInterface.segmentPoint
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) t)
          ((canonicalGraph C).point j) = 0 := by
      rw [← hpoint]
      exact _root_.eucDist_self _
    linarith

theorem graph_vertex_inOpenSegment_false_of_adj
    {C : _root_.UDConfig n} {v i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j)
    (hmem :
      PlanarInterface.InOpenSegment
        ((canonicalGraph C).point v)
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)) :
    False :=
  (graph_vertex_not_inOpenSegment_of_adj hAdj) hmem

/-- Canonical unit-distance adjacency is symmetric. -/
theorem canonicalAdj_symm
    {C : _root_.UDConfig n} {i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j) :
    (canonicalGraph C).Adj j i := by
  exact
    ((canonicalGraph C).adj_iff_unitDistanceAdj j i).2
      (GraphBridge.unitDistanceAdj_symm C
        (((canonicalGraph C).adj_iff_unitDistanceAdj i j).1 hAdj))

/-- The canonical point map of a separated `UDConfig` is injective. -/
theorem canonical_point_injective
    (C : _root_.UDConfig n) :
    Function.Injective (canonicalGraph C).point := by
  intro i j hij
  by_contra hne
  have hsep : 1 <= _root_.eucDist ((canonicalGraph C).point i)
      ((canonicalGraph C).point j) := by
    simpa using C.sep i j hne
  have hzero :
      _root_.eucDist ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) = 0 := by
    rw [hij]
    exact _root_.eucDist_self _
  linarith

/-- The endpoints of an ordered canonical edge are distinct as plane points. -/
theorem canonical_edge_point_ne_of_mem_edgeSet
    {C : _root_.UDConfig n} {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet) :
    (canonicalGraph C).point e.1 ≠ (canonicalGraph C).point e.2 := by
  intro hpoint
  have hindex : e.1 = e.2 := canonical_point_injective C hpoint
  exact ((canonicalGraph C).edge_mem_ordered he).ne hindex

/-- The endpoints of any adjacent canonical pair are distinct as plane points. -/
theorem canonical_adj_point_ne
    {C : _root_.UDConfig n} {i j : Fin n}
    (hAdj : (canonicalGraph C).Adj i j) :
    (canonicalGraph C).point i ≠ (canonicalGraph C).point j := by
  rcases hAdj with he | he
  · exact canonical_edge_point_ne_of_mem_edgeSet he
  · exact (canonical_edge_point_ne_of_mem_edgeSet he).symm

/-- Two unit edges starting at the same vertex cannot have an interior point
in common unless they have the same other endpoint. -/
theorem same_left_inOpenSegment_other_endpoint_eq
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} {i j k : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hik : (canonicalGraph C).Adj i k)
    (hpij :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j))
    (hpik :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point k)) :
    j = k := by
  rcases hpij with ⟨t, ht0, ht1, hpt⟩
  rcases hpik with ⟨s, hs0, hs1, hps⟩
  have hij_dist :
      _root_.eucDist ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) = 1 := by
    simpa [PlanarInterface.geometry_eucDist_eq_root] using
      ((canonicalGraph C).adj_geometry_dist_eq_one hij)
  have hik_dist :
      _root_.eucDist ((canonicalGraph C).point i)
        ((canonicalGraph C).point k) = 1 := by
    simpa [PlanarInterface.geometry_eucDist_eq_root] using
      ((canonicalGraph C).adj_geometry_dist_eq_one hik)
  have ht_dist :
      _root_.eucDist ((canonicalGraph C).point i) p = t := by
    rw [hpt, eucDist_left_segmentPoint _ _ t (le_of_lt ht0),
      hij_dist]
    ring
  have hs_dist :
      _root_.eucDist ((canonicalGraph C).point i) p = s := by
    rw [hps, eucDist_left_segmentPoint _ _ s (le_of_lt hs0),
      hik_dist]
    ring
  have hts : t = s := by linarith
  have hseg :
      PlanarInterface.segmentPoint
          ((canonicalGraph C).point i)
          ((canonicalGraph C).point j) t =
        PlanarInterface.segmentPoint
          ((canonicalGraph C).point i)
          ((canonicalGraph C).point k) t := by
    rw [← hpt, hps, ← hts]
  exact
    canonical_point_injective C
      (segmentPoint_eq_same_left_of_pos ht0 hseg)

/-- Any vertex with an incident canonical edge lies in the embedded drawing. -/
theorem vertex_mem_embeddedEdgeSet_of_incident
    {C : _root_.UDConfig n} {v w : Fin n}
    (hAdj : (canonicalGraph C).Adj v w) :
    (canonicalGraph C).point v ∈ embeddedEdgeSet C :=
  left_vertex_mem_embeddedEdgeSet_of_adj hAdj

theorem graph_vertex_mem_embeddedEdgeSet_iff_exists_adj
    {C : _root_.UDConfig n} {v : Fin n} :
    (canonicalGraph C).point v ∈ embeddedEdgeSet C <->
      Exists fun w : Fin n => (canonicalGraph C).Adj v w := by
  constructor
  · intro hv
    rcases hv with ⟨i, j, hAdj, hseg⟩
    rcases graph_vertex_on_unit_edge_segment_is_endpoint hAdj hseg with hvi | hvj
    · subst i
      exact ⟨j, hAdj⟩
    · subst j
      exact
        ⟨i,
          ((canonicalGraph C).adj_iff_unitDistanceAdj v i).2
            (GraphBridge.unitDistanceAdj_symm C
              (((canonicalGraph C).adj_iff_unitDistanceAdj i v).1 hAdj))⟩
  · rintro ⟨w, hAdj⟩
    exact vertex_mem_embeddedEdgeSet_of_incident hAdj

theorem graph_vertex_on_two_unit_edge_segments_share_endpoint
    {C : _root_.UDConfig n} {v i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hmemij :
      (canonicalGraph C).point v ∈
        closedSegment
          ((canonicalGraph C).point i)
          ((canonicalGraph C).point j))
    (hmemkl :
      (canonicalGraph C).point v ∈
        closedSegment
          ((canonicalGraph C).point k)
          ((canonicalGraph C).point l)) :
    (v = i ∨ v = j) /\ (v = k ∨ v = l) :=
  ⟨graph_vertex_on_unit_edge_segment_is_endpoint hij hmemij,
    graph_vertex_on_unit_edge_segment_is_endpoint hkl hmemkl⟩

/-- The graph-side S2 inputs imply every graph vertex lies on the embedded
unit-edge drawing.  Connectedness rules out isolated vertices because the
supplied unit-distance cycle provides a vertex in the nontrivial component. -/
theorem vertex_mem_embeddedEdgeSet_of_inputs
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    forall v : Fin n, (canonicalGraph C).point v ∈ embeddedEdgeSet C := by
  classical
  rcases inputs.hasUnitDistanceCycle with ⟨B⟩
  let k : Fin B.length := ⟨0, B.length_pos⟩
  let u : Fin n := B.vertex k
  intro v
  by_cases hvu : v = u
  · subst v
    exact left_vertex_mem_embeddedEdgeSet_of_adj (B.adjacent k)
  · have hreach :
        (GraphBridge.unitDistanceSimpleGraph C).Reachable v u :=
      inputs.connected v u
    have hv_support :
        v ∈ (GraphBridge.unitDistanceSimpleGraph C).support :=
      SimpleGraph.mem_support_of_reachable hvu hreach
    rcases
      (SimpleGraph.mem_support
        (G := GraphBridge.unitDistanceSimpleGraph C)).1 hv_support with
      ⟨w, hw⟩
    exact
      vertex_mem_embeddedEdgeSet_of_incident
        (((canonicalGraph C).adj_iff_unitDistanceAdj v w).2
          ((GraphBridge.unitDistanceSimpleGraph_adj C v w).1 hw))

/-- The embedded drawing is nonempty whenever the S2 graph-side inputs hold. -/
theorem embeddedEdgeSet_nonempty_of_inputs
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    (embeddedEdgeSet C).Nonempty := by
  classical
  obtain ⟨v⟩ := inputs.vertex_nonempty
  exact ⟨(canonicalGraph C).point v, vertex_mem_embeddedEdgeSet_of_inputs inputs v⟩

theorem adjacent_segments_not_cross_of_edgeVertexDisjoint
    {C : _root_.UDConfig n} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hdisj : PlanarInterface.EdgeVertexDisjoint (i, j) (k, l)) :
    ¬ PlanarInterface.SegmentsCrossInterior
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)
        ((canonicalGraph C).point k)
        ((canonicalGraph C).point l) := by
  have hij_dist :
      Geometry.Distance.eucDist (C.pts i) (C.pts j) = 1 := by
    simpa using ((canonicalGraph C).adj_geometry_dist_eq_one hij)
  have hkl_dist :
      Geometry.Distance.eucDist (C.pts k) (C.pts l) = 1 := by
    simpa using ((canonicalGraph C).adj_geometry_dist_eq_one hkl)
  simpa [PlanarInterface.EdgeSegmentsCross,
    PlanarInterface.StraightLineUnitDistanceGraph.point] using
    (NoncrossingUnitEdges.separated_unit_edges_not_cross
      C (e := (i, j)) (f := (k, l)) hdisj hij_dist hkl_dist)

theorem not_exists_common_inOpenSegment_of_adj_edgeVertexDisjoint
    {C : _root_.UDConfig n} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hdisj : PlanarInterface.EdgeVertexDisjoint (i, j) (k, l)) :
    ¬ Exists fun p : PlanarInterface.Point =>
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) /\
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point k)
        ((canonicalGraph C).point l) := by
  intro h
  exact
    adjacent_segments_not_cross_of_edgeVertexDisjoint hij hkl hdisj
      h

theorem inOpenSegment_inter_inOpenSegment_eq_empty_of_adj_edgeVertexDisjoint
    {C : _root_.UDConfig n} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hdisj : PlanarInterface.EdgeVertexDisjoint (i, j) (k, l)) :
    ({p | PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)} ∩
      {p | PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point k)
        ((canonicalGraph C).point l)} :
        Set PlanarInterface.Point) = ∅ := by
  ext p
  constructor
  · intro hp
    exact False.elim
      (not_exists_common_inOpenSegment_of_adj_edgeVertexDisjoint
        hij hkl hdisj ⟨p, hp.1, hp.2⟩)
  · intro hp
    exact False.elim hp

/-- Relative interiors of two canonical unit-edge segments are disjoint unless
the two ordered edges name the same unordered edge. -/
theorem common_inOpenSegment_edges_same_unordered
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hpij :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j))
    (hpkl :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point k)
        ((canonicalGraph C).point l)) :
    (i = k /\ j = l) \/ (i = l /\ j = k) := by
  classical
  by_cases hik : i = k
  · subst k
    have hjl :
        j = l :=
      same_left_inOpenSegment_other_endpoint_eq hij hkl hpij hpkl
    exact Or.inl ⟨rfl, hjl⟩
  by_cases hil : i = l
  · subst l
    have hik' :
        j = k :=
      same_left_inOpenSegment_other_endpoint_eq
        hij (canonicalAdj_symm hkl) hpij (inOpenSegment_symm hpkl)
    exact Or.inr ⟨rfl, hik'⟩
  by_cases hjk : j = k
  · subst k
    have hil' :
        i = l :=
      same_left_inOpenSegment_other_endpoint_eq
        (canonicalAdj_symm hij) hkl (inOpenSegment_symm hpij) hpkl
    exact Or.inr ⟨hil', rfl⟩
  by_cases hjl : j = l
  · subst l
    have hik' :
        i = k :=
      same_left_inOpenSegment_other_endpoint_eq
        (canonicalAdj_symm hij) (canonicalAdj_symm hkl)
        (inOpenSegment_symm hpij) (inOpenSegment_symm hpkl)
    exact Or.inl ⟨hik', rfl⟩
  have hdisj : PlanarInterface.EdgeVertexDisjoint (i, j) (k, l) :=
    ⟨hik, hil, hjk, hjl⟩
  exact False.elim
    (not_exists_common_inOpenSegment_of_adj_edgeVertexDisjoint
      hij hkl hdisj ⟨p, hpij, hpkl⟩)

/-- Ordered canonical edges are uniquely determined by any common relative
interior point. -/
theorem common_inOpenSegment_ordered_edges_eq
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    {e f : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hf : f ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2))
    (hpf :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point f.1)
        ((canonicalGraph C).point f.2)) :
    e = f := by
  rcases
      common_inOpenSegment_edges_same_unordered
        (Or.inl he) (Or.inl hf) hpe hpf with hsame | hrev
  · rcases hsame with ⟨h1, h2⟩
    cases e
    cases f
    simp_all
  · rcases hrev with ⟨h1, h2⟩
    have he_order : e.1 < e.2 :=
      (canonicalGraph C).edge_mem_ordered he
    have hf_order : f.1 < f.2 :=
      (canonicalGraph C).edge_mem_ordered hf
    have hlt_reverse : e.2 < e.1 := by
      simpa [h1, h2] using hf_order
    exact False.elim ((not_lt_of_ge he_order.le) hlt_reverse)

/-- If an interior point of one ordered canonical unit edge lies on the closed
segment of another ordered canonical unit edge, then the two ordered edges are
the same.  This is the pointwise algebraic core behind later local edge
isolation: away from endpoints, the drawing has a unique carrier edge. -/
theorem common_inOpenSegment_closedSegment_ordered_edges_eq
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    {e f : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hf : f ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2))
    (hpf :
      p ∈ closedSegment
        ((canonicalGraph C).point f.1)
        ((canonicalGraph C).point f.2)) :
    e = f := by
  rcases mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hpf with
      hp_left | hp_right | hpf_open
  · exact False.elim
      (graph_vertex_not_inOpenSegment_of_adj
        (C := C) (v := f.1) (Or.inl he) (by simpa [hp_left] using hpe))
  · exact False.elim
      (graph_vertex_not_inOpenSegment_of_adj
        (C := C) (v := f.2) (Or.inl he) (by simpa [hp_right] using hpe))
  · exact common_inOpenSegment_ordered_edges_eq he hf hpe hpf_open

/-- If an interior point of one ordered canonical edge lies on the closed
segment of another adjacent pair, then the adjacent pair names the same
unordered edge.  This removes ordered-edge bookkeeping before the local
edge-isolation proof: away from vertices, no other unit edge can pass through
the point. -/
theorem common_inOpenSegment_closedSegment_adj_same_unordered
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    {e : PlanarInterface.Edge n} {i j : Fin n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hij : (canonicalGraph C).Adj i j)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2))
    (hpij :
      p ∈ closedSegment
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)) :
    (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i) := by
  rcases hij with hij | hji
  · have hpair :
        e = (i, j) :=
      common_inOpenSegment_closedSegment_ordered_edges_eq
        he hij hpe hpij
    left
    constructor
    · simpa using congrArg Prod.fst hpair
    · simpa using congrArg Prod.snd hpair
  · have hpair :
        e = (j, i) :=
      common_inOpenSegment_closedSegment_ordered_edges_eq
        he hji hpe (by
          simpa [closedSegment_symm
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)] using hpij)
    right
    constructor
    · simpa using congrArg Prod.fst hpair
    · simpa using congrArg Prod.snd hpair

/-- Interior points of an ordered canonical unit edge have a unique unordered
edge carrier in the embedded drawing. -/
theorem embeddedEdgeSet_carrier_same_unordered_of_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2))
    {i j : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hpij :
      p ∈ closedSegment
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)) :
    (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i) :=
  common_inOpenSegment_closedSegment_adj_same_unordered he hij hpe hpij

/-! ### Local isolation of edge interiors -/

/-- The part of the embedded drawing carried by ordered canonical edges other
than `e`. -/
def embeddedEdgeSetExceptEdge
    (C : _root_.UDConfig n) (e : PlanarInterface.Edge n) :
    Set PlanarInterface.Point :=
  {p | Exists fun f : PlanarInterface.Edge n =>
    f ∈ (canonicalGraph C).edgeSet ∧ f ≠ e ∧
      p ∈ closedSegment
        ((canonicalGraph C).point f.1)
        ((canonicalGraph C).point f.2)}

theorem embeddedEdgeSetExceptEdge_eq_iUnion_edges
    (C : _root_.UDConfig n) (e : PlanarInterface.Edge n) :
    embeddedEdgeSetExceptEdge C e =
      ⋃ i : Fin n, ⋃ j : Fin n,
        {p | (i, j) ∈ (canonicalGraph C).edgeSet ∧
          (i, j) ≠ e ∧
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} := by
  ext p
  constructor
  · rintro ⟨f, hf, hne, hpf⟩
    refine Set.mem_iUnion.2 ⟨f.1, ?_⟩
    refine Set.mem_iUnion.2 ⟨f.2, ?_⟩
    simpa using And.intro hf (And.intro hne hpf)
  · intro hp
    rcases Set.mem_iUnion.1 hp with ⟨i, hi⟩
    rcases Set.mem_iUnion.1 hi with ⟨j, hj⟩
    exact ⟨(i, j), hj.1, hj.2.1, hj.2.2⟩

/-- The drawing carried by all ordered edges except `e` is closed. -/
theorem embeddedEdgeSetExceptEdge_closed
    (C : _root_.UDConfig n) (e : PlanarInterface.Edge n) :
    IsClosed (embeddedEdgeSetExceptEdge C e) := by
  rw [embeddedEdgeSetExceptEdge_eq_iUnion_edges]
  apply isClosed_iUnion_of_finite
  intro i
  apply isClosed_iUnion_of_finite
  intro j
  by_cases h :
      (i, j) ∈ (canonicalGraph C).edgeSet ∧ (i, j) ≠ e
  · rw [show {p | (i, j) ∈ (canonicalGraph C).edgeSet ∧
          (i, j) ≠ e ∧
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} =
          closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) by
        ext p
        constructor
        · intro hp
          exact hp.2.2
        · intro hp
          exact ⟨h.1, h.2, hp⟩]
    exact isClosed_closedSegment _ _
  · rw [show {p | (i, j) ∈ (canonicalGraph C).edgeSet ∧
          (i, j) ≠ e ∧
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} =
          (∅ : Set PlanarInterface.Point) by
        ext p
        constructor
        · intro hp
          exact False.elim (h ⟨hp.1, hp.2.1⟩)
        · intro hp
          exact False.elim hp]
    exact isClosed_empty

/-- An interior point of an ordered canonical edge is not carried by any other
ordered canonical edge. -/
theorem inOpenSegment_not_mem_embeddedEdgeSetExceptEdge
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2)) :
    p ∉ embeddedEdgeSetExceptEdge C e := by
  rintro ⟨f, hf, hne, hpf⟩
  exact hne
    (common_inOpenSegment_closedSegment_ordered_edges_eq
      (C := C) (p := p) (e := e) (f := f) he hf hpe hpf).symm

/-- Local edge isolation at an interior point of a canonical unit edge: inside
some ball around the point, every embedded-drawing point is carried by that
same closed edge segment. -/
theorem exists_ball_inter_embeddedEdgeSet_subset_closedSegment_of_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2)) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball p ε ∩ embeddedEdgeSet C ⊆
          closedSegment
            ((canonicalGraph C).point e.1)
            ((canonicalGraph C).point e.2) := by
  classical
  let other : Set PlanarInterface.Point :=
    embeddedEdgeSetExceptEdge C e
  have hclosed : IsClosed other :=
    embeddedEdgeSetExceptEdge_closed C e
  have hpnot : p ∉ other :=
    inOpenSegment_not_mem_embeddedEdgeSetExceptEdge he hpe
  by_cases hnonempty : other.Nonempty
  · refine ⟨Metric.infDist p other, ?_, ?_⟩
    · exact (hclosed.notMem_iff_infDist_pos hnonempty).1 hpnot
    · intro y hy
      have hyball : y ∈ Metric.ball p (Metric.infDist p other) := hy.1
      have hyembed : y ∈ embeddedEdgeSet C := hy.2
      have hynot_other : y ∉ other := by
        have hdist : dist p y < Metric.infDist p other := by
          simpa [dist_comm, Metric.mem_ball] using hyball
        exact Metric.notMem_of_dist_lt_infDist (x := p) (y := y)
          (s := other) hdist
      rcases
          mem_embeddedEdgeSet_iff_exists_edge_mem_closedSegment.1
            hyembed with
        ⟨f, hf, hfy⟩
      by_cases hfe : f = e
      · subst f
        exact hfy
      · exact False.elim (hynot_other ⟨f, hf, hfe, hfy⟩)
  · refine ⟨1, by norm_num, ?_⟩
    intro y hy
    have hyembed : y ∈ embeddedEdgeSet C := hy.2
    rcases
        mem_embeddedEdgeSet_iff_exists_edge_mem_closedSegment.1
          hyembed with
      ⟨f, hf, hfy⟩
    by_cases hfe : f = e
    · subst f
      exact hfy
    · exact False.elim (hnonempty ⟨y, ⟨f, hf, hfe, hfy⟩⟩)

/-- Local drawing equality at an interior point of an ordered canonical unit
edge: after shrinking to a small ball, the embedded drawing is exactly the
selected closed edge segment restricted to that ball. -/
theorem exists_ball_inter_embeddedEdgeSet_eq_inter_closedSegment_of_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2)) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball p ε ∩ embeddedEdgeSet C =
          Metric.ball p ε ∩
            closedSegment
              ((canonicalGraph C).point e.1)
              ((canonicalGraph C).point e.2) := by
  rcases
      exists_ball_inter_embeddedEdgeSet_subset_closedSegment_of_inOpenSegment
        he hpe with
    ⟨ε, hεpos, hsubset⟩
  refine ⟨ε, hεpos, ?_⟩
  ext y
  constructor
  · intro hy
    exact ⟨hy.1, hsubset hy⟩
  · intro hy
    exact
      ⟨hy.1,
        closedSegment_subset_embeddedEdgeSet_of_adj (Or.inl he) hy.2⟩

/-- Pointwise form of local edge-interior isolation.  In a sufficiently small
ball around an interior point of `e`, every embedded-drawing point lies on
the closed segment of `e`. -/
theorem exists_ball_forall_mem_closedSegment_of_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2)) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball p ε ->
            q ∈ embeddedEdgeSet C ->
              q ∈ closedSegment
                ((canonicalGraph C).point e.1)
                ((canonicalGraph C).point e.2) := by
  rcases
      exists_ball_inter_embeddedEdgeSet_subset_closedSegment_of_inOpenSegment
        he hpe with
    ⟨ε, hεpos, hsubset⟩
  exact ⟨ε, hεpos, fun q hqball hqdraw => hsubset ⟨hqball, hqdraw⟩⟩

/-- Adjacency-facing form of local edge-interior isolation.  In a sufficiently
small ball around an interior point of the adjacent pair `i j`, every
embedded-drawing point is carried by that same closed segment. -/
theorem exists_ball_forall_mem_closedSegment_of_adj_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} {i j : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hpij :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball p ε ->
            q ∈ embeddedEdgeSet C ->
              q ∈ closedSegment
                ((canonicalGraph C).point i)
                ((canonicalGraph C).point j) := by
  rcases hij with hij | hji
  · exact
      exists_ball_forall_mem_closedSegment_of_inOpenSegment
        (C := C) (p := p) (e := (i, j)) hij hpij
  · rcases
      exists_ball_forall_mem_closedSegment_of_inOpenSegment
        (C := C) (p := p) (e := (j, i)) hji
          (inOpenSegment_symm hpij) with
      ⟨ε, hεpos, hε⟩
    refine ⟨ε, hεpos, ?_⟩
    intro q hqball hqdraw
    simpa [closedSegment_symm
      ((canonicalGraph C).point i) ((canonicalGraph C).point j)] using
      hε q hqball hqdraw

/-- Local edge isolation at an interior point of an ordered canonical unit
edge, sharpened to the open segment: after shrinking to a small ball, every
embedded-drawing point in that ball lies in the same relative interior. -/
theorem exists_ball_inter_embeddedEdgeSet_subset_inOpenSegment_of_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2)) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball p ε ∩ embeddedEdgeSet C ⊆
          {q | PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point e.1)
            ((canonicalGraph C).point e.2)} := by
  rcases
      exists_ball_inter_embeddedEdgeSet_subset_closedSegment_of_inOpenSegment
        he hpe with
    ⟨ε_closed, hε_closed_pos, hclosed_subset⟩
  rcases
      exists_ball_inter_closedSegment_subset_inOpenSegment_of_ne
        (canonical_edge_point_ne_of_mem_edgeSet he) hpe with
    ⟨ε_open, hε_open_pos, hopen_subset⟩
  refine ⟨min ε_closed ε_open,
    lt_min hε_closed_pos hε_open_pos, ?_⟩
  intro q hq
  have hq_closed_ball : q ∈ Metric.ball p ε_closed :=
    Metric.ball_subset_ball (min_le_left ε_closed ε_open) hq.1
  have hq_open_ball : q ∈ Metric.ball p ε_open :=
    Metric.ball_subset_ball (min_le_right ε_closed ε_open) hq.1
  have hqseg :
      q ∈ closedSegment
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2) :=
    hclosed_subset ⟨hq_closed_ball, hq.2⟩
  exact hopen_subset ⟨hq_open_ball, hqseg⟩

/-- Pointwise form of local ordered-edge open-segment isolation. -/
theorem exists_ball_forall_mem_inOpenSegment_of_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2)) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball p ε ->
            q ∈ embeddedEdgeSet C ->
              PlanarInterface.InOpenSegment q
                ((canonicalGraph C).point e.1)
                ((canonicalGraph C).point e.2) := by
  rcases
      exists_ball_inter_embeddedEdgeSet_subset_inOpenSegment_of_inOpenSegment
        he hpe with
    ⟨ε, hεpos, hsubset⟩
  exact ⟨ε, hεpos, fun q hqball hqdraw => hsubset ⟨hqball, hqdraw⟩⟩

/-- Adjacency-facing local edge isolation at an interior point, sharpened to
the open segment of the given adjacent pair. -/
theorem exists_ball_inter_embeddedEdgeSet_subset_inOpenSegment_of_adj_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} {i j : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hpij :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball p ε ∩ embeddedEdgeSet C ⊆
          {q | PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} := by
  rcases hij with hij | hji
  · exact
      exists_ball_inter_embeddedEdgeSet_subset_inOpenSegment_of_inOpenSegment
        (C := C) (p := p) (e := (i, j)) hij hpij
  · rcases
      exists_ball_inter_embeddedEdgeSet_subset_inOpenSegment_of_inOpenSegment
        (C := C) (p := p) (e := (j, i)) hji
          (inOpenSegment_symm hpij) with
      ⟨ε, hεpos, hsubset⟩
    refine ⟨ε, hεpos, ?_⟩
    intro q hq
    exact inOpenSegment_symm (hsubset hq)

/-- Pointwise adjacency-facing form of local edge open-segment isolation. -/
theorem exists_ball_forall_mem_inOpenSegment_of_adj_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} {i j : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hpij :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball p ε ->
            q ∈ embeddedEdgeSet C ->
              PlanarInterface.InOpenSegment q
                ((canonicalGraph C).point i)
                ((canonicalGraph C).point j) := by
  rcases
      exists_ball_inter_embeddedEdgeSet_subset_inOpenSegment_of_adj_inOpenSegment
        hij hpij with
    ⟨ε, hεpos, hsubset⟩
  exact ⟨ε, hεpos, fun q hqball hqdraw => hsubset ⟨hqball, hqdraw⟩⟩

/-! ### Local isolation of vertex stars -/

/-- The finite set of graph vertices other than `v`, viewed as points in the
plane. -/
def graphVertexSetExcept
    (C : _root_.UDConfig n) (v : Fin n) :
    Set PlanarInterface.Point :=
  {p | Exists fun w : Fin n =>
    w ≠ v ∧ p = (canonicalGraph C).point w}

theorem graphVertexSetExcept_subset_vertexSet
    (C : _root_.UDConfig n) (v : Fin n) :
    graphVertexSetExcept C v ⊆ Set.range (canonicalGraph C).point := by
  rintro p ⟨w, _hwne, rfl⟩
  exact ⟨w, rfl⟩

/-- The set of graph vertices other than `v` is finite. -/
theorem graphVertexSetExcept_finite
    (C : _root_.UDConfig n) (v : Fin n) :
    (graphVertexSetExcept C v).Finite :=
  (Set.finite_range (canonicalGraph C).point).subset
    (graphVertexSetExcept_subset_vertexSet C v)

/-- The set of graph vertices other than `v` is closed. -/
theorem graphVertexSetExcept_closed
    (C : _root_.UDConfig n) (v : Fin n) :
    IsClosed (graphVertexSetExcept C v) :=
  (graphVertexSetExcept_finite C v).isClosed

/-- A graph vertex is not in the finite set of other graph vertices. -/
theorem graph_vertex_not_mem_graphVertexSetExcept
    {C : _root_.UDConfig n} (v : Fin n) :
    (canonicalGraph C).point v ∉ graphVertexSetExcept C v := by
  rintro ⟨w, hwne, hvw⟩
  exact hwne ((canonical_point_injective C hvw).symm)

/-- Around a graph vertex there is a ball containing no other graph vertices. -/
theorem exists_ball_forall_graph_vertex_eq_of_mem_ball
    {C : _root_.UDConfig n} (v : Fin n) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall w : Fin n,
          (canonicalGraph C).point w ∈
              Metric.ball ((canonicalGraph C).point v) ε ->
            w = v := by
  classical
  let other : Set PlanarInterface.Point := graphVertexSetExcept C v
  have hclosed : IsClosed other := graphVertexSetExcept_closed C v
  have hvnot : (canonicalGraph C).point v ∉ other :=
    graph_vertex_not_mem_graphVertexSetExcept v
  by_cases hnonempty : other.Nonempty
  · refine ⟨Metric.infDist ((canonicalGraph C).point v) other, ?_, ?_⟩
    · exact (hclosed.notMem_iff_infDist_pos hnonempty).1 hvnot
    · intro w hwball
      by_contra hwne
      have hwother : (canonicalGraph C).point w ∈ other := ⟨w, hwne, rfl⟩
      have hdist :
          dist ((canonicalGraph C).point v) ((canonicalGraph C).point w) <
            Metric.infDist ((canonicalGraph C).point v) other := by
        simpa [dist_comm, Metric.mem_ball] using hwball
      exact
        (Metric.notMem_of_dist_lt_infDist
          (x := (canonicalGraph C).point v)
          (y := (canonicalGraph C).point w)
          (s := other) hdist) hwother
  · refine ⟨1, by norm_num, ?_⟩
    intro w _hwball
    by_contra hwne
    exact False.elim (hnonempty ⟨(canonicalGraph C).point w, ⟨w, hwne, rfl⟩⟩)

/-- Set-valued form: a sufficiently small ball around `v` meets the graph
vertex set only at `v`. -/
theorem exists_ball_inter_vertexSet_subset_singleton
    {C : _root_.UDConfig n} (v : Fin n) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball ((canonicalGraph C).point v) ε ∩
            Set.range (canonicalGraph C).point ⊆
          {(canonicalGraph C).point v} := by
  rcases exists_ball_forall_graph_vertex_eq_of_mem_ball (C := C) v with
    ⟨ε, hεpos, hε⟩
  refine ⟨ε, hεpos, ?_⟩
  intro q hq
  rcases hq.2 with ⟨w, rfl⟩
  have hw : w = v := hε w hq.1
  simp [hw]

/-- The part of the embedded drawing carried by ordered canonical edges not
incident to `v`. -/
def embeddedEdgeSetNonincidentVertex
    (C : _root_.UDConfig n) (v : Fin n) :
    Set PlanarInterface.Point :=
  {p | Exists fun e : PlanarInterface.Edge n =>
    e ∈ (canonicalGraph C).edgeSet ∧ e.1 ≠ v ∧ e.2 ≠ v ∧
      p ∈ closedSegment
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2)}

theorem embeddedEdgeSetNonincidentVertex_eq_iUnion_edges
    (C : _root_.UDConfig n) (v : Fin n) :
    embeddedEdgeSetNonincidentVertex C v =
      ⋃ i : Fin n, ⋃ j : Fin n,
        {p | (i, j) ∈ (canonicalGraph C).edgeSet ∧
          i ≠ v ∧ j ≠ v ∧
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} := by
  ext p
  constructor
  · rintro ⟨e, he, hne1, hne2, hpf⟩
    refine Set.mem_iUnion.2 ⟨e.1, ?_⟩
    refine Set.mem_iUnion.2 ⟨e.2, ?_⟩
    exact ⟨he, hne1, hne2, hpf⟩
  · intro hp
    rcases Set.mem_iUnion.1 hp with ⟨i, hi⟩
    rcases Set.mem_iUnion.1 hi with ⟨j, hj⟩
    exact ⟨(i, j), hj.1, hj.2.1, hj.2.2.1, hj.2.2.2⟩

/-- The nonincident-edge part of the embedded drawing is closed. -/
theorem embeddedEdgeSetNonincidentVertex_closed
    (C : _root_.UDConfig n) (v : Fin n) :
    IsClosed (embeddedEdgeSetNonincidentVertex C v) := by
  rw [embeddedEdgeSetNonincidentVertex_eq_iUnion_edges]
  apply isClosed_iUnion_of_finite
  intro i
  apply isClosed_iUnion_of_finite
  intro j
  by_cases h :
      (i, j) ∈ (canonicalGraph C).edgeSet ∧ i ≠ v ∧ j ≠ v
  · rw [show {p | (i, j) ∈ (canonicalGraph C).edgeSet ∧
          i ≠ v ∧ j ≠ v ∧
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} =
          closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) by
        ext p
        constructor
        · intro hp
          exact hp.2.2.2
        · intro hp
          exact ⟨h.1, h.2.1, h.2.2, hp⟩]
    exact isClosed_closedSegment _ _
  · rw [show {p | (i, j) ∈ (canonicalGraph C).edgeSet ∧
          i ≠ v ∧ j ≠ v ∧
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} =
          (∅ : Set PlanarInterface.Point) by
        ext p
        constructor
        · intro hp
          exact False.elim (h ⟨hp.1, hp.2.1, hp.2.2.1⟩)
        · intro hp
          exact False.elim hp]
    exact isClosed_empty

/-- A graph vertex is not carried by any canonical unit edge nonincident to
that vertex. -/
theorem graph_vertex_not_mem_embeddedEdgeSetNonincidentVertex
    {C : _root_.UDConfig n} (v : Fin n) :
    (canonicalGraph C).point v ∉ embeddedEdgeSetNonincidentVertex C v := by
  rintro ⟨e, he, hne1, hne2, hpf⟩
  rcases
      graph_vertex_on_unit_edge_segment_is_endpoint
        (C := C) (v := v) (i := e.1) (j := e.2)
        (Or.inl he) hpf with hv1 | hv2
  · exact hne1 hv1.symm
  · exact hne2 hv2.symm

/-- Local vertex-star isolation: inside some ball around a graph vertex, every
embedded-drawing point is carried by an edge incident to that vertex. -/
theorem exists_ball_inter_embeddedEdgeSet_subset_incident_closedSegment
    {C : _root_.UDConfig n} (v : Fin n) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball ((canonicalGraph C).point v) ε ∩ embeddedEdgeSet C ⊆
          {p | Exists fun w : Fin n =>
            (canonicalGraph C).Adj v w ∧
              p ∈ closedSegment
                ((canonicalGraph C).point v)
                ((canonicalGraph C).point w)} := by
  classical
  let nonincident : Set PlanarInterface.Point :=
    embeddedEdgeSetNonincidentVertex C v
  have hclosed : IsClosed nonincident :=
    embeddedEdgeSetNonincidentVertex_closed C v
  have hvnot : (canonicalGraph C).point v ∉ nonincident :=
    graph_vertex_not_mem_embeddedEdgeSetNonincidentVertex v
  by_cases hnonempty : nonincident.Nonempty
  · refine ⟨Metric.infDist ((canonicalGraph C).point v) nonincident, ?_, ?_⟩
    · exact (hclosed.notMem_iff_infDist_pos hnonempty).1 hvnot
    · intro y hy
      have hyball :
          y ∈ Metric.ball ((canonicalGraph C).point v)
            (Metric.infDist ((canonicalGraph C).point v) nonincident) := hy.1
      have hyembed : y ∈ embeddedEdgeSet C := hy.2
      have hynot_nonincident : y ∉ nonincident := by
        have hdist :
            dist ((canonicalGraph C).point v) y <
              Metric.infDist ((canonicalGraph C).point v) nonincident := by
          simpa [dist_comm, Metric.mem_ball] using hyball
        exact Metric.notMem_of_dist_lt_infDist
          (x := (canonicalGraph C).point v) (y := y)
          (s := nonincident) hdist
      rcases
          mem_embeddedEdgeSet_iff_exists_edge_mem_closedSegment.1
            hyembed with
        ⟨e, he, hye⟩
      by_cases he1 : e.1 = v
      · refine ⟨e.2, ?_, ?_⟩
        · simpa [he1] using (Or.inl he : (canonicalGraph C).Adj e.1 e.2)
        · simpa [he1] using hye
      · by_cases he2 : e.2 = v
        · refine ⟨e.1, ?_, ?_⟩
          · simpa [he2] using
              canonicalAdj_symm (Or.inl he : (canonicalGraph C).Adj e.1 e.2)
          · simpa [he2, closedSegment_symm
              ((canonicalGraph C).point e.1)
              ((canonicalGraph C).point v)] using hye
        · exact False.elim (hynot_nonincident ⟨e, he, he1, he2, hye⟩)
  · refine ⟨1, by norm_num, ?_⟩
    intro y hy
    have hyembed : y ∈ embeddedEdgeSet C := hy.2
    rcases
        mem_embeddedEdgeSet_iff_exists_edge_mem_closedSegment.1
          hyembed with
      ⟨e, he, hye⟩
    by_cases he1 : e.1 = v
    · refine ⟨e.2, ?_, ?_⟩
      · simpa [he1] using (Or.inl he : (canonicalGraph C).Adj e.1 e.2)
      · simpa [he1] using hye
    · by_cases he2 : e.2 = v
      · refine ⟨e.1, ?_, ?_⟩
        · simpa [he2] using
            canonicalAdj_symm (Or.inl he : (canonicalGraph C).Adj e.1 e.2)
        · simpa [he2, closedSegment_symm
            ((canonicalGraph C).point e.1)
            ((canonicalGraph C).point v)] using hye
      · exact False.elim
          (hnonempty ⟨y, ⟨e, he, he1, he2, hye⟩⟩)

/-- Pointwise form of local vertex-star isolation.  In a sufficiently small
ball around a graph vertex, every embedded-drawing point lies on a closed
segment of an edge incident to that vertex. -/
theorem exists_ball_forall_mem_incident_closedSegment_of_vertex
    {C : _root_.UDConfig n} (v : Fin n) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball ((canonicalGraph C).point v) ε ->
            q ∈ embeddedEdgeSet C ->
              Exists fun w : Fin n =>
                (canonicalGraph C).Adj v w ∧
                  q ∈ closedSegment
                    ((canonicalGraph C).point v)
                    ((canonicalGraph C).point w) := by
  rcases
      exists_ball_inter_embeddedEdgeSet_subset_incident_closedSegment
        (C := C) v with
    ⟨ε, hεpos, hsubset⟩
  exact ⟨ε, hεpos, fun q hqball hqdraw => hsubset ⟨hqball, hqdraw⟩⟩

/-- The `ε`-germ of the directed edge from `v` to `w`: the part of its closed
straight segment that remains inside the ball centered at `v`. -/
def vertexIncidentGermW3
    (C : _root_.UDConfig n) (v w : Fin n) (ε : Real) :
    Set PlanarInterface.Point :=
  Metric.ball ((canonicalGraph C).point v) ε ∩
    closedSegment
      ((canonicalGraph C).point v)
      ((canonicalGraph C).point w)

/-- Local vertex-germ isolation: after shrinking around `v`, the embedded
drawing inside the ball is contained in the union of the `ε`-germs of the
edges incident to `v`. -/
theorem exists_ball_inter_embeddedEdgeSet_subset_vertexIncidentGermsW3
    {C : _root_.UDConfig n} (v : Fin n) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball ((canonicalGraph C).point v) ε ∩ embeddedEdgeSet C ⊆
          {p | Exists fun w : Fin n =>
            (canonicalGraph C).Adj v w ∧
              p ∈ vertexIncidentGermW3 C v w ε} := by
  rcases
      exists_ball_inter_embeddedEdgeSet_subset_incident_closedSegment
        (C := C) v with
    ⟨ε, hεpos, hsubset⟩
  refine ⟨ε, hεpos, ?_⟩
  intro p hp
  rcases hsubset hp with ⟨w, hvw, hpseg⟩
  exact ⟨w, hvw, hp.1, hpseg⟩

/-- Pointwise form of the W3 vertex-germ isolation statement. -/
theorem exists_ball_forall_mem_vertexIncidentGermW3
    {C : _root_.UDConfig n} (v : Fin n) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball ((canonicalGraph C).point v) ε ->
            q ∈ embeddedEdgeSet C ->
              Exists fun w : Fin n =>
                (canonicalGraph C).Adj v w ∧
                  q ∈ vertexIncidentGermW3 C v w ε := by
  rcases
      exists_ball_inter_embeddedEdgeSet_subset_vertexIncidentGermsW3
        (C := C) v with
    ⟨ε, hεpos, hsubset⟩
  exact ⟨ε, hεpos, fun q hqball hqdraw => hsubset ⟨hqball, hqdraw⟩⟩

theorem closedSegment_inter_closedSegment_eq_empty_of_adj_edgeVertexDisjoint
    {C : _root_.UDConfig n} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hdisj : PlanarInterface.EdgeVertexDisjoint (i, j) (k, l)) :
    (closedSegment
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j) ∩
      closedSegment
        ((canonicalGraph C).point k)
        ((canonicalGraph C).point l) :
        Set PlanarInterface.Point) = ∅ := by
  rcases hdisj with ⟨hik, hil, hjk, hjl⟩
  ext p
  constructor
  · intro hp
    rcases
        mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hp.1 with
      hpi | hpj | hpij
    · have hendpoint :
          i = k ∨ i = l := by
        rcases
          graph_vertex_on_unit_edge_segment_is_endpoint
            (C := C) (v := i) hkl (hpi ▸ hp.2) with hik' | hil'
        · exact Or.inl hik'
        · exact Or.inr hil'
      exact False.elim (hendpoint.elim hik hil)
    · have hendpoint :
          j = k ∨ j = l := by
        rcases
          graph_vertex_on_unit_edge_segment_is_endpoint
            (C := C) (v := j) hkl (hpj ▸ hp.2) with hjk' | hjl'
        · exact Or.inl hjk'
        · exact Or.inr hjl'
      exact False.elim (hendpoint.elim hjk hjl)
    · rcases
          mem_closedSegment_eq_left_or_eq_right_or_inOpenSegment hp.2 with
        hpk | hpl | hpkl
      · exact False.elim
          (graph_vertex_not_inOpenSegment_of_adj
            (C := C) (v := k) hij (hpk ▸ hpij))
      · exact False.elim
          (graph_vertex_not_inOpenSegment_of_adj
            (C := C) (v := l) hij (hpl ▸ hpij))
      · exact False.elim
          (adjacent_segments_not_cross_of_edgeVertexDisjoint
            hij hkl ⟨hik, hil, hjk, hjl⟩ ⟨p, hpij, hpkl⟩)
  · intro hp
    exact False.elim hp

theorem disjoint_closedSegment_of_adj_edgeVertexDisjoint
    {C : _root_.UDConfig n} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hdisj : PlanarInterface.EdgeVertexDisjoint (i, j) (k, l)) :
    Disjoint
      (closedSegment
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j))
      (closedSegment
        ((canonicalGraph C).point k)
        ((canonicalGraph C).point l)) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  exact closedSegment_inter_closedSegment_eq_empty_of_adj_edgeVertexDisjoint
    hij hkl hdisj

theorem not_edgeVertexDisjoint_of_adj_closedSegment_inter
    {C : _root_.UDConfig n} {i j k l : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hkl : (canonicalGraph C).Adj k l)
    (hinter :
      (closedSegment
          ((canonicalGraph C).point i)
          ((canonicalGraph C).point j) ∩
        closedSegment
          ((canonicalGraph C).point k)
          ((canonicalGraph C).point l) :
          Set PlanarInterface.Point).Nonempty) :
    ¬ PlanarInterface.EdgeVertexDisjoint (i, j) (k, l) := by
  intro hdisj
  rw [closedSegment_inter_closedSegment_eq_empty_of_adj_edgeVertexDisjoint
    hij hkl hdisj] at hinter
  exact Set.not_nonempty_empty hinter

/-- The embedded drawing is the set whose complement will be used for the
exterior-component proof. -/
def drawingComplement (C : _root_.UDConfig n) : Set PlanarInterface.Point :=
  (embeddedEdgeSet C)ᶜ

/-- Membership in the drawing complement is nonmembership in the embedded
unit-edge carrier. -/
theorem mem_drawingComplement_iff
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} :
    p ∈ drawingComplement C <-> p ∉ embeddedEdgeSet C :=
  Iff.rfl

/-- If a ball meets the embedded drawing only along a selected closed segment,
then the strict same-side part of that ball is contained in the drawing
complement.  This is the containment half of the local same-side exterior patch
needed for S2. -/
theorem sSameSide_ball_subset_drawingComplement_of_local_closedSegment
    {C : _root_.UDConfig n}
    {a b y z : PlanarInterface.Point} {ε : Real}
    (hlocal :
      Metric.ball z ε ∩ embeddedEdgeSet C ⊆ closedSegment a b) :
    ({q : PlanarInterface.Point |
        (line[ℝ, a, b] : AffineSubspace ℝ PlanarInterface.Point).SSameSide
          y q} ∩ Metric.ball z ε) ⊆ drawingComplement C := by
  intro q hq
  rw [drawingComplement]
  intro hqdraw
  have hqseg : q ∈ closedSegment a b := hlocal ⟨hq.2, hqdraw⟩
  exact sSameSide_line_not_mem_closedSegment hq.1 hqseg

/-- Normal-coordinate side-ball containment version of
`sSameSide_ball_subset_drawingComplement_of_local_closedSegment`.
If a ball meets the embedded drawing only along a selected closed segment, then
any smaller positive side-ball is contained in the drawing complement. -/
theorem edgePositiveSideBall_subset_drawingComplement_of_local_closedSegment
    {C : _root_.UDConfig n}
    {a b z : PlanarInterface.Point} {r ε : Real}
    (hr : r ≤ ε)
    (hlocal :
      Metric.ball z ε ∩ embeddedEdgeSet C ⊆ closedSegment a b) :
    edgePositiveSideBall a b z r ⊆ drawingComplement C := by
  intro q hq
  rw [drawingComplement]
  intro hqdraw
  have hqball_eps : q ∈ Metric.ball z ε :=
    Metric.ball_subset_ball hr hq.2
  have hqseg : q ∈ closedSegment a b := hlocal ⟨hqball_eps, hqdraw⟩
  have hzero : edgeNormalCoord a b q = 0 :=
    edgeNormalCoord_eq_zero_of_mem_closedSegment hqseg
  have hpos : 0 < edgeNormalCoord a b q := hq.1
  linarith

/-- Swapped-orientation version of
`edgePositiveSideBall_subset_drawingComplement_of_local_closedSegment`.  It
lets the local side proof choose either strict side of the isolated edge. -/
theorem edgePositiveSideBall_swap_subset_drawingComplement_of_local_closedSegment
    {C : _root_.UDConfig n}
    {a b z : PlanarInterface.Point} {r ε : Real}
    (hr : r ≤ ε)
    (hlocal :
      Metric.ball z ε ∩ embeddedEdgeSet C ⊆ closedSegment a b) :
    edgePositiveSideBall b a z r ⊆ drawingComplement C := by
  exact
    edgePositiveSideBall_subset_drawingComplement_of_local_closedSegment
      (C := C) (a := b) (b := a) (z := z) (r := r) (ε := ε) hr
      (by
        intro q hq
        rw [closedSegment_symm]
        exact hlocal hq)

/-- The complement of the embedded drawing is open. -/
theorem drawingComplement_open
    (C : _root_.UDConfig n) :
    IsOpen (drawingComplement C) := by
  simpa [drawingComplement] using (embeddedEdgeSet_closed C).isOpen_compl

/-- The drawing complement is nonempty.  A finite union of compact edge
segments cannot cover the whole Euclidean plane. -/
theorem drawingComplement_nonempty
    (C : _root_.UDConfig n) :
    (drawingComplement C).Nonempty := by
  by_contra h
  have hsubset : (Set.univ : Set PlanarInterface.Point) ⊆ embeddedEdgeSet C := by
    intro p _hp
    by_contra hp
    exact h ⟨p, hp⟩
  have hb_univ : Bornology.IsBounded (Set.univ : Set PlanarInterface.Point) :=
    (embeddedEdgeSet_compact C).isBounded.subset hsubset
  exact NormedSpace.unbounded_univ ℝ PlanarInterface.Point hb_univ

/-- The open x-axis ray to the right of `R`, used to select a concrete
unbounded component of the drawing complement after a compactness bound is
chosen. -/
def xAxisRay (R : Real) : Set PlanarInterface.Point :=
  {p | Exists fun t : Real => R < t /\ p = (t, 0)}

/-- Membership in the chosen rightward x-axis ray, written in coordinates. -/
theorem mem_xAxisRay_iff
    {R : Real} {p : PlanarInterface.Point} :
    p ∈ xAxisRay R <-> R < p.1 /\ p.2 = 0 := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp [ht]
  · rcases p with ⟨x, y⟩
    rintro ⟨hx, hy⟩
    refine ⟨x, hx, ?_⟩
    have hy' : y = 0 := by
      simpa using hy
    exact Prod.ext rfl hy'

/-- Coordinate points strictly to the right of `R` lie on the x-axis ray. -/
theorem mk_mem_xAxisRay
    (R t : Real) (ht : R < t) :
    ((t, 0) : PlanarInterface.Point) ∈ xAxisRay R :=
  ⟨t, ht, rfl⟩

/-- A point on the x-axis ray has first coordinate strictly larger than the
cutoff. -/
theorem xAxisRay_fst_gt
    {R : Real} {p : PlanarInterface.Point}
    (hp : p ∈ xAxisRay R) :
    R < p.1 :=
  (mem_xAxisRay_iff.1 hp).1

/-- A point on the x-axis ray has second coordinate zero. -/
theorem xAxisRay_snd_eq_zero
    {R : Real} {p : PlanarInterface.Point}
    (hp : p ∈ xAxisRay R) :
    p.2 = 0 :=
  (mem_xAxisRay_iff.1 hp).2

/-- The canonical base point used for the rightward unbounded component. -/
def xAxisRayBase (R : Real) : PlanarInterface.Point :=
  (R + 1, 0)

/-- The canonical base point lies on its rightward x-axis ray. -/
theorem xAxisRayBase_mem (R : Real) :
    xAxisRayBase R ∈ xAxisRay R := by
  exact mk_mem_xAxisRay R (R + 1) (by linarith)

theorem xAxisRay_eq_image_Ioi (R : Real) :
    xAxisRay R =
      (fun t : Real => ((t, 0) : PlanarInterface.Point)) '' Set.Ioi R := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · intro hp
    rcases hp with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

/-- The chosen x-axis ray is preconnected. -/
theorem xAxisRay_preconnected (R : Real) :
    IsPreconnected (xAxisRay R) := by
  rw [xAxisRay_eq_image_Ioi]
  exact isPreconnected_Ioi.image _ (by fun_prop)

theorem fst_image_xAxisRay (R : Real) :
    Prod.fst '' xAxisRay R = Set.Ioi R := by
  ext t
  constructor
  · intro ht
    rcases ht with ⟨p, hp, rfl⟩
    rcases hp with ⟨u, hu, rfl⟩
    exact hu
  · intro ht
    exact ⟨(t, 0), ⟨t, ht, rfl⟩, rfl⟩

/-- The chosen x-axis ray is unbounded. -/
theorem xAxisRay_unbounded (R : Real) :
    ¬ Bornology.IsBounded (xAxisRay R) := by
  intro hbounded
  have hfst : Bornology.IsBounded (Prod.fst '' xAxisRay R) :=
    Bornology.IsBounded.image_fst hbounded
  have hIoi : Bornology.IsBounded (Set.Ioi R) := by
    simpa [fst_image_xAxisRay R] using hfst
  exact
      (not_bddAbove_Ioi (a := R))
      (isBounded_iff_bddBelow_bddAbove.mp hIoi).2

/-- If a rightward x-axis ray is contained in an open candidate set, then it is
contained in the connected component of that set containing the canonical base
point. -/
theorem xAxisRay_subset_connectedComponentIn
    {U : Set PlanarInterface.Point} {R : Real}
    (hsubset : xAxisRay R ⊆ U) :
    xAxisRay R ⊆ connectedComponentIn U (xAxisRayBase R) :=
  (xAxisRay_preconnected R).subset_connectedComponentIn
    (xAxisRayBase_mem R) hsubset

/-- Any ambient component containing a full rightward x-axis ray is unbounded. -/
theorem connectedComponentIn_xAxisRayBase_unbounded
    {U : Set PlanarInterface.Point} {R : Real}
    (hsubset : xAxisRay R ⊆ U) :
    ¬ Bornology.IsBounded (connectedComponentIn U (xAxisRayBase R)) := by
  intro hbounded_component
  exact xAxisRay_unbounded R
    (hbounded_component.subset
      (xAxisRay_subset_connectedComponentIn hsubset))

theorem xAxisRay_subset_closedBall_compl
    (R : Real) (hR : 0 <= R) :
    xAxisRay R ⊆ (Metric.closedBall (0 : PlanarInterface.Point) R)ᶜ := by
  intro p hp hpball
  rcases hp with ⟨t, ht, rfl⟩
  have ht_nonneg : 0 <= t := le_trans hR ht.le
  have hdist : dist (0 : PlanarInterface.Point) (t, 0) <= R := by
    simpa [Metric.mem_closedBall] using hpball
  have hdist_eq : dist (0 : PlanarInterface.Point) (t, 0) = |t| := by
    rw [dist_eq_norm]
    simp
  have ht_abs : R < |t| := by
    simpa [abs_of_nonneg ht_nonneg] using ht
  exact not_le_of_gt ht_abs (hdist_eq ▸ hdist)

/-- Compactness gives a nonnegative closed ball containing the embedded
drawing. -/
theorem exists_nonnegative_closedBall_bound_embeddedEdgeSet
    (C : _root_.UDConfig n) :
    Exists fun R : Real =>
      0 <= R /\
        embeddedEdgeSet C ⊆ Metric.closedBall (0 : PlanarInterface.Point) R := by
  rcases
      (Metric.isBounded_iff_subset_closedBall
        (0 : PlanarInterface.Point)).mp
        (embeddedEdgeSet_compact C).isBounded with
    ⟨A, hA⟩
  exact
    ⟨max A 0, le_max_right A 0, fun p hp =>
      Metric.closedBall_subset_closedBall (le_max_left A 0) (hA hp)⟩

/-- A nonnegative closed-ball bound for the drawing puts the corresponding
rightward x-axis ray in the drawing complement. -/
theorem xAxisRay_subset_drawingComplement_of_closedBall_bound
    {C : _root_.UDConfig n} {R : Real}
    (hR : 0 <= R)
    (hbound :
      embeddedEdgeSet C ⊆ Metric.closedBall (0 : PlanarInterface.Point) R) :
    xAxisRay R ⊆ drawingComplement C := by
  intro p hp
  rw [drawingComplement]
  intro hpdraw
  exact xAxisRay_subset_closedBall_compl R hR hp (hbound hpdraw)

/-- Some rightward x-axis ray lies entirely in the drawing complement. -/
theorem exists_xAxisRay_subset_drawingComplement
    (C : _root_.UDConfig n) :
    Exists fun R : Real => 0 <= R /\ xAxisRay R ⊆ drawingComplement C := by
  rcases exists_nonnegative_closedBall_bound_embeddedEdgeSet C with
    ⟨R, hR, hbound⟩
  exact
    ⟨R, hR,
      xAxisRay_subset_drawingComplement_of_closedBall_bound hR hbound⟩

/-- Compactness plus the rightward-ray construction produces a concrete
unbounded connected component of the drawing complement, namely the component
of the canonical x-axis base point. -/
theorem exists_xAxisRay_subset_drawingComplement_component_unbounded
    (C : _root_.UDConfig n) :
    Exists fun R : Real =>
      0 <= R /\
        xAxisRay R ⊆ drawingComplement C /\
          xAxisRayBase R ∈ drawingComplement C /\
            xAxisRay R ⊆
              connectedComponentIn (drawingComplement C) (xAxisRayBase R) /\
              ¬ Bornology.IsBounded
                (connectedComponentIn (drawingComplement C) (xAxisRayBase R)) := by
  rcases exists_xAxisRay_subset_drawingComplement C with ⟨R, hR, hsubset⟩
  exact
    ⟨R, hR, hsubset, hsubset (xAxisRayBase_mem R),
      xAxisRay_subset_connectedComponentIn hsubset,
      connectedComponentIn_xAxisRayBase_unbounded hsubset⟩

/-- The S2 graph-side inputs keep every graph vertex out of the open drawing
complement, because every graph vertex lies on the embedded unit-edge
drawing. -/
theorem graph_vertex_not_mem_drawingComplement_of_inputs
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    forall v : Fin n,
      (canonicalGraph C).point v ∉ drawingComplement C := by
  intro v
  simpa [drawingComplement] using vertex_mem_embeddedEdgeSet_of_inputs inputs v

/-- Every graph vertex has an incident canonical edge under the S2 graph-side
inputs. -/
theorem graph_vertex_incident_of_inputs
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C) :
    forall v : Fin n, Exists fun w : Fin n => (canonicalGraph C).Adj v w := by
  intro v
  exact
    graph_vertex_mem_embeddedEdgeSet_iff_exists_adj.1
      (vertex_mem_embeddedEdgeSet_of_inputs inputs v)

/-- Canonical edge-set membership gives the corresponding closed segment as a
subset of the embedded drawing. -/
theorem closedSegment_subset_embeddedEdgeSet_of_edge_mem
    {C : _root_.UDConfig n} {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet) :
    closedSegment ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2) ⊆
      embeddedEdgeSet C := by
  exact closedSegment_subset_embeddedEdgeSet_of_adj (Or.inl he)

/-- The frontier of the whole drawing complement is carried by the embedded
unit-edge drawing.  Selecting the exterior component and proving which of
these drawing points lie on its frontier remains the S2 topology theorem. -/
theorem frontier_drawingComplement_subset_embeddedEdgeSet
    (C : _root_.UDConfig n) :
    frontier (drawingComplement C) ⊆ embeddedEdgeSet C := by
  intro p hp
  have hp' : p ∈ frontier (embeddedEdgeSet C) := by
    simpa [drawingComplement, frontier_compl] using hp
  simpa [(embeddedEdgeSet_closed C).closure_eq] using
    (frontier_subset_closure (s := embeddedEdgeSet C) hp')

/-- A point on the frontier of a connected component of an open set cannot
still lie in the ambient open set. -/
theorem not_mem_open_of_mem_frontier_connectedComponentIn
    {α : Type*} [TopologicalSpace α] [LocallyConnectedSpace α]
    {U : Set α} {x y : α} (hU : IsOpen U)
    (hy : y ∈ frontier (connectedComponentIn U x)) :
    y ∉ U := by
  intro hyU
  let E : Set α := connectedComponentIn U x
  let Ey : Set α := connectedComponentIn U y
  have hEopen : IsOpen E := hU.connectedComponentIn
  have hEyopen : IsOpen Ey := hU.connectedComponentIn
  have hy_closureE : y ∈ closure E := frontier_subset_closure hy
  have hyEy : y ∈ Ey := mem_connectedComponentIn hyU
  have hEy_inter_E : (Ey ∩ E).Nonempty :=
    (mem_closure_iff.mp hy_closureE) Ey hEyopen hyEy
  rcases hEy_inter_E with ⟨z, hzEy, hzE⟩
  have hExz : connectedComponentIn U x = connectedComponentIn U z :=
    connectedComponentIn_eq hzE
  have hEyz : connectedComponentIn U y = connectedComponentIn U z :=
    connectedComponentIn_eq hzEy
  have hEy_eq_E : Ey = E := by
    dsimp [Ey, E]
    exact hEyz.trans hExz.symm
  have hyE : y ∈ E := by
    simpa [hEy_eq_E] using hyEy
  have hmem : y ∈ E ∩ frontier E := ⟨hyE, hy⟩
  have hdisj : E ∩ frontier E = ∅ := hEopen.inter_frontier_eq
  rw [hdisj] at hmem
  exact hmem

/-- The frontier of a connected component of an open set lies in the frontier
of the ambient open set. -/
theorem frontier_connectedComponentIn_subset_frontier
    {α : Type*} [TopologicalSpace α] [LocallyConnectedSpace α]
    {U : Set α} {x : α} (hU : IsOpen U) :
    frontier (connectedComponentIn U x) ⊆ frontier U := by
  intro y hy
  rw [hU.frontier_eq]
  exact
    ⟨closure_mono (connectedComponentIn_subset U x)
        (frontier_subset_closure hy),
      not_mem_open_of_mem_frontier_connectedComponentIn hU hy⟩

/-- From a rightward x-axis ray in the drawing complement, choose an extremal
frontier seed for the connected component containing the ray base: the seed is
on the actual component frontier, lies on the embedded drawing, and realizes the
distance from the ray base to the component complement. -/
theorem exists_xAxisRayBase_extremal_frontier_seed
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    {R : Real}
    (hsubset : xAxisRay R ⊆ drawingComplement C) :
    Exists fun p : PlanarInterface.Point =>
      p ∈ frontier
          (connectedComponentIn (drawingComplement C) (xAxisRayBase R)) /\
        p ∈ embeddedEdgeSet C /\
          Metric.infDist (xAxisRayBase R)
              (connectedComponentIn (drawingComplement C) (xAxisRayBase R))ᶜ =
            dist (xAxisRayBase R) p := by
  let component : Set PlanarInterface.Point :=
    connectedComponentIn (drawingComplement C) (xAxisRayBase R)
  have hbase_drawingComplement :
      xAxisRayBase R ∈ drawingComplement C :=
    hsubset (xAxisRayBase_mem R)
  have hbase_component : xAxisRayBase R ∈ component := by
    exact mem_connectedComponentIn hbase_drawingComplement
  have hcomponent_ne_univ : component ≠ Set.univ := by
    intro hcomponent
    obtain ⟨v⟩ := inputs.vertex_nonempty
    have hvcomponent : (canonicalGraph C).point v ∈ component := by
      rw [hcomponent]
      exact Set.mem_univ _
    have hv_drawingComplement :
        (canonicalGraph C).point v ∈ drawingComplement C :=
      connectedComponentIn_subset (drawingComplement C) (xAxisRayBase R)
        hvcomponent
    exact graph_vertex_not_mem_drawingComplement_of_inputs inputs v
      hv_drawingComplement
  rcases
      exists_mem_frontier_infDist_compl_eq_dist
        (x := xAxisRayBase R) (s := component)
        hbase_component hcomponent_ne_univ with
    ⟨p, hpfrontier, hpdist⟩
  have hpfrontier_drawingComplement :
      p ∈ frontier (drawingComplement C) :=
    frontier_connectedComponentIn_subset_frontier
      (drawingComplement_open C) (by simpa [component] using hpfrontier)
  exact
    ⟨p, by simpa [component] using hpfrontier,
      frontier_drawingComplement_subset_embeddedEdgeSet C
        hpfrontier_drawingComplement,
      by simpa [component] using hpdist⟩

/-- Combined rightward-ray handoff: compactness chooses a rightward ray in the
drawing complement; its base component is unbounded; and an extremal frontier
seed on the embedded drawing is available for that same component. -/
theorem exists_xAxisRay_unbounded_component_extremal_frontier_seed
    (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    Exists fun R : Real =>
      Exists fun p : PlanarInterface.Point =>
        0 <= R /\
          xAxisRay R ⊆ drawingComplement C /\
            xAxisRayBase R ∈ drawingComplement C /\
              xAxisRay R ⊆
                connectedComponentIn (drawingComplement C) (xAxisRayBase R) /\
                ¬ Bornology.IsBounded
                  (connectedComponentIn (drawingComplement C)
                    (xAxisRayBase R)) /\
                  p ∈ frontier
                    (connectedComponentIn (drawingComplement C)
                      (xAxisRayBase R)) /\
                    p ∈ embeddedEdgeSet C /\
                      Metric.infDist (xAxisRayBase R)
                          (connectedComponentIn (drawingComplement C)
                            (xAxisRayBase R))ᶜ =
                        dist (xAxisRayBase R) p := by
  rcases exists_xAxisRay_subset_drawingComplement_component_unbounded C with
    ⟨R, hR, hsubset, hbase, hray_component, hcomponent_unbounded⟩
  rcases exists_xAxisRayBase_extremal_frontier_seed inputs hsubset with
    ⟨p, hpfrontier, hpdraw, hpdist⟩
  exact
    ⟨R, p, hR, hsubset, hbase, hray_component, hcomponent_unbounded,
      hpfrontier, hpdraw, hpdist⟩

/-- Edge-interior isolation on the frontier of the whole drawing complement:
near an interior point of a canonical ordered edge, every complement-frontier
point is still in that same edge interior. -/
theorem exists_ball_inter_frontier_drawingComplement_subset_inOpenSegment_of_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2)) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball p ε ∩ frontier (drawingComplement C) ⊆
          {q | PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point e.1)
            ((canonicalGraph C).point e.2)} := by
  rcases
      exists_ball_inter_embeddedEdgeSet_subset_inOpenSegment_of_inOpenSegment
        he hpe with
    ⟨ε, hεpos, hlocal⟩
  refine ⟨ε, hεpos, ?_⟩
  intro q hq
  exact hlocal
    ⟨hq.1, frontier_drawingComplement_subset_embeddedEdgeSet C hq.2⟩

/-- Pointwise edge-interior isolation on the frontier of the whole drawing
complement. -/
theorem exists_ball_forall_frontier_drawingComplement_mem_inOpenSegment_of_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2)) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball p ε ->
            q ∈ frontier (drawingComplement C) ->
              PlanarInterface.InOpenSegment q
                ((canonicalGraph C).point e.1)
                ((canonicalGraph C).point e.2) := by
  rcases
      exists_ball_inter_frontier_drawingComplement_subset_inOpenSegment_of_inOpenSegment
        he hpe with
    ⟨ε, hεpos, hsubset⟩
  exact ⟨ε, hεpos, fun q hqball hqfrontier =>
    hsubset ⟨hqball, hqfrontier⟩⟩

/-- Adjacency-facing edge-interior isolation on the frontier of the whole
drawing complement. -/
theorem exists_ball_inter_frontier_drawingComplement_subset_inOpenSegment_of_adj_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} {i j : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hpij :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball p ε ∩ frontier (drawingComplement C) ⊆
          {q | PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} := by
  rcases
      exists_ball_inter_embeddedEdgeSet_subset_inOpenSegment_of_adj_inOpenSegment
        hij hpij with
    ⟨ε, hεpos, hlocal⟩
  refine ⟨ε, hεpos, ?_⟩
  intro q hq
  exact hlocal
    ⟨hq.1, frontier_drawingComplement_subset_embeddedEdgeSet C hq.2⟩

/-- Pointwise adjacency-facing edge-interior isolation on the frontier of the
whole drawing complement. -/
theorem exists_ball_forall_frontier_drawingComplement_mem_inOpenSegment_of_adj_inOpenSegment
    {C : _root_.UDConfig n} {p : PlanarInterface.Point} {i j : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hpij :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball p ε ->
            q ∈ frontier (drawingComplement C) ->
              PlanarInterface.InOpenSegment q
                ((canonicalGraph C).point i)
                ((canonicalGraph C).point j) := by
  rcases
      exists_ball_inter_frontier_drawingComplement_subset_inOpenSegment_of_adj_inOpenSegment
        hij hpij with
    ⟨ε, hεpos, hsubset⟩
  exact ⟨ε, hεpos, fun q hqball hqfrontier =>
    hsubset ⟨hqball, hqfrontier⟩⟩

/-- Ordered-edge component-frontier edge-interior isolation for the drawing
complement. -/
theorem exists_ball_inter_frontier_connectedComponentIn_drawingComplement_subset_inOpenSegment_of_inOpenSegment
    {C : _root_.UDConfig n} (base : PlanarInterface.Point)
    {p : PlanarInterface.Point} {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2)) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball p ε ∩
            frontier (connectedComponentIn (drawingComplement C) base) ⊆
          {q | PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point e.1)
            ((canonicalGraph C).point e.2)} := by
  rcases
      exists_ball_inter_frontier_drawingComplement_subset_inOpenSegment_of_inOpenSegment
        he hpe with
    ⟨ε, hεpos, hlocal⟩
  refine ⟨ε, hεpos, ?_⟩
  intro q hq
  exact hlocal
    ⟨hq.1,
      frontier_connectedComponentIn_subset_frontier
        (drawingComplement_open C) hq.2⟩

/-- Pointwise ordered-edge component-frontier edge-interior isolation for the
drawing complement. -/
theorem exists_ball_forall_frontier_connectedComponentIn_drawingComplement_mem_inOpenSegment_of_inOpenSegment
    {C : _root_.UDConfig n} (base : PlanarInterface.Point)
    {p : PlanarInterface.Point} {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hpe :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point e.1)
        ((canonicalGraph C).point e.2)) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball p ε ->
            q ∈ frontier (connectedComponentIn (drawingComplement C) base) ->
              PlanarInterface.InOpenSegment q
                ((canonicalGraph C).point e.1)
                ((canonicalGraph C).point e.2) := by
  rcases
      exists_ball_inter_frontier_connectedComponentIn_drawingComplement_subset_inOpenSegment_of_inOpenSegment
        base he hpe with
    ⟨ε, hεpos, hsubset⟩
  exact ⟨ε, hεpos, fun q hqball hqfrontier =>
    hsubset ⟨hqball, hqfrontier⟩⟩

/-- Component-frontier edge-interior isolation for the drawing complement.
This is the local form needed when the exterior sector has already selected a
component of the complement. -/
theorem exists_ball_inter_frontier_connectedComponentIn_drawingComplement_subset_inOpenSegment_of_adj_inOpenSegment
    {C : _root_.UDConfig n} (base : PlanarInterface.Point)
    {p : PlanarInterface.Point} {i j : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hpij :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball p ε ∩
            frontier (connectedComponentIn (drawingComplement C) base) ⊆
          {q | PlanarInterface.InOpenSegment q
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j)} := by
  rcases
      exists_ball_inter_frontier_drawingComplement_subset_inOpenSegment_of_adj_inOpenSegment
        hij hpij with
    ⟨ε, hεpos, hlocal⟩
  refine ⟨ε, hεpos, ?_⟩
  intro q hq
  exact hlocal
    ⟨hq.1,
      frontier_connectedComponentIn_subset_frontier
        (drawingComplement_open C) hq.2⟩

/-- Pointwise component-frontier edge-interior isolation for the drawing
complement. -/
theorem exists_ball_forall_frontier_connectedComponentIn_drawingComplement_mem_inOpenSegment_of_adj_inOpenSegment
    {C : _root_.UDConfig n} (base : PlanarInterface.Point)
    {p : PlanarInterface.Point} {i j : Fin n}
    (hij : (canonicalGraph C).Adj i j)
    (hpij :
      PlanarInterface.InOpenSegment p
        ((canonicalGraph C).point i)
        ((canonicalGraph C).point j)) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball p ε ->
            q ∈ frontier (connectedComponentIn (drawingComplement C) base) ->
              PlanarInterface.InOpenSegment q
                ((canonicalGraph C).point i)
                ((canonicalGraph C).point j) := by
  rcases
      exists_ball_inter_frontier_connectedComponentIn_drawingComplement_subset_inOpenSegment_of_adj_inOpenSegment
        base hij hpij with
    ⟨ε, hεpos, hsubset⟩
  exact ⟨ε, hεpos, fun q hqball hqfrontier =>
    hsubset ⟨hqball, hqfrontier⟩⟩

/-- Local frontier-sector isolation at a vertex: after shrinking around `v`,
the frontier of the whole drawing complement is carried by incident W3
vertex germs. -/
theorem exists_ball_inter_frontier_drawingComplement_subset_vertexIncidentGermsW3
    {C : _root_.UDConfig n} (v : Fin n) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball ((canonicalGraph C).point v) ε ∩
            frontier (drawingComplement C) ⊆
          {p | Exists fun w : Fin n =>
            (canonicalGraph C).Adj v w ∧
              p ∈ vertexIncidentGermW3 C v w ε} := by
  rcases
      exists_ball_inter_embeddedEdgeSet_subset_vertexIncidentGermsW3
        (C := C) v with
    ⟨ε, hεpos, hlocal⟩
  refine ⟨ε, hεpos, ?_⟩
  intro p hp
  exact hlocal
    ⟨hp.1, frontier_drawingComplement_subset_embeddedEdgeSet C hp.2⟩

/-- Pointwise form of local frontier-sector isolation at a vertex.  A frontier
point of the whole drawing complement that is sufficiently near `v` lies in
one of the W3 incident germs from `v`. -/
theorem exists_ball_forall_frontier_drawingComplement_mem_vertexIncidentGermW3
    {C : _root_.UDConfig n} (v : Fin n) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball ((canonicalGraph C).point v) ε ->
            q ∈ frontier (drawingComplement C) ->
              Exists fun w : Fin n =>
                (canonicalGraph C).Adj v w ∧
                  q ∈ vertexIncidentGermW3 C v w ε := by
  rcases
      exists_ball_inter_frontier_drawingComplement_subset_vertexIncidentGermsW3
        (C := C) v with
    ⟨ε, hεpos, hsubset⟩
  exact ⟨ε, hεpos, fun q hqball hqfrontier =>
    hsubset ⟨hqball, hqfrontier⟩⟩

/-- Component-frontier form of the W3 vertex-germ isolation row.  For any
chosen component of the drawing complement, frontier points sufficiently near a
graph vertex are carried by the incident germs at that vertex. -/
theorem exists_ball_forall_frontier_connectedComponentIn_drawingComplement_mem_vertexIncidentGermW3
    {C : _root_.UDConfig n} (base : PlanarInterface.Point) (v : Fin n) :
    Exists fun ε : Real =>
      0 < ε ∧
        forall q : PlanarInterface.Point,
          q ∈ Metric.ball ((canonicalGraph C).point v) ε ->
            q ∈ frontier (connectedComponentIn (drawingComplement C) base) ->
              Exists fun w : Fin n =>
                (canonicalGraph C).Adj v w ∧
                  q ∈ vertexIncidentGermW3 C v w ε := by
  rcases
      exists_ball_forall_frontier_drawingComplement_mem_vertexIncidentGermW3
        (C := C) v with
    ⟨ε, hεpos, hlocal⟩
  refine ⟨ε, hεpos, ?_⟩
  intro q hqball hqfrontier
  exact hlocal q hqball
    (frontier_connectedComponentIn_subset_frontier
      (drawingComplement_open C) hqfrontier)

/-- Set-valued component-frontier form of W3 vertex-germ isolation.  Near a
graph vertex, the frontier of any selected drawing-complement component is
carried by the incident vertex germs. -/
theorem exists_ball_inter_frontier_connectedComponentIn_drawingComplement_subset_vertexIncidentGermsW3
    {C : _root_.UDConfig n} (base : PlanarInterface.Point) (v : Fin n) :
    Exists fun ε : Real =>
      0 < ε ∧
        Metric.ball ((canonicalGraph C).point v) ε ∩
            frontier (connectedComponentIn (drawingComplement C) base) ⊆
          {p | Exists fun w : Fin n =>
            (canonicalGraph C).Adj v w ∧
              p ∈ vertexIncidentGermW3 C v w ε} := by
  rcases
      exists_ball_inter_frontier_drawingComplement_subset_vertexIncidentGermsW3
        (C := C) v with
    ⟨ε, hεpos, hlocal⟩
  refine ⟨ε, hεpos, ?_⟩
  intro p hp
  exact hlocal
    ⟨hp.1,
      frontier_connectedComponentIn_subset_frontier
        (drawingComplement_open C) hp.2⟩

/-- A point on the frontier of the whole drawing complement lies on a concrete
canonical unit-edge segment. -/
theorem exists_edge_segment_of_mem_frontier_drawingComplement
    {C : _root_.UDConfig n} {p : PlanarInterface.Point}
    (hp : p ∈ frontier (drawingComplement C)) :
    Exists fun i : Fin n =>
      Exists fun j : Fin n =>
        (canonicalGraph C).Adj i j /\
          p ∈ closedSegment
            ((canonicalGraph C).point i)
            ((canonicalGraph C).point j) := by
  simpa [embeddedEdgeSet] using
    frontier_drawingComplement_subset_embeddedEdgeSet C hp

/-- A graph vertex on the frontier of the whole drawing complement has an
incident canonical edge. -/
theorem frontier_drawingComplement_graph_vertex_incident
    {C : _root_.UDConfig n} {v : Fin n}
    (hv : (canonicalGraph C).point v ∈ frontier (drawingComplement C)) :
    Exists fun w : Fin n => (canonicalGraph C).Adj v w := by
  exact
    graph_vertex_mem_embeddedEdgeSet_iff_exists_adj.1
      (frontier_drawingComplement_subset_embeddedEdgeSet C hv)

end

end FinitePlaneDrawing
end Swanepoel
end ErdosProblems1066
