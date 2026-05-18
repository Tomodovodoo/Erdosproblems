import ErdosProblems1066.Swanepoel.NonconcaveArcConcrete
import ErdosProblems1066.Swanepoel.M8TurnBoundsConcrete

set_option autoImplicit false

/-!
# Nonconcave arc angle facts

This file isolates the remaining nonconcave-arc angle input as a small real
inequality package and proves the arithmetic consequences needed by the
existing turn-bound pipeline.

The checked content here is only normalization and budget arithmetic.  The
geometric angle estimates themselves remain explicit fields:

* raw turns are nonnegative on the arc indices `1, ..., 13`;
* the raw total turn is bounded by a geometric angle budget;
* that budget is below `pi / 3`.

Those facts are enough to build `M8TurnBoundsFromArc.NonconcaveArcTurnData`,
and hence the concrete M8 turn-bound records.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace NonconcaveArcAngleFacts

open Lemma10Inequalities
open M8TurnBoundsConcrete
open M8TurnBoundsFromArc
open NonconcaveArcConcrete

universe u

variable {n : Nat}

/-! ## Raw angle-budget facts -/

/--
Minimal remaining geometric input for one nonconcave arc.

The field `totalTurn_le_geometricAngleBudget` is the place where the actual
outer-boundary/subpolygon angle comparison enters.  Everything below this
structure is a checked reduction from those real inequalities to the turn data
used by the M8 construction.
-/
structure NonconcaveArcGeometricAngleFacts where
  rawTurn : Nat -> Real
  geometricAngleBudget : Real
  rawTurn_nonnegative_on_arc :
    forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k
  totalTurn_le_geometricAngleBudget :
    totalTurn rawTurn <= geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :
    geometricAngleBudget < Real.pi / 3

/-! ## Lemma 6/7 boundary-subpolygon adapters -/

/--
The checked contradiction shape behind the Lemma 6 gap step.

The Euclidean content of Lemma 6 must supply a concrete subpolygon attached to
the same planar-boundary data whose degree counts violate the already-proved
subpolygon low-degree inequality.  Once such a subpolygon is supplied, the
contradiction is purely checked arithmetic/counting.
-/
structure SubpolygonLowDegreeViolation
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  carrier : D.Subpolygon
  lowDegree_violation :
    2 * (D.subpolygonData carrier).counts.D2 +
        (D.subpolygonData carrier).counts.D3 < 6

namespace SubpolygonLowDegreeViolation

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- A supplied low-degree violation contradicts the checked subpolygon
low-degree theorem carried by the planar-boundary data. -/
theorem false (V : SubpolygonLowDegreeViolation D) : False := by
  have hlow :
      6 <=
        2 * (D.subpolygonData V.carrier).counts.D2 +
          (D.subpolygonData V.carrier).counts.D3 :=
    PlanarBoundaryFinal.PlanarBoundaryData.subpolygonLowDegreeInequality_viaBoundaryCounting
      D V.carrier
  exact (not_lt_of_ge hlow) V.lowDegree_violation

end SubpolygonLowDegreeViolation

/--
Exact checked interface for Swanepoel Lemma 6.

For a project-local gap predicate and a project-local negative/concavity
predicate, the remaining Euclidean lemma is precisely: if the gap occurs and
the negative conclusion does not, then one can construct a subpolygon
low-degree violation for the same boundary data.
-/
structure Lemma6GapToNegativeCertificate
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G)
    (gap negative : Prop) where
  gap_without_negative_violates_subpolygon_low_degree :
    gap -> Not negative -> SubpolygonLowDegreeViolation D

namespace Lemma6GapToNegativeCertificate

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
variable {gap negative : Prop}

/-- Lemma 6 in usable form: the gap forces the negative/concavity conclusion. -/
theorem negative_of_gap
    (C : Lemma6GapToNegativeCertificate D gap negative) :
    gap -> negative := by
  intro hgap
  by_contra hnegative
  exact
    (C.gap_without_negative_violates_subpolygon_low_degree
      hgap hnegative).false

end Lemma6GapToNegativeCertificate

/--
Exact checked interface for the Lemma 7 degree-three/gap iteration along the
thirteen-turn `m = 8` arc.

The fields separate the genuinely geometric work from the checked route:
Lemma 6 certificates rule out every gap on `turnIndexSet`; after those gaps
are ruled out, the caller must supply the local nonnegativity and total-budget
comparisons for the raw turn function.
-/
structure Lemma7ArcAngleCertificate
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  rawTurn : Nat -> Real
  geometricAngleBudget : Real
  gapAt : Nat -> Prop
  negativeAt : Nat -> Prop
  lemma6_gap_forces_negative :
    forall k : Nat, Membership.mem turnIndexSet k ->
      Lemma6GapToNegativeCertificate D (gapAt k) (negativeAt k)
  negative_absent_on_arc :
    forall k : Nat, Membership.mem turnIndexSet k -> Not (negativeAt k)
  rawTurn_nonnegative_of_no_gap :
    forall k : Nat, Membership.mem turnIndexSet k ->
      Not (gapAt k) -> 0 <= rawTurn k
  totalTurn_le_geometricAngleBudget_of_no_gap :
    (forall k : Nat, Membership.mem turnIndexSet k -> Not (gapAt k)) ->
      totalTurn rawTurn <= geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :
    geometricAngleBudget < Real.pi / 3

namespace Lemma7ArcAngleCertificate

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- Lemma 7 gap iteration, expressed on the concrete thirteen arc indices:
Lemma 6 plus absence of negative/concave failures rules out each gap. -/
theorem no_gap_on_arc
    (C : Lemma7ArcAngleCertificate D) :
    forall k : Nat, Membership.mem turnIndexSet k -> Not (C.gapAt k) := by
  intro k hk hgap
  exact
    C.negative_absent_on_arc k hk
      ((C.lemma6_gap_forces_negative k hk).negative_of_gap hgap)

/-- Raw turn nonnegativity after the Lemma 7 no-gap iteration. -/
theorem rawTurn_nonnegative_on_arc
    (C : Lemma7ArcAngleCertificate D) :
    forall k : Nat, Membership.mem turnIndexSet k -> 0 <= C.rawTurn k := by
  intro k hk
  exact C.rawTurn_nonnegative_of_no_gap k hk (C.no_gap_on_arc k hk)

/-- Total raw turn bounded by the geometric budget after the Lemma 7 no-gap
iteration. -/
theorem totalTurn_le_geometricAngleBudget
    (C : Lemma7ArcAngleCertificate D) :
    totalTurn C.rawTurn <= C.geometricAngleBudget :=
  C.totalTurn_le_geometricAngleBudget_of_no_gap C.no_gap_on_arc

/-- The Lemma 6/7 certificate supplies exactly the downstream nonconcave-arc
geometric angle facts. -/
def toNonconcaveArcGeometricAngleFacts
    (C : Lemma7ArcAngleCertificate D) :
    NonconcaveArcGeometricAngleFacts where
  rawTurn := C.rawTurn
  geometricAngleBudget := C.geometricAngleBudget
  rawTurn_nonnegative_on_arc := C.rawTurn_nonnegative_on_arc
  totalTurn_le_geometricAngleBudget :=
    C.totalTurn_le_geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :=
    C.geometricAngleBudget_lt_pi_div_three

@[simp]
theorem toNonconcaveArcGeometricAngleFacts_rawTurn
    (C : Lemma7ArcAngleCertificate D) :
    C.toNonconcaveArcGeometricAngleFacts.rawTurn = C.rawTurn :=
  rfl

@[simp]
theorem toNonconcaveArcGeometricAngleFacts_geometricAngleBudget
    (C : Lemma7ArcAngleCertificate D) :
    C.toNonconcaveArcGeometricAngleFacts.geometricAngleBudget =
      C.geometricAngleBudget :=
  rfl

end Lemma7ArcAngleCertificate

namespace NonconcaveArcGeometricAngleFacts

/-- The raw total turn inherits the strict `pi / 3` bound from the geometric
budget. -/
theorem raw_totalTurn_lt_pi_div_three
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.rawTurn < Real.pi / 3 :=
  lt_of_le_of_lt A.totalTurn_le_geometricAngleBudget
    A.geometricAngleBudget_lt_pi_div_three

/-- The raw total turn is nonnegative because each arc turn is nonnegative. -/
theorem raw_totalTurn_nonnegative
    (A : NonconcaveArcGeometricAngleFacts) :
    0 <= totalTurn A.rawTurn := by
  unfold totalTurn
  exact Finset.sum_nonneg fun k hk =>
    A.rawTurn_nonnegative_on_arc k hk

/-- The geometric budget is nonnegative as a consequence of the raw total-turn
lower bound and the supplied budget comparison. -/
theorem geometricAngleBudget_nonnegative
    (A : NonconcaveArcGeometricAngleFacts) :
    0 <= A.geometricAngleBudget :=
  le_trans A.raw_totalTurn_nonnegative
    A.totalTurn_le_geometricAngleBudget

/-- Expand the total turn into the thirteen raw arc turns. -/
theorem raw_totalTurn_eq_sum_thirteen
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.rawTurn =
      A.rawTurn 1 + A.rawTurn 2 + A.rawTurn 3 + A.rawTurn 4 +
      A.rawTurn 5 + A.rawTurn 6 + A.rawTurn 7 + A.rawTurn 8 +
      A.rawTurn 9 + A.rawTurn 10 + A.rawTurn 11 + A.rawTurn 12 +
      A.rawTurn 13 := by
  unfold totalTurn turnIndexSet
  norm_num [Finset.sum_Icc_succ_top, add_assoc]

/-- The raw total turn is the explicit thirteen-term M8 arc sum used by the
concrete nonconcave-arc facade. -/
theorem raw_totalTurn_eq_m8ThirteenTurnSum
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.rawTurn = m8ThirteenTurnSum A.rawTurn :=
  totalTurn_eq_m8ThirteenTurnSum A.rawTurn

/-- The explicit thirteen-term raw arc sum is bounded by the geometric
angle budget. -/
theorem raw_m8ThirteenTurnSum_le_geometricAngleBudget
    (A : NonconcaveArcGeometricAngleFacts) :
    m8ThirteenTurnSum A.rawTurn <= A.geometricAngleBudget := by
  simpa [A.raw_totalTurn_eq_m8ThirteenTurnSum] using
    A.totalTurn_le_geometricAngleBudget

/-- The explicit thirteen-term raw arc sum is below `pi / 3`. -/
theorem raw_m8ThirteenTurnSum_lt_pi_div_three
    (A : NonconcaveArcGeometricAngleFacts) :
    m8ThirteenTurnSum A.rawTurn < Real.pi / 3 := by
  simpa [A.raw_totalTurn_eq_m8ThirteenTurnSum] using
    A.raw_totalTurn_lt_pi_div_three

/-! ## Normalization off the arc -/

/-- The normalized turn function keeps raw turns on `1, ..., 13` and is zero
outside those arc indices. -/
def normalizedTurn (A : NonconcaveArcGeometricAngleFacts) (k : Nat) :
    Real :=
  if Membership.mem turnIndexSet k then A.rawTurn k else 0

@[simp]
theorem normalizedTurn_of_mem
    (A : NonconcaveArcGeometricAngleFacts) {k : Nat}
    (hk : Membership.mem turnIndexSet k) :
    A.normalizedTurn k = A.rawTurn k := by
  simp [normalizedTurn, hk]

@[simp]
theorem normalizedTurn_of_not_mem
    (A : NonconcaveArcGeometricAngleFacts) {k : Nat}
    (hk : Not (Membership.mem turnIndexSet k)) :
    A.normalizedTurn k = 0 := by
  simp [normalizedTurn, hk]

/-- The normalized turn is nonnegative at every natural index. -/
theorem normalizedTurn_nonnegative
    (A : NonconcaveArcGeometricAngleFacts) (k : Nat) :
    0 <= A.normalizedTurn k := by
  by_cases hk : Membership.mem turnIndexSet k
  case pos =>
    simpa [normalizedTurn, hk] using
      A.rawTurn_nonnegative_on_arc k hk
  case neg =>
    simp [normalizedTurn, hk]

/-- Normalization does not change the total turn, since the total only sums
over the arc index set. -/
theorem totalTurn_normalizedTurn_eq_rawTurn
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.normalizedTurn = totalTurn A.rawTurn := by
  unfold totalTurn
  apply Finset.sum_congr rfl
  intro k hk
  exact A.normalizedTurn_of_mem hk

/-- The normalized total turn is bounded by the same geometric budget. -/
theorem totalTurn_normalizedTurn_le_geometricAngleBudget
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.normalizedTurn <= A.geometricAngleBudget := by
  simpa [A.totalTurn_normalizedTurn_eq_rawTurn] using
    A.totalTurn_le_geometricAngleBudget

/-- The normalized total turn is below `pi / 3`. -/
theorem totalTurn_normalizedTurn_lt_pi_div_three
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.normalizedTurn < Real.pi / 3 := by
  simpa [A.totalTurn_normalizedTurn_eq_rawTurn] using
    A.raw_totalTurn_lt_pi_div_three

/-- The explicit normalized thirteen-term sum agrees with the raw
thirteen-term arc sum. -/
theorem normalizedTurn_m8ThirteenTurnSum_eq_raw
    (A : NonconcaveArcGeometricAngleFacts) :
    m8ThirteenTurnSum A.normalizedTurn =
      m8ThirteenTurnSum A.rawTurn := by
  calc
    m8ThirteenTurnSum A.normalizedTurn =
        totalTurn A.normalizedTurn :=
      (totalTurn_eq_m8ThirteenTurnSum A.normalizedTurn).symm
    _ = totalTurn A.rawTurn :=
      A.totalTurn_normalizedTurn_eq_rawTurn
    _ = m8ThirteenTurnSum A.rawTurn :=
      totalTurn_eq_m8ThirteenTurnSum A.rawTurn

/-- The explicit normalized thirteen-term sum is bounded by the geometric
angle budget. -/
theorem normalizedTurn_m8ThirteenTurnSum_le_geometricAngleBudget
    (A : NonconcaveArcGeometricAngleFacts) :
    m8ThirteenTurnSum A.normalizedTurn <= A.geometricAngleBudget := by
  simpa [A.normalizedTurn_m8ThirteenTurnSum_eq_raw] using
    A.raw_m8ThirteenTurnSum_le_geometricAngleBudget

/-- The explicit normalized thirteen-term sum is below `pi / 3`. -/
theorem normalizedTurn_m8ThirteenTurnSum_lt_pi_div_three
    (A : NonconcaveArcGeometricAngleFacts) :
    m8ThirteenTurnSum A.normalizedTurn < Real.pi / 3 := by
  simpa [A.normalizedTurn_m8ThirteenTurnSum_eq_raw] using
    A.raw_m8ThirteenTurnSum_lt_pi_div_three

/-! ## Conversion to existing concrete interfaces -/

/-- Repackage the geometric facts as the existing concrete angle-inequality
record. -/
def toNonconcaveArcAngleInequalities
    (A : NonconcaveArcGeometricAngleFacts) :
    NonconcaveArcAngleInequalities where
  rawTurn := A.rawTurn
  geometricAngleBudget := A.geometricAngleBudget
  rawTurn_nonnegative_on_arc := A.rawTurn_nonnegative_on_arc
  totalTurn_le_geometricAngleBudget :=
    A.totalTurn_le_geometricAngleBudget
  geometricAngleBudget_lt_pi_div_three :=
    A.geometricAngleBudget_lt_pi_div_three

@[simp]
theorem toNonconcaveArcAngleInequalities_rawTurn
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toNonconcaveArcAngleInequalities.rawTurn = A.rawTurn :=
  rfl

@[simp]
theorem toNonconcaveArcAngleInequalities_geometricAngleBudget
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toNonconcaveArcAngleInequalities.geometricAngleBudget =
      A.geometricAngleBudget :=
  rfl

/-- The minimal geometric angle facts produce the arc turn data expected by
`M8TurnBoundsFromArc`. -/
def toNonconcaveArcTurnData
    (A : NonconcaveArcGeometricAngleFacts) :
    NonconcaveArcTurnData where
  rawTurn := A.rawTurn
  rawTurn_nonnegative_on_arc := A.rawTurn_nonnegative_on_arc
  raw_totalTurn_lt_pi_div_three :=
    A.raw_totalTurn_lt_pi_div_three

@[simp]
theorem toNonconcaveArcTurnData_rawTurn
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toNonconcaveArcTurnData.rawTurn = A.rawTurn :=
  rfl

/-- The normalized turn used in this file agrees with the normalization in
`NonconcaveArcTurnData`. -/
@[simp]
theorem toNonconcaveArcTurnData_turn
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toNonconcaveArcTurnData.turn = A.normalizedTurn := by
  funext k
  by_cases hk : Membership.mem turnIndexSet k
  case pos =>
    simp [NonconcaveArcTurnData.turn, normalizedTurn, hk]
  case neg =>
    simp [NonconcaveArcTurnData.turn, normalizedTurn, hk]

/-- The conversion through `NonconcaveArcConcrete` gives the same raw turn
data as the direct construction above. -/
theorem concrete_toNonconcaveArcTurnData_eq
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toNonconcaveArcAngleInequalities.toNonconcaveArcTurnData =
      A.toNonconcaveArcTurnData :=
  rfl

/-- The existing arc-data total-turn normalization is the same equality proved
directly above. -/
theorem arcData_totalTurn_turn_eq_rawTurn
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.toNonconcaveArcTurnData.turn =
      totalTurn A.rawTurn := by
  simpa [A.toNonconcaveArcTurnData_turn] using
    A.totalTurn_normalizedTurn_eq_rawTurn

/-- Honest turn bounds produced from the minimal geometric facts. -/
def toHonestTurnBounds
    (A : NonconcaveArcGeometricAngleFacts) :
    TurnBoundsInterface.HonestTurnBounds :=
  M8TurnBoundsConcrete.honestTurnBounds A.toNonconcaveArcTurnData

/-- Construction-level M8 turn bounds produced from the minimal geometric
facts. -/
def toM8TurnBounds
    (A : NonconcaveArcGeometricAngleFacts) :
    M8ConstructionInterface.M8TurnBounds :=
  M8TurnBoundsConcrete.m8TurnBounds A.toNonconcaveArcTurnData

@[simp]
theorem toHonestTurnBounds_turn
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toHonestTurnBounds.turn = A.normalizedTurn := by
  simp [toHonestTurnBounds,
    A.toNonconcaveArcTurnData_turn
  ]

@[simp]
theorem toM8TurnBounds_turn
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toM8TurnBounds.turn = A.normalizedTurn := by
  simp [toM8TurnBounds,
    A.toNonconcaveArcTurnData_turn
  ]

/-- Pointwise M8 turn nonnegativity after normalization. -/
theorem toM8TurnBounds_turn_nonnegative
    (A : NonconcaveArcGeometricAngleFacts) (k : Nat) :
    0 <= A.toM8TurnBounds.turn k := by
  simpa [A.toM8TurnBounds_turn] using
    A.normalizedTurn_nonnegative k

/-- The M8 total turn is bounded by the supplied geometric angle budget. -/
theorem toM8TurnBounds_totalTurn_le_geometricAngleBudget
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.toM8TurnBounds.turn <= A.geometricAngleBudget := by
  simpa [A.toM8TurnBounds_turn] using
    A.totalTurn_normalizedTurn_le_geometricAngleBudget

/-- The M8 total turn is below `pi / 3`. -/
theorem toM8TurnBounds_totalTurn_lt_pi_div_three
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.toM8TurnBounds.turn < Real.pi / 3 := by
  simpa [A.toM8TurnBounds_turn] using
    A.totalTurn_normalizedTurn_lt_pi_div_three

@[simp]
theorem toM8TurnBounds_turn_of_mem
    (A : NonconcaveArcGeometricAngleFacts) {k : Nat}
    (hk : Membership.mem turnIndexSet k) :
    A.toM8TurnBounds.turn k = A.rawTurn k := by
  simpa [A.toM8TurnBounds_turn] using
    A.normalizedTurn_of_mem hk

@[simp]
theorem toM8TurnBounds_turn_of_not_mem
    (A : NonconcaveArcGeometricAngleFacts) {k : Nat}
    (hk : Not (Membership.mem turnIndexSet k)) :
    A.toM8TurnBounds.turn k = 0 := by
  simpa [A.toM8TurnBounds_turn] using
    A.normalizedTurn_of_not_mem hk

/-- Normalization preserves the raw total turn on the M8 package. -/
theorem toM8TurnBounds_totalTurn_eq_rawTurn
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.toM8TurnBounds.turn = totalTurn A.rawTurn := by
  simpa [A.toM8TurnBounds_turn] using
    A.totalTurn_normalizedTurn_eq_rawTurn

/-- The M8 package total turn is its explicit thirteen-term sum. -/
theorem toM8TurnBounds_totalTurn_eq_m8ThirteenTurnSum
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.toM8TurnBounds.turn =
      m8ThirteenTurnSum A.toM8TurnBounds.turn :=
  totalTurn_eq_m8ThirteenTurnSum A.toM8TurnBounds.turn

/-- The M8 package thirteen-term sum agrees with the raw arc sum. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_eq_raw
    (A : NonconcaveArcGeometricAngleFacts) :
    m8ThirteenTurnSum A.toM8TurnBounds.turn =
      m8ThirteenTurnSum A.rawTurn := by
  calc
    m8ThirteenTurnSum A.toM8TurnBounds.turn =
        totalTurn A.toM8TurnBounds.turn :=
      (totalTurn_eq_m8ThirteenTurnSum A.toM8TurnBounds.turn).symm
    _ = totalTurn A.rawTurn :=
      A.toM8TurnBounds_totalTurn_eq_rawTurn
    _ = m8ThirteenTurnSum A.rawTurn :=
      totalTurn_eq_m8ThirteenTurnSum A.rawTurn

/-- The M8 package total turn is the explicit raw thirteen-term arc sum. -/
theorem toM8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.toM8TurnBounds.turn =
      m8ThirteenTurnSum A.rawTurn := by
  simpa [A.raw_totalTurn_eq_m8ThirteenTurnSum] using
    A.toM8TurnBounds_totalTurn_eq_rawTurn

/-- The M8 package thirteen-term sum is bounded by the geometric angle
budget. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_le_geometricAngleBudget
    (A : NonconcaveArcGeometricAngleFacts) :
    m8ThirteenTurnSum A.toM8TurnBounds.turn <=
      A.geometricAngleBudget := by
  simpa [A.toM8TurnBounds_m8ThirteenTurnSum_eq_raw] using
    A.raw_m8ThirteenTurnSum_le_geometricAngleBudget

/-- The M8 package thirteen-term sum is below `pi / 3`. -/
theorem toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three
    (A : NonconcaveArcGeometricAngleFacts) :
    m8ThirteenTurnSum A.toM8TurnBounds.turn < Real.pi / 3 := by
  simpa [A.toM8TurnBounds_m8ThirteenTurnSum_eq_raw] using
    A.raw_m8ThirteenTurnSum_lt_pi_div_three

/-- Named projection of the construction-level pointwise nonnegativity field.
-/
theorem toM8TurnBounds_turn_nonnegative_field
    (A : NonconcaveArcGeometricAngleFacts) :
    forall k : Nat, 0 <= A.toM8TurnBounds.turn k :=
  A.toM8TurnBounds.turn_nonnegative

/-- Named projection of the construction-level total-turn field. -/
theorem toM8TurnBounds_total_turn_lt_pi_div_three_field
    (A : NonconcaveArcGeometricAngleFacts) :
    totalTurn A.toM8TurnBounds.turn < Real.pi / 3 :=
  A.toM8TurnBounds.total_turn_lt_pi_div_three

/-! ## Bundled M8 outputs -/

/--
Reusable output bundle from geometric angle facts to the M8 turn-bound
interfaces.

This packages the raw certificate, normalized arc data, honest turn bounds,
construction-level M8 turn bounds, and the arithmetic projections that the
final nonconcave-arc route otherwise has to rebuild.
-/
structure M8TurnBoundOutputs
    (A : NonconcaveArcGeometricAngleFacts) where
  angleFacts : NonconcaveArcGeometricAngleFacts
  arcData : NonconcaveArcTurnData
  honestTurnBounds : TurnBoundsInterface.HonestTurnBounds
  m8TurnBounds : M8ConstructionInterface.M8TurnBounds
  angleFacts_eq : angleFacts = A
  arcData_rawTurn : arcData.rawTurn = A.rawTurn
  arcData_turn : arcData.turn = A.normalizedTurn
  honestTurnBounds_turn :
    honestTurnBounds.turn = A.normalizedTurn
  m8TurnBounds_turn :
    m8TurnBounds.turn = A.normalizedTurn
  raw_totalTurn_nonnegative :
    0 <= totalTurn A.rawTurn
  geometricAngleBudget_nonnegative :
    0 <= A.geometricAngleBudget
  raw_totalTurn_lt_pi_div_three :
    totalTurn A.rawTurn < Real.pi / 3
  raw_totalTurn_eq_m8ThirteenTurnSum :
    totalTurn A.rawTurn = m8ThirteenTurnSum A.rawTurn
  raw_m8ThirteenTurnSum_le_geometricAngleBudget :
    m8ThirteenTurnSum A.rawTurn <= A.geometricAngleBudget
  raw_m8ThirteenTurnSum_lt_pi_div_three :
    m8ThirteenTurnSum A.rawTurn < Real.pi / 3
  m8TurnBounds_turn_nonnegative :
    forall k : Nat, 0 <= m8TurnBounds.turn k
  m8TurnBounds_totalTurn_eq_rawTurn :
    totalTurn m8TurnBounds.turn = totalTurn A.rawTurn
  m8TurnBounds_totalTurn_eq_m8ThirteenTurnSum :
    totalTurn m8TurnBounds.turn =
      m8ThirteenTurnSum m8TurnBounds.turn
  m8TurnBounds_m8ThirteenTurnSum_eq_raw :
    m8ThirteenTurnSum m8TurnBounds.turn =
      m8ThirteenTurnSum A.rawTurn
  m8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum :
    totalTurn m8TurnBounds.turn = m8ThirteenTurnSum A.rawTurn
  m8TurnBounds_totalTurn_le_geometricAngleBudget :
    totalTurn m8TurnBounds.turn <= A.geometricAngleBudget
  m8TurnBounds_totalTurn_lt_pi_div_three :
    totalTurn m8TurnBounds.turn < Real.pi / 3
  m8TurnBounds_total_turn_lt_pi_div_three_field :
    totalTurn m8TurnBounds.turn < Real.pi / 3
  m8TurnBounds_m8ThirteenTurnSum_le_geometricAngleBudget :
    m8ThirteenTurnSum m8TurnBounds.turn <= A.geometricAngleBudget
  m8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three :
    m8ThirteenTurnSum m8TurnBounds.turn < Real.pi / 3

/-- Extract all M8 turn-bound outputs from the geometric angle facts. -/
def toM8TurnBoundOutputs
    (A : NonconcaveArcGeometricAngleFacts) :
    M8TurnBoundOutputs A where
  angleFacts := A
  arcData := A.toNonconcaveArcTurnData
  honestTurnBounds := A.toHonestTurnBounds
  m8TurnBounds := A.toM8TurnBounds
  angleFacts_eq := rfl
  arcData_rawTurn := rfl
  arcData_turn := A.toNonconcaveArcTurnData_turn
  honestTurnBounds_turn := A.toHonestTurnBounds_turn
  m8TurnBounds_turn := A.toM8TurnBounds_turn
  raw_totalTurn_nonnegative := A.raw_totalTurn_nonnegative
  geometricAngleBudget_nonnegative := A.geometricAngleBudget_nonnegative
  raw_totalTurn_lt_pi_div_three := A.raw_totalTurn_lt_pi_div_three
  raw_totalTurn_eq_m8ThirteenTurnSum :=
    A.raw_totalTurn_eq_m8ThirteenTurnSum
  raw_m8ThirteenTurnSum_le_geometricAngleBudget :=
    A.raw_m8ThirteenTurnSum_le_geometricAngleBudget
  raw_m8ThirteenTurnSum_lt_pi_div_three :=
    A.raw_m8ThirteenTurnSum_lt_pi_div_three
  m8TurnBounds_turn_nonnegative := A.toM8TurnBounds_turn_nonnegative
  m8TurnBounds_totalTurn_eq_rawTurn :=
    A.toM8TurnBounds_totalTurn_eq_rawTurn
  m8TurnBounds_totalTurn_eq_m8ThirteenTurnSum :=
    A.toM8TurnBounds_totalTurn_eq_m8ThirteenTurnSum
  m8TurnBounds_m8ThirteenTurnSum_eq_raw :=
    A.toM8TurnBounds_m8ThirteenTurnSum_eq_raw
  m8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum :=
    A.toM8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum
  m8TurnBounds_totalTurn_le_geometricAngleBudget :=
    A.toM8TurnBounds_totalTurn_le_geometricAngleBudget
  m8TurnBounds_totalTurn_lt_pi_div_three :=
    A.toM8TurnBounds_totalTurn_lt_pi_div_three
  m8TurnBounds_total_turn_lt_pi_div_three_field :=
    A.toM8TurnBounds_total_turn_lt_pi_div_three_field
  m8TurnBounds_m8ThirteenTurnSum_le_geometricAngleBudget :=
    A.toM8TurnBounds_m8ThirteenTurnSum_le_geometricAngleBudget
  m8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three :=
    A.toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three

@[simp]
theorem toM8TurnBoundOutputs_arcData
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toM8TurnBoundOutputs.arcData = A.toNonconcaveArcTurnData :=
  rfl

@[simp]
theorem toM8TurnBoundOutputs_m8TurnBounds
    (A : NonconcaveArcGeometricAngleFacts) :
    A.toM8TurnBoundOutputs.m8TurnBounds = A.toM8TurnBounds :=
  rfl

end NonconcaveArcGeometricAngleFacts

namespace Lemma7ArcAngleCertificate

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- The Lemma 6/7 route is immediately usable by the existing M8 turn-bound
pipeline. -/
def toM8TurnBounds
    (C : Lemma7ArcAngleCertificate D) :
    M8ConstructionInterface.M8TurnBounds :=
  C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds

/-- The Lemma 6/7 route as normalized nonconcave-arc turn data. -/
def toNonconcaveArcTurnData
    (C : Lemma7ArcAngleCertificate D) :
    NonconcaveArcTurnData :=
  C.toNonconcaveArcGeometricAngleFacts.toNonconcaveArcTurnData

/-- The Lemma 6/7 route as honest turn bounds. -/
def toHonestTurnBounds
    (C : Lemma7ArcAngleCertificate D) :
    TurnBoundsInterface.HonestTurnBounds :=
  C.toNonconcaveArcGeometricAngleFacts.toHonestTurnBounds

@[simp]
theorem toM8TurnBounds_turn
    (C : Lemma7ArcAngleCertificate D) :
    C.toM8TurnBounds.turn =
      C.toNonconcaveArcGeometricAngleFacts.normalizedTurn :=
  C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_turn

@[simp]
theorem toNonconcaveArcTurnData_rawTurn
    (C : Lemma7ArcAngleCertificate D) :
    C.toNonconcaveArcTurnData.rawTurn = C.rawTurn :=
  rfl

@[simp]
theorem toNonconcaveArcTurnData_turn
    (C : Lemma7ArcAngleCertificate D) :
    C.toNonconcaveArcTurnData.turn =
      C.toNonconcaveArcGeometricAngleFacts.normalizedTurn :=
  C.toNonconcaveArcGeometricAngleFacts.toNonconcaveArcTurnData_turn

@[simp]
theorem toHonestTurnBounds_turn
    (C : Lemma7ArcAngleCertificate D) :
    C.toHonestTurnBounds.turn =
      C.toNonconcaveArcGeometricAngleFacts.normalizedTurn :=
  C.toNonconcaveArcGeometricAngleFacts.toHonestTurnBounds_turn

@[simp]
theorem toM8TurnBounds_turn_of_mem
    (C : Lemma7ArcAngleCertificate D) {k : Nat}
    (hk : Membership.mem turnIndexSet k) :
    C.toM8TurnBounds.turn k = C.rawTurn k := by
  simpa using
    C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_turn_of_mem hk

@[simp]
theorem toM8TurnBounds_turn_of_not_mem
    (C : Lemma7ArcAngleCertificate D) {k : Nat}
    (hk : Not (Membership.mem turnIndexSet k)) :
    C.toM8TurnBounds.turn k = 0 := by
  simpa using
    C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_turn_of_not_mem hk

theorem toM8TurnBounds_turn_nonnegative
    (C : Lemma7ArcAngleCertificate D) (k : Nat) :
    0 <= C.toM8TurnBounds.turn k :=
  C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_turn_nonnegative k

theorem raw_totalTurn_nonnegative
    (C : Lemma7ArcAngleCertificate D) :
    0 <= totalTurn C.rawTurn :=
  C.toNonconcaveArcGeometricAngleFacts.raw_totalTurn_nonnegative

theorem geometricAngleBudget_nonnegative
    (C : Lemma7ArcAngleCertificate D) :
    0 <= C.geometricAngleBudget :=
  C.toNonconcaveArcGeometricAngleFacts.geometricAngleBudget_nonnegative

theorem raw_totalTurn_eq_m8ThirteenTurnSum
    (C : Lemma7ArcAngleCertificate D) :
    totalTurn C.rawTurn = m8ThirteenTurnSum C.rawTurn :=
  C.toNonconcaveArcGeometricAngleFacts.raw_totalTurn_eq_m8ThirteenTurnSum

theorem raw_m8ThirteenTurnSum_le_geometricAngleBudget
    (C : Lemma7ArcAngleCertificate D) :
    m8ThirteenTurnSum C.rawTurn <= C.geometricAngleBudget :=
  C.toNonconcaveArcGeometricAngleFacts.raw_m8ThirteenTurnSum_le_geometricAngleBudget

theorem raw_m8ThirteenTurnSum_lt_pi_div_three
    (C : Lemma7ArcAngleCertificate D) :
    m8ThirteenTurnSum C.rawTurn < Real.pi / 3 :=
  C.toNonconcaveArcGeometricAngleFacts.raw_m8ThirteenTurnSum_lt_pi_div_three

theorem toM8TurnBounds_totalTurn_eq_rawTurn
    (C : Lemma7ArcAngleCertificate D) :
    totalTurn C.toM8TurnBounds.turn = totalTurn C.rawTurn :=
  C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_totalTurn_eq_rawTurn

theorem toM8TurnBounds_totalTurn_lt_pi_div_three
    (C : Lemma7ArcAngleCertificate D) :
    totalTurn C.toM8TurnBounds.turn < Real.pi / 3 :=
  C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_totalTurn_lt_pi_div_three

theorem toM8TurnBounds_totalTurn_le_geometricAngleBudget
    (C : Lemma7ArcAngleCertificate D) :
    totalTurn C.toM8TurnBounds.turn <= C.geometricAngleBudget :=
  C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_totalTurn_le_geometricAngleBudget

theorem toM8TurnBounds_totalTurn_eq_m8ThirteenTurnSum
    (C : Lemma7ArcAngleCertificate D) :
    totalTurn C.toM8TurnBounds.turn =
      m8ThirteenTurnSum C.toM8TurnBounds.turn :=
  C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_totalTurn_eq_m8ThirteenTurnSum

theorem toM8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum
    (C : Lemma7ArcAngleCertificate D) :
    totalTurn C.toM8TurnBounds.turn =
      m8ThirteenTurnSum C.rawTurn :=
  C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum

theorem toM8TurnBounds_m8ThirteenTurnSum_eq_raw
    (C : Lemma7ArcAngleCertificate D) :
    m8ThirteenTurnSum C.toM8TurnBounds.turn =
      m8ThirteenTurnSum C.rawTurn :=
  C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_m8ThirteenTurnSum_eq_raw

theorem toM8TurnBounds_m8ThirteenTurnSum_le_geometricAngleBudget
    (C : Lemma7ArcAngleCertificate D) :
    m8ThirteenTurnSum C.toM8TurnBounds.turn <= C.geometricAngleBudget :=
  C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_m8ThirteenTurnSum_le_geometricAngleBudget

theorem toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three
    (C : Lemma7ArcAngleCertificate D) :
    m8ThirteenTurnSum C.toM8TurnBounds.turn < Real.pi / 3 :=
  C.toNonconcaveArcGeometricAngleFacts.toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three

theorem toM8TurnBounds_total_turn_lt_pi_div_three_field
    (C : Lemma7ArcAngleCertificate D) :
    totalTurn C.toM8TurnBounds.turn < Real.pi / 3 :=
  C.toM8TurnBounds.total_turn_lt_pi_div_three

/-- Reusable M8 output bundle produced directly from Lemma 6/7 certificate
data. -/
structure M8TurnBoundOutputs
    (C : Lemma7ArcAngleCertificate D) where
  noGapOnArc :
    forall k : Nat, Membership.mem turnIndexSet k -> Not (C.gapAt k)
  rawTurn_nonnegative_on_arc :
    forall k : Nat, Membership.mem turnIndexSet k -> 0 <= C.rawTurn k
  totalTurn_le_geometricAngleBudget :
    totalTurn C.rawTurn <= C.geometricAngleBudget
  angleFacts : NonconcaveArcGeometricAngleFacts
  arcData : NonconcaveArcTurnData
  honestTurnBounds : TurnBoundsInterface.HonestTurnBounds
  m8TurnBounds : M8ConstructionInterface.M8TurnBounds
  angleFacts_rawTurn : angleFacts.rawTurn = C.rawTurn
  angleFacts_geometricAngleBudget :
    angleFacts.geometricAngleBudget = C.geometricAngleBudget
  arcData_rawTurn : arcData.rawTurn = C.rawTurn
  arcData_turn : arcData.turn = angleFacts.normalizedTurn
  honestTurnBounds_turn : honestTurnBounds.turn = angleFacts.normalizedTurn
  m8TurnBounds_turn : m8TurnBounds.turn = angleFacts.normalizedTurn
  raw_totalTurn_nonnegative :
    0 <= totalTurn C.rawTurn
  geometricAngleBudget_nonnegative :
    0 <= C.geometricAngleBudget
  raw_totalTurn_eq_m8ThirteenTurnSum :
    totalTurn C.rawTurn = m8ThirteenTurnSum C.rawTurn
  raw_m8ThirteenTurnSum_le_geometricAngleBudget :
    m8ThirteenTurnSum C.rawTurn <= C.geometricAngleBudget
  raw_m8ThirteenTurnSum_lt_pi_div_three :
    m8ThirteenTurnSum C.rawTurn < Real.pi / 3
  m8TurnBounds_turn_nonnegative :
    forall k : Nat, 0 <= m8TurnBounds.turn k
  m8TurnBounds_totalTurn_eq_rawTurn :
    totalTurn m8TurnBounds.turn = totalTurn C.rawTurn
  m8TurnBounds_totalTurn_le_geometricAngleBudget :
    totalTurn m8TurnBounds.turn <= C.geometricAngleBudget
  m8TurnBounds_totalTurn_lt_pi_div_three :
    totalTurn m8TurnBounds.turn < Real.pi / 3
  m8TurnBounds_totalTurn_eq_m8ThirteenTurnSum :
    totalTurn m8TurnBounds.turn =
      m8ThirteenTurnSum m8TurnBounds.turn
  m8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum :
    totalTurn m8TurnBounds.turn = m8ThirteenTurnSum C.rawTurn
  m8TurnBounds_total_turn_lt_pi_div_three_field :
    totalTurn m8TurnBounds.turn < Real.pi / 3
  m8TurnBounds_m8ThirteenTurnSum_eq_raw :
    m8ThirteenTurnSum m8TurnBounds.turn = m8ThirteenTurnSum C.rawTurn
  m8TurnBounds_m8ThirteenTurnSum_le_geometricAngleBudget :
    m8ThirteenTurnSum m8TurnBounds.turn <= C.geometricAngleBudget
  m8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three :
    m8ThirteenTurnSum m8TurnBounds.turn < Real.pi / 3

/-- Extract all reusable M8 outputs from Lemma 6/7 certificate data. -/
def toM8TurnBoundOutputs
    (C : Lemma7ArcAngleCertificate D) :
    M8TurnBoundOutputs C where
  noGapOnArc := C.no_gap_on_arc
  rawTurn_nonnegative_on_arc := C.rawTurn_nonnegative_on_arc
  totalTurn_le_geometricAngleBudget :=
    C.totalTurn_le_geometricAngleBudget
  angleFacts := C.toNonconcaveArcGeometricAngleFacts
  arcData := C.toNonconcaveArcTurnData
  honestTurnBounds := C.toHonestTurnBounds
  m8TurnBounds := C.toM8TurnBounds
  angleFacts_rawTurn := rfl
  angleFacts_geometricAngleBudget := rfl
  arcData_rawTurn := rfl
  arcData_turn := C.toNonconcaveArcTurnData_turn
  honestTurnBounds_turn := C.toHonestTurnBounds_turn
  m8TurnBounds_turn := C.toM8TurnBounds_turn
  raw_totalTurn_nonnegative := C.raw_totalTurn_nonnegative
  geometricAngleBudget_nonnegative := C.geometricAngleBudget_nonnegative
  raw_totalTurn_eq_m8ThirteenTurnSum :=
    C.raw_totalTurn_eq_m8ThirteenTurnSum
  raw_m8ThirteenTurnSum_le_geometricAngleBudget :=
    C.raw_m8ThirteenTurnSum_le_geometricAngleBudget
  raw_m8ThirteenTurnSum_lt_pi_div_three :=
    C.raw_m8ThirteenTurnSum_lt_pi_div_three
  m8TurnBounds_turn_nonnegative := C.toM8TurnBounds_turn_nonnegative
  m8TurnBounds_totalTurn_eq_rawTurn :=
    C.toM8TurnBounds_totalTurn_eq_rawTurn
  m8TurnBounds_totalTurn_le_geometricAngleBudget :=
    C.toM8TurnBounds_totalTurn_le_geometricAngleBudget
  m8TurnBounds_totalTurn_lt_pi_div_three :=
    C.toM8TurnBounds_totalTurn_lt_pi_div_three
  m8TurnBounds_totalTurn_eq_m8ThirteenTurnSum :=
    C.toM8TurnBounds_totalTurn_eq_m8ThirteenTurnSum
  m8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum :=
    C.toM8TurnBounds_totalTurn_eq_raw_m8ThirteenTurnSum
  m8TurnBounds_total_turn_lt_pi_div_three_field :=
    C.toM8TurnBounds_total_turn_lt_pi_div_three_field
  m8TurnBounds_m8ThirteenTurnSum_eq_raw :=
    C.toM8TurnBounds_m8ThirteenTurnSum_eq_raw
  m8TurnBounds_m8ThirteenTurnSum_le_geometricAngleBudget :=
    C.toM8TurnBounds_m8ThirteenTurnSum_le_geometricAngleBudget
  m8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three :=
    C.toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three

@[simp]
theorem toM8TurnBoundOutputs_m8TurnBounds
    (C : Lemma7ArcAngleCertificate D) :
    C.toM8TurnBoundOutputs.m8TurnBounds = C.toM8TurnBounds :=
  rfl

@[simp]
theorem toM8TurnBoundOutputs_arcData
    (C : Lemma7ArcAngleCertificate D) :
    C.toM8TurnBoundOutputs.arcData = C.toNonconcaveArcTurnData :=
  rfl

end Lemma7ArcAngleCertificate

end NonconcaveArcAngleFacts
end Swanepoel
end ErdosProblems1066

end
