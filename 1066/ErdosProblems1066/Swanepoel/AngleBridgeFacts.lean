import ErdosProblems1066.Swanepoel.TriangleAngleFacts

/-!
# Distance-to-dot-product bridge facts for Swanepoel angle obligations

This file contains only kernel-checked algebra around the Euclidean distance
assumptions that occur in the E22/E23 Figure 8/Figure 9 reductions.  The goal
is to turn explicit unit/minimum-distance hypotheses into the `sqDist` and
`dotAt` hypotheses used by `Swanepoel.TriangleAngleFacts`.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace AngleBridgeFacts

open TriangleAngleFacts

abbrev Point : Type :=
  TriangleAngleFacts.Point

def eucDist (p q : Point) : Real :=
  Geometry.Distance.eucDist p q

def EucUnit (p q : Point) : Prop :=
  eucDist p q = 1

def EucSeparated (p q : Point) : Prop :=
  1 <= eucDist p q

lemma sqDist_eq_one_of_eucUnit {p q : Point} (h : EucUnit p q) :
    sqDist p q = 1 :=
  (geometry_eucDist_eq_one_iff_sqDist_eq_one p q).mp h

lemma eucUnit_of_sqDist_eq_one {p q : Point} (h : sqDist p q = 1) :
    EucUnit p q :=
  (geometry_eucDist_eq_one_iff_sqDist_eq_one p q).mpr h

lemma one_le_sqDist_of_eucSeparated {p q : Point} (h : EucSeparated p q) :
    1 <= sqDist p q := by
  rw [sqDist_eq]
  exact (Geometry.Distance.eucDist_ge_one_iff p q).mp h

lemma eucSeparated_of_one_le_sqDist {p q : Point} (h : 1 <= sqDist p q) :
    EucSeparated p q := by
  rw [sqDist_eq] at h
  exact (Geometry.Distance.eucDist_ge_one_iff p q).mpr h

lemma eucUnit_comm {p q : Point} (h : EucUnit p q) :
    EucUnit q p := by
  unfold EucUnit eucDist at *
  rwa [Geometry.Distance.eucDist_comm]

lemma eucSeparated_comm {p q : Point} (h : EucSeparated p q) :
    EucSeparated q p := by
  unfold EucSeparated eucDist at *
  rwa [Geometry.Distance.eucDist_comm]

lemma sqDist_unit_sides_of_eucUnit_sides
    {a b c : Point} (hab : EucUnit a b) (hcb : EucUnit c b) :
    sqDist a b = 1 /\ sqDist c b = 1 :=
  ⟨sqDist_eq_one_of_eucUnit hab, sqDist_eq_one_of_eucUnit hcb⟩

lemma dotAt_le_half_of_eucUnit_sides_eucSeparated_base
    {a b c : Point} (hab : EucUnit a b) (hcb : EucUnit c b)
    (hac : EucSeparated a c) :
    dotAt a b c <= 1 / 2 :=
  dotAt_le_half_of_unit_sides_sqDist_ge_one
    (sqDist_eq_one_of_eucUnit hab)
    (sqDist_eq_one_of_eucUnit hcb)
    (one_le_sqDist_of_eucSeparated hac)

lemma half_le_dotAt_of_eucUnit_sides_sqDist_base_le_one
    {a b c : Point} (hab : EucUnit a b) (hcb : EucUnit c b)
    (hac : sqDist a c <= 1) :
    1 / 2 <= dotAt a b c :=
  half_le_dotAt_of_unit_sides_sqDist_le_one
    (sqDist_eq_one_of_eucUnit hab)
    (sqDist_eq_one_of_eucUnit hcb)
    hac

lemma one_le_sqDist_iff_dotAt_le_half_of_eucUnit_sides
    {a b c : Point} (hab : EucUnit a b) (hcb : EucUnit c b) :
    1 <= sqDist a c <-> dotAt a b c <= 1 / 2 := by
  constructor
  · intro hbase
    exact dotAt_le_half_of_unit_sides_sqDist_ge_one
      (sqDist_eq_one_of_eucUnit hab)
      (sqDist_eq_one_of_eucUnit hcb)
      hbase
  · intro hdot
    exact one_le_sqDist_of_unit_sides_dotAt_le_half
      (sqDist_eq_one_of_eucUnit hab)
      (sqDist_eq_one_of_eucUnit hcb)
      hdot

lemma sqDist_le_one_iff_half_le_dotAt_of_eucUnit_sides
    {a b c : Point} (hab : EucUnit a b) (hcb : EucUnit c b) :
    sqDist a c <= 1 <-> 1 / 2 <= dotAt a b c := by
  constructor
  · intro hbase
    exact half_le_dotAt_of_unit_sides_sqDist_le_one
      (sqDist_eq_one_of_eucUnit hab)
      (sqDist_eq_one_of_eucUnit hcb)
      hbase
  · intro hdot
    exact sqDist_le_one_of_unit_sides_half_le_dotAt
      (sqDist_eq_one_of_eucUnit hab)
      (sqDist_eq_one_of_eucUnit hcb)
      hdot

lemma sqDist_base_eq_two_sub_two_dotAt_of_eucUnit_sides
    {a b c : Point} (hab : EucUnit a b) (hcb : EucUnit c b) :
    sqDist a c = 2 - 2 * dotAt a b c :=
  sqDist_eq_two_sub_two_dotAt_of_unit_sides
    (sqDist_eq_one_of_eucUnit hab)
    (sqDist_eq_one_of_eucUnit hcb)

lemma dotAt_eq_half_of_eucUnit_equilateral
    {a b c : Point} (hab : EucUnit a b) (hcb : EucUnit c b)
    (hac : EucUnit a c) :
    dotAt a b c = 1 / 2 :=
  dotAt_eq_half_of_equilateral_unit
    (sqDist_eq_one_of_eucUnit hab)
    (sqDist_eq_one_of_eucUnit hcb)
    (sqDist_eq_one_of_eucUnit hac)

/-! ## Named Figure 8 and Figure 9 distance packages -/

/-- The distance data in the Figure 8 analytic reduction that is immediately
usable by the square-distance/dot-product lemmas.  The point `p` is the common
unit neighbour of `qi` and `qj`; `s` and `r` are the two comparison vertices. -/
structure Figure8DistanceData (p qi qj s r : Point) where
  p_qi : EucUnit p qi
  p_qj : EucUnit p qj
  qi_s : EucUnit qi s
  qj_r : EucUnit qj r
  qi_qj_sep : EucSeparated qi qj
  s_r_sep : EucSeparated s r

namespace Figure8DistanceData

variable {p qi qj s r : Point}

lemma qi_qj_sqDist_ge_one (D : Figure8DistanceData p qi qj s r) :
    1 <= sqDist qi qj :=
  one_le_sqDist_of_eucSeparated
    (Figure8DistanceData.qi_qj_sep D)

lemma s_r_sqDist_ge_one (D : Figure8DistanceData p qi qj s r) :
    1 <= sqDist s r :=
  one_le_sqDist_of_eucSeparated
    (Figure8DistanceData.s_r_sep D)

lemma central_dotAt_le_half (D : Figure8DistanceData p qi qj s r) :
    dotAt qi p qj <= 1 / 2 :=
  dotAt_le_half_of_eucUnit_sides_eucSeparated_base
    (eucUnit_comm (Figure8DistanceData.p_qi D))
    (eucUnit_comm (Figure8DistanceData.p_qj D))
    (Figure8DistanceData.qi_qj_sep D)

lemma central_sqDist_eq_two_sub_two_dotAt
    (D : Figure8DistanceData p qi qj s r) :
    sqDist qi qj = 2 - 2 * dotAt qi p qj :=
  sqDist_base_eq_two_sub_two_dotAt_of_eucUnit_sides
    (eucUnit_comm (Figure8DistanceData.p_qi D))
    (eucUnit_comm (Figure8DistanceData.p_qj D))

lemma separated_chord_dotAt_le_half
    (D : Figure8DistanceData p qi qj s r)
    (hqs : EucUnit qi r) :
  dotAt s qi r <= 1 / 2 :=
  dotAt_le_half_of_eucUnit_sides_eucSeparated_base
    (eucUnit_comm (Figure8DistanceData.qi_s D)) (eucUnit_comm hqs)
    (Figure8DistanceData.s_r_sep D)

end Figure8DistanceData

/-- The distance data in the Figure 9 analytic reduction that feeds the same
`sqDist`/`dotAt` API. -/
structure Figure9DistanceData (p qi qj s r : Point) where
  p_qi : EucUnit p qi
  p_qj : EucUnit p qj
  qi_s : EucUnit qi s
  qj_r : EucUnit qj r
  qi_qj_sep : EucSeparated qi qj
  p_s_sep : EucSeparated p s
  p_r_sep : EucSeparated p r
  s_r_sep : EucSeparated s r

namespace Figure9DistanceData

variable {p qi qj s r : Point}

lemma central_dotAt_le_half (D : Figure9DistanceData p qi qj s r) :
    dotAt qi p qj <= 1 / 2 :=
  dotAt_le_half_of_eucUnit_sides_eucSeparated_base
    (eucUnit_comm (Figure9DistanceData.p_qi D))
    (eucUnit_comm (Figure9DistanceData.p_qj D))
    (Figure9DistanceData.qi_qj_sep D)

lemma left_comparison_dotAt_le_half
    (D : Figure9DistanceData p qi qj s r) :
  dotAt p qi s <= 1 / 2 :=
  dotAt_le_half_of_eucUnit_sides_eucSeparated_base
    (Figure9DistanceData.p_qi D)
    (eucUnit_comm (Figure9DistanceData.qi_s D))
    (Figure9DistanceData.p_s_sep D)

lemma right_comparison_dotAt_le_half
    (D : Figure9DistanceData p qi qj s r) :
  dotAt p qj r <= 1 / 2 :=
  dotAt_le_half_of_eucUnit_sides_eucSeparated_base
    (Figure9DistanceData.p_qj D)
    (eucUnit_comm (Figure9DistanceData.qj_r D))
    (Figure9DistanceData.p_r_sep D)

lemma comparison_chord_sqDist_ge_one
    (D : Figure9DistanceData p qi qj s r) :
    1 <= sqDist s r :=
  one_le_sqDist_of_eucSeparated
    (Figure9DistanceData.s_r_sep D)

lemma left_base_sqDist_ge_one
    (D : Figure9DistanceData p qi qj s r) :
    1 <= sqDist p s :=
  one_le_sqDist_of_eucSeparated
    (Figure9DistanceData.p_s_sep D)

lemma right_base_sqDist_ge_one
    (D : Figure9DistanceData p qi qj s r) :
    1 <= sqDist p r :=
  one_le_sqDist_of_eucSeparated
    (Figure9DistanceData.p_r_sep D)

end Figure9DistanceData

end AngleBridgeFacts
end Swanepoel
end ErdosProblems1066

end
