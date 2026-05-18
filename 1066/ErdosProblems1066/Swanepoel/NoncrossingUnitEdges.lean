import ErdosProblems1066.Swanepoel.PlanarInterface

/-!
# Noncrossing obstruction for separated unit edges

This module proves the analytic obstruction behind the straight-line
noncrossing interface: if two unit segments meet in their relative interiors,
then some endpoint of one segment is closer than `1` to some endpoint of the
other.  A separated unit-distance configuration therefore cannot contain such
a crossing between disjoint unit edges.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace NoncrossingUnitEdges

open PlanarInterface

abbrev Point : Type :=
  PlanarInterface.Point

/-- Squared Euclidean distance, avoiding square roots in the algebraic core. -/
def sqDist (p q : Point) : Real :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

lemma sqDist_eq_geometry_eucDist_sq (p q : Point) :
    sqDist p q = Geometry.Distance.eucDist p q ^ 2 := by
  rw [Geometry.Distance.eucDist_sq]
  rfl

lemma geometry_eucDist_lt_one_of_sqDist_lt_one {p q : Point}
    (h : sqDist p q < 1) :
    Geometry.Distance.eucDist p q < 1 := by
  by_contra hnot
  have hdist : 1 <= Geometry.Distance.eucDist p q := le_of_not_gt hnot
  have hsq : 1 <= sqDist p q := by
    simpa [sqDist] using (Geometry.Distance.eucDist_ge_one_iff p q).1 hdist
  linarith

lemma root_eucDist_lt_one_of_sqDist_lt_one {p q : Point}
    (h : sqDist p q < 1) :
    _root_.eucDist p q < 1 := by
  simpa [PlanarInterface.geometry_eucDist_eq_root] using
    geometry_eucDist_lt_one_of_sqDist_lt_one h

lemma weighted_cross_coordinate_identity (s t u v : Real) :
    (1 - s) * (1 - t) * (s * u - t * v) ^ 2 +
      (1 - s) * t * (s * u + (1 - t) * v) ^ 2 +
      s * (1 - t) * (-(1 - s) * u - t * v) ^ 2 +
      s * t * (-(1 - s) * u + (1 - t) * v) ^ 2 =
        s * (1 - s) * u ^ 2 + t * (1 - t) * v ^ 2 := by
  ring

set_option maxHeartbeats 2000000 in
-- The weighted-coordinate expansion is a large polynomial identity plus four
-- endpoint inequalities; keeping it in one theorem avoids introducing an
-- unproved geometric interface, but it needs a higher heartbeat budget.
/--
Algebraic core: if two unit segments have a common relative-interior point,
then not all four cross-endpoint squared distances can be at least `1`.
-/
theorem unit_segments_cross_not_all_endpoint_sqDist_ge_one
    {a b c d x : Point} {s t : Real}
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hxab : x = segmentPoint a b s) (hxcd : x = segmentPoint c d t)
    (hab : sqDist a b = 1) (hcd : sqDist c d = 1) :
    ¬ (1 <= sqDist a c /\ 1 <= sqDist a d /\
        1 <= sqDist b c /\ 1 <= sqDist b d) := by
  intro hall
  rcases hall with ⟨hac, had, hbc, hbd⟩
  have hxab1 : x.1 = (1 - s) * a.1 + s * b.1 := by
    simpa [segmentPoint] using congrArg Prod.fst hxab
  have hxab2 : x.2 = (1 - s) * a.2 + s * b.2 := by
    simpa [segmentPoint] using congrArg Prod.snd hxab
  have hxcd1 : x.1 = (1 - t) * c.1 + t * d.1 := by
    simpa [segmentPoint] using congrArg Prod.fst hxcd
  have hxcd2 : x.2 = (1 - t) * c.2 + t * d.2 := by
    simpa [segmentPoint] using congrArg Prod.snd hxcd
  unfold sqDist at hab hcd hac had hbc hbd
  have hac1 : a.1 - c.1 = s * (a.1 - b.1) - t * (c.1 - d.1) := by
    nlinarith [hxab1, hxcd1]
  have hac2 : a.2 - c.2 = s * (a.2 - b.2) - t * (c.2 - d.2) := by
    nlinarith [hxab2, hxcd2]
  have had1 : a.1 - d.1 = s * (a.1 - b.1) + (1 - t) * (c.1 - d.1) := by
    calc
      a.1 - d.1 = (a.1 - c.1) + (c.1 - d.1) := by ring
      _ = s * (a.1 - b.1) + (1 - t) * (c.1 - d.1) := by
        rw [hac1]
        ring
  have had2 : a.2 - d.2 = s * (a.2 - b.2) + (1 - t) * (c.2 - d.2) := by
    calc
      a.2 - d.2 = (a.2 - c.2) + (c.2 - d.2) := by ring
      _ = s * (a.2 - b.2) + (1 - t) * (c.2 - d.2) := by
        rw [hac2]
        ring
  have hbc1 : b.1 - c.1 = -(1 - s) * (a.1 - b.1) - t * (c.1 - d.1) := by
    calc
      b.1 - c.1 = (a.1 - c.1) - (a.1 - b.1) := by ring
      _ = -(1 - s) * (a.1 - b.1) - t * (c.1 - d.1) := by
        rw [hac1]
        ring
  have hbc2 : b.2 - c.2 = -(1 - s) * (a.2 - b.2) - t * (c.2 - d.2) := by
    calc
      b.2 - c.2 = (a.2 - c.2) - (a.2 - b.2) := by ring
      _ = -(1 - s) * (a.2 - b.2) - t * (c.2 - d.2) := by
        rw [hac2]
        ring
  have hbd1 : b.1 - d.1 = -(1 - s) * (a.1 - b.1) + (1 - t) * (c.1 - d.1) := by
    calc
      b.1 - d.1 = (b.1 - c.1) + (c.1 - d.1) := by ring
      _ = -(1 - s) * (a.1 - b.1) + (1 - t) * (c.1 - d.1) := by
        rw [hbc1]
        ring
  have hbd2 : b.2 - d.2 = -(1 - s) * (a.2 - b.2) + (1 - t) * (c.2 - d.2) := by
    calc
      b.2 - d.2 = (b.2 - c.2) + (c.2 - d.2) := by ring
      _ = -(1 - s) * (a.2 - b.2) + (1 - t) * (c.2 - d.2) := by
        rw [hbc2]
        ring
  have hweighted :
      (1 - s) * (1 - t) *
          ((a.1 - c.1) ^ 2 + (a.2 - c.2) ^ 2) +
        (1 - s) * t *
          ((a.1 - d.1) ^ 2 + (a.2 - d.2) ^ 2) +
        s * (1 - t) *
          ((b.1 - c.1) ^ 2 + (b.2 - c.2) ^ 2) +
        s * t *
          ((b.1 - d.1) ^ 2 + (b.2 - d.2) ^ 2) =
        s * (1 - s) + t * (1 - t) := by
    rw [hac1, hac2, had1, had2, hbc1, hbc2, hbd1, hbd2]
    calc
      (1 - s) * (1 - t) *
            ((s * (a.1 - b.1) - t * (c.1 - d.1)) ^ 2 +
              (s * (a.2 - b.2) - t * (c.2 - d.2)) ^ 2) +
          (1 - s) * t *
            ((s * (a.1 - b.1) + (1 - t) * (c.1 - d.1)) ^ 2 +
              (s * (a.2 - b.2) + (1 - t) * (c.2 - d.2)) ^ 2) +
          s * (1 - t) *
            ((-(1 - s) * (a.1 - b.1) - t * (c.1 - d.1)) ^ 2 +
              (-(1 - s) * (a.2 - b.2) - t * (c.2 - d.2)) ^ 2) +
          s * t *
            ((-(1 - s) * (a.1 - b.1) + (1 - t) * (c.1 - d.1)) ^ 2 +
              (-(1 - s) * (a.2 - b.2) + (1 - t) * (c.2 - d.2)) ^ 2)
          =
          ((1 - s) * (1 - t) *
              (s * (a.1 - b.1) - t * (c.1 - d.1)) ^ 2 +
            (1 - s) * t *
              (s * (a.1 - b.1) + (1 - t) * (c.1 - d.1)) ^ 2 +
            s * (1 - t) *
              (-(1 - s) * (a.1 - b.1) - t * (c.1 - d.1)) ^ 2 +
            s * t *
              (-(1 - s) * (a.1 - b.1) + (1 - t) * (c.1 - d.1)) ^ 2) +
          ((1 - s) * (1 - t) *
              (s * (a.2 - b.2) - t * (c.2 - d.2)) ^ 2 +
            (1 - s) * t *
              (s * (a.2 - b.2) + (1 - t) * (c.2 - d.2)) ^ 2 +
            s * (1 - t) *
              (-(1 - s) * (a.2 - b.2) - t * (c.2 - d.2)) ^ 2 +
            s * t *
              (-(1 - s) * (a.2 - b.2) + (1 - t) * (c.2 - d.2)) ^ 2) := by
            ring
      _ =
          (s * (1 - s) * (a.1 - b.1) ^ 2 +
              t * (1 - t) * (c.1 - d.1) ^ 2) +
            (s * (1 - s) * (a.2 - b.2) ^ 2 +
              t * (1 - t) * (c.2 - d.2) ^ 2) := by
            rw [weighted_cross_coordinate_identity,
              weighted_cross_coordinate_identity]
      _ = s * (1 - s) *
              ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) +
            t * (1 - t) *
              ((c.1 - d.1) ^ 2 + (c.2 - d.2) ^ 2) := by
            ring
      _ = s * (1 - s) + t * (1 - t) := by
            rw [hab, hcd]
            ring
  have hs_nonneg : 0 <= s := le_of_lt hs0
  have ht_nonneg : 0 <= t := le_of_lt ht0
  have h1s_nonneg : 0 <= 1 - s := by linarith
  have h1t_nonneg : 0 <= 1 - t := by linarith
  have hwac_nonneg : 0 <= (1 - s) * (1 - t) :=
    mul_nonneg h1s_nonneg h1t_nonneg
  have hwad_nonneg : 0 <= (1 - s) * t :=
    mul_nonneg h1s_nonneg ht_nonneg
  have hwbc_nonneg : 0 <= s * (1 - t) :=
    mul_nonneg hs_nonneg h1t_nonneg
  have hwbd_nonneg : 0 <= s * t :=
    mul_nonneg hs_nonneg ht_nonneg
  have hwac :
      (1 - s) * (1 - t) <=
        (1 - s) * (1 - t) *
          ((a.1 - c.1) ^ 2 + (a.2 - c.2) ^ 2) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hac hwac_nonneg
  have hwad :
      (1 - s) * t <=
        (1 - s) * t *
          ((a.1 - d.1) ^ 2 + (a.2 - d.2) ^ 2) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left had hwad_nonneg
  have hwbc :
      s * (1 - t) <=
        s * (1 - t) *
          ((b.1 - c.1) ^ 2 + (b.2 - c.2) ^ 2) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbc hwbc_nonneg
  have hwbd :
      s * t <=
        s * t *
          ((b.1 - d.1) ^ 2 + (b.2 - d.2) ^ 2) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hbd hwbd_nonneg
  have hsumWeights :
      (1 - s) * (1 - t) + (1 - s) * t + s * (1 - t) + s * t = 1 := by
    ring
  have hlower :
      1 <=
        (1 - s) * (1 - t) *
            ((a.1 - c.1) ^ 2 + (a.2 - c.2) ^ 2) +
          (1 - s) * t *
            ((a.1 - d.1) ^ 2 + (a.2 - d.2) ^ 2) +
          s * (1 - t) *
            ((b.1 - c.1) ^ 2 + (b.2 - c.2) ^ 2) +
          s * t *
            ((b.1 - d.1) ^ 2 + (b.2 - d.2) ^ 2) := by
    linarith only [hwac, hwad, hwbc, hwbd, hsumWeights]
  have hupper : s * (1 - s) + t * (1 - t) < 1 := by
    nlinarith only [sq_nonneg (s - 1 / 2), sq_nonneg (t - 1 / 2)]
  linarith only [hweighted, hlower, hupper]

/--
Two crossing unit segments force a forbidden endpoint distance, stated with
squared distances.
-/
theorem unit_segments_cross_forces_endpoint_sqDist_lt_one
    {a b c d : Point}
    (hab : sqDist a b = 1) (hcd : sqDist c d = 1)
    (hcross : SegmentsCrossInterior a b c d) :
    sqDist a c < 1 \/ sqDist a d < 1 \/
      sqDist b c < 1 \/ sqDist b d < 1 := by
  rcases hcross with ⟨x, ⟨s, hs0, hs1, hxab⟩, ⟨t, ht0, ht1, hxcd⟩⟩
  by_contra hnot
  have hac : 1 <= sqDist a c := by
    exact le_of_not_gt (by
      intro h
      exact hnot (Or.inl h))
  have had : 1 <= sqDist a d := by
    exact le_of_not_gt (by
      intro h
      exact hnot (Or.inr (Or.inl h)))
  have hbc : 1 <= sqDist b c := by
    exact le_of_not_gt (by
      intro h
      exact hnot (Or.inr (Or.inr (Or.inl h))))
  have hbd : 1 <= sqDist b d := by
    exact le_of_not_gt (by
      intro h
      exact hnot (Or.inr (Or.inr (Or.inr h)))
      )
  exact unit_segments_cross_not_all_endpoint_sqDist_ge_one hs0 hs1 ht0 ht1 hxab hxcd hab hcd
    ⟨hac, had, hbc, hbd⟩

/--
Two crossing unit segments force a forbidden endpoint distance, stated with
Euclidean distances.
-/
theorem unit_segments_cross_forces_endpoint_dist_lt_one
    {a b c d : Point}
    (hab : Geometry.Distance.eucDist a b = 1)
    (hcd : Geometry.Distance.eucDist c d = 1)
    (hcross : SegmentsCrossInterior a b c d) :
    Geometry.Distance.eucDist a c < 1 \/ Geometry.Distance.eucDist a d < 1 \/
      Geometry.Distance.eucDist b c < 1 \/ Geometry.Distance.eucDist b d < 1 := by
  have habsq : sqDist a b = 1 := by
    simpa [sqDist] using (Geometry.Distance.eucDist_eq_one_iff a b).1 hab
  have hcdsq : sqDist c d = 1 := by
    simpa [sqDist] using (Geometry.Distance.eucDist_eq_one_iff c d).1 hcd
  rcases unit_segments_cross_forces_endpoint_sqDist_lt_one habsq hcdsq hcross with
    h | h | h | h
  · exact Or.inl (geometry_eucDist_lt_one_of_sqDist_lt_one h)
  · exact Or.inr (Or.inl (geometry_eucDist_lt_one_of_sqDist_lt_one h))
  · exact Or.inr (Or.inr (Or.inl (geometry_eucDist_lt_one_of_sqDist_lt_one h)))
  · exact Or.inr (Or.inr (Or.inr (geometry_eucDist_lt_one_of_sqDist_lt_one h)))

/--
Separated unit-distance configurations cannot have a relative-interior crossing
between disjoint unit edges.
-/
theorem separated_unit_edges_not_cross
    {n : Nat} (C : _root_.UDConfig n) {e f : Edge n}
    (hdisj : EdgeVertexDisjoint e f)
    (he : Geometry.Distance.eucDist (C.pts e.1) (C.pts e.2) = 1)
    (hf : Geometry.Distance.eucDist (C.pts f.1) (C.pts f.2) = 1) :
    ¬ EdgeSegmentsCross C e f := by
  intro hcross
  rcases hdisj with ⟨he1f1, he1f2, he2f1, he2f2⟩
  have hsep_e1f1 : 1 <= _root_.eucDist (C.pts e.1) (C.pts f.1) :=
    C.sep e.1 f.1 he1f1
  have hsep_e1f2 : 1 <= _root_.eucDist (C.pts e.1) (C.pts f.2) :=
    C.sep e.1 f.2 he1f2
  have hsep_e2f1 : 1 <= _root_.eucDist (C.pts e.2) (C.pts f.1) :=
    C.sep e.2 f.1 he2f1
  have hsep_e2f2 : 1 <= _root_.eucDist (C.pts e.2) (C.pts f.2) :=
    C.sep e.2 f.2 he2f2
  rcases unit_segments_cross_forces_endpoint_dist_lt_one he hf hcross with
    h | h | h | h
  · have hroot : _root_.eucDist (C.pts e.1) (C.pts f.1) < 1 := by
      simpa [PlanarInterface.geometry_eucDist_eq_root] using h
    linarith
  · have hroot : _root_.eucDist (C.pts e.1) (C.pts f.2) < 1 := by
      simpa [PlanarInterface.geometry_eucDist_eq_root] using h
    linarith
  · have hroot : _root_.eucDist (C.pts e.2) (C.pts f.1) < 1 := by
      simpa [PlanarInterface.geometry_eucDist_eq_root] using h
    linarith
  · have hroot : _root_.eucDist (C.pts e.2) (C.pts f.2) < 1 := by
      simpa [PlanarInterface.geometry_eucDist_eq_root] using h
    linarith

theorem unitDistanceEdges_not_cross
    {n : Nat} (C : _root_.UDConfig n) {e f : Edge n}
    (hdisj : EdgeVertexDisjoint e f)
    (he : e ∈ GraphBridge.unitDistanceEdges C)
    (hf : f ∈ GraphBridge.unitDistanceEdges C) :
    ¬ EdgeSegmentsCross C e f := by
  exact separated_unit_edges_not_cross C hdisj
    (PlanarInterface.mem_unitDistanceEdges_endpoints_geometry_dist_eq_one C he)
    (PlanarInterface.mem_unitDistanceEdges_endpoints_geometry_dist_eq_one C hf)

end NoncrossingUnitEdges
end Swanepoel
end ErdosProblems1066

end
