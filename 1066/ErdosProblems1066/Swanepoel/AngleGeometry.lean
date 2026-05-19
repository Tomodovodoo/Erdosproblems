import ErdosProblems1066.Swanepoel.AngleBridgeFacts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Swanepoel angle geometry

This module is a small, kernel-checked bridge from the repository's concrete
coordinate algebra in `TriangleAngleFacts` to mathlib's unoriented vector angle
API.

The existing Swanepoel files use `Point = Real x Real` together with hand-rolled
`sqDist` and `dotAt`.  Mathlib's angle API is available for inner product
spaces, so we embed the concrete plane into `EuclideanSpace Real (Fin 2)` and
state the angle at `b` as the angle between the two embedded side vectors.

What is not done here: polygon interior angles and angle-sum theorems for
faces.  Those still require extra geometric hypotheses about the cyclic
order/noncrossing embedding.  The lemmas below are the reusable local facts
needed first: unit side vectors with dot product at most `1 / 2` make an
unoriented angle at least `pi / 3`, and a checked oriented-angle chain
telescopes once S3 supplies the actual no-wrap/cyclic-order facts.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace AngleGeometry

open TriangleAngleFacts
open scoped EuclideanSpace

abbrev Point : Type :=
  TriangleAngleFacts.Point

abbrev Vec2 : Type :=
  EuclideanSpace Real (Fin 2)

/-- Embed the repository's concrete pair coordinates into mathlib's Euclidean
space. -/
def toVec (p : Point) : Vec2 :=
  WithLp.toLp 2 ![p.1, p.2]

/-- The mathlib unoriented angle between the two side vectors based at `b`. -/
def angleAt (a b c : Point) : Real :=
  InnerProductGeometry.angle (toVec (vsub a b)) (toVec (vsub c b))

lemma angleAt_nonneg (a b c : Point) :
    0 <= angleAt a b c := by
  exact InnerProductGeometry.angle_nonneg _ _

lemma angleAt_le_pi (a b c : Point) :
    angleAt a b c <= Real.pi := by
  exact InnerProductGeometry.angle_le_pi _ _

lemma angleAt_mem_Icc_zero_pi (a b c : Point) :
    Set.Icc 0 Real.pi (angleAt a b c) := by
  exact Set.mem_Icc.mpr
    (And.intro (angleAt_nonneg a b c) (angleAt_le_pi a b c))

/-- Real-angle unwrapping for a consecutive gap-angle telescope.

The intended S3 use is: cyclic order/no-crossing supplies the equality in
`Real.Angle`, and the outer-face half-plane/no-wrap facts supply the interval
bounds.  This lemma then converts that oriented telescope into an equality of
ordinary real angle sums. -/
lemma gapAngleSum_eq_sectorAngle_of_realAngle_eq_no_wrap
    {m : Nat} (gap : Fin m -> Real) {sector : Real}
    (hgap_nonneg : forall i, 0 <= gap i)
    (hsector_nonneg : 0 <= sector)
    (hsector_le_pi : sector <= Real.pi)
    (hsum_le_pi : Finset.sum Finset.univ gap <= Real.pi)
    (hangle :
      ((Finset.sum Finset.univ gap : Real) : Real.Angle) =
        (sector : Real.Angle)) :
    Finset.sum Finset.univ gap = sector := by
  have hsum_nonneg : 0 <= Finset.sum Finset.univ gap := by
    exact Finset.sum_nonneg (fun i _ => hgap_nonneg i)
  have hsum_toReal :
      (((Finset.sum Finset.univ gap : Real) : Real.Angle).toReal) =
        Finset.sum Finset.univ gap := by
    rw [Real.Angle.toReal_coe_eq_self_iff]
    exact And.intro (by nlinarith [Real.pi_pos, hsum_nonneg]) hsum_le_pi
  have hsector_toReal : ((sector : Real.Angle).toReal) = sector := by
    rw [Real.Angle.toReal_coe_eq_self_iff]
    exact And.intro (by nlinarith [Real.pi_pos, hsector_nonneg]) hsector_le_pi
  calc
    Finset.sum Finset.univ gap =
        (((Finset.sum Finset.univ gap : Real) : Real.Angle).toReal) :=
      hsum_toReal.symm
    _ = ((sector : Real.Angle).toReal) := by rw [hangle]
    _ = sector := hsector_toReal

/-- Inequality form of
`gapAngleSum_eq_sectorAngle_of_realAngle_eq_no_wrap`, matching the local S3
sector-containment row. -/
lemma gapAngleSum_le_sectorAngle_of_realAngle_eq_no_wrap
    {m : Nat} (gap : Fin m -> Real) {sector : Real}
    (hgap_nonneg : forall i, 0 <= gap i)
    (hsector_nonneg : 0 <= sector)
    (hsector_le_pi : sector <= Real.pi)
    (hsum_le_pi : Finset.sum Finset.univ gap <= Real.pi)
    (hangle :
      ((Finset.sum Finset.univ gap : Real) : Real.Angle) =
        (sector : Real.Angle)) :
    Finset.sum Finset.univ gap <= sector :=
  le_of_eq
    (gapAngleSum_eq_sectorAngle_of_realAngle_eq_no_wrap
      gap hgap_nonneg hsector_nonneg hsector_le_pi hsum_le_pi hangle)

/-- Finite oriented-angle telescope for a chain of nonzero rays.

This is deliberately only the algebraic `Real.Angle` statement supplied by
`Orientation.oangle_add`: S3 still has to prove that the chosen Euclidean rays
occur in cyclic order and that the resulting real representative does not
wrap. -/
lemma oangle_sum_range_succ_eq_oangle
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [Fact (Module.finrank Real V = 2)]
    (o : Orientation Real V (Fin 2)) (ray : Nat -> V) (m : Nat)
    (hnonzero : (i : Nat) -> i <= m -> ray i ≠ 0) :
    (Finset.sum (Finset.range m)
        (fun i => o.oangle (ray i) (ray (i + 1)))) =
      o.oangle (ray 0) (ray m) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hprev : (i : Nat) -> i <= m -> ray i ≠ 0 := by
        intro i hi
        exact hnonzero i (Nat.le_trans hi (Nat.le_succ m))
      rw [Finset.sum_range_succ, ih hprev]
      exact o.oangle_add
        (hnonzero 0 (Nat.zero_le _))
        (hnonzero m (Nat.le_succ m))
        (hnonzero (m + 1) le_rfl)

/-- The `Real.Angle` identity behind a consecutive gap-angle telescope.

This is the algebraic part only: each real gap value is identified with the
oriented angle between consecutive rays, and the sector value is identified
with the oriented angle between the endpoints. -/
lemma realAngle_gapAngleSum_eq_sectorAngle_of_oangle_chain
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [Fact (Module.finrank Real V = 2)]
    (o : Orientation Real V (Fin 2)) {m : Nat}
    (ray : Nat -> V) (gap : Fin m -> Real) {sector : Real}
    (hray_nonzero : (i : Nat) -> i <= m -> ray i ≠ 0)
    (hgap_oangle : forall i : Fin m,
      ((gap i : Real) : Real.Angle) =
        o.oangle (ray i.val) (ray (i.val + 1)))
    (hsector_oangle :
      (sector : Real.Angle) = o.oangle (ray 0) (ray m)) :
    ((Finset.sum Finset.univ gap : Real) : Real.Angle) =
      (sector : Real.Angle) := by
  have hgapAngle :
      ((Finset.sum Finset.univ gap : Real) : Real.Angle) =
        Finset.sum Finset.univ
          (fun i : Fin m => ((gap i : Real) : Real.Angle)) := by
    exact map_sum Real.Angle.coeHom gap Finset.univ
  have hfin_to_range :
      Finset.sum Finset.univ
          (fun i : Fin m => ((gap i : Real) : Real.Angle)) =
        Finset.sum (Finset.range m)
          (fun i => o.oangle (ray i) (ray (i + 1))) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simpa using hgap_oangle i
  calc
    ((Finset.sum Finset.univ gap : Real) : Real.Angle)
        = Finset.sum Finset.univ
            (fun i : Fin m => ((gap i : Real) : Real.Angle)) := hgapAngle
    _ = Finset.sum (Finset.range m)
        (fun i => o.oangle (ray i) (ray (i + 1))) := hfin_to_range
    _ = o.oangle (ray 0) (ray m) :=
        oangle_sum_range_succ_eq_oangle o ray m hray_nonzero
    _ = (sector : Real.Angle) := hsector_oangle.symm

/-- Real no-wrap form of `oangle_sum_range_succ_eq_oangle`.

The hypotheses `hgap_oangle` and `hsector_oangle` are the exact oriented-angle
facts S3 must obtain from cyclic neighbor order.  The nonnegativity and
`<= pi` assumptions are only the no-wrap data needed to pass from
`Real.Angle` back to ordinary real sums. -/
lemma gapAngleSum_eq_sectorAngle_of_oangle_chain_no_wrap
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [Fact (Module.finrank Real V = 2)]
    (o : Orientation Real V (Fin 2)) {m : Nat}
    (ray : Nat -> V) (gap : Fin m -> Real) {sector : Real}
    (hray_nonzero : (i : Nat) -> i <= m -> ray i ≠ 0)
    (hgap_nonneg : forall i, 0 <= gap i)
    (hsector_nonneg : 0 <= sector)
    (hsector_le_pi : sector <= Real.pi)
    (hsum_le_pi : Finset.sum Finset.univ gap <= Real.pi)
    (hgap_oangle : forall i : Fin m,
      ((gap i : Real) : Real.Angle) =
        o.oangle (ray i.val) (ray (i.val + 1)))
    (hsector_oangle :
      (sector : Real.Angle) = o.oangle (ray 0) (ray m)) :
    Finset.sum Finset.univ gap = sector := by
  have hangle :
      ((Finset.sum Finset.univ gap : Real) : Real.Angle) =
        (sector : Real.Angle) :=
    realAngle_gapAngleSum_eq_sectorAngle_of_oangle_chain
      o ray gap hray_nonzero hgap_oangle hsector_oangle
  exact gapAngleSum_eq_sectorAngle_of_realAngle_eq_no_wrap
    gap hgap_nonneg hsector_nonneg hsector_le_pi hsum_le_pi hangle

/-- Inequality no-wrap form of `oangle_sum_range_succ_eq_oangle`, matching
the sector-containment row used by the S3 interval construction. -/
lemma gapAngleSum_le_sectorAngle_of_oangle_chain_no_wrap
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [Fact (Module.finrank Real V = 2)]
    (o : Orientation Real V (Fin 2)) {m : Nat}
    (ray : Nat -> V) (gap : Fin m -> Real) {sector : Real}
    (hray_nonzero : (i : Nat) -> i <= m -> ray i ≠ 0)
    (hgap_nonneg : forall i, 0 <= gap i)
    (hsector_nonneg : 0 <= sector)
    (hsector_le_pi : sector <= Real.pi)
    (hsum_le_pi : Finset.sum Finset.univ gap <= Real.pi)
    (hgap_oangle : forall i : Fin m,
      ((gap i : Real) : Real.Angle) =
        o.oangle (ray i.val) (ray (i.val + 1)))
    (hsector_oangle :
      (sector : Real.Angle) = o.oangle (ray 0) (ray m)) :
    Finset.sum Finset.univ gap <= sector := by
  exact gapAngleSum_le_sectorAngle_of_realAngle_eq_no_wrap
    gap hgap_nonneg hsector_nonneg hsector_le_pi hsum_le_pi
    (realAngle_gapAngleSum_eq_sectorAngle_of_oangle_chain
      o ray gap hray_nonzero hgap_oangle hsector_oangle)

/-- Left endpoint of the `i`th consecutive gap in a chain of `m + 1`
neighbouring rays. -/
def gapChainLeftIndex (m : Nat) (i : Fin m) : Fin (m + 1) :=
  ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self m)⟩

/-- Right endpoint of the `i`th consecutive gap in a chain of `m + 1`
neighbouring rays. -/
def gapChainRightIndex (m : Nat) (i : Fin m) : Fin (m + 1) :=
  ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

/-- Fin-indexed version of `oangle_sum_range_succ_eq_oangle`.

This matches interval data stored as a list of `m + 1` neighbours: the sum of
the `m` consecutive oriented gaps telescopes to the first-to-last oriented
sector. -/
lemma oangle_sum_fin_succ_eq_oangle
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [Fact (Module.finrank Real V = 2)]
    (o : Orientation Real V (Fin 2)) {m : Nat}
    (ray : Fin (m + 1) -> V)
    (hray_nonzero : forall i, ray i ≠ 0) :
    (Finset.sum Finset.univ
        (fun i : Fin m =>
          o.oangle (ray (gapChainLeftIndex m i))
            (ray (gapChainRightIndex m i)))) =
      o.oangle (ray ⟨0, Nat.succ_pos m⟩)
        (ray ⟨m, Nat.lt_succ_self m⟩) := by
  let rayNat : Nat -> V := fun i =>
    if hi : i <= m then ray ⟨i, Nat.lt_succ_of_le hi⟩
    else ray ⟨m, Nat.lt_succ_self m⟩
  have hrayNat_nonzero : (i : Nat) -> i <= m -> rayNat i ≠ 0 := by
    intro i hi
    dsimp [rayNat]
    rw [dif_pos hi]
    exact hray_nonzero _
  have hsum :
      Finset.sum Finset.univ
          (fun i : Fin m =>
            o.oangle (ray (gapChainLeftIndex m i))
              (ray (gapChainRightIndex m i))) =
        Finset.sum (Finset.range m)
          (fun i => o.oangle (rayNat i) (rayNat (i + 1))) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    have hi_left : i.1 <= m := Nat.le_of_lt i.2
    have hi_right : i.1 + 1 <= m := Nat.succ_le_of_lt i.2
    dsimp [rayNat]
    rw [dif_pos hi_left, dif_pos hi_right]
    rfl
  calc
    Finset.sum Finset.univ
        (fun i : Fin m =>
          o.oangle (ray (gapChainLeftIndex m i))
            (ray (gapChainRightIndex m i)))
        = Finset.sum (Finset.range m)
            (fun i => o.oangle (rayNat i) (rayNat (i + 1))) := hsum
    _ = o.oangle (rayNat 0) (rayNat m) :=
        oangle_sum_range_succ_eq_oangle o rayNat m hrayNat_nonzero
    _ = o.oangle (ray ⟨0, Nat.succ_pos m⟩)
        (ray ⟨m, Nat.lt_succ_self m⟩) := by
      simp [rayNat]

/-- Fin-indexed `Real.Angle` telescope for consecutive gap values. -/
lemma realAngle_gapAngleSum_eq_sectorAngle_of_oangle_fin_chain
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [Fact (Module.finrank Real V = 2)]
    (o : Orientation Real V (Fin 2)) {m : Nat}
    (ray : Fin (m + 1) -> V) (gap : Fin m -> Real) {sector : Real}
    (hray_nonzero : forall i, ray i ≠ 0)
    (hgap_oangle : forall i : Fin m,
      ((gap i : Real) : Real.Angle) =
        o.oangle (ray (gapChainLeftIndex m i))
          (ray (gapChainRightIndex m i)))
    (hsector_oangle :
      (sector : Real.Angle) =
        o.oangle (ray ⟨0, Nat.succ_pos m⟩)
          (ray ⟨m, Nat.lt_succ_self m⟩)) :
    ((Finset.sum Finset.univ gap : Real) : Real.Angle) =
      (sector : Real.Angle) := by
  have hgapAngle :
      ((Finset.sum Finset.univ gap : Real) : Real.Angle) =
        Finset.sum Finset.univ
          (fun i : Fin m => ((gap i : Real) : Real.Angle)) := by
    exact map_sum Real.Angle.coeHom gap Finset.univ
  have hfin_to_chain :
      Finset.sum Finset.univ
          (fun i : Fin m => ((gap i : Real) : Real.Angle)) =
        Finset.sum Finset.univ
          (fun i : Fin m =>
            o.oangle (ray (gapChainLeftIndex m i))
              (ray (gapChainRightIndex m i))) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    exact hgap_oangle i
  calc
    ((Finset.sum Finset.univ gap : Real) : Real.Angle)
        = Finset.sum Finset.univ
            (fun i : Fin m => ((gap i : Real) : Real.Angle)) := hgapAngle
    _ = Finset.sum Finset.univ
        (fun i : Fin m =>
          o.oangle (ray (gapChainLeftIndex m i))
            (ray (gapChainRightIndex m i))) := hfin_to_chain
    _ = o.oangle (ray ⟨0, Nat.succ_pos m⟩)
        (ray ⟨m, Nat.lt_succ_self m⟩) :=
        oangle_sum_fin_succ_eq_oangle o ray hray_nonzero
    _ = (sector : Real.Angle) := hsector_oangle.symm

/-- Equality no-wrap form for a `Fin (m + 1)` chain of consecutive gap values. -/
lemma gapAngleSum_eq_sectorAngle_of_oangle_fin_chain_no_wrap
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [Fact (Module.finrank Real V = 2)]
    (o : Orientation Real V (Fin 2)) {m : Nat}
    (ray : Fin (m + 1) -> V) (gap : Fin m -> Real) {sector : Real}
    (hray_nonzero : forall i, ray i ≠ 0)
    (hgap_nonneg : forall i, 0 <= gap i)
    (hsector_nonneg : 0 <= sector)
    (hsector_le_pi : sector <= Real.pi)
    (hsum_le_pi : Finset.sum Finset.univ gap <= Real.pi)
    (hgap_oangle : forall i : Fin m,
      ((gap i : Real) : Real.Angle) =
        o.oangle (ray (gapChainLeftIndex m i))
          (ray (gapChainRightIndex m i)))
    (hsector_oangle :
      (sector : Real.Angle) =
        o.oangle (ray ⟨0, Nat.succ_pos m⟩)
          (ray ⟨m, Nat.lt_succ_self m⟩)) :
    Finset.sum Finset.univ gap = sector := by
  exact gapAngleSum_eq_sectorAngle_of_realAngle_eq_no_wrap
    gap hgap_nonneg hsector_nonneg hsector_le_pi hsum_le_pi
    (realAngle_gapAngleSum_eq_sectorAngle_of_oangle_fin_chain
      o ray gap hray_nonzero hgap_oangle hsector_oangle)

/-- Inequality no-wrap form for a `Fin (m + 1)` chain of consecutive gap
values, shaped for sector-containment rows. -/
lemma gapAngleSum_le_sectorAngle_of_oangle_fin_chain_no_wrap
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [Fact (Module.finrank Real V = 2)]
    (o : Orientation Real V (Fin 2)) {m : Nat}
    (ray : Fin (m + 1) -> V) (gap : Fin m -> Real) {sector : Real}
    (hray_nonzero : forall i, ray i ≠ 0)
    (hgap_nonneg : forall i, 0 <= gap i)
    (hsector_nonneg : 0 <= sector)
    (hsector_le_pi : sector <= Real.pi)
    (hsum_le_pi : Finset.sum Finset.univ gap <= Real.pi)
    (hgap_oangle : forall i : Fin m,
      ((gap i : Real) : Real.Angle) =
        o.oangle (ray (gapChainLeftIndex m i))
          (ray (gapChainRightIndex m i)))
    (hsector_oangle :
      (sector : Real.Angle) =
        o.oangle (ray ⟨0, Nat.succ_pos m⟩)
          (ray ⟨m, Nat.lt_succ_self m⟩)) :
    Finset.sum Finset.univ gap <= sector := by
  exact gapAngleSum_le_sectorAngle_of_realAngle_eq_no_wrap
    gap hgap_nonneg hsector_nonneg hsector_le_pi hsum_le_pi
    (realAngle_gapAngleSum_eq_sectorAngle_of_oangle_fin_chain
      o ray gap hray_nonzero hgap_oangle hsector_oangle)

/-- Equality form specialized to the real values carried by consecutive
`angleAt` gaps in a `Fin (m + 1)` neighbour chain around a fixed center. -/
lemma angleAt_gapAngleSum_eq_angleAt_sector_of_oangle_fin_neighbor_chain_no_wrap
    (o : Orientation Real Vec2 (Fin 2)) {m : Nat}
    (center : Point) (neighbor : Fin (m + 1) -> Point)
    (hray_nonzero :
      forall i, toVec (vsub (neighbor i) center) ≠ 0)
    (hsum_le_pi :
      Finset.sum Finset.univ
          (fun i : Fin m =>
            angleAt (neighbor (gapChainLeftIndex m i)) center
              (neighbor (gapChainRightIndex m i))) <= Real.pi)
    (hgap_oangle : forall i : Fin m,
      ((angleAt (neighbor (gapChainLeftIndex m i)) center
          (neighbor (gapChainRightIndex m i)) : Real) : Real.Angle) =
        o.oangle (toVec (vsub (neighbor (gapChainLeftIndex m i)) center))
          (toVec (vsub (neighbor (gapChainRightIndex m i)) center)))
    (hsector_oangle :
      (angleAt (neighbor ⟨0, Nat.succ_pos m⟩) center
          (neighbor ⟨m, Nat.lt_succ_self m⟩) : Real.Angle) =
        o.oangle (toVec (vsub (neighbor ⟨0, Nat.succ_pos m⟩) center))
          (toVec (vsub (neighbor ⟨m, Nat.lt_succ_self m⟩) center))) :
    Finset.sum Finset.univ
        (fun i : Fin m =>
          angleAt (neighbor (gapChainLeftIndex m i)) center
            (neighbor (gapChainRightIndex m i))) =
      angleAt (neighbor ⟨0, Nat.succ_pos m⟩) center
        (neighbor ⟨m, Nat.lt_succ_self m⟩) := by
  exact gapAngleSum_eq_sectorAngle_of_oangle_fin_chain_no_wrap
    o (fun i => toVec (vsub (neighbor i) center))
    (fun i : Fin m =>
      angleAt (neighbor (gapChainLeftIndex m i)) center
        (neighbor (gapChainRightIndex m i)))
    hray_nonzero
    (fun i =>
      angleAt_nonneg (neighbor (gapChainLeftIndex m i)) center
        (neighbor (gapChainRightIndex m i)))
    (angleAt_nonneg (neighbor ⟨0, Nat.succ_pos m⟩) center
      (neighbor ⟨m, Nat.lt_succ_self m⟩))
    (angleAt_le_pi (neighbor ⟨0, Nat.succ_pos m⟩) center
      (neighbor ⟨m, Nat.lt_succ_self m⟩))
    hsum_le_pi hgap_oangle hsector_oangle

/-- Inequality form specialized to the real values carried by consecutive
`angleAt` gaps in a `Fin (m + 1)` neighbour chain around a fixed center.  After
expanding `UnitSeparatedAngle.value`, this is the sector inequality needed for
cyclic unit-neighbour interval rows. -/
lemma angleAt_gapAngleSum_le_angleAt_sector_of_oangle_fin_neighbor_chain_no_wrap
    (o : Orientation Real Vec2 (Fin 2)) {m : Nat}
    (center : Point) (neighbor : Fin (m + 1) -> Point)
    (hray_nonzero :
      forall i, toVec (vsub (neighbor i) center) ≠ 0)
    (hsum_le_pi :
      Finset.sum Finset.univ
          (fun i : Fin m =>
            angleAt (neighbor (gapChainLeftIndex m i)) center
              (neighbor (gapChainRightIndex m i))) <= Real.pi)
    (hgap_oangle : forall i : Fin m,
      ((angleAt (neighbor (gapChainLeftIndex m i)) center
          (neighbor (gapChainRightIndex m i)) : Real) : Real.Angle) =
        o.oangle (toVec (vsub (neighbor (gapChainLeftIndex m i)) center))
          (toVec (vsub (neighbor (gapChainRightIndex m i)) center)))
    (hsector_oangle :
      (angleAt (neighbor ⟨0, Nat.succ_pos m⟩) center
          (neighbor ⟨m, Nat.lt_succ_self m⟩) : Real.Angle) =
        o.oangle (toVec (vsub (neighbor ⟨0, Nat.succ_pos m⟩) center))
          (toVec (vsub (neighbor ⟨m, Nat.lt_succ_self m⟩) center))) :
    Finset.sum Finset.univ
        (fun i : Fin m =>
          angleAt (neighbor (gapChainLeftIndex m i)) center
            (neighbor (gapChainRightIndex m i))) <=
      angleAt (neighbor ⟨0, Nat.succ_pos m⟩) center
        (neighbor ⟨m, Nat.lt_succ_self m⟩) := by
  exact gapAngleSum_le_sectorAngle_of_oangle_fin_chain_no_wrap
    o (fun i => toVec (vsub (neighbor i) center))
    (fun i : Fin m =>
      angleAt (neighbor (gapChainLeftIndex m i)) center
        (neighbor (gapChainRightIndex m i)))
    hray_nonzero
    (fun i =>
      angleAt_nonneg (neighbor (gapChainLeftIndex m i)) center
        (neighbor (gapChainRightIndex m i)))
    (angleAt_nonneg (neighbor ⟨0, Nat.succ_pos m⟩) center
      (neighbor ⟨m, Nat.lt_succ_self m⟩))
    (angleAt_le_pi (neighbor ⟨0, Nat.succ_pos m⟩) center
      (neighbor ⟨m, Nat.lt_succ_self m⟩))
    hsum_le_pi hgap_oangle hsector_oangle

lemma pi_div_three_mem_Icc_zero_pi :
    Set.Icc 0 Real.pi (Real.pi / 3) := by
  exact Set.mem_Icc.mpr
    (And.intro (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))

lemma inner_toVec_eq_dot (u v : Point) :
    inner Real (toVec u) (toVec v) = dot u v := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [toVec, dot, dotProduct, Fin.sum_univ_two]
  ring

lemma norm_toVec_sq_eq_sqNorm (u : Point) :
    norm (toVec u) ^ 2 = sqNorm u := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [toVec, sqNorm, dot, Fin.sum_univ_two]
  ring

lemma norm_toVec_eq_one_of_sqNorm_eq_one {u : Point} (hu : sqNorm u = 1) :
    norm (toVec u) = 1 := by
  have hsq : norm (toVec u) ^ 2 = 1 := by
    rw [norm_toVec_sq_eq_sqNorm, hu]
  nlinarith [norm_nonneg (toVec u), sq_nonneg (norm (toVec u) - 1)]

lemma norm_toVec_vsub_eq_one_of_sqDist_eq_one {p q : Point}
    (hpq : sqDist p q = 1) :
    norm (toVec (vsub p q)) = 1 := by
  exact norm_toVec_eq_one_of_sqNorm_eq_one hpq

lemma cos_angleAt_eq_dotAt_of_unit_sides
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1) :
    Real.cos (angleAt a b c) = dotAt a b c := by
  unfold angleAt
  rw [show
      Real.cos
          (InnerProductGeometry.angle
            (toVec (vsub a b)) (toVec (vsub c b))) =
        inner Real (toVec (vsub a b)) (toVec (vsub c b)) from
        (InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
          (norm_toVec_vsub_eq_one_of_sqDist_eq_one hab)
          (norm_toVec_vsub_eq_one_of_sqDist_eq_one hcb)).symm,
    inner_toVec_eq_dot]
  rfl

/-- Abstract mathlib angle estimate: two unit vectors with inner product at most
`1 / 2` have angle at least `pi / 3`. -/
lemma pi_div_three_le_angle_of_unit_inner_le_half
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    {x y : V} (hx : norm x = 1) (hy : norm y = 1)
    (hinner : inner Real x y <= 1 / 2) :
    Real.pi / 3 <= InnerProductGeometry.angle x y := by
  have hangle_mem :
      Set.Icc 0 Real.pi (InnerProductGeometry.angle x y) := by
    exact Set.mem_Icc.mpr
      (And.intro
        (InnerProductGeometry.angle_nonneg x y)
        (InnerProductGeometry.angle_le_pi x y))
  have hthird_mem : Set.Icc 0 Real.pi (Real.pi / 3) := by
    exact Set.mem_Icc.mpr
      (And.intro (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hcos_le :
      Real.cos (InnerProductGeometry.angle x y) <= Real.cos (Real.pi / 3) := by
    rw [show Real.cos (InnerProductGeometry.angle x y) =
        inner Real x y from
          (InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hx hy).symm,
      Real.cos_pi_div_three]
    exact hinner
  exact (Real.strictAntiOn_cos.le_iff_ge hangle_mem hthird_mem).mp hcos_le

/-- Equality version of the previous estimate. -/
lemma angle_eq_pi_div_three_of_unit_inner_eq_half
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    {x y : V} (hx : norm x = 1) (hy : norm y = 1)
    (hinner : inner Real x y = 1 / 2) :
    InnerProductGeometry.angle x y = Real.pi / 3 := by
  have hangle_mem :
      Set.Icc 0 Real.pi (InnerProductGeometry.angle x y) := by
    exact Set.mem_Icc.mpr
      (And.intro
        (InnerProductGeometry.angle_nonneg x y)
        (InnerProductGeometry.angle_le_pi x y))
  have hthird_mem : Set.Icc 0 Real.pi (Real.pi / 3) := by
    exact Set.mem_Icc.mpr
      (And.intro (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hcos_eq :
      Real.cos (InnerProductGeometry.angle x y) = Real.cos (Real.pi / 3) := by
    rw [show Real.cos (InnerProductGeometry.angle x y) =
        inner Real x y from
          (InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hx hy).symm,
      Real.cos_pi_div_three]
    exact hinner
  exact (Real.injOn_cos.eq_iff hangle_mem hthird_mem).mp hcos_eq

/-- Concrete Swanepoel bridge: unit side squared-distances plus a `dotAt`
upper bound imply the corresponding mathlib angle is at least `pi / 3`. -/
lemma pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hdot : dotAt a b c <= 1 / 2) :
    Real.pi / 3 <= angleAt a b c := by
  unfold angleAt
  refine pi_div_three_le_angle_of_unit_inner_le_half
    (norm_toVec_vsub_eq_one_of_sqDist_eq_one hab)
    (norm_toVec_vsub_eq_one_of_sqDist_eq_one hcb) ?_
  rwa [inner_toVec_eq_dot]

lemma angleAt_eq_pi_div_three_of_unit_sides_dotAt_eq_half
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hdot : dotAt a b c = 1 / 2) :
    angleAt a b c = Real.pi / 3 := by
  unfold angleAt
  refine angle_eq_pi_div_three_of_unit_inner_eq_half
    (norm_toVec_vsub_eq_one_of_sqDist_eq_one hab)
    (norm_toVec_vsub_eq_one_of_sqDist_eq_one hcb) ?_
  rwa [inner_toVec_eq_dot]

/-- The distance form most often used in minimum-distance graphs: if the two
sides from `b` are unit and the base is at least unit squared-distance, then
the mathlib angle at `b` is at least `pi / 3`. -/
lemma pi_div_three_le_angleAt_of_unit_sides_sqDist_ge_one
    {a b c : Point} (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hbase : 1 <= sqDist a c) :
    Real.pi / 3 <= angleAt a b c :=
  pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half hab hcb
    (dotAt_le_half_of_unit_sides_sqDist_ge_one hab hcb hbase)

structure AngleAtPiDivThreePrereqs (a b c : Point) : Prop where
  left_sqDist_eq_one : sqDist a b = 1
  right_sqDist_eq_one : sqDist c b = 1
  dotAt_le_half : dotAt a b c <= 1 / 2

namespace AngleAtPiDivThreePrereqs

theorem angle_lower {a b c : Point}
    (H : AngleAtPiDivThreePrereqs a b c) :
    Real.pi / 3 <= angleAt a b c :=
  pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half
    H.left_sqDist_eq_one H.right_sqDist_eq_one H.dotAt_le_half

end AngleAtPiDivThreePrereqs

def AngleAtContainedIn (a b c : Point) (window : Real) : Prop :=
  angleAt a b c <= window

lemma pi_div_three_le_of_angleAt_containedIn
    {a b c : Point} {window : Real}
    (hangle : Real.pi / 3 <= angleAt a b c)
    (hcontained : AngleAtContainedIn a b c window) :
    Real.pi / 3 <= window :=
  le_trans hangle hcontained

lemma pi_div_three_le_window_of_unit_sides_dotAt_le_half
    {a b c : Point} {window : Real}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hdot : dotAt a b c <= 1 / 2)
    (hcontained : AngleAtContainedIn a b c window) :
    Real.pi / 3 <= window :=
  pi_div_three_le_of_angleAt_containedIn
    (pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half hab hcb hdot)
    hcontained

lemma pi_div_three_le_window_of_unit_sides_sqDist_ge_one
    {a b c : Point} {window : Real}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1)
    (hbase : 1 <= sqDist a c)
    (hcontained : AngleAtContainedIn a b c window) :
    Real.pi / 3 <= window :=
  pi_div_three_le_of_angleAt_containedIn
    (pi_div_three_le_angleAt_of_unit_sides_sqDist_ge_one hab hcb hbase)
    hcontained

/-- Equilateral unit triangles have mathlib angle exactly `pi / 3` at the
chosen vertex. -/
lemma angleAt_eq_pi_div_three_of_equilateral_unit
    {a b c : Point}
    (hab : sqDist a b = 1) (hcb : sqDist c b = 1) (hac : sqDist a c = 1) :
    angleAt a b c = Real.pi / 3 :=
  angleAt_eq_pi_div_three_of_unit_sides_dotAt_eq_half hab hcb
    (dotAt_eq_half_of_equilateral_unit hab hcb hac)

/-- Euclidean-distance-facing wrapper using `AngleBridgeFacts`: two unit edges
from `b` and a separated base force angle at least `pi / 3`. -/
lemma pi_div_three_le_angleAt_of_eucUnit_sides_eucSeparated_base
    {a b c : Point}
    (hab : AngleBridgeFacts.EucUnit a b)
    (hcb : AngleBridgeFacts.EucUnit c b)
    (hac : AngleBridgeFacts.EucSeparated a c) :
    Real.pi / 3 <= angleAt a b c :=
  pi_div_three_le_angleAt_of_unit_sides_dotAt_le_half
    (AngleBridgeFacts.sqDist_eq_one_of_eucUnit hab)
    (AngleBridgeFacts.sqDist_eq_one_of_eucUnit hcb)
    (AngleBridgeFacts.dotAt_le_half_of_eucUnit_sides_eucSeparated_base
      hab hcb hac)

lemma pi_div_three_le_window_of_eucUnit_sides_eucSeparated_base
    {a b c : Point} {window : Real}
    (hab : AngleBridgeFacts.EucUnit a b)
    (hcb : AngleBridgeFacts.EucUnit c b)
    (hac : AngleBridgeFacts.EucSeparated a c)
    (hcontained : AngleAtContainedIn a b c window) :
    Real.pi / 3 <= window :=
  pi_div_three_le_of_angleAt_containedIn
    (pi_div_three_le_angleAt_of_eucUnit_sides_eucSeparated_base
      hab hcb hac)
    hcontained

/-- Concrete check on the explicit equilateral triangle from
`TriangleAngleFacts`. -/
lemma angleAt_origin_of_concrete_equilateral :
    angleAt (1, 0) (0, 0) equilateralApex = Real.pi / 3 :=
  angleAt_eq_pi_div_three_of_equilateral_unit
    (by simpa [sqDist_comm] using sqDist_origin_unitBase_right)
    (by simpa [sqDist_comm] using sqDist_origin_equilateralApex)
    sqDist_unitBase_right_equilateralApex

end AngleGeometry
end Swanepoel
end ErdosProblems1066

end
