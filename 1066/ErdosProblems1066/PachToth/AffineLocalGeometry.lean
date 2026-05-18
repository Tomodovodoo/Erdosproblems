import ErdosProblems1066.PachToth.ExactLocalGeometry
import ErdosProblems1066.UnitDistanceBounds

/-!
# Affine transport for Pach--Toth local geometry

Translation lemmas for the point-level geometry used to move exact local
Pach--Toth blocks into global positions without changing unit distances or
minimum separation.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace AffineLocalGeometry

open FiniteGraph
open ExactLocalGeometry

/-- Points in the Euclidean plane. -/
abbrev Point : Type := Real × Real

/-- Squared Euclidean distance, without the square root. -/
def distSq (p q : Point) : Real :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Translate a point by an offset vector. -/
def translatePoint (offset p : Point) : Point :=
  (p.1 + offset.1, p.2 + offset.2)

/-- Unit-distance predicate for explicit points. -/
def unitDistance (p q : Point) : Prop :=
  Geometry.Distance.eucDist p q = 1

/-- Minimum-separation predicate for explicit points. -/
def separated (p q : Point) : Prop :=
  1 <= Geometry.Distance.eucDist p q

@[simp]
theorem distSq_self (p : Point) : distSq p p = 0 := by
  simp [distSq]

theorem distSq_comm (p q : Point) : distSq p q = distSq q p := by
  simp [distSq]
  ring

theorem eucDist_eq_root_eucDist (p q : Point) :
    Geometry.Distance.eucDist p q = _root_.eucDist p q := by
  rfl

theorem distSq_eq_eucDist_sq (p q : Point) :
    distSq p q = Geometry.Distance.eucDist p q ^ 2 := by
  rw [Geometry.Distance.eucDist_sq]
  rfl

@[simp]
theorem translate_fst (offset p : Point) :
    (translatePoint offset p).1 = p.1 + offset.1 := rfl

@[simp]
theorem translate_snd (offset p : Point) :
    (translatePoint offset p).2 = p.2 + offset.2 := rfl

/-- Translating both endpoints preserves squared distance. -/
@[simp]
theorem distSq_translate_translate (offset p q : Point) :
    distSq (translatePoint offset p) (translatePoint offset q) = distSq p q := by
  unfold distSq translatePoint
  ring

/-- Translating both endpoints preserves Euclidean distance. -/
@[simp]
theorem dist_translate_translate (offset p q : Point) :
    Geometry.Distance.eucDist (translatePoint offset p) (translatePoint offset q) =
      Geometry.Distance.eucDist p q := by
  unfold Geometry.Distance.eucDist translatePoint
  congr 1
  ring

/-- Translating both endpoints preserves the legacy root Euclidean distance. -/
@[simp]
theorem root_dist_translate_translate (offset p q : Point) :
    _root_.eucDist (translatePoint offset p) (translatePoint offset q) = _root_.eucDist p q := by
  unfold _root_.eucDist translatePoint
  congr 1
  ring

/-- Translating both endpoints preserves unit-distance facts. -/
theorem unitDistance_translate (offset p q : Point) :
    unitDistance (translatePoint offset p) (translatePoint offset q) <-> unitDistance p q := by
  simp [unitDistance]

/-- Root-distance version of `unitDistance_translate`, for `UDConfig` callers. -/
theorem root_unitDistance_translate (offset p q : Point) :
    _root_.eucDist (translatePoint offset p) (translatePoint offset q) = 1 <->
      _root_.eucDist p q = 1 := by
  simp

/-- Translating both endpoints preserves separation facts. -/
theorem separated_translate (offset p q : Point) :
    separated (translatePoint offset p) (translatePoint offset q) <-> separated p q := by
  simp [separated]

/-- Root-distance version of `separated_translate`, for `UDConfig` callers. -/
theorem root_separated_translate (offset p q : Point) :
    1 <= _root_.eucDist (translatePoint offset p) (translatePoint offset q) <->
      1 <= _root_.eucDist p q := by
  simp

/-- A `UDConfig` translated by a fixed offset. -/
def UDConfig.translate {n : Nat} (offset : Point) (C : _root_.UDConfig n) :
    _root_.UDConfig n where
  pts := fun i => translatePoint offset (C.pts i)
  sep := by
    intro i j hij
    simpa only [root_dist_translate_translate] using C.sep i j hij

@[simp]
theorem UDConfig.translate_pts {n : Nat} (offset : Point) (C : _root_.UDConfig n)
    (i : Fin n) :
    (UDConfig.translate offset C).pts i = translatePoint offset (C.pts i) :=
  rfl

/-- Translating a configuration preserves unit-distance adjacency. -/
theorem UDConfig.unitDistance_translate {n : Nat} (offset : Point)
    (C : _root_.UDConfig n) (i j : Fin n) :
    _root_.eucDist ((UDConfig.translate offset C).pts i)
        ((UDConfig.translate offset C).pts j) = 1 <->
      _root_.eucDist (C.pts i) (C.pts j) = 1 := by
  simp [UDConfig.translate]

/-- Translating a configuration preserves separation between explicit labels. -/
theorem UDConfig.separated_translate {n : Nat} (offset : Point)
    (C : _root_.UDConfig n) (i j : Fin n) :
    1 <= _root_.eucDist ((UDConfig.translate offset C).pts i)
        ((UDConfig.translate offset C).pts j) <->
      1 <= _root_.eucDist (C.pts i) (C.pts j) := by
  simp [UDConfig.translate]

/-- Translating a configuration preserves independent sets. -/
theorem UDConfig.isIndep_translate {n : Nat} (offset : Point)
    (C : _root_.UDConfig n) (s : Finset (Fin n)) :
    (UDConfig.translate offset C).IsIndep s <-> C.IsIndep s := by
  simp [UDConfig.IsIndep]

/-- The exact local point translated by a block offset. -/
def translatedLocalPoint (offset : Point) (v : LocalVertex) : Point :=
  translatePoint offset (localPoint v)

/-- Same-block exact finite edges remain unit edges after translation. -/
theorem translatedLocal_adj_unit_distance (offset : Point) :
    forall u v : LocalVertex, adj u v = true ->
      Geometry.Distance.eucDist
        (translatedLocalPoint offset u) (translatedLocalPoint offset v) = 1 := by
  intro u v huv
  simpa [translatedLocalPoint, unitDistance] using
    (unitDistance_translate offset (localPoint u) (localPoint v)).2
      (adj_unit_distance u v huv)

/-- Root-distance version of `translatedLocal_adj_unit_distance`. -/
theorem translatedLocal_root_adj_unit_distance (offset : Point) :
    forall u v : LocalVertex, adj u v = true ->
      _root_.eucDist
        (translatedLocalPoint offset u) (translatedLocalPoint offset v) = 1 := by
  intro u v huv
  simpa [eucDist_eq_root_eucDist] using
    translatedLocal_adj_unit_distance offset u v huv

/-- Distinct exact local vertices remain separated after translation. -/
theorem translatedLocal_separated (offset : Point) :
    forall u v : LocalVertex, u ≠ v ->
      1 <= Geometry.Distance.eucDist
        (translatedLocalPoint offset u) (translatedLocalPoint offset v) := by
  intro u v huv
  simpa [translatedLocalPoint, separated] using
    (separated_translate offset (localPoint u) (localPoint v)).2
      (local_separated u v huv)

/-- Root-distance version of `translatedLocal_separated`. -/
theorem translatedLocal_root_separated (offset : Point) :
    forall u v : LocalVertex, u ≠ v ->
      1 <= _root_.eucDist
        (translatedLocalPoint offset u) (translatedLocalPoint offset v) := by
  intro u v huv
  simpa [eucDist_eq_root_eucDist] using
    translatedLocal_separated offset u v huv

end AffineLocalGeometry
end PachToth
end ErdosProblems1066

end
