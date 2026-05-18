import ErdosProblems1066.PachToth.AffineLocalGeometry
import ErdosProblems1066.PachToth.CrossBlockGeometry
import ErdosProblems1066.PachToth.PlacementBridge

/-!
# Real Translation Obstruction for Pach--Toth Connectors

The grid-obstruction module proves that no integer triangular-grid offset
realizes all four directed connector edges.  This file strengthens that check:
even an arbitrary real translation of the exact local block cannot make all
four connector edges unit at once.

This matters because the paper's construction is explicitly non-rigid.  The
remaining global geometry must use a genuine deformed placement certificate,
not a translated-copy shortcut.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace RealTranslationObstruction

open FiniteGraph
open FiniteGraph.LocalVertex
open ExactLocalGeometry

abbrev R2 := Prod Real Real

theorem eucDist_relative_translate (a b : R2) (u v : LocalVertex) :
    Geometry.Distance.eucDist (localPoint u)
        (AffineLocalGeometry.translatedLocalPoint
          ((b.1 - a.1, b.2 - a.2) : R2) v) =
      _root_.eucDist
        (AffineLocalGeometry.translatedLocalPoint a u)
        (AffineLocalGeometry.translatedLocalPoint b v) := by
  simp [Geometry.Distance.eucDist, _root_.eucDist,
    AffineLocalGeometry.translatedLocalPoint,
    AffineLocalGeometry.translatePoint]
  congr 1
  ring

/-- The four connector equations for an arbitrary real translation are
inconsistent. -/
theorem no_real_offset_connector_equations (x y h : Real)
    (hh : h ^ 2 = (3 : Real) / 4) :
    ¬ ((2 * h - x) ^ 2 + (-y - 3) ^ 2 = 1 ∧
        (3 * h - x) ^ 2 + (-y - 5 / 2) ^ 2 = 1 ∧
        (4 * h - x) ^ 2 + (3 - y) ^ 2 = 1 ∧
        (5 * h - x) ^ 2 + (5 / 2 - y) ^ 2 = 1) := by
  intro hs
  rcases hs with ⟨h211, h212, h400, h402⟩
  nlinarith [hh, h211, h212, h400, h402]

/-- No arbitrary real translation of the next exact local block realizes all
four finite Pach--Toth connector edges as unit-distance edges. -/
theorem no_real_translation_realizes_all_connector_units (offset : R2) :
    ¬ (Geometry.Distance.eucDist (localPoint T2_2)
          (AffineLocalGeometry.translatedLocalPoint offset T1_1) = 1 ∧
        Geometry.Distance.eucDist (localPoint T2_2)
          (AffineLocalGeometry.translatedLocalPoint offset T1_2) = 1 ∧
        Geometry.Distance.eucDist (localPoint T4_0)
          (AffineLocalGeometry.translatedLocalPoint offset T0_0) = 1 ∧
        Geometry.Distance.eucDist (localPoint T4_0)
          (AffineLocalGeometry.translatedLocalPoint offset T0_2) = 1) := by
  intro hs
  rcases hs with ⟨h211, h212, h400, h402⟩
  rw [Geometry.Distance.eucDist_eq_one_iff] at h211 h212 h400 h402
  norm_num [AffineLocalGeometry.translatedLocalPoint,
    AffineLocalGeometry.translatePoint, localPoint, localGrid,
    GridPoint.toPoint, T2_2, T1_1, T1_2, T4_0, T0_0, T0_2, T] at h211 h212 h400 h402
  nlinarith [GridPoint.h_sq, h211, h212, h400, h402]

/-- The translated closed-chain specialization is impossible for the exact
local block model.  This theorem intentionally leaves the deformed placement
interfaces untouched: those are the right target for the paper's non-rigid
construction. -/
theorem no_translated_closed_chain_placement
    {k : Nat} {hk : 0 < k}
    (P : PlacementBridge.TranslatedClosedChainPlacement k hk) :
    False := by
  classical
  let i : Fin k := ⟨0, hk⟩
  let offset : R2 :=
    ((P.offset (Arithmetic.cyclicSucc hk i)).1 - (P.offset i).1,
      (P.offset (Arithmetic.cyclicSucc hk i)).2 - (P.offset i).2)
  have h211 :
      Geometry.Distance.eucDist (localPoint T2_2)
        (AffineLocalGeometry.translatedLocalPoint offset T1_1) = 1 := by
    have h := P.cross_connector_edges_unit i T2_2 T1_1 (by decide)
    simpa [offset] using
      (eucDist_relative_translate (P.offset i)
        (P.offset (Arithmetic.cyclicSucc hk i)) T2_2 T1_1).trans h
  have h212 :
      Geometry.Distance.eucDist (localPoint T2_2)
        (AffineLocalGeometry.translatedLocalPoint offset T1_2) = 1 := by
    have h := P.cross_connector_edges_unit i T2_2 T1_2 (by decide)
    simpa [offset] using
      (eucDist_relative_translate (P.offset i)
        (P.offset (Arithmetic.cyclicSucc hk i)) T2_2 T1_2).trans h
  have h400 :
      Geometry.Distance.eucDist (localPoint T4_0)
        (AffineLocalGeometry.translatedLocalPoint offset T0_0) = 1 := by
    have h := P.cross_connector_edges_unit i T4_0 T0_0 (by decide)
    simpa [offset] using
      (eucDist_relative_translate (P.offset i)
        (P.offset (Arithmetic.cyclicSucc hk i)) T4_0 T0_0).trans h
  have h402 :
      Geometry.Distance.eucDist (localPoint T4_0)
        (AffineLocalGeometry.translatedLocalPoint offset T0_2) = 1 := by
    have h := P.cross_connector_edges_unit i T4_0 T0_2 (by decide)
    simpa [offset] using
      (eucDist_relative_translate (P.offset i)
        (P.offset (Arithmetic.cyclicSucc hk i)) T4_0 T0_2).trans h
  exact no_real_translation_realizes_all_connector_units offset
    ⟨h211, h212, h400, h402⟩

end RealTranslationObstruction
end PachToth
end ErdosProblems1066

end
