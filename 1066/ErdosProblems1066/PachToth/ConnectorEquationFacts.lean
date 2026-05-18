import ErdosProblems1066.PachToth.AffineLocalGeometry

/-!
# Pach--Toth Connector Equation Facts

Small algebraic facts about the four real translation equations for the
Pach--Toth connector edges.  The statements are separated from the translated
chain obstruction so later deformation work can reuse the linear consequences
and the smaller inconsistent triples directly.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace ConnectorEquationFacts

open FiniteGraph.LocalVertex
open ExactLocalGeometry

abbrev R2 := Prod Real Real

/-- The equation for `T2_2 -> T1_1` under a real offset `(x,y)`. -/
def eq211 (x y eta : Real) : Prop :=
  (2 * eta - x) ^ 2 + (-y - 3) ^ 2 = 1

/-- The equation for `T2_2 -> T1_2` under a real offset `(x,y)`. -/
def eq212 (x y eta : Real) : Prop :=
  (3 * eta - x) ^ 2 + (-y - 5 / 2) ^ 2 = 1

/-- The equation for `T4_0 -> T0_0` under a real offset `(x,y)`. -/
def eq400 (x y eta : Real) : Prop :=
  (4 * eta - x) ^ 2 + (3 - y) ^ 2 = 1

/-- The equation for `T4_0 -> T0_2` under a real offset `(x,y)`. -/
def eq402 (x y eta : Real) : Prop :=
  (5 * eta - x) ^ 2 + (5 / 2 - y) ^ 2 = 1

theorem distSq_T2_2_translated_T1_1 (offset : R2) :
    AffineLocalGeometry.distSq (localPoint T2_2)
        (AffineLocalGeometry.translatedLocalPoint offset T1_1) =
      (2 * h - offset.1) ^ 2 + (-offset.2 - 3) ^ 2 := by
  norm_num [AffineLocalGeometry.distSq, AffineLocalGeometry.translatedLocalPoint,
    AffineLocalGeometry.translatePoint, localPoint, localGrid, GridPoint.toPoint, h,
    T2_2, T1_1, T]
  ring

theorem distSq_T2_2_translated_T1_2 (offset : R2) :
    AffineLocalGeometry.distSq (localPoint T2_2)
        (AffineLocalGeometry.translatedLocalPoint offset T1_2) =
      (3 * h - offset.1) ^ 2 + (-offset.2 - 5 / 2) ^ 2 := by
  norm_num [AffineLocalGeometry.distSq, AffineLocalGeometry.translatedLocalPoint,
    AffineLocalGeometry.translatePoint, localPoint, localGrid, GridPoint.toPoint, h,
    T2_2, T1_2, T]
  ring

theorem distSq_T4_0_translated_T0_0 (offset : R2) :
    AffineLocalGeometry.distSq (localPoint T4_0)
        (AffineLocalGeometry.translatedLocalPoint offset T0_0) =
      (4 * h - offset.1) ^ 2 + (3 - offset.2) ^ 2 := by
  norm_num [AffineLocalGeometry.distSq, AffineLocalGeometry.translatedLocalPoint,
    AffineLocalGeometry.translatePoint, localPoint, localGrid, GridPoint.toPoint, h,
    T4_0, T0_0, T]
  ring

theorem distSq_T4_0_translated_T0_2 (offset : R2) :
    AffineLocalGeometry.distSq (localPoint T4_0)
        (AffineLocalGeometry.translatedLocalPoint offset T0_2) =
      (5 * h - offset.1) ^ 2 + (5 / 2 - offset.2) ^ 2 := by
  norm_num [AffineLocalGeometry.distSq, AffineLocalGeometry.translatedLocalPoint,
    AffineLocalGeometry.translatePoint, localPoint, localGrid, GridPoint.toPoint, h,
    T4_0, T0_2, T]
  ring

/-- The two connector equations out of `T2_2` force a line. -/
theorem eq211_eq212_linear {x y eta : Real}
    (heta : eta ^ 2 = (3 : Real) / 4)
    (h211 : eq211 x y eta) (h212 : eq212 x y eta) :
    2 * x * eta + y = 1 := by
  unfold eq211 at h211
  unfold eq212 at h212
  nlinarith

/-- The two connector equations out of `T4_0` force a line. -/
theorem eq400_eq402_linear {x y eta : Real}
    (heta : eta ^ 2 = (3 : Real) / 4)
    (h400 : eq400 x y eta) (h402 : eq402 x y eta) :
    2 * x * eta - y = 4 := by
  unfold eq400 at h400
  unfold eq402 at h402
  nlinarith

theorem eq211_eq212_eq400_false {x y eta : Real}
    (heta : eta ^ 2 = (3 : Real) / 4)
    (h211 : eq211 x y eta) (h212 : eq212 x y eta) (h400 : eq400 x y eta) :
    False := by
  have hline := eq211_eq212_linear heta h211 h212
  unfold eq400 at h400
  have hy : y = 1 - 2 * x * eta := by
    nlinarith
  subst y
  nlinarith [sq_nonneg x]

theorem eq211_eq212_eq402_false {x y eta : Real}
    (heta : eta ^ 2 = (3 : Real) / 4)
    (h211 : eq211 x y eta) (h212 : eq212 x y eta) (h402 : eq402 x y eta) :
    False := by
  have hline := eq211_eq212_linear heta h211 h212
  unfold eq402 at h402
  have hy : y = 1 - 2 * x * eta := by
    nlinarith
  subst y
  nlinarith [sq_nonneg (2 * x - eta)]

/-- The `T4_0` pair together with `T2_2 -> T1_1` pins down the offset. -/
theorem eq400_eq402_eq211_force_x {x y eta : Real}
    (heta : eta ^ 2 = (3 : Real) / 4)
    (h400 : eq400 x y eta) (h402 : eq402 x y eta) (h211 : eq211 x y eta) :
    x = eta := by
  have hline := eq400_eq402_linear heta h400 h402
  unfold eq211 at h211
  have hy : y = 2 * x * eta - 4 := by
    nlinarith
  subst y
  nlinarith [sq_nonneg (x - eta)]

/-- The `T4_0` pair together with `T2_2 -> T1_1` pins down the vertical offset. -/
theorem eq400_eq402_eq211_force_y {x y eta : Real}
    (heta : eta ^ 2 = (3 : Real) / 4)
    (h400 : eq400 x y eta) (h402 : eq402 x y eta) (h211 : eq211 x y eta) :
    y = -5 / 2 := by
  have hx := eq400_eq402_eq211_force_x heta h400 h402 h211
  have hline := eq400_eq402_linear heta h400 h402
  rw [hx] at hline
  nlinarith

theorem eq400_eq402_eq212_false {x y eta : Real}
    (heta : eta ^ 2 = (3 : Real) / 4)
    (h400 : eq400 x y eta) (h402 : eq402 x y eta) (h212 : eq212 x y eta) :
    False := by
  have hline := eq400_eq402_linear heta h400 h402
  unfold eq212 at h212
  have hy : y = 2 * x * eta - 4 := by
    nlinarith
  subst y
  nlinarith [sq_nonneg (2 * x - 3 * eta)]

theorem not_eq211_eq212_eq400 (x y eta : Real)
    (heta : eta ^ 2 = (3 : Real) / 4) :
    Not (eq211 x y eta /\ eq212 x y eta /\ eq400 x y eta) := by
  rintro ⟨h211, h212, h400⟩
  exact eq211_eq212_eq400_false heta h211 h212 h400

theorem not_eq211_eq212_eq402 (x y eta : Real)
    (heta : eta ^ 2 = (3 : Real) / 4) :
    Not (eq211 x y eta /\ eq212 x y eta /\ eq402 x y eta) := by
  rintro ⟨h211, h212, h402⟩
  exact eq211_eq212_eq402_false heta h211 h212 h402

theorem not_eq400_eq402_eq212 (x y eta : Real)
    (heta : eta ^ 2 = (3 : Real) / 4) :
    Not (eq400 x y eta /\ eq402 x y eta /\ eq212 x y eta) := by
  rintro ⟨h400, h402, h212⟩
  exact eq400_eq402_eq212_false heta h400 h402 h212

/-- If both source-pairs held, the offset would have a fixed projection. -/
theorem both_pairs_force_x_mul_height {x y eta : Real}
    (heta : eta ^ 2 = (3 : Real) / 4)
    (h211 : eq211 x y eta) (h212 : eq212 x y eta)
    (h400 : eq400 x y eta) (h402 : eq402 x y eta) :
    x * eta = 5 / 4 := by
  have hleft := eq211_eq212_linear heta h211 h212
  have hright := eq400_eq402_linear heta h400 h402
  nlinarith

/-- If both source-pairs held, the vertical offset would be fixed. -/
theorem both_pairs_force_y {x y eta : Real}
    (heta : eta ^ 2 = (3 : Real) / 4)
    (h211 : eq211 x y eta) (h212 : eq212 x y eta)
    (h400 : eq400 x y eta) (h402 : eq402 x y eta) :
    y = -3 / 2 := by
  have hleft := eq211_eq212_linear heta h211 h212
  have hright := eq400_eq402_linear heta h400 h402
  nlinarith

theorem not_all_four_connector_equations (x y eta : Real)
    (heta : eta ^ 2 = (3 : Real) / 4) :
    Not (eq211 x y eta /\ eq212 x y eta /\ eq400 x y eta /\ eq402 x y eta) := by
  rintro ⟨h211, h212, h400, _h402⟩
  exact eq211_eq212_eq400_false heta h211 h212 h400

end ConnectorEquationFacts
end PachToth
end ErdosProblems1066

end
