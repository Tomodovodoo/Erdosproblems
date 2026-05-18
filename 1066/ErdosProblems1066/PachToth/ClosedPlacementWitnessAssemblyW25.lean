import ErdosProblems1066.PachToth.FullMetricClosedPlacementW24
import ErdosProblems1066.PachToth.FreePlacementSourceFieldsW24

set_option autoImplicit false

/-!
# W25 closed-placement witness assembly

This file assembles the W24 full/free/reduced closed-placement witness
interfaces into one hierarchy.  The constructive spine is:

* full generated metric witness -> closed placements -> free placement fields
  -> explicit edge soundness;
* reduced generated metric witness -> closed placements -> free placement
  fields -> explicit edge soundness;
* free placement fields <-> families of `DeformedPlacement.ClosedPlacement`.

The reverse from `ExplicitEdgeSoundness` to closed/free placement data is not
constructive in the current interface: edge soundness remembers only the global
configuration and edge equations, while `ClosedPlacement` also packages a
block-local point map and global separation proof for that map.  Likewise,
free closed-placement data does not reconstruct the generated family, closure
equations, or generated metric fields required by the full/reduced witnesses.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementWitnessAssemblyW25

open FiniteGraph

noncomputable section

abbrev FullMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.FullMetricClosedPlacementWitness

abbrev ReducedMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness

abbrev MinimalFreePlacementFields : Type :=
  FreePlacementSourceFieldsW24.MinimalFreePlacementFields

abbrev ClosedPlacementFamily : Type :=
  forall (k : Nat) (hk : 0 < k), DeformedPlacement.ClosedPlacement k hk

abbrev ExplicitEdgeSoundnessFamily : Type :=
  forall (k : Nat) (hk : 0 < k),
    GeometricSoundness.ExplicitEdgeSoundness k hk

/-! ## Constructive conversions -/

def closedPlacementFamilyOfFullMetricWitness
    (W : FullMetricClosedPlacementWitness) :
    ClosedPlacementFamily :=
  W.closedPlacementFamily

def closedPlacementFamilyOfReducedMetricWitness
    (W : ReducedMetricClosedPlacementWitness) :
    ClosedPlacementFamily :=
  W.closedPlacementFamily

def closedPlacementFamilyOfMinimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    ClosedPlacementFamily :=
  S.toClosedPlacement

def minimalFreePlacementFieldsOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    MinimalFreePlacementFields :=
  FreePlacementSourceFieldsW24.ofClosedPlacements H

def minimalFreePlacementFieldsOfFullMetricWitness
    (W : FullMetricClosedPlacementWitness) :
    MinimalFreePlacementFields :=
  minimalFreePlacementFieldsOfClosedPlacementFamily
    (closedPlacementFamilyOfFullMetricWitness W)

def minimalFreePlacementFieldsOfReducedMetricWitness
    (W : ReducedMetricClosedPlacementWitness) :
    MinimalFreePlacementFields :=
  minimalFreePlacementFieldsOfClosedPlacementFamily
    (closedPlacementFamilyOfReducedMetricWitness W)

def explicitEdgeSoundnessFamilyOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    ExplicitEdgeSoundnessFamily :=
  fun k hk => (H k hk).toExplicitEdgeSoundness

def explicitEdgeSoundnessFamilyOfMinimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    ExplicitEdgeSoundnessFamily :=
  fun k hk => S.toExplicitEdgeSoundness k hk

def explicitEdgeSoundnessFamilyOfFullMetricWitness
    (W : FullMetricClosedPlacementWitness) :
    ExplicitEdgeSoundnessFamily :=
  W.explicitEdgeSoundnessFamily

def explicitEdgeSoundnessFamilyOfReducedMetricWitness
    (W : ReducedMetricClosedPlacementWitness) :
    ExplicitEdgeSoundnessFamily :=
  W.explicitEdgeSoundnessFamily

@[simp]
theorem closedPlacementFamilyOfFullMetricWitness_point
    (W : FullMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (closedPlacementFamilyOfFullMetricWitness W k hk).point i v =
      GeneratedClosedChain.generatedPoint (W.family.O k hk) hk
        (W.family.base k hk) (W.family.orientation k hk) i v :=
  rfl

@[simp]
theorem closedPlacementFamilyOfReducedMetricWitness_point
    (W : ReducedMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (closedPlacementFamilyOfReducedMetricWitness W k hk).point i v =
      GeneratedClosedChain.generatedPoint (W.family.O k hk) hk
        (W.family.base k hk) (W.family.orientation k hk) i v :=
  rfl

@[simp]
theorem closedPlacementFamilyOfMinimalFreePlacementFields_point
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (closedPlacementFamilyOfMinimalFreePlacementFields S k hk).point i v =
      S.point k hk i v :=
  rfl

@[simp]
theorem minimalFreePlacementFieldsOfClosedPlacementFamily_point
    (H : ClosedPlacementFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (minimalFreePlacementFieldsOfClosedPlacementFamily H).point k hk i v =
      (H k hk).point i v :=
  rfl

@[simp]
theorem minimalFreePlacementFieldsOfFullMetricWitness_point
    (W : FullMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (minimalFreePlacementFieldsOfFullMetricWitness W).point k hk i v =
      GeneratedClosedChain.generatedPoint (W.family.O k hk) hk
        (W.family.base k hk) (W.family.orientation k hk) i v :=
  rfl

@[simp]
theorem minimalFreePlacementFieldsOfReducedMetricWitness_point
    (W : ReducedMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (minimalFreePlacementFieldsOfReducedMetricWitness W).point k hk i v =
      GeneratedClosedChain.generatedPoint (W.family.O k hk) hk
        (W.family.base k hk) (W.family.orientation k hk) i v :=
  rfl

/-! ## Exact reversible layer -/

theorem minimalFreePlacementFields_nonempty_iff_closedPlacementFamily_nonempty :
    Nonempty MinimalFreePlacementFields ↔ Nonempty ClosedPlacementFamily := by
  constructor
  · intro h
    rcases h with ⟨S⟩
    exact ⟨closedPlacementFamilyOfMinimalFreePlacementFields S⟩
  · intro h
    rcases h with ⟨H⟩
    exact ⟨minimalFreePlacementFieldsOfClosedPlacementFamily H⟩

theorem closedPlacementFamily_nonempty_iff_minimalFreePlacementFields_nonempty :
    Nonempty ClosedPlacementFamily ↔ Nonempty MinimalFreePlacementFields :=
  minimalFreePlacementFields_nonempty_iff_closedPlacementFamily_nonempty.symm

theorem closedPlacementFamily_roundTrip_point
    (H : ClosedPlacementFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (closedPlacementFamilyOfMinimalFreePlacementFields
      (minimalFreePlacementFieldsOfClosedPlacementFamily H) k hk).point i v =
        (H k hk).point i v :=
  rfl

theorem minimalFreePlacementFields_roundTrip_point
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (minimalFreePlacementFieldsOfClosedPlacementFamily
      (closedPlacementFamilyOfMinimalFreePlacementFields S)).point k hk i v =
        S.point k hk i v :=
  rfl

/-! ## One-way downstream layer -/

theorem explicitEdgeSoundnessFamily_nonempty_of_closedPlacementFamily_nonempty :
    Nonempty ClosedPlacementFamily -> Nonempty ExplicitEdgeSoundnessFamily := by
  intro h
  rcases h with ⟨H⟩
  exact ⟨explicitEdgeSoundnessFamilyOfClosedPlacementFamily H⟩

theorem explicitEdgeSoundnessFamily_nonempty_of_minimalFreePlacementFields_nonempty :
    Nonempty MinimalFreePlacementFields -> Nonempty ExplicitEdgeSoundnessFamily := by
  intro h
  exact
    explicitEdgeSoundnessFamily_nonempty_of_closedPlacementFamily_nonempty
      (minimalFreePlacementFields_nonempty_iff_closedPlacementFamily_nonempty.mp h)

theorem minimalFreePlacementFields_nonempty_of_fullMetricWitness_nonempty :
    Nonempty FullMetricClosedPlacementWitness ->
      Nonempty MinimalFreePlacementFields := by
  intro h
  rcases h with ⟨W⟩
  exact ⟨minimalFreePlacementFieldsOfFullMetricWitness W⟩

theorem minimalFreePlacementFields_nonempty_of_reducedMetricWitness_nonempty :
    Nonempty ReducedMetricClosedPlacementWitness ->
      Nonempty MinimalFreePlacementFields := by
  intro h
  rcases h with ⟨W⟩
  exact ⟨minimalFreePlacementFieldsOfReducedMetricWitness W⟩

theorem closedPlacementFamily_nonempty_of_fullMetricWitness_nonempty :
    Nonempty FullMetricClosedPlacementWitness -> Nonempty ClosedPlacementFamily := by
  intro h
  rcases h with ⟨W⟩
  exact ⟨closedPlacementFamilyOfFullMetricWitness W⟩

theorem closedPlacementFamily_nonempty_of_reducedMetricWitness_nonempty :
    Nonempty ReducedMetricClosedPlacementWitness ->
      Nonempty ClosedPlacementFamily := by
  intro h
  rcases h with ⟨W⟩
  exact ⟨closedPlacementFamilyOfReducedMetricWitness W⟩

theorem explicitEdgeSoundnessFamily_nonempty_of_fullMetricWitness_nonempty :
    Nonempty FullMetricClosedPlacementWitness ->
      Nonempty ExplicitEdgeSoundnessFamily := by
  intro h
  rcases h with ⟨W⟩
  exact ⟨explicitEdgeSoundnessFamilyOfFullMetricWitness W⟩

theorem explicitEdgeSoundnessFamily_nonempty_of_reducedMetricWitness_nonempty :
    Nonempty ReducedMetricClosedPlacementWitness ->
      Nonempty ExplicitEdgeSoundnessFamily := by
  intro h
  rcases h with ⟨W⟩
  exact ⟨explicitEdgeSoundnessFamilyOfReducedMetricWitness W⟩

/-! ## Target reductions from each assembled surface -/

theorem exactTarget_of_closedPlacementFamily
    (H : ClosedPlacementFamily) :
    targetUpperConstructionFiveSixteen :=
  DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements H

theorem exactTarget_of_explicitEdgeSoundnessFamily
    (H : ExplicitEdgeSoundnessFamily) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_explicitEdgeSoundness H

theorem exactTarget_of_minimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    targetUpperConstructionFiveSixteen :=
  FreePlacementSourceFieldsW24.targetUpperConstructionFiveSixteen_of_freePlacementSourceFields
    S

theorem exactTarget_of_fullMetricWitness
    (W : FullMetricClosedPlacementWitness) :
    targetUpperConstructionFiveSixteen :=
  W.targetUpperConstructionFiveSixteen

theorem exactTarget_of_reducedMetricWitness
    (W : ReducedMetricClosedPlacementWitness) :
    targetUpperConstructionFiveSixteen :=
  W.targetUpperConstructionFiveSixteen

/-! ## Missing constructive reverse directions -/

/-- Missing: an edge-soundness family alone does not expose the block-local
point map and separation proof required by `ClosedPlacementFamily`. -/
abbrev MissingExplicitEdgeSoundnessToClosedPlacementFamily : Type :=
  ExplicitEdgeSoundnessFamily -> ClosedPlacementFamily

/-- Missing for the same reason as
`MissingExplicitEdgeSoundnessToClosedPlacementFamily`. -/
abbrev MissingExplicitEdgeSoundnessToMinimalFreePlacementFields : Type :=
  ExplicitEdgeSoundnessFamily -> MinimalFreePlacementFields

/-- Missing: free placement fields forget the generated chain family, closure
equations, and reduced metric package. -/
abbrev MissingMinimalFreePlacementFieldsToReducedMetricWitness : Type :=
  MinimalFreePlacementFields -> ReducedMetricClosedPlacementWitness

/-- Missing: free placement fields forget the generated chain family, closure
equations, and full metric package. -/
abbrev MissingMinimalFreePlacementFieldsToFullMetricWitness : Type :=
  MinimalFreePlacementFields -> FullMetricClosedPlacementWitness

/-- Missing: the reduced witness does not include the full same-block isometry
field expected by the full-metric witness. -/
abbrev MissingReducedMetricWitnessToFullMetricWitness : Type :=
  ReducedMetricClosedPlacementWitness -> FullMetricClosedPlacementWitness

/-- Missing: the full witness does not include the base-isometry and transition
same-block-distance preservation fields expected by the reduced witness. -/
abbrev MissingFullMetricWitnessToReducedMetricWitness : Type :=
  FullMetricClosedPlacementWitness -> ReducedMetricClosedPlacementWitness

end

end ClosedPlacementWitnessAssemblyW25
end PachToth
end ErdosProblems1066
