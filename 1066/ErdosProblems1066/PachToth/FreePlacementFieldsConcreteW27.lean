import ErdosProblems1066.PachToth.ClosedPlacementConcreteConstructionW26
import ErdosProblems1066.PachToth.DirectReducedMetricInputW26
import ErdosProblems1066.PachToth.FullToReducedMetricClosureW26
import ErdosProblems1066.PachToth.NonRoleSplitSourceConstructionW26

set_option autoImplicit false

/-!
# W27 concrete free-placement fields

This worker keeps the free-placement lane source-faithful.  It constructs
actual `FreePlacementSourceFieldsW24.MinimalFreePlacementFields` from every
currently available closed-placement component surface, including the W26
concrete lower-table handoffs.  It also records the honest remaining boundary:
successor orbit closure is exactly the extra datum needed to upgrade minimal
free-placement fields to the W26 concrete closed-orbit package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FreePlacementFieldsConcreteW27

open FiniteGraph

noncomputable section

abbrev MinimalFreePlacementFields : Type :=
  FreePlacementSourceFieldsW24.MinimalFreePlacementFields

abbrev W19RawClosedPlacementFamilyFields : Type :=
  NonRigidClosedPlacementDataW19.RawClosedPlacementFamilyFields

abbrev W19ComponentFamily : Type :=
  NonRigidClosedPlacementDataW19.ComponentFamily

abbrev W19ExplicitClosedPlacementCertificateFamily : Type :=
  NonRigidClosedPlacementDataW19.ExplicitClosedPlacementCertificateFamily

abbrev ClosedPlacementFamily : Type :=
  ClosedPlacementWitnessAssemblyW25.ClosedPlacementFamily

abbrev W10ClosedPlacementPackage : Type :=
  ArbitraryNBridgeW10.ClosedPlacementPackage

abbrev FullMetricClosedPlacementWitness : Type :=
  ClosedPlacementWitnessAssemblyW25.FullMetricClosedPlacementWitness

abbrev ReducedMetricClosedPlacementWitness : Type :=
  ClosedPlacementWitnessAssemblyW25.ReducedMetricClosedPlacementWitness

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  DirectReducedMetricInputW26.ConcreteNonConnectorLowerTableFamily

abbrev DirectFullMetricSourcePackage : Type :=
  DirectFullMetricSourceInhabitationW25.DirectFullMetricSourcePackage

abbrev W20SourceFields : Type :=
  DirectReducedMetricInputW26.W20SourceFields

abbrev W19InputPackage : Type :=
  DirectReducedMetricInputW26.W19InputPackage

abbrev ConcreteClosedOrbitFamily : Type :=
  ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily

abbrev MinimalFieldsWithOrbitClosure : Type :=
  ClosedPlacementConcreteConstructionW26.MinimalFieldsWithOrbitClosure

/-! ## Direct closed-placement component constructors -/

def minimalFreePlacementFieldsOfW19RawFields
    (F : W19RawClosedPlacementFamilyFields) :
    MinimalFreePlacementFields :=
  FreePlacementSourceFieldsW24.ofRawClosedPlacementFamilyFields F

def minimalFreePlacementFieldsOfW19ComponentFamily
    (F : W19ComponentFamily) :
    MinimalFreePlacementFields :=
  FreePlacementSourceFieldsW24.ofComponentFamily F

def closedPlacementFamilyOfW19Certificates
    (C : W19ExplicitClosedPlacementCertificateFamily) :
    ClosedPlacementFamily :=
  NonRigidClosedPlacementDataW19.closedPlacementFamilyOfCertificates C

def minimalFreePlacementFieldsOfW19Certificates
    (C : W19ExplicitClosedPlacementCertificateFamily) :
    MinimalFreePlacementFields :=
  FreePlacementSourceFieldsW24.ofClosedPlacements
    (closedPlacementFamilyOfW19Certificates C)

def minimalFreePlacementFieldsOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    MinimalFreePlacementFields :=
  ClosedPlacementWitnessAssemblyW25.minimalFreePlacementFieldsOfClosedPlacementFamily
    H

def minimalFreePlacementFieldsOfW10ClosedPlacementPackage
    (P : W10ClosedPlacementPackage) :
    MinimalFreePlacementFields :=
  minimalFreePlacementFieldsOfClosedPlacementFamily P.placement

def minimalFreePlacementFieldsOfFullMetricWitness
    (W : FullMetricClosedPlacementWitness) :
    MinimalFreePlacementFields :=
  ClosedPlacementWitnessAssemblyW25.minimalFreePlacementFieldsOfFullMetricWitness
    W

def minimalFreePlacementFieldsOfReducedMetricWitness
    (W : ReducedMetricClosedPlacementWitness) :
    MinimalFreePlacementFields :=
  ClosedPlacementWitnessAssemblyW25.minimalFreePlacementFieldsOfReducedMetricWitness
    W

@[simp]
theorem minimalFreePlacementFieldsOfW19RawFields_point
    (F : W19RawClosedPlacementFamilyFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (minimalFreePlacementFieldsOfW19RawFields F).point k hk i v =
      F.point k hk i v :=
  rfl

@[simp]
theorem minimalFreePlacementFieldsOfW19ComponentFamily_point
    (F : W19ComponentFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (minimalFreePlacementFieldsOfW19ComponentFamily F).point k hk i v =
      (F.components k hk).point i v :=
  rfl

@[simp]
theorem minimalFreePlacementFieldsOfW19Certificates_point
    (C : W19ExplicitClosedPlacementCertificateFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (minimalFreePlacementFieldsOfW19Certificates C).point k hk i v =
      (C k hk).point i v :=
  rfl

@[simp]
theorem minimalFreePlacementFieldsOfClosedPlacementFamily_point
    (H : ClosedPlacementFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (minimalFreePlacementFieldsOfClosedPlacementFamily H).point k hk i v =
      (H k hk).point i v :=
  rfl

/-! ## W26 concrete lower-table constructors -/

def w20SourceFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    W20SourceFields :=
  DirectReducedMetricInputW26.w20SourceFieldsOfConcreteLowerTables C

def w19InputPackageOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    W19InputPackage :=
  DirectReducedMetricInputW26.w19InputPackageOfConcreteLowerTables C

def reducedMetricWitnessOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ReducedMetricClosedPlacementWitness :=
  FullToReducedMetricClosureW26.reducedMetricClosedPlacementWitnessOfConcreteLowerTables
    C

def fullMetricWitnessOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    FullMetricClosedPlacementWitness :=
  DirectFullMetricSourceInhabitationW25.fullMetricClosedPlacementWitnessOfConcreteLowerTables
    C

def minimalFreePlacementFieldsOfConcreteLowerTablesReduced
    (C : ConcreteNonConnectorLowerTableFamily) :
    MinimalFreePlacementFields :=
  FreePlacementSourceFieldsW24.W20SourceFields.toMinimalFreePlacementFields
    (w20SourceFieldsOfConcreteLowerTables C)

def minimalFreePlacementFieldsOfConcreteLowerTablesFull
    (C : ConcreteNonConnectorLowerTableFamily) :
    MinimalFreePlacementFields :=
  minimalFreePlacementFieldsOfFullMetricWitness
    (fullMetricWitnessOfConcreteLowerTables C)

/-- Preferred W27 concrete constructor: W26 lower tables give actual W24
minimal free-placement fields through the reduced W20/W19 closed-placement
handoff. -/
def minimalFreePlacementFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    MinimalFreePlacementFields :=
  minimalFreePlacementFieldsOfConcreteLowerTablesReduced C

def minimalFreePlacementFieldsOfDirectFullMetricSourcePackage
    (P : DirectFullMetricSourcePackage) :
    MinimalFreePlacementFields :=
  minimalFreePlacementFieldsOfFullMetricWitness P.closedPlacementWitness

@[simp]
theorem minimalFreePlacementFieldsOfConcreteLowerTables_point
    (C : ConcreteNonConnectorLowerTableFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (minimalFreePlacementFieldsOfConcreteLowerTables C).point k hk i v =
      GeneratedClosedChain.generatedPoint
        (C.periodSearch.transitions.toFigure2TransitionObligations)
        hk BaseTransitionRealization.exactBase
        (C.periodSearch.orientation k hk) i v :=
  rfl

@[simp]
theorem minimalFreePlacementFieldsOfConcreteLowerTablesFull_point
    (C : ConcreteNonConnectorLowerTableFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (minimalFreePlacementFieldsOfConcreteLowerTablesFull C).point k hk i v =
      GeneratedClosedChain.generatedPoint
        (C.periodSearch.transitions.toFigure2TransitionObligations)
        hk BaseTransitionRealization.exactBase
        (C.periodSearch.orientation k hk) i v :=
  rfl

theorem nonempty_minimalFreePlacementFields_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty MinimalFreePlacementFields :=
  Nonempty.intro (minimalFreePlacementFieldsOfConcreteLowerTables C)

theorem nonempty_minimalFreePlacementFields_of_nonempty_concreteLowerTables :
    Nonempty ConcreteNonConnectorLowerTableFamily ->
      Nonempty MinimalFreePlacementFields := by
  intro h
  cases h with
  | intro C =>
      exact nonempty_minimalFreePlacementFields_of_concreteLowerTables C

theorem nonempty_minimalFreePlacementFields_of_directFullMetricSourcePackage
    (P : DirectFullMetricSourcePackage) :
    Nonempty MinimalFreePlacementFields :=
  Nonempty.intro (minimalFreePlacementFieldsOfDirectFullMetricSourcePackage P)

theorem nonempty_minimalFreePlacementFields_of_closedPlacementFamily :
    Nonempty ClosedPlacementFamily -> Nonempty MinimalFreePlacementFields := by
  intro h
  cases h with
  | intro H =>
      exact Nonempty.intro (minimalFreePlacementFieldsOfClosedPlacementFamily H)

/-! ## Honest orbit-closure boundary -/

def minimalFieldsWithOrbitClosureOfConcreteClosedOrbitFamily
    (F : ConcreteClosedOrbitFamily) :
    MinimalFieldsWithOrbitClosure :=
  F.toMinimalFieldsWithOrbitClosure

def concreteClosedOrbitFamilyOfMinimalFieldsWithOrbitClosure
    (M : MinimalFieldsWithOrbitClosure) :
    ConcreteClosedOrbitFamily :=
  M.toConcreteClosedOrbitFamily

theorem nonempty_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure :
    Nonempty ConcreteClosedOrbitFamily <->
      Nonempty MinimalFieldsWithOrbitClosure :=
  ClosedPlacementConcreteConstructionW26.nonempty_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure

theorem nonempty_minimalFreePlacementFields_of_concreteClosedOrbitFamily :
    Nonempty ConcreteClosedOrbitFamily ->
      Nonempty MinimalFreePlacementFields := by
  intro h
  cases h with
  | intro F =>
      exact Nonempty.intro F.toMinimalFreePlacementFields

theorem nonempty_minimalFreePlacementFields_of_minimalFieldsWithOrbitClosure :
    Nonempty MinimalFieldsWithOrbitClosure ->
      Nonempty MinimalFreePlacementFields := by
  intro h
  cases h with
  | intro M =>
      exact Nonempty.intro M.fields

/-- The precise orbit blocker: failing concrete closed-orbit data is the same
as failing minimal fields equipped with successor closure. -/
theorem not_nonempty_concreteClosedOrbitFamily_iff_not_minimalFieldsWithOrbitClosure :
    Not (Nonempty ConcreteClosedOrbitFamily) <->
      Not (Nonempty MinimalFieldsWithOrbitClosure) := by
  constructor
  · intro hclosed hminimal
    exact hclosed
      (nonempty_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure.2
        hminimal)
  · intro hminimal hclosed
    exact hminimal
      (nonempty_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure.1
        hclosed)

theorem no_minimalFieldsWithOrbitClosure_of_no_concreteClosedOrbitFamily
    (h : Not (Nonempty ConcreteClosedOrbitFamily)) :
    Not (Nonempty MinimalFieldsWithOrbitClosure) :=
  not_nonempty_concreteClosedOrbitFamily_iff_not_minimalFieldsWithOrbitClosure.1
    h

theorem no_concreteClosedOrbitFamily_of_no_minimalFieldsWithOrbitClosure
    (h : Not (Nonempty MinimalFieldsWithOrbitClosure)) :
    Not (Nonempty ConcreteClosedOrbitFamily) :=
  not_nonempty_concreteClosedOrbitFamily_iff_not_minimalFieldsWithOrbitClosure.2
    h

/-- A weaker blocker for the free-placement lane: if even minimal fields are
impossible, then none of the stronger concrete lower-table or orbit packages
can be inhabited. -/
structure FreePlacementBlocker where
  no_minimal : Not (Nonempty MinimalFreePlacementFields)

namespace FreePlacementBlocker

theorem no_concreteLowerTables
    (B : FreePlacementBlocker) :
    Not (Nonempty ConcreteNonConnectorLowerTableFamily) := by
  intro h
  exact B.no_minimal
    (nonempty_minimalFreePlacementFields_of_nonempty_concreteLowerTables h)

theorem no_concreteClosedOrbitFamily
    (B : FreePlacementBlocker) :
    Not (Nonempty ConcreteClosedOrbitFamily) := by
  intro h
  exact B.no_minimal
    (nonempty_minimalFreePlacementFields_of_concreteClosedOrbitFamily h)

theorem no_minimalFieldsWithOrbitClosure
    (B : FreePlacementBlocker) :
    Not (Nonempty MinimalFieldsWithOrbitClosure) := by
  intro h
  exact B.no_minimal
    (nonempty_minimalFreePlacementFields_of_minimalFieldsWithOrbitClosure h)

end FreePlacementBlocker

end

end FreePlacementFieldsConcreteW27
end PachToth

namespace Verified

abbrev PachTothW27MinimalFreePlacementFields : Type :=
  PachToth.FreePlacementFieldsConcreteW27.MinimalFreePlacementFields

abbrev PachTothW27FreePlacementConcreteNonConnectorLowerTableFamily : Type :=
  PachToth.FreePlacementFieldsConcreteW27.ConcreteNonConnectorLowerTableFamily

abbrev PachTothW27FreePlacementConcreteClosedOrbitFamily : Type :=
  PachToth.FreePlacementFieldsConcreteW27.ConcreteClosedOrbitFamily

abbrev PachTothW27MinimalFieldsWithOrbitClosure : Type :=
  PachToth.FreePlacementFieldsConcreteW27.MinimalFieldsWithOrbitClosure

theorem pachtoth_w27_nonempty_minimalFreePlacementFields_of_concreteLowerTables :
    Nonempty PachTothW27FreePlacementConcreteNonConnectorLowerTableFamily ->
      Nonempty PachTothW27MinimalFreePlacementFields :=
  PachToth.FreePlacementFieldsConcreteW27.nonempty_minimalFreePlacementFields_of_nonempty_concreteLowerTables

theorem pachtoth_w27_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure :
    Nonempty PachTothW27FreePlacementConcreteClosedOrbitFamily <->
      Nonempty PachTothW27MinimalFieldsWithOrbitClosure :=
  PachToth.FreePlacementFieldsConcreteW27.nonempty_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure

theorem pachtoth_w27_not_concreteClosedOrbitFamily_iff_not_minimalFieldsWithOrbitClosure :
    Not (Nonempty PachTothW27FreePlacementConcreteClosedOrbitFamily) <->
      Not (Nonempty PachTothW27MinimalFieldsWithOrbitClosure) :=
  PachToth.FreePlacementFieldsConcreteW27.not_nonempty_concreteClosedOrbitFamily_iff_not_minimalFieldsWithOrbitClosure

end Verified
end ErdosProblems1066
