import ErdosProblems1066.Swanepoel.OuterBoundaryLabelFacts
import ErdosProblems1066.Swanepoel.BoundaryLabelCertificateAssembly
import ErdosProblems1066.Swanepoel.BoundaryLabelExtractionTasks
import ErdosProblems1066.Swanepoel.Lemma8NeighborExtractionConcrete
import ErdosProblems1066.Swanepoel.MinimalFailureW8RowAssembly
import ErdosProblems1066.Swanepoel.SwanepoelRemainingObligationsW9

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W10 boundary-label instantiation adapters

This module is a checked adapter layer for the W9 Swanepoel rows.  It projects
explicit boundary-label packages to the local labels and extracted `r_i, s_i`
extra-neighbor data, and it reindexes the existing W8 boundary/long-arc source
row as the W9 base row.

The later window and no-start/K23 inputs remain explicit row parameters.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryLabelInstantiationW10

open BoundaryLabelCertificateAssembly
open BoundarySpineFiniteCertificate
open GraphBridge
open Lemma8NeighborExtractionConcrete
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalFailureW8RowAssembly
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-! ## Explicit boundary-label packages -/

namespace BoundaryLabelPackageAdapters

variable {C : _root_.UDConfig n}

/-- Forget an explicit boundary-label package to its non-cyclic extra-neighbor
extraction data. -/
def extraNeighborData
    (D : M8BoundaryLabelPackage C) :
    M8ExtraNeighborData D.spine :=
  M8ExtraNeighborData.ofLemma8Combinatorics D.lemma8

/-- The cyclic-order record carried by an explicit boundary-label package. -/
def cyclicOrder
    (D : M8BoundaryLabelPackage C) :
    M8ExtraNeighborData.CyclicOrder (extraNeighborData D) :=
  M8ExtraNeighborData.cyclicOrderOfLemma8Combinatorics D.lemma8

@[simp]
theorem extraNeighborData_r
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    (extraNeighborData D).r i = D.lemma8.r i :=
  rfl

@[simp]
theorem extraNeighborData_s
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    (extraNeighborData D).s i = D.lemma8.s i :=
  rfl

@[simp]
theorem localLabels_p
    (D : M8BoundaryLabelPackage C) (i : M8BoundaryIndex) :
    D.toM8LocalLabels.labels.p i = D.spine.p i :=
  BoundaryLabelExtractionTasks.M8BoundaryLabelPackage.localLabels_p D i

@[simp]
theorem localLabels_q
    (D : M8BoundaryLabelPackage C) (i : M8TriangleIndex) :
    D.toM8LocalLabels.labels.q i = D.spine.q i :=
  BoundaryLabelExtractionTasks.M8BoundaryLabelPackage.localLabels_q D i

@[simp]
theorem localLabels_r
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    D.toM8LocalLabels.labels.r i = (extraNeighborData D).r i :=
  rfl

@[simp]
theorem localLabels_s
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    D.toM8LocalLabels.labels.s i = (extraNeighborData D).s i :=
  rfl

/-- The local boundary-edge predicate is exactly the stored boundary-spine
predicate. -/
theorem localLabels_boundaryEdge
    (D : M8BoundaryLabelPackage C) (i : M8TriangleIndex) :
    D.toM8LocalLabels.predicates.data.boundaryEdge i := by
  simpa using
    OuterBoundaryLabelFacts.M8BoundaryLabelPackage.boundaryEdge D i

/-- The local triangle-witness predicate is exactly the stored boundary-spine
predicate. -/
theorem localLabels_triangleWitness
    (D : M8BoundaryLabelPackage C) (i : M8TriangleIndex) :
    D.toM8LocalLabels.predicates.data.triangleWitness i := by
  simpa using
    OuterBoundaryLabelFacts.M8BoundaryLabelPackage.triangleWitness D i

/-- The local extra-neighbor predicate is supplied by the extracted
extra-neighbor data. -/
theorem localLabels_extraNeighborWitness
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    D.toM8LocalLabels.predicates.data.extraNeighborWitness i := by
  simpa using
    (extraNeighborData D).extraNeighborWitness_holds i

theorem extraNeighborData_r_neighbor
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.centerQ i) ((extraNeighborData D).r i) :=
  (extraNeighborData D).r_neighbor i

theorem extraNeighborData_s_neighbor
    (D : M8BoundaryLabelPackage C) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (D.spine.centerQ i) ((extraNeighborData D).s i) :=
  (extraNeighborData D).s_neighbor i

theorem extraNeighborData_named_of_extra_neighbor
    (D : M8BoundaryLabelPackage C)
    {i : M8ExtraIndex} {x : Fin n}
    (hadj : (unitDistanceLocalGraph C).Adj (D.spine.centerQ i) x)
    (hnot : Not (D.spine.forbiddenExtraNeighbor i x)) :
    x = (extraNeighborData D).r i \/
      x = (extraNeighborData D).s i :=
  (extraNeighborData D).named_of_extra_neighbor hadj hnot

end BoundaryLabelPackageAdapters

/-! ## Finite boundary-label certificates -/

namespace FiniteBoundaryLabelCertificateAdapters

variable {C : _root_.UDConfig n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
variable {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
variable {hmin : IsMinimalClearedFailure C}

/-- Extract the non-cyclic extra-neighbor data from a finite boundary-label
certificate. -/
def extraNeighborData
    (K : M8FiniteBoundaryLabelCertificate D connectedNoCut hmin) :
    M8ExtraNeighborData K.spine :=
  M8ExtraNeighborData.ofLemma8Combinatorics K.lemma8

@[simp]
theorem localLabels_p
    (K : M8FiniteBoundaryLabelCertificate D connectedNoCut hmin)
    (i : M8BoundaryIndex) :
    K.toM8LocalLabels.labels.p i = K.finiteLabels.p i :=
  BoundaryLabelCertificateAssembly.M8FiniteBoundaryLabelCertificate.labels_p
    K i

@[simp]
theorem localLabels_q
    (K : M8FiniteBoundaryLabelCertificate D connectedNoCut hmin)
    (i : M8TriangleIndex) :
    K.toM8LocalLabels.labels.q i = K.finiteLabels.q i :=
  BoundaryLabelCertificateAssembly.M8FiniteBoundaryLabelCertificate.labels_q
    K i

@[simp]
theorem localLabels_r
    (K : M8FiniteBoundaryLabelCertificate D connectedNoCut hmin)
    (i : M8ExtraIndex) :
    K.toM8LocalLabels.labels.r i = (extraNeighborData K).r i :=
  rfl

@[simp]
theorem localLabels_s
    (K : M8FiniteBoundaryLabelCertificate D connectedNoCut hmin)
    (i : M8ExtraIndex) :
    K.toM8LocalLabels.labels.s i = (extraNeighborData K).s i :=
  rfl

theorem extraNeighborData_extraNeighborWitness
    (K : M8FiniteBoundaryLabelCertificate D connectedNoCut hmin)
    (i : M8ExtraIndex) :
    (extraNeighborData K).extraNeighborWitness i :=
  (extraNeighborData K).extraNeighborWitness_holds i

theorem localLabels_extraNeighborWitness
    (K : M8FiniteBoundaryLabelCertificate D connectedNoCut hmin)
    (i : M8ExtraIndex) :
    K.toM8LocalLabels.predicates.data.extraNeighborWitness i :=
  K.extraNeighborWitness i

end FiniteBoundaryLabelCertificateAdapters

/-! ## Existing W8 source rows as W9 base rows -/

namespace MinimalFailureW8BoundaryLongArcData

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The W9 topology/angle/subpolygon row carried by an existing W8 source row. -/
def toW9TopologyAngleSubpolygonRow
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C where
  topology := D.topology
  outerAngleBounds := D.outerAngleBounds
  Subpolygon := D.Subpolygon
  subpolygonData := D.subpolygonData
  longArc := D.longArc

/-- The W9 boundary-label row carried by an existing W8 source row. -/
def toW9BoundaryLabelRow
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    SwanepoelRemainingObligationsW9.BoundaryLabelRow.{u}
      C hmin (toW9TopologyAngleSubpolygonRow D) where
  remainingNoCutSlack := D.remainingNoCutSlack
  spineCertificate := D.spineCertificate
  lemma8Existence := D.lemma8Existence

/-- The W9 base row obtained by repackaging the existing W8 source row. -/
def toW9BaseRow
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    SwanepoelRemainingObligationsW9.BaseRow.{u} C hmin where
  topology := toW9TopologyAngleSubpolygonRow D
  boundaryLabels := toW9BoundaryLabelRow D

/-- Extra-neighbor data extracted from the Lemma 8 row of the W8 source. -/
def extraNeighborData
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    M8ExtraNeighborData D.spine :=
  M8ExtraNeighborData.ofMissingExistenceConditions D.lemma8Existence

@[simp]
theorem extraNeighborData_r
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8ExtraIndex) :
    (extraNeighborData D).r i = D.lemma8.r i :=
  rfl

@[simp]
theorem extraNeighborData_s
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8ExtraIndex) :
    (extraNeighborData D).s i = D.lemma8.s i :=
  rfl

@[simp]
theorem toW9BaseRow_toW8BoundaryLongArcData
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    (toW9BaseRow D).toW8BoundaryLongArcData = D := by
  cases D
  rfl

@[simp]
theorem toW9BaseRow_labels
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    (toW9BaseRow D).labels = D.labels := by
  cases D
  rfl

@[simp]
theorem toW9BaseRow_localLabels
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) :
    (toW9BaseRow D).localLabels = D.labels.toM8LocalLabels := by
  cases D
  rfl

@[simp]
theorem localLabels_r
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8ExtraIndex) :
    D.labels.toM8LocalLabels.labels.r i = (extraNeighborData D).r i :=
  rfl

@[simp]
theorem localLabels_s
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8ExtraIndex) :
    D.labels.toM8LocalLabels.labels.s i = (extraNeighborData D).s i :=
  rfl

theorem localLabels_extraNeighborWitness
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin)
    (i : M8ExtraIndex) :
    D.labels.toM8LocalLabels.predicates.data.extraNeighborWitness i :=
  D.labels.extraNeighborWitness_holds i

/-- Direct W9 rows still require the window and no-start inputs for the exact
base row produced by the boundary-label adapter. -/
structure DirectRowInputs
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) where
  window :
    SwanepoelRemainingObligationsW9.WindowRow.{u}
      C hmin (toW9BaseRow D)
  noStart :
    SwanepoelRemainingObligationsW9.NoStartRow.{u}
      C hmin (toW9BaseRow D)

namespace DirectRowInputs

/-- Repackage explicit direct W9 inputs as the W9 minimal-failure direct row. -/
def toW9MinimalFailureDirectRow
    {D : MinimalFailureW8BoundaryLongArcData.{u} C hmin}
    (R : DirectRowInputs D) :
    SwanepoelRemainingObligationsW9.MinimalFailureDirectRow.{u} C hmin where
  base := toW9BaseRow D
  window := R.window
  noStart := R.noStart

@[simp]
theorem toW9MinimalFailureDirectRow_base
    {D : MinimalFailureW8BoundaryLongArcData.{u} C hmin}
    (R : DirectRowInputs D) :
    R.toW9MinimalFailureDirectRow.base = toW9BaseRow D :=
  rfl

end DirectRowInputs

/-- K23 W9 rows still require the window and K23 inputs for the exact base row
produced by the boundary-label adapter. -/
structure K23RowInputs
    (D : MinimalFailureW8BoundaryLongArcData.{u} C hmin) where
  window :
    SwanepoelRemainingObligationsW9.WindowRow.{u}
      C hmin (toW9BaseRow D)
  k23NoEarly :
    SwanepoelRemainingObligationsW9.K23NoEarlyRow.{u}
      C hmin (toW9BaseRow D)

namespace K23RowInputs

/-- Repackage explicit K23 W9 inputs as the W9 minimal-failure K23 row. -/
def toW9MinimalFailureK23Row
    {D : MinimalFailureW8BoundaryLongArcData.{u} C hmin}
    (R : K23RowInputs D) :
    SwanepoelRemainingObligationsW9.MinimalFailureK23Row.{u} C hmin where
  base := toW9BaseRow D
  window := R.window
  k23NoEarly := R.k23NoEarly

@[simp]
theorem toW9MinimalFailureK23Row_base
    {D : MinimalFailureW8BoundaryLongArcData.{u} C hmin}
    (R : K23RowInputs D) :
    R.toW9MinimalFailureK23Row.base = toW9BaseRow D :=
  rfl

end K23RowInputs

end MinimalFailureW8BoundaryLongArcData

end

end BoundaryLabelInstantiationW10
end Swanepoel
end ErdosProblems1066
