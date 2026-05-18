import ErdosProblems1066.PachToth.RoleHingeAngleCertificates
import ErdosProblems1066.PachToth.RoleHingeTransitionSearch
import ErdosProblems1066.PachToth.FlexibleBranchCoordinateSearch
import ErdosProblems1066.PachToth.ExactLocalTransitionObligationMatrix
import ErdosProblems1066.PachToth.PolynomialCertificateExtraction

set_option autoImplicit false

/-!
# W10 polynomial systems for role-hinge data

This module packages the role-hinge search obligations as explicit equation
systems.  Connector equations, the two angle-controlled port-pair equations,
and exact-local squared-distance rows are kept as separate fields.  The
projections below route those fields to the existing flexible/candidate
interfaces, while the concrete four-target map is exposed only as a filtered
possible-row system together with its checked blocked-row obstruction.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingePolynomialSystemW10

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole
abbrev PossibleExactLocalRow :=
  ExactLocalTransitionObligationMatrix.IsPossibleExactLocalRow
abbrev DerivableExactLocalRow :=
  FlexibleBranchCoordinateSearch.DerivableExactLocalRow
abbrev RoleHingedPeriodSearchFamily :=
  PolynomialCertificateExtraction.RoleHingedPeriodSearchFamily

/-! ## Branch equation systems -/

/-- Raw connector equations: every role-table connector target is the named
unit hinge point from the source block. -/
def ConnectorEquationSystem
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (roleAngle : ConnectorRole -> Real) : Prop :=
  forall (source : LocalVertex -> R2) (u v : LocalVertex)
    (role : ConnectorRole),
      Figure2EdgeTable.nextConnectorRole u v = some role ->
        placeNext source v =
          UnitVectorGeometry.hingePoint (source u) (roleAngle role)

/-- The two same-source port-pair equations in angle form. -/
abbrev PortPairEquationSystem
    (roleAngle : ConnectorRole -> Real) : Prop :=
  RoleHingeAngleCertificates.RoleHingeAngleEquations roleAngle

/-- Exact-local squared-distance equations restricted by a row predicate. -/
def ExactLocalRowEquationSystem
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (row : LocalVertex -> LocalVertex -> Prop) : Prop :=
  forall source : LocalVertex -> R2,
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
      forall u v : LocalVertex,
        row u v ->
          RoleHingeSameBlockAlgebra.sqDist
              (placeNext source u) (placeNext source v) =
            ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

/-- Full exact-local equation system for all ordered local rows. -/
def FullExactLocalEquationSystem
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) : Prop :=
  ExactLocalRowEquationSystem placeNext (fun _ _ => True)

/-- Filtered exact-local equation system for rows allowed by the W8/W9
possible-row matrix. -/
def PossibleExactLocalEquationSystem
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) : Prop :=
  ExactLocalRowEquationSystem placeNext PossibleExactLocalRow

/-- The possible-row matrix and the W9 derivable-row spelling are equivalent. -/
theorem possibleExactLocalRow_iff_derivableExactLocalRow
    (u v : LocalVertex) :
    PossibleExactLocalRow u v <-> DerivableExactLocalRow u v := by
  constructor
  · intro hrow
    rcases hrow with hdiag | hinherited | hpair
    · exact Or.inl hdiag
    · exact Or.inr (Or.inr hinherited)
    · exact Or.inr (Or.inl hpair)
  · intro hrow
    rcases hrow with hdiag | hpair | hinherited
    · exact Or.inl hdiag
    · exact Or.inr (Or.inr hpair)
    · exact Or.inr (Or.inl hinherited)

/-- The possible-row and derivable-row equation systems are the same filtered
exact-local obligation. -/
theorem possibleExactLocalEquationSystem_iff_derivableRows
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) :
    PossibleExactLocalEquationSystem placeNext <->
      ExactLocalRowEquationSystem placeNext DerivableExactLocalRow := by
  constructor
  · intro hsystem source hsource u v hrow
    exact hsystem source hsource u v
      ((possibleExactLocalRow_iff_derivableExactLocalRow u v).mpr hrow)
  · intro hsystem source hsource u v hrow
    exact hsystem source hsource u v
      ((possibleExactLocalRow_iff_derivableExactLocalRow u v).mp hrow)

/-- Full row equations are exactly the existing exact-local preservation
predicate. -/
theorem fullExactLocalEquationSystem_iff_preservesExactLocalSqDistances
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) :
    FullExactLocalEquationSystem placeNext <->
      RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances placeNext := by
  constructor
  · intro hsystem source hsource u v
    exact hsystem source hsource u v trivial
  · intro hpres source hsource u v _hrow
    exact hpres source hsource u v

/-- A completed branch polynomial system: connector equations, port-pair
angle equations, and all exact-local rows. -/
structure BranchPolynomialSystem where
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2
  roleAngle : ConnectorRole -> Real
  connector :
    ConnectorEquationSystem placeNext roleAngle
  portPair :
    PortPairEquationSystem roleAngle
  exactLocal :
    FullExactLocalEquationSystem placeNext

namespace BranchPolynomialSystem

/-- Connector role data projected from the branch equation system. -/
def toConnectorUnitRoleData
    (B : BranchPolynomialSystem) :
    FlexibleExactLocalTransition.ConnectorUnitRoleData where
  placeNext := B.placeNext
  roleAngle := B.roleAngle
  realizes_role := B.connector

@[simp]
theorem toConnectorUnitRoleData_placeNext
    (B : BranchPolynomialSystem) :
    B.toConnectorUnitRoleData.placeNext = B.placeNext :=
  rfl

@[simp]
theorem toConnectorUnitRoleData_roleAngle
    (B : BranchPolynomialSystem) :
    B.toConnectorUnitRoleData.roleAngle = B.roleAngle :=
  rfl

/-- Connector-level transition facts projected from the branch system. -/
def toConnectorTransitionFacts
    (B : BranchPolynomialSystem) :
    RoleHingeTransitionSearch.RoleHingeConnectorTransitionFacts :=
  B.toConnectorUnitRoleData.toConnectorTransitionFacts

@[simp]
theorem toConnectorTransitionFacts_placeNext
    (B : BranchPolynomialSystem) :
    B.toConnectorTransitionFacts.placeNext = B.placeNext :=
  rfl

@[simp]
theorem toConnectorTransitionFacts_roleAngle
    (B : BranchPolynomialSystem) :
    B.toConnectorTransitionFacts.roleAngle = B.roleAngle :=
  rfl

/-- Connector unit edges are derived from the connector equation system. -/
theorem connector_unit_edges
    (B : BranchPolynomialSystem) :
    HingedTransitionInterface.ConnectorUnitEdges B.placeNext :=
  B.toConnectorUnitRoleData.connector_unit_edges

/-- The port-pair equations give the two same-source unit-edge obligations. -/
theorem portPairUnitEdges
    (B : BranchPolynomialSystem) :
    And
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (B.placeNext source T1_1) (B.placeNext source T1_2) = 1)
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (B.placeNext source T0_0) (B.placeNext source T0_2) = 1) :=
  RoleHingeAngleCertificates.portPairUnitEdges_of_angleEquations_realizes
    B.placeNext B.roleAngle B.connector B.portPair

/-- Full exact-local row equations in the existing preservation spelling. -/
theorem preservesExactLocalSqDistances
    (B : BranchPolynomialSystem) :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances B.placeNext :=
  (fullExactLocalEquationSystem_iff_preservesExactLocalSqDistances
    B.placeNext).mp B.exactLocal

/-- Row-level access to the exact-local equation system. -/
theorem exactLocalRow
    (B : BranchPolynomialSystem)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    (u v : LocalVertex) :
    RoleHingeSameBlockAlgebra.sqDist
        (B.placeNext source u) (B.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  B.preservesExactLocalSqDistances source hsource u v

/-- Projection to the flexible exact-local branch interface. -/
def toFlexibleBranch
    (B : BranchPolynomialSystem) :
    FlexibleExactLocalTransition.Branch where
  connector := B.toConnectorUnitRoleData
  exactLocal :=
    { preserves_exact_local_sq_distances :=
        B.preservesExactLocalSqDistances }

@[simp]
theorem toFlexibleBranch_placeNext
    (B : BranchPolynomialSystem) :
    B.toFlexibleBranch.placeNext = B.placeNext :=
  rfl

/-- Projection to the non-rigid candidate branch interface. -/
def toBranchCandidate
    (B : BranchPolynomialSystem) :
    RoleHingeCandidateSearchSurface.BranchCandidate where
  placeNext := B.placeNext
  roleAngle := B.roleAngle
  realizes_role := B.connector
  preserves_exactLocal_sqDistances := B.preservesExactLocalSqDistances

@[simp]
theorem toBranchCandidate_placeNext
    (B : BranchPolynomialSystem) :
    B.toBranchCandidate.placeNext = B.placeNext :=
  rfl

end BranchPolynomialSystem

/-! ## Filtered branch systems -/

/-- Connector and port-pair equations together with only the filtered
possible exact-local rows. -/
structure FilteredBranchPolynomialSystem where
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2
  roleAngle : ConnectorRole -> Real
  connector :
    ConnectorEquationSystem placeNext roleAngle
  portPair :
    PortPairEquationSystem roleAngle
  possibleRows :
    PossibleExactLocalEquationSystem placeNext

namespace FilteredBranchPolynomialSystem

/-- Projection to the W9 coordinate-data surface. -/
def toBranchCoordinateData
    (B : FilteredBranchPolynomialSystem) :
    FlexibleBranchCoordinateSearch.BranchCoordinateData where
  placeNext := B.placeNext
  roleAngle := B.roleAngle
  realizes_role := B.connector
  angleEquations := B.portPair

@[simp]
theorem toBranchCoordinateData_placeNext
    (B : FilteredBranchPolynomialSystem) :
    B.toBranchCoordinateData.placeNext = B.placeNext :=
  rfl

@[simp]
theorem toBranchCoordinateData_roleAngle
    (B : FilteredBranchPolynomialSystem) :
    B.toBranchCoordinateData.roleAngle = B.roleAngle :=
  rfl

/-- Connector role data projected from a filtered branch system. -/
def toConnectorUnitRoleData
    (B : FilteredBranchPolynomialSystem) :
    FlexibleExactLocalTransition.ConnectorUnitRoleData where
  placeNext := B.placeNext
  roleAngle := B.roleAngle
  realizes_role := B.connector

/-- Connector-level transition facts projected from a filtered branch. -/
def toConnectorTransitionFacts
    (B : FilteredBranchPolynomialSystem) :
    RoleHingeTransitionSearch.RoleHingeConnectorTransitionFacts :=
  B.toConnectorUnitRoleData.toConnectorTransitionFacts

/-- Connector unit edges are still available for filtered systems. -/
theorem connector_unit_edges
    (B : FilteredBranchPolynomialSystem) :
    HingedTransitionInterface.ConnectorUnitEdges B.placeNext :=
  B.toConnectorUnitRoleData.connector_unit_edges

/-- The port-pair equations give the two same-source unit-edge obligations for
a filtered branch as well. -/
theorem portPairUnitEdges
    (B : FilteredBranchPolynomialSystem) :
    And
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (B.placeNext source T1_1) (B.placeNext source T1_2) = 1)
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (B.placeNext source T0_0) (B.placeNext source T0_2) = 1) :=
  RoleHingeAngleCertificates.portPairUnitEdges_of_angleEquations_realizes
    B.placeNext B.roleAngle B.connector B.portPair

/-- Row-level access to the filtered possible-row equation system. -/
theorem possibleRow
    (B : FilteredBranchPolynomialSystem)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : PossibleExactLocalRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (B.placeNext source u) (B.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  B.possibleRows source hsource u v hrow

/-- Filtered possible rows, restated in the W9 derivable-row spelling. -/
theorem derivableRow
    (B : FilteredBranchPolynomialSystem)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : DerivableExactLocalRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (B.placeNext source u) (B.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  (possibleExactLocalEquationSystem_iff_derivableRows B.placeNext).mp
    B.possibleRows source hsource u v hrow

end FilteredBranchPolynomialSystem

/-! ## Same/opposite systems -/

/-- Completed same/opposite branch equation systems. -/
structure SameOppositePolynomialSystem where
  same : BranchPolynomialSystem
  opposite : BranchPolynomialSystem

namespace SameOppositePolynomialSystem

/-- Projection to the non-rigid same/opposite candidate interface. -/
def toSameOppositeCandidate
    (S : SameOppositePolynomialSystem) :
    RoleHingeCandidateSearchSurface.SameOppositeCandidate where
  same := S.same.toBranchCandidate
  opposite := S.opposite.toBranchCandidate

@[simp]
theorem toSameOppositeCandidate_same_placeNext
    (S : SameOppositePolynomialSystem) :
    S.toSameOppositeCandidate.same.placeNext = S.same.placeNext :=
  rfl

@[simp]
theorem toSameOppositeCandidate_opposite_placeNext
    (S : SameOppositePolynomialSystem) :
    S.toSameOppositeCandidate.opposite.placeNext =
      S.opposite.placeNext :=
  rfl

/-- Projection to the flexible exact-local same/opposite interface. -/
def toFlexibleSameOpposite
    (S : SameOppositePolynomialSystem) :
    FlexibleExactLocalTransition.SameOpposite where
  same := S.same.toFlexibleBranch
  opposite := S.opposite.toFlexibleBranch

/-- Figure 2 connector obligations projected from the same/opposite system. -/
def toFigure2TransitionObligations
    (S : SameOppositePolynomialSystem) :
    Figure2Certificate.SameOppositeTransitionObligations :=
  S.toSameOppositeCandidate.toFigure2TransitionObligations

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (S : SameOppositePolynomialSystem) :
    S.toFigure2TransitionObligations.samePlaceNext =
      S.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (S : SameOppositePolynomialSystem) :
    S.toFigure2TransitionObligations.oppositePlaceNext =
      S.opposite.placeNext :=
  rfl

/-- Branchwise exact-local equations imply the generated-transition exact-local
invariant. -/
theorem generatedTransitionsPreserveExactLocalSqDistances
    (S : SameOppositePolynomialSystem) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      S.toFigure2TransitionObligations :=
  S.toSameOppositeCandidate.generatedTransitionsPreserveExactLocalSqDistances

end SameOppositePolynomialSystem

/-- Filtered same/opposite branch equation systems. -/
structure FilteredSameOppositePolynomialSystem where
  same : FilteredBranchPolynomialSystem
  opposite : FilteredBranchPolynomialSystem

namespace FilteredSameOppositePolynomialSystem

/-- Projection to the W9 same/opposite coordinate-data surface. -/
def toCoordinateData
    (S : FilteredSameOppositePolynomialSystem) :
    FlexibleBranchCoordinateSearch.SameOppositeCoordinateData where
  same := S.same.toBranchCoordinateData
  opposite := S.opposite.toBranchCoordinateData

/-- Figure 2 connector obligations projected from the filtered system. -/
def toFigure2TransitionObligations
    (S : FilteredSameOppositePolynomialSystem) :
    Figure2Certificate.SameOppositeTransitionObligations :=
  S.toCoordinateData.toFigure2TransitionObligations

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (S : FilteredSameOppositePolynomialSystem) :
    S.toFigure2TransitionObligations.samePlaceNext =
      S.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (S : FilteredSameOppositePolynomialSystem) :
    S.toFigure2TransitionObligations.oppositePlaceNext =
      S.opposite.placeNext :=
  rfl

end FilteredSameOppositePolynomialSystem

/-! ## Concrete filtered system and obstruction -/

/-- The concrete same branch satisfies the connector, port-pair, and possible
exact-local row systems. -/
def concreteSameFilteredBranchSystem :
    FilteredBranchPolynomialSystem where
  placeNext := RoleHingeConcreteSearch.samePlaceNext
  roleAngle := RoleHingeConcreteSearch.sameRoleAngle
  connector :=
    RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
      RoleHingeConcreteSearch.sameRoleAngle
  portPair := RoleHingeConcreteSearch.sameRoleAngle_angleEquations
  possibleRows := by
    intro source hsource u v hrow
    exact
      ExactLocalTransitionObligationMatrix.samePlaceNext_possibleRow_sqDist
        hsource hrow

/-- The concrete opposite branch satisfies the connector, port-pair, and
possible exact-local row systems. -/
def concreteOppositeFilteredBranchSystem :
    FilteredBranchPolynomialSystem where
  placeNext := RoleHingeConcreteSearch.oppositePlaceNext
  roleAngle := RoleHingeConcreteSearch.oppositeRoleAngle
  connector :=
    RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
      RoleHingeConcreteSearch.oppositeRoleAngle
  portPair := RoleHingeConcreteSearch.oppositeRoleAngle_angleEquations
  possibleRows := by
    intro source hsource u v hrow
    exact
      ExactLocalTransitionObligationMatrix.oppositePlaceNext_possibleRow_sqDist
        hsource hrow

/-- The concrete same/opposite maps as a filtered possible-row system. -/
def concreteFilteredSameOppositeSystem :
    FilteredSameOppositePolynomialSystem where
  same := concreteSameFilteredBranchSystem
  opposite := concreteOppositeFilteredBranchSystem

@[simp]
theorem concreteFilteredSameOppositeSystem_same_placeNext :
    concreteFilteredSameOppositeSystem.same.placeNext =
      RoleHingeConcreteSearch.samePlaceNext :=
  rfl

@[simp]
theorem concreteFilteredSameOppositeSystem_opposite_placeNext :
    concreteFilteredSameOppositeSystem.opposite.placeNext =
      RoleHingeConcreteSearch.oppositePlaceNext :=
  rfl

/-- A single exact-base polynomial row obstruction. -/
def ExactBasePolynomialRowObstruction
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (u v : LocalVertex) : Prop :=
  Not
    (RoleHingeSameBlockAlgebra.sqDist
        (placeNext ExactLocalGeometry.localPoint u)
        (placeNext ExactLocalGeometry.localPoint v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4)

/-- An exact-base row obstruction rules out any row system containing that row. -/
theorem not_exactLocalRowEquationSystem_of_exactBaseObstruction
    {placeNext : (LocalVertex -> R2) -> LocalVertex -> R2}
    {row : LocalVertex -> LocalVertex -> Prop}
    {u v : LocalVertex}
    (hrow : row u v)
    (hobs : ExactBasePolynomialRowObstruction placeNext u v) :
    Not (ExactLocalRowEquationSystem placeNext row) := by
  intro hsystem
  exact hobs
    (hsystem ExactLocalGeometry.localPoint
      RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
      u v hrow)

/-- Same branch: the blocked row `T1_1,r` is an exact-base polynomial
obstruction. -/
theorem sameConcrete_T1_1_r_exactBaseObstruction :
    ExactBasePolynomialRowObstruction
      RoleHingeConcreteSearch.samePlaceNext T1_1 LocalVertex.r :=
  ExactLocalTransitionObligationMatrix.samePlaceNext_exactBase_T1_1_r_forces_contradiction

/-- Opposite branch: the same blocked row is also an exact-base polynomial
obstruction. -/
theorem oppositeConcrete_T1_1_r_exactBaseObstruction :
    ExactBasePolynomialRowObstruction
      RoleHingeConcreteSearch.oppositePlaceNext T1_1 LocalVertex.r :=
  ExactLocalTransitionObligationMatrix.oppositePlaceNext_exactBase_T1_1_r_forces_contradiction

/-- Any same-branch row equation system containing `T1_1,r` is obstructed. -/
theorem sameConcrete_not_rowSystem_containing_T1_1_r
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T1_1 LocalVertex.r) :
    Not
      (ExactLocalRowEquationSystem
        RoleHingeConcreteSearch.samePlaceNext row) :=
  not_exactLocalRowEquationSystem_of_exactBaseObstruction
    hrow sameConcrete_T1_1_r_exactBaseObstruction

/-- Any opposite-branch row equation system containing `T1_1,r` is obstructed. -/
theorem oppositeConcrete_not_rowSystem_containing_T1_1_r
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T1_1 LocalVertex.r) :
    Not
      (ExactLocalRowEquationSystem
        RoleHingeConcreteSearch.oppositePlaceNext row) :=
  not_exactLocalRowEquationSystem_of_exactBaseObstruction
    hrow oppositeConcrete_T1_1_r_exactBaseObstruction

/-- The concrete same branch cannot satisfy the full exact-local equation
system. -/
theorem sameConcrete_not_fullExactLocalEquationSystem :
    Not
      (FullExactLocalEquationSystem
        RoleHingeConcreteSearch.samePlaceNext) :=
  sameConcrete_not_rowSystem_containing_T1_1_r trivial

/-- The concrete opposite branch cannot satisfy the full exact-local equation
system. -/
theorem oppositeConcrete_not_fullExactLocalEquationSystem :
    Not
      (FullExactLocalEquationSystem
        RoleHingeConcreteSearch.oppositePlaceNext) :=
  oppositeConcrete_not_rowSystem_containing_T1_1_r trivial

/-- Consequently the concrete filtered same branch cannot be upgraded to a
completed branch polynomial system with the same map. -/
theorem not_concreteSame_completedBranchPolynomialSystem :
    Not
      (exists B : BranchPolynomialSystem,
        B.placeNext = RoleHingeConcreteSearch.samePlaceNext) := by
  rintro ⟨B, hplace⟩
  exact sameConcrete_not_fullExactLocalEquationSystem
    (by simpa [hplace] using B.exactLocal)

/-- Consequently the concrete filtered opposite branch cannot be upgraded to a
completed branch polynomial system with the same map. -/
theorem not_concreteOpposite_completedBranchPolynomialSystem :
    Not
      (exists B : BranchPolynomialSystem,
        B.placeNext = RoleHingeConcreteSearch.oppositePlaceNext) := by
  rintro ⟨B, hplace⟩
  exact oppositeConcrete_not_fullExactLocalEquationSystem
    (by simpa [hplace] using B.exactLocal)

/-! ## Cross-block polynomial certificate projections -/

/-- Supplied generated-point non-connector polynomial certificates, kept as a
named W10 system so the branch/period equations remain separate from the
cross-block lower-table fields. -/
structure CrossBlockPolynomialSystem
    (F : RoleHingedPeriodSearchFamily) where
  certificates :
    PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily F

namespace CrossBlockPolynomialSystem

/-- Projection to the generated-point non-connector polynomial table family. -/
def toGeneratedPointNonConnectorPolynomialTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockPolynomialSystem F) :
    PolynomialCertificateExtraction.GeneratedPointNonConnectorPolynomialTableFamily F :=
  C.certificates.toGeneratedPointNonConnectorPolynomialTableFamily

/-- Projection to normalized cross-block lower bounds. -/
def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockPolynomialSystem F) :
    PolynomialCertificateExtraction.CrossBlockLowerBounds F :=
  C.certificates.toCrossBlockLowerBounds

/-- Generated global separation supplied by the polynomial certificates at one
positive period length. -/
theorem separated
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockPolynomialSystem F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.certificates.separated k hk

/-- Exact target projection from supplied polynomial certificates. -/
theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockPolynomialSystem F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.certificates.targetUpperConstructionFiveSixteen

/-- Arbitrary-target projection from supplied polynomial certificates. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockPolynomialSystem F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.certificates.targetUpperConstructionFiveSixteenArbitrary

end CrossBlockPolynomialSystem

end RoleHingePolynomialSystemW10
end PachToth
end ErdosProblems1066

end
