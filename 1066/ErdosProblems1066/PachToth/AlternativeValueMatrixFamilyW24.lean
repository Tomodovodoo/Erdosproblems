import ErdosProblems1066.PachToth.ArbitraryNFinalSourceInhabitationW22
import ErdosProblems1066.PachToth.ConcreteValueMatrixRowPackageInhabitationW23
import ErdosProblems1066.PachToth.CandidateValueMatrixRowPackageInhabitationW23
import ErdosProblems1066.PachToth.ExplicitClosedPlacementInputPackageW20

set_option autoImplicit false

/-!
# W24 alternative value-matrix family route

The W22/W23 concrete and candidate value-matrix row packages are blocked in
this checkout by the strong role-hinge transition records.  This file keeps a
separate route that does not mention `PeriodSearchData`, period candidates, or
role-hinge transitions.

The replacement source is deliberately minimal at the generated-chain level:
a generated family, closure equations, a direct distance-value matrix proving
global separation, and the two reduced same-block metric fields required by
the current W20 input surface.  From that package we bridge cleanly to the
existing W20 source/input package and W22 `KnownBoundsRemainingData` endpoints.
-/

namespace ErdosProblems1066
namespace PachToth
namespace AlternativeValueMatrixFamilyW24

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev GeneratedChainFamily : Type :=
  GeneratedSeparationInterface.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  ExplicitClosedPlacementInputPackageW20.GeneratedChainFamilyClosures F

abbrev GeneratedGlobalSeparationAt
    (F : GeneratedChainFamily)
    (k : Nat) (hk : 0 < k) : Prop :=
  GeneratedSeparationInterface.GeneratedGlobalSeparation
    (F.O k hk) hk (F.base k hk) (F.orientation k hk)

abbrev GeneratedSameBlockIsometryAt
    (F : GeneratedChainFamily)
    (k : Nat) (hk : 0 < k) : Prop :=
  GeneratedSeparationInterface.GeneratedSameBlockIsometry
    (F.O k hk) hk (F.base k hk) (F.orientation k hk)

abbrev GeneratedBaseSameBlockIsometryAt
    (F : GeneratedChainFamily)
    (k : Nat) (hk : 0 < k) : Prop :=
  GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
    (F.base k hk)

abbrev GeneratedTransitionsPreserveSameBlockDistancesAt
    (F : GeneratedChainFamily)
    (k : Nat) (hk : 0 < k) : Prop :=
  GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
    (F.O k hk)

abbrev FullMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  ExplicitClosedPlacementInputPackageW20.ReducedMetricHypotheses F

abbrev W20SourceFields : Type :=
  ArbitraryNInputPackageRouteW21.W20SourceFields

abbrev W20ClosureReducedMetricSourceFields : Type :=
  ExplicitClosedPlacementInputPackageW20.GeneratedFamilyClosureReducedMetricSourceFields

abbrev W19InputPackage : Type :=
  ExplicitClosedPlacementInputPackageW20.W19InputPackage

abbrev W22KnownBoundsRemainingData : Type :=
  ArbitraryNFinalSourceInhabitationW22.KnownBoundsRemainingData

abbrev ExactTarget : Prop :=
  ArbitraryNFinalSourceInhabitationW22.ExactTarget

abbrev ArbitraryTarget : Prop :=
  ArbitraryNFinalSourceInhabitationW22.ArbitraryTarget

abbrev ArbitraryBound (n : Nat) : Prop :=
  ArbitraryNFinalSourceInhabitationW22.ArbitraryBound n

/-- A role-free value matrix over a generated-chain family.

The matrix records the actual generated Euclidean distance for every pair of
generated vertices and proves the `>= 1` lower bound whenever the two generated
vertices are distinct.  The final two fields are exactly the reduced
same-block metric data needed by W20; no role-hinge transition record is
required. -/
structure AlternativeValueMatrixFamily where
  family : GeneratedChainFamily
  closure : GeneratedChainFamilyClosures family
  value :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  value_eq_eucDist :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        value k hk i u j v =
          _root_.eucDist
            (GeneratedClosedChain.generatedPoint
              (family.O k hk) hk (family.base k hk)
              (family.orientation k hk) i u)
            (GeneratedClosedChain.generatedPoint
              (family.O k hk) hk (family.base k hk)
              (family.orientation k hk) j v)
  value_ge_one_of_ne :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= value k hk i u j v
  base_same_block_isometry :
    forall (k : Nat) (hk : 0 < k),
      GeneratedBaseSameBlockIsometryAt family k hk
  transition_preserves_same_block_distances :
    forall (k : Nat) (hk : 0 < k),
      GeneratedTransitionsPreserveSameBlockDistancesAt family k hk

namespace AlternativeValueMatrixFamily

/-- The direct value matrix supplies global separation for the generated
family. -/
def separated
    (A : AlternativeValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparationAt A.family k hk := by
  intro i u j v hne
  have hge := A.value_ge_one_of_ne k hk i u j v hne
  have hvalue := A.value_eq_eucDist k hk i u j v
  simpa [GeneratedGlobalSeparationAt, hvalue] using hge

/-- Reduced metric package required by W20. -/
def toReducedMetricHypotheses
    (A : AlternativeValueMatrixFamily) :
    ReducedMetricHypotheses A.family where
  metric := fun k hk =>
    { separated := A.separated k hk
      base_same_block_isometry := A.base_same_block_isometry k hk
      transition_preserves_same_block_distances :=
        A.transition_preserves_same_block_distances k hk }

/-- The same fields also expose the full generated-family metric interface. -/
def toFullMetricHypotheses
    (A : AlternativeValueMatrixFamily) :
    FullMetricHypotheses A.family where
  metric := fun k hk =>
    { separated := A.separated k hk
      same_block_isometry :=
        GeneratedSeparationInterface.same_block_isometry_of_reduced
          (A.family.O k hk) hk (A.family.base k hk)
          (A.family.orientation k hk)
          ((A.toReducedMetricHypotheses).metric k hk) }

@[simp]
theorem toReducedMetricHypotheses_metric_separated
    (A : AlternativeValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    ((A.toReducedMetricHypotheses).metric k hk).separated =
      A.separated k hk :=
  rfl

@[simp]
theorem toReducedMetricHypotheses_metric_baseSameBlock
    (A : AlternativeValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    ((A.toReducedMetricHypotheses).metric k hk).base_same_block_isometry =
      A.base_same_block_isometry k hk :=
  rfl

@[simp]
theorem toReducedMetricHypotheses_metric_transitionPreserves
    (A : AlternativeValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    ((A.toReducedMetricHypotheses).metric k hk).transition_preserves_same_block_distances =
      A.transition_preserves_same_block_distances k hk :=
  rfl

/-- Bridge to the W20 closure-plus-reduced-metric source endpoint. -/
def toW20ClosureReducedMetricSourceFields
    (A : AlternativeValueMatrixFamily) :
    W20ClosureReducedMetricSourceFields where
  family := A.family
  closure := A.closure
  reducedMetric := A.toReducedMetricHypotheses

@[simp]
theorem toW20ClosureReducedMetricSourceFields_family
    (A : AlternativeValueMatrixFamily) :
    A.toW20ClosureReducedMetricSourceFields.family = A.family :=
  rfl

@[simp]
theorem toW20ClosureReducedMetricSourceFields_closure
    (A : AlternativeValueMatrixFamily) :
    A.toW20ClosureReducedMetricSourceFields.closure = A.closure :=
  rfl

@[simp]
theorem toW20ClosureReducedMetricSourceFields_metric
    (A : AlternativeValueMatrixFamily) :
    A.toW20ClosureReducedMetricSourceFields.reducedMetric =
      A.toReducedMetricHypotheses :=
  rfl

/-- Bridge to the raw W20 source-field endpoint used by W21. -/
def toW20SourceFields
    (A : AlternativeValueMatrixFamily) :
    W20SourceFields where
  O := A.family.O
  base := A.family.base
  orientation := A.family.orientation
  closure := A.closure
  separated := A.separated
  base_same_block_isometry := A.base_same_block_isometry
  transition_preserves_same_block_distances :=
    A.transition_preserves_same_block_distances

@[simp]
theorem toW20SourceFields_family
    (A : AlternativeValueMatrixFamily) :
    A.toW20SourceFields.family = A.family := by
  cases A
  rfl

/-- Bridge to the current W19 input package endpoint. -/
def toInputPackage
    (A : AlternativeValueMatrixFamily) :
    W19InputPackage :=
  A.toW20ClosureReducedMetricSourceFields.toInputPackage

@[simp]
theorem toInputPackage_family
    (A : AlternativeValueMatrixFamily) :
    A.toInputPackage.family = A.family :=
  rfl

@[simp]
theorem toInputPackage_closure
    (A : AlternativeValueMatrixFamily) :
    A.toInputPackage.closure = A.closure :=
  rfl

@[simp]
theorem toInputPackage_metric
    (A : AlternativeValueMatrixFamily) :
    A.toInputPackage.metric = A.toReducedMetricHypotheses :=
  rfl

/-- Bridge to the W22 `KnownBoundsRemainingData` endpoint. -/
def toKnownBoundsRemainingData
    (A : AlternativeValueMatrixFamily) :
    W22KnownBoundsRemainingData :=
  A.toInputPackage

theorem nonempty_knownBoundsRemainingData
    (A : AlternativeValueMatrixFamily) :
    Nonempty W22KnownBoundsRemainingData :=
  Nonempty.intro A.toKnownBoundsRemainingData

/-- Exact target through the W20 input package. -/
theorem exactTarget
    (A : AlternativeValueMatrixFamily) :
    ExactTarget :=
  A.toInputPackage.targetUpperConstructionFiveSixteen

/-- Arbitrary target through the W22 checked-remainder endpoint. -/
theorem arbitraryTarget_checkedRemainders
    (A : AlternativeValueMatrixFamily) :
    ArbitraryTarget :=
  ArbitraryNFinalSourceInhabitationW22.arbitraryTarget_of_knownBoundsRemainingData_checkedRemainders
    A.nonempty_knownBoundsRemainingData

theorem upper_bound_five_sixteen_arbitrary_checkedRemainders
    (A : AlternativeValueMatrixFamily) (n : Nat) :
    ArbitraryBound n :=
  A.arbitraryTarget_checkedRemainders n

/-- Any existing W19 input package can be viewed as the alternative value
matrix by choosing its actual generated distances as the values.  This is an
adapter, not a new construction. -/
def ofInputPackage
    (P : W19InputPackage) :
    AlternativeValueMatrixFamily where
  family := P.family
  closure := P.closure
  value := fun k hk i u j v =>
    _root_.eucDist
      (GeneratedClosedChain.generatedPoint
        (P.family.O k hk) hk (P.family.base k hk)
        (P.family.orientation k hk) i u)
      (GeneratedClosedChain.generatedPoint
        (P.family.O k hk) hk (P.family.base k hk)
        (P.family.orientation k hk) j v)
  value_eq_eucDist := by
    intro _k _hk _i _u _j _v
    rfl
  value_ge_one_of_ne := by
    intro k hk i u j v hne
    exact (P.metric.metric k hk).separated i u j v hne
  base_same_block_isometry := fun k hk =>
    (P.metric.metric k hk).base_same_block_isometry
  transition_preserves_same_block_distances := fun k hk =>
    (P.metric.metric k hk).transition_preserves_same_block_distances

theorem nonempty_alternativeValueMatrixFamily_iff_knownBoundsRemainingData :
    Nonempty AlternativeValueMatrixFamily <-> Nonempty W22KnownBoundsRemainingData := by
  constructor
  · intro h
    cases h with
    | intro A => exact A.nonempty_knownBoundsRemainingData
  · intro h
    cases h with
    | intro P => exact Nonempty.intro (ofInputPackage P)

/-- Existing concrete W22 value matrices factor through this role-free
adapter only after they have already produced the W19 input package. -/
def ofConcreteValueMatrixFamily
    (C : ConcreteValueMatrixToInputPackageW21.ConcreteValueMatrixFamily) :
    AlternativeValueMatrixFamily :=
  ofInputPackage
    (ConcreteValueMatrixToInputPackageW21.inputPackageOfConcreteValueMatrixFamily
      C)

/-- Existing concrete W22 row packages also factor through the same W19 input
package adapter. -/
def ofConcreteRowPackage
    (P : ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage) :
    AlternativeValueMatrixFamily :=
  ofConcreteValueMatrixFamily P.toConcreteValueMatrixFamily

end AlternativeValueMatrixFamily

/-! ## Current direct concrete/candidate value-matrix blockers -/

theorem not_nonempty_concreteRowPackage :
    Not
      (Nonempty
        ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage) :=
  ConcreteValueMatrixRowPackageInhabitationW23.not_nonempty_rowPackage

theorem not_nonempty_concreteValueMatrixFamily :
    Not
      (Nonempty
        ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixFamily) :=
  ConcreteValueMatrixRowPackageInhabitationW23.no_concreteValueMatrixFamily_from_w18RowFamilies

theorem not_nonempty_candidateValueMatrixRowPackage :
    Not
      (Nonempty
        ConcreteValueMatrixFamilyInhabitationW22.CandidateValueMatrixRowPackage) :=
  CandidateValueMatrixRowPackageInhabitationW23.not_nonempty_candidateValueMatrixRowPackage

theorem not_nonempty_candidateValueMatrixFamily :
    Not
      (Nonempty
        ConcreteValueMatrixFamilyInhabitationW22.CandidateValueMatrixFamily) :=
  CandidateValueMatrixRowPackageInhabitationW23.not_nonempty_candidateValueMatrixFamily

/-- Public W20 source-field bridge from the alternative value-matrix family. -/
def w20SourceFieldsOfAlternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    W20SourceFields :=
  A.toW20SourceFields

/-- Public W20 closure/reduced-metric source bridge from the alternative
value-matrix family. -/
def w20ClosureReducedMetricSourceFieldsOfAlternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    W20ClosureReducedMetricSourceFields :=
  A.toW20ClosureReducedMetricSourceFields

/-- Public W22 remaining-data bridge from the alternative value-matrix family. -/
def knownBoundsRemainingDataOfAlternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    W22KnownBoundsRemainingData :=
  A.toKnownBoundsRemainingData

theorem nonempty_knownBoundsRemainingData_of_alternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    Nonempty W22KnownBoundsRemainingData :=
  A.nonempty_knownBoundsRemainingData

theorem exactTarget_of_alternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    ExactTarget :=
  A.exactTarget

theorem arbitraryTarget_of_alternativeValueMatrixFamily_checkedRemainders
    (A : AlternativeValueMatrixFamily) :
    ArbitraryTarget :=
  A.arbitraryTarget_checkedRemainders

theorem upper_bound_five_sixteen_arbitrary_of_alternativeValueMatrixFamily_checkedRemainders
    (A : AlternativeValueMatrixFamily) (n : Nat) :
    ArbitraryBound n :=
  A.upper_bound_five_sixteen_arbitrary_checkedRemainders n

end

end AlternativeValueMatrixFamilyW24
end PachToth

namespace Verified

abbrev PachTothW24AlternativeValueMatrixFamily : Type :=
  PachToth.AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily

abbrev PachTothW24KnownBoundsRemainingData : Type :=
  PachToth.AlternativeValueMatrixFamilyW24.W22KnownBoundsRemainingData

theorem pachtoth_w24_nonempty_alternativeValueMatrixFamily_iff_knownBoundsRemainingData :
    Nonempty PachTothW24AlternativeValueMatrixFamily <->
      Nonempty PachTothW24KnownBoundsRemainingData :=
  PachToth.AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily.nonempty_alternativeValueMatrixFamily_iff_knownBoundsRemainingData

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w24_alternativeValueMatrixFamily
    (A : PachTothW24AlternativeValueMatrixFamily) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.AlternativeValueMatrixFamilyW24.upper_bound_five_sixteen_arbitrary_of_alternativeValueMatrixFamily_checkedRemainders
    A n

end Verified
end ErdosProblems1066
