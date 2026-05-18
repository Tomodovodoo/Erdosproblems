import ErdosProblems1066.PachToth.LengthTwoThreeCaseW10
import ErdosProblems1066.PachToth.ArbitraryNClosureCandidate
import ErdosProblems1066.PachToth.EventualRoleHingeClosure

set_option autoImplicit false

/-!
# W11 length-four and length-five small-case surfaces

This module extends the checked small-length non-connector surface past
`LengthTwoThreeCaseW10`.  It enumerates the missing upper-triangle
polynomial inequalities for `k = 4` and `k = 5`, repackages those fields into
the existing value-matrix and cross-block lower-table interfaces, and exposes
the exact-block/eventual-route projections that are already available from
the imported route modules.

No search result is asserted here.  The k=4 and k=5 facts remain explicit
input fields, and the eventual arbitrary route still asks for the exact block
targets below its block threshold.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LengthFourFiveCaseW11

open ConcreteValueCertificateExamples

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  ConcreteValueCertificateExamples.RoleHingedPeriodSearchFamily

abbrev PeriodSearchData :=
  ConcreteNonConnectorValueMatrix.PeriodSearchData

abbrev PeriodCandidateFamily :=
  ConcreteNonConnectorValueMatrix.PeriodCandidateFamily

abbrev LocalVertexIndex :=
  ConcreteValueCertificateExamples.LocalVertexIndex

abbrev UpperTrianglePosition :=
  ConcreteValueCertificateExamples.UpperTrianglePosition

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  ConcreteValueCertificateExamples.PositionNonConnector hk p

abbrev NonConnectorValueMatrix :=
  ConcreteValueCertificateExamples.NonConnectorValueMatrix

abbrev NonConnectorLowerTable :=
  ConcreteNonConnectorValueMatrix.NonConnectorLowerTable

abbrev PositionValueCertificate :=
  ConcreteValueCertificateExamples.PositionValueCertificate

abbrev UpperTriangleNonConnectorSqValueTable :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueTable

abbrev UpperTriangleNonConnectorSqValueVectorCertificate :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueVectorCertificate

abbrev UpperTriangleNonConnectorSqValueListCertificate :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueListCertificate

def fourPositive : 0 < 4 :=
  Nat.zero_lt_succ 3

def fivePositive : 0 < 5 :=
  Nat.zero_lt_succ 4

def lengthFourPosition01
    (u v : LocalVertexIndex) : UpperTrianglePosition 4 where
  left := 0
  leftVertex := u
  right := 1
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFourPosition02
    (u v : LocalVertexIndex) : UpperTrianglePosition 4 where
  left := 0
  leftVertex := u
  right := 2
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFourPosition03
    (u v : LocalVertexIndex) : UpperTrianglePosition 4 where
  left := 0
  leftVertex := u
  right := 3
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFourPosition12
    (u v : LocalVertexIndex) : UpperTrianglePosition 4 where
  left := 1
  leftVertex := u
  right := 2
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFourPosition13
    (u v : LocalVertexIndex) : UpperTrianglePosition 4 where
  left := 1
  leftVertex := u
  right := 3
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFourPosition23
    (u v : LocalVertexIndex) : UpperTrianglePosition 4 where
  left := 2
  leftVertex := u
  right := 3
  rightVertex := v
  left_lt_right := by
    norm_num

abbrev LengthFourMissingNonConnectorInequality01
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fourPositive (lengthFourPosition01 u v) ->
    1 <= (lengthFourPosition01 u v).polynomial F fourPositive

abbrev LengthFourMissingNonConnectorInequality02
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fourPositive (lengthFourPosition02 u v) ->
    1 <= (lengthFourPosition02 u v).polynomial F fourPositive

abbrev LengthFourMissingNonConnectorInequality03
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fourPositive (lengthFourPosition03 u v) ->
    1 <= (lengthFourPosition03 u v).polynomial F fourPositive

abbrev LengthFourMissingNonConnectorInequality12
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fourPositive (lengthFourPosition12 u v) ->
    1 <= (lengthFourPosition12 u v).polynomial F fourPositive

abbrev LengthFourMissingNonConnectorInequality13
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fourPositive (lengthFourPosition13 u v) ->
    1 <= (lengthFourPosition13 u v).polynomial F fourPositive

abbrev LengthFourMissingNonConnectorInequality23
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fourPositive (lengthFourPosition23 u v) ->
    1 <= (lengthFourPosition23 u v).polynomial F fourPositive

/-- The full length-four ledger: six upper-triangle block pairs, each with
one inequality for every pair of local vertices. -/
structure LengthFourMissingNonConnectorInequalities
    (F : RoleHingedPeriodSearchFamily) where
  inequality01 :
    forall u v : LocalVertexIndex,
      LengthFourMissingNonConnectorInequality01 F u v
  inequality02 :
    forall u v : LocalVertexIndex,
      LengthFourMissingNonConnectorInequality02 F u v
  inequality03 :
    forall u v : LocalVertexIndex,
      LengthFourMissingNonConnectorInequality03 F u v
  inequality12 :
    forall u v : LocalVertexIndex,
      LengthFourMissingNonConnectorInequality12 F u v
  inequality13 :
    forall u v : LocalVertexIndex,
      LengthFourMissingNonConnectorInequality13 F u v
  inequality23 :
    forall u v : LocalVertexIndex,
      LengthFourMissingNonConnectorInequality23 F u v

theorem lengthFour_polynomial_ge_one_of_missing
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFourMissingNonConnectorInequalities F)
    (p : UpperTrianglePosition 4)
    (hp : PositionNonConnector fourPositive p) :
    1 <= p.polynomial F fourPositive := by
  cases p with
  | mk left leftVertex right rightVertex left_lt_right =>
      fin_cases left <;> fin_cases right
      all_goals simp at left_lt_right
      all_goals first
        | omega
        | exact H.inequality01 leftVertex rightVertex hp
        | exact H.inequality02 leftVertex rightVertex hp
        | exact H.inequality03 leftVertex rightVertex hp
        | exact H.inequality12 leftVertex rightVertex hp
        | exact H.inequality13 leftVertex rightVertex hp
        | exact H.inequality23 leftVertex rightVertex hp

def lengthFourMatrixOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFourMissingNonConnectorInequalities F) :
    NonConnectorValueMatrix F 4 fourPositive :=
  matrixOfPerPositionPolynomialInequalities F 4 fourPositive
    (lengthFour_polynomial_ge_one_of_missing F H)

def lengthFourPositionValueCertificateOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFourMissingNonConnectorInequalities F) :
    PositionValueCertificate F 4 fourPositive :=
  (lengthFourMatrixOfMissingInequalities F H).toPositionValueCertificate

def lengthFourSqValueTableOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFourMissingNonConnectorInequalities F) :
    UpperTriangleNonConnectorSqValueTable F 4 fourPositive :=
  (lengthFourMatrixOfMissingInequalities F H).toSqValueTable

def lengthFourLowerTableOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFourMissingNonConnectorInequalities F) :
    NonConnectorLowerTable F 4 fourPositive :=
  (lengthFourMatrixOfMissingInequalities F H).toNonConnectorLowerTable

def lengthFourMatrixOfVectorCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueVectorCertificate F 4 fourPositive) :
    NonConnectorValueMatrix F 4 fourPositive :=
  matrixOfVectorCertificate C

def lengthFourMatrixOfListCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueListCertificate F 4 fourPositive) :
    NonConnectorValueMatrix F 4 fourPositive :=
  matrixOfListCertificate C

def lengthFivePosition01
    (u v : LocalVertexIndex) : UpperTrianglePosition 5 where
  left := 0
  leftVertex := u
  right := 1
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFivePosition02
    (u v : LocalVertexIndex) : UpperTrianglePosition 5 where
  left := 0
  leftVertex := u
  right := 2
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFivePosition03
    (u v : LocalVertexIndex) : UpperTrianglePosition 5 where
  left := 0
  leftVertex := u
  right := 3
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFivePosition04
    (u v : LocalVertexIndex) : UpperTrianglePosition 5 where
  left := 0
  leftVertex := u
  right := 4
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFivePosition12
    (u v : LocalVertexIndex) : UpperTrianglePosition 5 where
  left := 1
  leftVertex := u
  right := 2
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFivePosition13
    (u v : LocalVertexIndex) : UpperTrianglePosition 5 where
  left := 1
  leftVertex := u
  right := 3
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFivePosition14
    (u v : LocalVertexIndex) : UpperTrianglePosition 5 where
  left := 1
  leftVertex := u
  right := 4
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFivePosition23
    (u v : LocalVertexIndex) : UpperTrianglePosition 5 where
  left := 2
  leftVertex := u
  right := 3
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFivePosition24
    (u v : LocalVertexIndex) : UpperTrianglePosition 5 where
  left := 2
  leftVertex := u
  right := 4
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthFivePosition34
    (u v : LocalVertexIndex) : UpperTrianglePosition 5 where
  left := 3
  leftVertex := u
  right := 4
  rightVertex := v
  left_lt_right := by
    norm_num

abbrev LengthFiveMissingNonConnectorInequality01
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fivePositive (lengthFivePosition01 u v) ->
    1 <= (lengthFivePosition01 u v).polynomial F fivePositive

abbrev LengthFiveMissingNonConnectorInequality02
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fivePositive (lengthFivePosition02 u v) ->
    1 <= (lengthFivePosition02 u v).polynomial F fivePositive

abbrev LengthFiveMissingNonConnectorInequality03
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fivePositive (lengthFivePosition03 u v) ->
    1 <= (lengthFivePosition03 u v).polynomial F fivePositive

abbrev LengthFiveMissingNonConnectorInequality04
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fivePositive (lengthFivePosition04 u v) ->
    1 <= (lengthFivePosition04 u v).polynomial F fivePositive

abbrev LengthFiveMissingNonConnectorInequality12
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fivePositive (lengthFivePosition12 u v) ->
    1 <= (lengthFivePosition12 u v).polynomial F fivePositive

abbrev LengthFiveMissingNonConnectorInequality13
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fivePositive (lengthFivePosition13 u v) ->
    1 <= (lengthFivePosition13 u v).polynomial F fivePositive

abbrev LengthFiveMissingNonConnectorInequality14
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fivePositive (lengthFivePosition14 u v) ->
    1 <= (lengthFivePosition14 u v).polynomial F fivePositive

abbrev LengthFiveMissingNonConnectorInequality23
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fivePositive (lengthFivePosition23 u v) ->
    1 <= (lengthFivePosition23 u v).polynomial F fivePositive

abbrev LengthFiveMissingNonConnectorInequality24
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fivePositive (lengthFivePosition24 u v) ->
    1 <= (lengthFivePosition24 u v).polynomial F fivePositive

abbrev LengthFiveMissingNonConnectorInequality34
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector fivePositive (lengthFivePosition34 u v) ->
    1 <= (lengthFivePosition34 u v).polynomial F fivePositive

/-- The full length-five ledger: ten upper-triangle block pairs, each with
one inequality for every pair of local vertices. -/
structure LengthFiveMissingNonConnectorInequalities
    (F : RoleHingedPeriodSearchFamily) where
  inequality01 :
    forall u v : LocalVertexIndex,
      LengthFiveMissingNonConnectorInequality01 F u v
  inequality02 :
    forall u v : LocalVertexIndex,
      LengthFiveMissingNonConnectorInequality02 F u v
  inequality03 :
    forall u v : LocalVertexIndex,
      LengthFiveMissingNonConnectorInequality03 F u v
  inequality04 :
    forall u v : LocalVertexIndex,
      LengthFiveMissingNonConnectorInequality04 F u v
  inequality12 :
    forall u v : LocalVertexIndex,
      LengthFiveMissingNonConnectorInequality12 F u v
  inequality13 :
    forall u v : LocalVertexIndex,
      LengthFiveMissingNonConnectorInequality13 F u v
  inequality14 :
    forall u v : LocalVertexIndex,
      LengthFiveMissingNonConnectorInequality14 F u v
  inequality23 :
    forall u v : LocalVertexIndex,
      LengthFiveMissingNonConnectorInequality23 F u v
  inequality24 :
    forall u v : LocalVertexIndex,
      LengthFiveMissingNonConnectorInequality24 F u v
  inequality34 :
    forall u v : LocalVertexIndex,
      LengthFiveMissingNonConnectorInequality34 F u v

theorem lengthFive_polynomial_ge_one_of_missing
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFiveMissingNonConnectorInequalities F)
    (p : UpperTrianglePosition 5)
    (hp : PositionNonConnector fivePositive p) :
    1 <= p.polynomial F fivePositive := by
  cases p with
  | mk left leftVertex right rightVertex left_lt_right =>
      fin_cases left <;> fin_cases right
      all_goals simp at left_lt_right
      all_goals first
        | omega
        | exact H.inequality01 leftVertex rightVertex hp
        | exact H.inequality02 leftVertex rightVertex hp
        | exact H.inequality03 leftVertex rightVertex hp
        | exact H.inequality04 leftVertex rightVertex hp
        | exact H.inequality12 leftVertex rightVertex hp
        | exact H.inequality13 leftVertex rightVertex hp
        | exact H.inequality14 leftVertex rightVertex hp
        | exact H.inequality23 leftVertex rightVertex hp
        | exact H.inequality24 leftVertex rightVertex hp
        | exact H.inequality34 leftVertex rightVertex hp

def lengthFiveMatrixOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFiveMissingNonConnectorInequalities F) :
    NonConnectorValueMatrix F 5 fivePositive :=
  matrixOfPerPositionPolynomialInequalities F 5 fivePositive
    (lengthFive_polynomial_ge_one_of_missing F H)

def lengthFivePositionValueCertificateOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFiveMissingNonConnectorInequalities F) :
    PositionValueCertificate F 5 fivePositive :=
  (lengthFiveMatrixOfMissingInequalities F H).toPositionValueCertificate

def lengthFiveSqValueTableOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFiveMissingNonConnectorInequalities F) :
    UpperTriangleNonConnectorSqValueTable F 5 fivePositive :=
  (lengthFiveMatrixOfMissingInequalities F H).toSqValueTable

def lengthFiveLowerTableOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFiveMissingNonConnectorInequalities F) :
    NonConnectorLowerTable F 5 fivePositive :=
  (lengthFiveMatrixOfMissingInequalities F H).toNonConnectorLowerTable

def lengthFiveMatrixOfVectorCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueVectorCertificate F 5 fivePositive) :
    NonConnectorValueMatrix F 5 fivePositive :=
  matrixOfVectorCertificate C

def lengthFiveMatrixOfListCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueListCertificate F 5 fivePositive) :
    NonConnectorValueMatrix F 5 fivePositive :=
  matrixOfListCertificate C

/-! ## Joint k=4/k=5 value and lower-table adapters -/

structure LengthFourFiveMissingNonConnectorInequalities
    (F : RoleHingedPeriodSearchFamily) where
  lengthFour : LengthFourMissingNonConnectorInequalities F
  lengthFive : LengthFiveMissingNonConnectorInequalities F

structure LengthFourFiveValueMatrices
    (F : RoleHingedPeriodSearchFamily) where
  lengthFour : NonConnectorValueMatrix F 4 fourPositive
  lengthFive : NonConnectorValueMatrix F 5 fivePositive

structure LengthFourFiveLowerTables
    (F : RoleHingedPeriodSearchFamily) where
  lengthFour : NonConnectorLowerTable F 4 fourPositive
  lengthFive : NonConnectorLowerTable F 5 fivePositive

def lengthFourFiveMatricesOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFourFiveMissingNonConnectorInequalities F) :
    LengthFourFiveValueMatrices F where
  lengthFour := lengthFourMatrixOfMissingInequalities F H.lengthFour
  lengthFive := lengthFiveMatrixOfMissingInequalities F H.lengthFive

def lengthFourFiveLowerTablesOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFourFiveMissingNonConnectorInequalities F) :
    LengthFourFiveLowerTables F where
  lengthFour := lengthFourLowerTableOfMissingInequalities F H.lengthFour
  lengthFive := lengthFiveLowerTableOfMissingInequalities F H.lengthFive

theorem lengthFour_missing_localVertexPair_count :
    6 * 16 * 16 = 1536 := by
  norm_num

theorem lengthFive_missing_localVertexPair_count :
    10 * 16 * 16 = 2560 := by
  norm_num

/-! ## Fixed period/cross-block candidate certificates -/

/-- One fixed block count with period data and its checked non-connector
cross-block lower table. -/
structure FixedPeriodNonConnectorLowerTable
    (periodSearch : PeriodSearchData)
    (k : Nat) (hk : 0 < k) where
  table : NonConnectorLowerTable
    periodSearch.toRoleHingedPeriodSearchFamily k hk

namespace FixedPeriodNonConnectorLowerTable

def generatedGlobalSeparation
    {periodSearch : PeriodSearchData}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodNonConnectorLowerTable periodSearch k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      periodSearch.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (periodSearch.orientation k hk) :=
  C.table.generatedGlobalSeparation

def reducedMetricHypotheses
    {periodSearch : PeriodSearchData}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodNonConnectorLowerTable periodSearch k hk) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      periodSearch.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (periodSearch.orientation k hk) :=
  GeneratedMetricClosure.generatedReducedMetricHypotheses
    periodSearch.transitions hk (periodSearch.orientation k hk)
    C.generatedGlobalSeparation

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {periodSearch : PeriodSearchData}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodNonConnectorLowerTable periodSearch k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteenAt_exactBlock_reduced
      periodSearch.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (periodSearch.orientation k hk)
      (periodSearch.generatedPeriod k hk)
      C.reducedMetricHypotheses

end FixedPeriodNonConnectorLowerTable

abbrev LengthFourPeriodNonConnectorLowerTable
    (periodSearch : PeriodSearchData) :=
  FixedPeriodNonConnectorLowerTable periodSearch 4 fourPositive

abbrev LengthFivePeriodNonConnectorLowerTable
    (periodSearch : PeriodSearchData) :=
  FixedPeriodNonConnectorLowerTable periodSearch 5 fivePositive

def lengthFourPeriodLowerTableOfMissingInequalities
    (periodSearch : PeriodSearchData)
    (H :
      LengthFourMissingNonConnectorInequalities
        periodSearch.toRoleHingedPeriodSearchFamily) :
    LengthFourPeriodNonConnectorLowerTable periodSearch where
  table :=
    lengthFourLowerTableOfMissingInequalities
      periodSearch.toRoleHingedPeriodSearchFamily H

def lengthFivePeriodLowerTableOfMissingInequalities
    (periodSearch : PeriodSearchData)
    (H :
      LengthFiveMissingNonConnectorInequalities
        periodSearch.toRoleHingedPeriodSearchFamily) :
    LengthFivePeriodNonConnectorLowerTable periodSearch where
  table :=
    lengthFiveLowerTableOfMissingInequalities
      periodSearch.toRoleHingedPeriodSearchFamily H

theorem targetUpperConstructionFiveSixteenAt_lengthFour_exactBlock
    {periodSearch : PeriodSearchData}
    (C : LengthFourPeriodNonConnectorLowerTable periodSearch) :
    targetUpperConstructionFiveSixteenAt (16 * 4) :=
  C.targetUpperConstructionFiveSixteenAt_exactBlock

theorem targetUpperConstructionFiveSixteenAt_lengthFive_exactBlock
    {periodSearch : PeriodSearchData}
    (C : LengthFivePeriodNonConnectorLowerTable periodSearch) :
    targetUpperConstructionFiveSixteenAt (16 * 5) :=
  C.targetUpperConstructionFiveSixteenAt_exactBlock

structure LengthFourFivePeriodNonConnectorLowerTables
    (periodSearch : PeriodSearchData) where
  lengthFour : LengthFourPeriodNonConnectorLowerTable periodSearch
  lengthFive : LengthFivePeriodNonConnectorLowerTable periodSearch

def lengthFourFivePeriodLowerTablesOfMissingInequalities
    (periodSearch : PeriodSearchData)
    (H :
      LengthFourFiveMissingNonConnectorInequalities
        periodSearch.toRoleHingedPeriodSearchFamily) :
    LengthFourFivePeriodNonConnectorLowerTables periodSearch where
  lengthFour :=
    lengthFourPeriodLowerTableOfMissingInequalities
      periodSearch H.lengthFour
  lengthFive :=
    lengthFivePeriodLowerTableOfMissingInequalities
      periodSearch H.lengthFive

structure LengthFourFiveExactBlockTargets where
  lengthFour : targetUpperConstructionFiveSixteenAt (16 * 4)
  lengthFive : targetUpperConstructionFiveSixteenAt (16 * 5)

def LengthFourFivePeriodNonConnectorLowerTables.toExactBlockTargets
    {periodSearch : PeriodSearchData}
    (C : LengthFourFivePeriodNonConnectorLowerTables periodSearch) :
    LengthFourFiveExactBlockTargets where
  lengthFour := C.lengthFour.targetUpperConstructionFiveSixteenAt_exactBlock
  lengthFive := C.lengthFive.targetUpperConstructionFiveSixteenAt_exactBlock

/-- One fixed candidate period count with its non-connector lower table. -/
structure FixedCandidateNonConnectorLowerTable
    (period : PeriodCandidateFamily)
    (k : Nat) (hk : 0 < k) where
  table : NonConnectorLowerTable period.toRoleHingedPeriodSearchFamily k hk

namespace FixedCandidateNonConnectorLowerTable

def generatedGlobalSeparation
    {period : PeriodCandidateFamily}
    {k : Nat} {hk : 0 < k}
    (C : FixedCandidateNonConnectorLowerTable period k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      (ConcretePeriodCandidateSearch.transitionObligationsOfFacts
        period.transitions)
      hk
      BaseTransitionRealization.exactBase
      (period.orientation k hk) := by
  exact C.table.generatedGlobalSeparation

def reducedMetricHypotheses
    {period : PeriodCandidateFamily}
    {k : Nat} {hk : 0 < k}
    (C : FixedCandidateNonConnectorLowerTable period k hk) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      (ConcretePeriodCandidateSearch.transitionObligationsOfFacts
        period.transitions)
      hk
      BaseTransitionRealization.exactBase
      (period.orientation k hk) :=
  GeneratedMetricClosure.generatedReducedMetricHypotheses
    period.transitions.toRoleHingeTransitions hk
    (period.orientation k hk)
    C.generatedGlobalSeparation

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {period : PeriodCandidateFamily}
    {k : Nat} {hk : 0 < k}
    (C : FixedCandidateNonConnectorLowerTable period k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteenAt_exactBlock_reduced
      (ConcretePeriodCandidateSearch.transitionObligationsOfFacts
        period.transitions)
      hk
      BaseTransitionRealization.exactBase
      (period.orientation k hk)
      ((period.candidate k hk).generatedPeriod)
      C.reducedMetricHypotheses

end FixedCandidateNonConnectorLowerTable

abbrev LengthFourCandidateNonConnectorLowerTable
    (period : PeriodCandidateFamily) :=
  FixedCandidateNonConnectorLowerTable period 4 fourPositive

abbrev LengthFiveCandidateNonConnectorLowerTable
    (period : PeriodCandidateFamily) :=
  FixedCandidateNonConnectorLowerTable period 5 fivePositive

def lengthFourCandidateLowerTableOfMissingInequalities
    (period : PeriodCandidateFamily)
    (H :
      LengthFourMissingNonConnectorInequalities
        period.toRoleHingedPeriodSearchFamily) :
    LengthFourCandidateNonConnectorLowerTable period where
  table :=
    lengthFourLowerTableOfMissingInequalities
      period.toRoleHingedPeriodSearchFamily H

def lengthFiveCandidateLowerTableOfMissingInequalities
    (period : PeriodCandidateFamily)
    (H :
      LengthFiveMissingNonConnectorInequalities
        period.toRoleHingedPeriodSearchFamily) :
    LengthFiveCandidateNonConnectorLowerTable period where
  table :=
    lengthFiveLowerTableOfMissingInequalities
      period.toRoleHingedPeriodSearchFamily H

theorem targetUpperConstructionFiveSixteenAt_lengthFour_candidateExactBlock
    {period : PeriodCandidateFamily}
    (C : LengthFourCandidateNonConnectorLowerTable period) :
    targetUpperConstructionFiveSixteenAt (16 * 4) :=
  C.targetUpperConstructionFiveSixteenAt_exactBlock

theorem targetUpperConstructionFiveSixteenAt_lengthFive_candidateExactBlock
    {period : PeriodCandidateFamily}
    (C : LengthFiveCandidateNonConnectorLowerTable period) :
    targetUpperConstructionFiveSixteenAt (16 * 5) :=
  C.targetUpperConstructionFiveSixteenAt_exactBlock

structure LengthFourFiveCandidateNonConnectorLowerTables
    (period : PeriodCandidateFamily) where
  lengthFour : LengthFourCandidateNonConnectorLowerTable period
  lengthFive : LengthFiveCandidateNonConnectorLowerTable period

def lengthFourFiveCandidateLowerTablesOfMissingInequalities
    (period : PeriodCandidateFamily)
    (H :
      LengthFourFiveMissingNonConnectorInequalities
        period.toRoleHingedPeriodSearchFamily) :
    LengthFourFiveCandidateNonConnectorLowerTables period where
  lengthFour :=
    lengthFourCandidateLowerTableOfMissingInequalities
      period H.lengthFour
  lengthFive :=
    lengthFiveCandidateLowerTableOfMissingInequalities
      period H.lengthFive

def LengthFourFiveCandidateNonConnectorLowerTables.toExactBlockTargets
    {period : PeriodCandidateFamily}
    (C : LengthFourFiveCandidateNonConnectorLowerTables period) :
    LengthFourFiveExactBlockTargets where
  lengthFour := C.lengthFour.targetUpperConstructionFiveSixteenAt_exactBlock
  lengthFive := C.lengthFive.targetUpperConstructionFiveSixteenAt_exactBlock

/-! ## Eventual route surface with explicit lower block fields -/

/-- Exact block targets below block threshold six.  The k=4 and k=5 fields
are the new fields supplied by this module; the k=1,2,3 fields remain
separate inputs rather than being inferred from the length-four/five data. -/
structure ExactBlockTargetsBelowSix where
  lengthOne : targetUpperConstructionFiveSixteenAt (16 * 1)
  lengthTwo : targetUpperConstructionFiveSixteenAt (16 * 2)
  lengthThree : targetUpperConstructionFiveSixteenAt (16 * 3)
  lengthFourFive : LengthFourFiveExactBlockTargets

def ExactBlockTargetsBelowSix.exactBlock
    (C : ExactBlockTargetsBelowSix) :
    forall k : Nat, k < 6 -> 0 < k ->
      targetUpperConstructionFiveSixteenAt (16 * k) := by
  intro k hk6 hk0
  have hk_cases : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 := by
    omega
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl
  · exact C.lengthOne
  · exact C.lengthTwo
  · exact C.lengthThree
  · exact C.lengthFourFive.lengthFour
  · exact C.lengthFourFive.lengthFive

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualBelowSix
    (O : EventualRoleHingeClosure.EventualFiniteCertificateObligations 6)
    (C : ExactBlockTargetsBelowSix) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ArbitraryNClosureCandidate.arbitrary_of_eventualFiniteCertificates_exactBlockSmallCases
    O C.exactBlock

theorem lengthFourFive_remainder_arithmetic_sample :
    Arithmetic.ceilDiv (5 * (16 * 5 + 15)) 16 = 30 := by
  norm_num [Arithmetic.ceilDiv]

theorem smallCase_remainder_four :
    targetUpperConstructionFiveSixteenAt 4 :=
  SmallCaseCertificates.targetUpperConstructionFiveSixteenAt_r4

theorem smallCase_remainder_five :
    targetUpperConstructionFiveSixteenAt 5 :=
  SmallCaseCertificates.targetUpperConstructionFiveSixteenAt_r5

end

end LengthFourFiveCaseW11
end PachToth
end ErdosProblems1066
