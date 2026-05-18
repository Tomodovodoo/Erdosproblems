import ErdosProblems1066.Swanepoel.ConcreteW23ComponentsInhabitationW26
import ErdosProblems1066.Swanepoel.NoCutConcreteEliminationW26

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W27 pointwise cut side-card/pay-for-cut concrete fields

This worker keeps the cut-side arithmetic field pointwise.  A supplied
side-card family is converted to the W25 pay-for-cut family by the W25
equivalence, then used as the no-cut component consumed by the W26 concrete
W23 component package.  The tail remains an actual W23 tail over that no-cut
component, rather than an endpoint-only lower-bound wrapper.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CutSideCardPayForCutConcreteW27

open CutVertexInterface
open MinimalGraphFacts

noncomputable section

abbrev MinimalFailurePointwiseSideCardFamily : Prop :=
  CutVertexContradictionInhabitationW25.MinimalFailurePointwiseSideCardFamily

abbrev MinimalFailurePointwisePayForCutFamily : Prop :=
  CutVertexContradictionInhabitationW25.MinimalFailurePointwisePayForCutFamily

abbrev MinimalFailureCutVertexContradictionFamily : Prop :=
  CutVertexContradictionInhabitationW25.MinimalFailureCutVertexContradictionFamily

abbrev MinimalCutVertexBlockerExists : Prop :=
  CutVertexContradictionInhabitationW25.MinimalCutVertexBlockerExists

abbrev ConcreteNoCutTheorem : Prop :=
  ConcreteW23ComponentsInhabitationW26.ConcreteNoCutTheorem

abbrev ConcreteW23Components : Type 1 :=
  ConcreteW23ComponentsInhabitationW26.ConcreteW23Components

abbrev ConcreteW23ComponentsExceptNoCut
    (noCut : ConcreteNoCutTheorem) : Type 1 :=
  ConcreteW23ComponentsInhabitationW26.ConcreteW23ComponentsExceptNoCut noCut

abbrev Target : Prop :=
  ConcreteW23ComponentsInhabitationW26.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  ConcreteW23ComponentsInhabitationW26.LowerBoundAt n C

def payForCutFamilyOfSideCardFamily
    (H : MinimalFailurePointwiseSideCardFamily) :
    MinimalFailurePointwisePayForCutFamily :=
  (CutVertexContradictionInhabitationW25.pointwisePayForCutFamily_iff_pointwiseSideCardFamily).2
    H

def sideCardFamilyOfPayForCutFamily
    (H : MinimalFailurePointwisePayForCutFamily) :
    MinimalFailurePointwiseSideCardFamily :=
  (CutVertexContradictionInhabitationW25.pointwisePayForCutFamily_iff_pointwiseSideCardFamily).1
    H

def cutVertexContradictionFamilyOfPayForCutFamily
    (H : MinimalFailurePointwisePayForCutFamily) :
    MinimalFailureCutVertexContradictionFamily :=
  (CutVertexContradictionInhabitationW25.cutVertexContradictionFamily_iff_pointwisePayForCutFamily).2
    H

def cutVertexContradictionFamilyOfSideCardFamily
    (H : MinimalFailurePointwiseSideCardFamily) :
    MinimalFailureCutVertexContradictionFamily :=
  cutVertexContradictionFamilyOfPayForCutFamily
    (payForCutFamilyOfSideCardFamily H)

def notBlockerOfPayForCutFamily
    (H : MinimalFailurePointwisePayForCutFamily) :
    Not MinimalCutVertexBlockerExists :=
  (CutVertexContradictionInhabitationW25.not_nonempty_minimalCutVertexBlocker_iff_pointwisePayForCutFamily).2
    H

def notBlockerOfSideCardFamily
    (H : MinimalFailurePointwiseSideCardFamily) :
    Not MinimalCutVertexBlockerExists :=
  (CutVertexContradictionInhabitationW25.not_nonempty_minimalCutVertexBlocker_iff_pointwiseSideCardFamily).2
    H

def noCutComponentOfPayForCutFamily
    (H : MinimalFailurePointwisePayForCutFamily) :
    ConcreteNoCutTheorem :=
  ConcreteW23ComponentsInhabitationW26.noCutComponentOfCutVertexContradictionFamily
    (cutVertexContradictionFamilyOfPayForCutFamily H)

def noCutComponentOfSideCardFamily
    (H : MinimalFailurePointwiseSideCardFamily) :
    ConcreteNoCutTheorem :=
  noCutComponentOfPayForCutFamily (payForCutFamilyOfSideCardFamily H)

/-- The actual pointwise cut-side fields: side-card is retained as data, and
pay-for-cut is retained beside it as the W25-equivalent field. -/
structure PointwiseSideCardPayForCutFields : Type where
  sideCard : MinimalFailurePointwiseSideCardFamily
  payForCut : MinimalFailurePointwisePayForCutFamily

namespace PointwiseSideCardPayForCutFields

def ofSideCard
    (H : MinimalFailurePointwiseSideCardFamily) :
    PointwiseSideCardPayForCutFields where
  sideCard := H
  payForCut := payForCutFamilyOfSideCardFamily H

def ofPayForCut
    (H : MinimalFailurePointwisePayForCutFamily) :
    PointwiseSideCardPayForCutFields where
  sideCard := sideCardFamilyOfPayForCutFamily H
  payForCut := H

def cutVertexContradiction
    (F : PointwiseSideCardPayForCutFields) :
    MinimalFailureCutVertexContradictionFamily :=
  cutVertexContradictionFamilyOfPayForCutFamily F.payForCut

def notBlocker
    (F : PointwiseSideCardPayForCutFields) :
    Not MinimalCutVertexBlockerExists :=
  notBlockerOfPayForCutFamily F.payForCut

def noCutComponent
    (F : PointwiseSideCardPayForCutFields) :
    ConcreteNoCutTheorem :=
  noCutComponentOfPayForCutFamily F.payForCut

theorem sideCard_at
    (F : PointwiseSideCardPayForCutFields)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    PayForCutArithmeticW16.MinimalitySelectedPartitionSideCardInequality
      hmin P :=
  F.sideCard C hmin P

theorem payForCut_at
    (F : PointwiseSideCardPayForCutFields)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    NoCutMinimalityProofW15.MinimalitySelectedPartitionPaysCut hmin P :=
  F.payForCut C hmin P

theorem false_of_supplied_cutPartition
    (F : PointwiseSideCardPayForCutFields)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    False :=
  CutVertexContradictionInhabitationW25.false_of_minimalFailure_partition_pointwisePayForCut
    hmin P (F.payForCut_at C hmin P)

def concreteW23ComponentsOfTail
    (F : PointwiseSideCardPayForCutFields)
    (tail : ConcreteW23ComponentsExceptNoCut F.noCutComponent) :
    ConcreteW23Components :=
  ConcreteW23ComponentsInhabitationW26.concreteW23ComponentsOfNoCutTail
    tail

theorem concreteW23Components_nonempty_of_tail
    (F : PointwiseSideCardPayForCutFields)
    (tail : ConcreteW23ComponentsExceptNoCut F.noCutComponent) :
    Nonempty ConcreteW23Components :=
  Nonempty.intro (F.concreteW23ComponentsOfTail tail)

end PointwiseSideCardPayForCutFields

/--
Concrete W23 fields fed by actual pointwise cut arithmetic.  The no-cut
component is computed from the pointwise pay-for-cut field, and the remaining
W23 components are the real W26 tail over that component.
-/
structure CutSideCardPayForCutConcreteFields : Type 1 where
  pointwise : PointwiseSideCardPayForCutFields
  tail : ConcreteW23ComponentsExceptNoCut pointwise.noCutComponent

namespace CutSideCardPayForCutConcreteFields

def ofSideCardTail
    (H : MinimalFailurePointwiseSideCardFamily)
    (tail :
      ConcreteW23ComponentsExceptNoCut
        (noCutComponentOfSideCardFamily H)) :
    CutSideCardPayForCutConcreteFields where
  pointwise := PointwiseSideCardPayForCutFields.ofSideCard H
  tail := tail

def ofPayForCutTail
    (H : MinimalFailurePointwisePayForCutFamily)
    (tail :
      ConcreteW23ComponentsExceptNoCut
        (noCutComponentOfPayForCutFamily H)) :
    CutSideCardPayForCutConcreteFields where
  pointwise := PointwiseSideCardPayForCutFields.ofPayForCut H
  tail := tail

def concreteW23Components
    (F : CutSideCardPayForCutConcreteFields) :
    ConcreteW23Components :=
  F.pointwise.concreteW23ComponentsOfTail F.tail

theorem concreteW23Components_nonempty
    (F : CutSideCardPayForCutConcreteFields) :
    Nonempty ConcreteW23Components :=
  Nonempty.intro F.concreteW23Components

theorem targetLowerBoundEightThirtyOne
    (F : CutSideCardPayForCutConcreteFields) :
    Target :=
  ConcreteW23ComponentsInhabitationW26.targetLowerBoundEightThirtyOne_of_noCut_tail
    F.tail

theorem lower_bound_eight_thirty_one
    (F : CutSideCardPayForCutConcreteFields)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  F.targetLowerBoundEightThirtyOne n C

end CutSideCardPayForCutConcreteFields

theorem concreteW23Components_nonempty_of_sideCard_tail
    (H : MinimalFailurePointwiseSideCardFamily)
    (tail :
      ConcreteW23ComponentsExceptNoCut
        (noCutComponentOfSideCardFamily H)) :
    Nonempty ConcreteW23Components :=
  (CutSideCardPayForCutConcreteFields.ofSideCardTail H tail)
    |>.concreteW23Components_nonempty

theorem concreteW23Components_nonempty_of_payForCut_tail
    (H : MinimalFailurePointwisePayForCutFamily)
    (tail :
      ConcreteW23ComponentsExceptNoCut
        (noCutComponentOfPayForCutFamily H)) :
    Nonempty ConcreteW23Components :=
  (CutSideCardPayForCutConcreteFields.ofPayForCutTail H tail)
    |>.concreteW23Components_nonempty

theorem targetLowerBoundEightThirtyOne_of_sideCard_tail
    (H : MinimalFailurePointwiseSideCardFamily)
    (tail :
      ConcreteW23ComponentsExceptNoCut
        (noCutComponentOfSideCardFamily H)) :
    Target :=
  (CutSideCardPayForCutConcreteFields.ofSideCardTail H tail)
    |>.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_sideCard_tail
    (H : MinimalFailurePointwiseSideCardFamily)
    (tail :
      ConcreteW23ComponentsExceptNoCut
        (noCutComponentOfSideCardFamily H))
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_sideCard_tail H tail n C

end

end CutSideCardPayForCutConcreteW27
end Swanepoel

namespace Verified

abbrev SwanepoelW27PointwiseSideCardPayForCutFields : Type :=
  Swanepoel.CutSideCardPayForCutConcreteW27.PointwiseSideCardPayForCutFields

abbrev SwanepoelW27CutSideCardPayForCutConcreteFields : Type 1 :=
  Swanepoel.CutSideCardPayForCutConcreteW27.CutSideCardPayForCutConcreteFields

theorem swanepoelW27_payForCut_at
    (F : SwanepoelW27PointwiseSideCardPayForCutFields)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : Swanepoel.MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : Swanepoel.CutVertexInterface.CutVertexPartition C) :
    Swanepoel.NoCutMinimalityProofW15.MinimalitySelectedPartitionPaysCut
      hmin P :=
  Swanepoel.CutSideCardPayForCutConcreteW27.PointwiseSideCardPayForCutFields.payForCut_at
    F C hmin P

theorem lower_bound_eight_thirty_one_of_swanepoelW27_cutSideCardPayForCutConcreteFields
    (F : SwanepoelW27CutSideCardPayForCutConcreteFields)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.CutSideCardPayForCutConcreteW27.CutSideCardPayForCutConcreteFields.lower_bound_eight_thirty_one
    F n C

end Verified
end ErdosProblems1066
