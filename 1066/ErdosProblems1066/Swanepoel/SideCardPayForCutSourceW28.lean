import ErdosProblems1066.Swanepoel.CutSideCardPayForCutConcreteW27
import ErdosProblems1066.Swanepoel.NoCutLocalDeletionConcreteW27
import ErdosProblems1066.Swanepoel.PayForCutProducerFamilyW20

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W28 side-card/pay-for-cut source boundary

This file keeps the W27 cut-side fields honest.  A W18/W20 pay-for-cut
producer, a W26 partition-local deletion eliminator, or any equivalent
no-blocker proof all build the actual W27 pointwise side-card/pay-for-cut
record.  Conversely, that pointwise record eliminates the concrete cut-vertex
blocker, so the blocker is the exact obstruction to inhabiting the pointwise
cut-side source.

For the full W27 concrete field record, no tail data is fabricated: the
checked boundary is exactly W26's concrete W23 component package, equivalently
no-blocker plus the remaining W23 tail over the induced no-cut theorem.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SideCardPayForCutSourceW28

noncomputable section

abbrev MinimalFailurePointwiseSideCardFamily : Prop :=
  CutSideCardPayForCutConcreteW27.MinimalFailurePointwiseSideCardFamily

abbrev MinimalFailurePointwisePayForCutFamily : Prop :=
  CutSideCardPayForCutConcreteW27.MinimalFailurePointwisePayForCutFamily

abbrev MinimalCutVertexBlockerExists : Prop :=
  CutSideCardPayForCutConcreteW27.MinimalCutVertexBlockerExists

abbrev PointwiseSideCardPayForCutFields : Type :=
  CutSideCardPayForCutConcreteW27.PointwiseSideCardPayForCutFields

abbrev CutSideCardPayForCutConcreteFields : Type 1 :=
  CutSideCardPayForCutConcreteW27.CutSideCardPayForCutConcreteFields

abbrev PayForCutConcreteProducerFamily : Type 1 :=
  PointwiseFamilyProducerW18.PayForCutConcreteProducerFamily

abbrev ConcreteNoCutTheorem : Prop :=
  CutSideCardPayForCutConcreteW27.ConcreteNoCutTheorem

abbrev ConcreteW23Components : Type 1 :=
  CutSideCardPayForCutConcreteW27.ConcreteW23Components

abbrev ConcreteW23ComponentsExceptNoCut
    (noCut : ConcreteNoCutTheorem) : Type 1 :=
  CutSideCardPayForCutConcreteW27.ConcreteW23ComponentsExceptNoCut noCut

abbrev CutPartitionDegreeDeletionEliminator : Prop :=
  NoCutConcreteEliminationW26.CutPartitionDegreeDeletionEliminator

abbrev CutPartitionLocalClosedNeighborhoodDeletionEliminator : Prop :=
  NoCutConcreteEliminationW26.CutPartitionLocalClosedNeighborhoodDeletionEliminator

abbrev CutPartitionDirectCardBoundCertificateEliminator : Prop :=
  NoCutConcreteEliminationW26.CutPartitionDirectCardBoundCertificateEliminator

def pointwiseSideCardFamilyOfPayForCutProducer
    (F : PayForCutConcreteProducerFamily) :
    MinimalFailurePointwiseSideCardFamily := by
  intro n C hmin P
  exact
    (PayForCutConcreteInequalityW17.concreteSelectedSideCardInequality_iff_w16
      hmin P).1 (F.row C hmin P)

def pointwisePayForCutFamilyOfPayForCutProducer
    (F : PayForCutConcreteProducerFamily) :
    MinimalFailurePointwisePayForCutFamily :=
  (CutVertexContradictionInhabitationW25.pointwisePayForCutFamily_iff_pointwiseSideCardFamily).2
    (pointwiseSideCardFamilyOfPayForCutProducer F)

def pointwiseFieldsOfPayForCutProducer
    (F : PayForCutConcreteProducerFamily) :
    PointwiseSideCardPayForCutFields :=
  CutSideCardPayForCutConcreteW27.PointwiseSideCardPayForCutFields.ofSideCard
    (pointwiseSideCardFamilyOfPayForCutProducer F)

def payForCutProducerOfPointwiseFields
    (F : PointwiseSideCardPayForCutFields) :
    PayForCutConcreteProducerFamily where
  row := by
    intro n C hmin P
    exact
      (PayForCutConcreteInequalityW17.concreteSelectedSideCardInequality_iff_w16
        hmin P).2 (F.sideCard C hmin P)

theorem nonempty_pointwiseFields_iff_payForCutProducer :
    Nonempty PointwiseSideCardPayForCutFields <->
      Nonempty PayForCutConcreteProducerFamily := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro (payForCutProducerOfPointwiseFields F)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact Nonempty.intro (pointwiseFieldsOfPayForCutProducer F)

def pointwiseFieldsOfNotBlocker
    (h : Not MinimalCutVertexBlockerExists) :
    PointwiseSideCardPayForCutFields :=
  CutSideCardPayForCutConcreteW27.PointwiseSideCardPayForCutFields.ofSideCard
    ((CutVertexContradictionInhabitationW25.not_nonempty_minimalCutVertexBlocker_iff_pointwiseSideCardFamily).1
      h)

theorem nonempty_pointwiseFields_iff_notBlocker :
    Nonempty PointwiseSideCardPayForCutFields <->
      Not MinimalCutVertexBlockerExists := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact F.notBlocker
  case mpr =>
    intro h
    exact Nonempty.intro (pointwiseFieldsOfNotBlocker h)

theorem nonempty_pointwiseFields_iff_w20PayForCutProducer :
    Nonempty PointwiseSideCardPayForCutFields <->
      Nonempty PayForCutConcreteProducerFamily :=
  nonempty_pointwiseFields_iff_payForCutProducer

theorem w20PayForCutProducer_nonempty_iff_notBlocker :
    Nonempty PayForCutConcreteProducerFamily <->
      Not MinimalCutVertexBlockerExists :=
  nonempty_pointwiseFields_iff_payForCutProducer.symm.trans
    nonempty_pointwiseFields_iff_notBlocker

theorem not_nonempty_pointwiseFields_iff_blocker :
    Not (Nonempty PointwiseSideCardPayForCutFields) <->
      MinimalCutVertexBlockerExists := by
  classical
  constructor
  case mp =>
    intro hmissing
    by_contra hblocker
    exact hmissing (nonempty_pointwiseFields_iff_notBlocker.2 hblocker)
  case mpr =>
    intro hblocker hfields
    exact (nonempty_pointwiseFields_iff_notBlocker.1 hfields) hblocker

theorem blocker_obstructs_pointwiseFields
    (hblocker : MinimalCutVertexBlockerExists) :
    Not (Nonempty PointwiseSideCardPayForCutFields) :=
  not_nonempty_pointwiseFields_iff_blocker.2 hblocker

def pointwiseFieldsOfCutPartitionDegreeDeletionEliminator
    (H : CutPartitionDegreeDeletionEliminator) :
    PointwiseSideCardPayForCutFields :=
  CutSideCardPayForCutConcreteW27.PointwiseSideCardPayForCutFields.ofPayForCut
    (NoCutConcreteEliminationW26.pointwisePayForCutFamily_of_cutPartitionDegreeDeletionEliminator
      H)

def pointwiseFieldsOfCutPartitionLocalClosedNeighborhood
    (H : CutPartitionLocalClosedNeighborhoodDeletionEliminator) :
    PointwiseSideCardPayForCutFields :=
  pointwiseFieldsOfCutPartitionDegreeDeletionEliminator
    (NoCutConcreteEliminationW26.cutPartitionDegreeDeletionEliminator_of_localClosedNeighborhood
      H)

def pointwiseFieldsOfCutPartitionDirectCardBound
    (H : CutPartitionDirectCardBoundCertificateEliminator) :
    PointwiseSideCardPayForCutFields :=
  pointwiseFieldsOfNotBlocker
    (NoCutConcreteEliminationW26.not_nonempty_minimalCutVertexBlocker_of_cutPartitionDirectCardBound
      H)

def pointwiseFieldsOfTupledClosedNeighborhood
    (H :
      NoCutLocalDeletionConcreteW27.CutPartitionTupledClosedNeighborhoodDeletionData) :
    PointwiseSideCardPayForCutFields :=
  pointwiseFieldsOfCutPartitionDegreeDeletionEliminator
    (NoCutLocalDeletionConcreteW27.cutPartitionDegreeDeletionEliminator_of_tupledClosedNeighborhood
      H)

def pointwiseFieldsOfTupledDirectCardBound
    (H :
      NoCutLocalDeletionConcreteW27.CutPartitionTupledDirectCardBoundDeletionData) :
    PointwiseSideCardPayForCutFields :=
  pointwiseFieldsOfCutPartitionDirectCardBound
    (NoCutLocalDeletionConcreteW27.cutPartitionDirectCardBoundCertificateEliminator_of_tupled
      H)

def pointwiseFieldsOfDeficientNeighborhood
    (H :
      NoCutLocalDeletionConcreteW27.CutPartitionDeficientNeighborhoodDeletionData) :
    PointwiseSideCardPayForCutFields :=
  pointwiseFieldsOfCutPartitionDirectCardBound
    (NoCutLocalDeletionConcreteW27.cutPartitionDirectCardBoundCertificateEliminator_of_deficientNeighborhood
      H)

def concreteFieldsOfPointwiseTail
    (F : PointwiseSideCardPayForCutFields)
    (tail : ConcreteW23ComponentsExceptNoCut F.noCutComponent) :
    CutSideCardPayForCutConcreteFields where
  pointwise := F
  tail := tail

def concreteFieldsOfPayForCutProducerTail
    (F : PayForCutConcreteProducerFamily)
    (tail :
      ConcreteW23ComponentsExceptNoCut
        (pointwiseFieldsOfPayForCutProducer F).noCutComponent) :
    CutSideCardPayForCutConcreteFields :=
  concreteFieldsOfPointwiseTail (pointwiseFieldsOfPayForCutProducer F) tail

def concreteFieldsOfNotBlockerTail
    (h : Not MinimalCutVertexBlockerExists)
    (tail :
      ConcreteW23ComponentsExceptNoCut
        (pointwiseFieldsOfNotBlocker h).noCutComponent) :
    CutSideCardPayForCutConcreteFields :=
  concreteFieldsOfPointwiseTail (pointwiseFieldsOfNotBlocker h) tail

theorem nonempty_concreteFields_iff_pointwise_tail :
    Nonempty CutSideCardPayForCutConcreteFields <->
      Exists fun F : PointwiseSideCardPayForCutFields =>
        Nonempty (ConcreteW23ComponentsExceptNoCut F.noCutComponent) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact Exists.intro F.pointwise (Nonempty.intro F.tail)
  case mpr =>
    intro h
    cases h with
    | intro F htail =>
        cases htail with
        | intro tail =>
            exact Nonempty.intro (concreteFieldsOfPointwiseTail F tail)

theorem nonempty_concreteFields_iff_notBlocker_tail :
    Nonempty CutSideCardPayForCutConcreteFields <->
      Exists fun h : Not MinimalCutVertexBlockerExists =>
        Nonempty
          (ConcreteW23ComponentsExceptNoCut
            (ConcreteW23ComponentsInhabitationW26.noCutComponentOfNotCutVertexBlocker
              h)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        refine Exists.intro F.pointwise.notBlocker ?_
        have hcanonical :
            (ConcreteW23ComponentsInhabitationW26.noCutComponentOfNotCutVertexBlocker
                F.pointwise.notBlocker :
              ConcreteNoCutTheorem) =
              (F.pointwise.noCutComponent : ConcreteNoCutTheorem) :=
          Subsingleton.elim _ _
        rw [hcanonical]
        exact Nonempty.intro F.tail
  case mpr =>
    intro h
    cases h with
    | intro hnot htail =>
        cases htail with
        | intro tail =>
            let F := pointwiseFieldsOfNotBlocker hnot
            have hcanonical :
                (F.noCutComponent : ConcreteNoCutTheorem) =
                  (ConcreteW23ComponentsInhabitationW26.noCutComponentOfNotCutVertexBlocker
                    hnot : ConcreteNoCutTheorem) :=
              Subsingleton.elim _ _
            have tail' : ConcreteW23ComponentsExceptNoCut F.noCutComponent := by
              rw [hcanonical]
              exact tail
            exact
              Nonempty.intro
                (concreteFieldsOfPointwiseTail F tail')

theorem nonempty_concreteFields_iff_concreteW23Components :
    Nonempty CutSideCardPayForCutConcreteFields <->
      Nonempty ConcreteW23Components :=
  nonempty_concreteFields_iff_notBlocker_tail.trans
    ConcreteW23ComponentsInhabitationW26.concreteW23Components_nonempty_iff_notBlocker_tail.symm

theorem concreteW23Components_nonempty_of_concreteFields
    (F : CutSideCardPayForCutConcreteFields) :
    Nonempty ConcreteW23Components :=
  nonempty_concreteFields_iff_concreteW23Components.1
    (Nonempty.intro F)

theorem concreteFields_nonempty_of_concreteW23Components
    (h : Nonempty ConcreteW23Components) :
    Nonempty CutSideCardPayForCutConcreteFields :=
  nonempty_concreteFields_iff_concreteW23Components.2 h

end

end SideCardPayForCutSourceW28
end Swanepoel

namespace Verified

abbrev SwanepoelW28PointwiseSideCardPayForCutFields : Type :=
  Swanepoel.SideCardPayForCutSourceW28.PointwiseSideCardPayForCutFields

abbrev SwanepoelW28CutSideCardPayForCutConcreteFields : Type 1 :=
  Swanepoel.SideCardPayForCutSourceW28.CutSideCardPayForCutConcreteFields

theorem swanepoelW28_pointwiseFields_exactly_notBlocker :
    Nonempty SwanepoelW28PointwiseSideCardPayForCutFields <->
      Not
        Swanepoel.SideCardPayForCutSourceW28.MinimalCutVertexBlockerExists :=
  Swanepoel.SideCardPayForCutSourceW28.nonempty_pointwiseFields_iff_notBlocker

theorem swanepoelW28_pointwiseFields_exactly_w20PayForCutProducer :
    Nonempty SwanepoelW28PointwiseSideCardPayForCutFields <->
      Nonempty
        Swanepoel.SideCardPayForCutSourceW28.PayForCutConcreteProducerFamily :=
  Swanepoel.SideCardPayForCutSourceW28.nonempty_pointwiseFields_iff_w20PayForCutProducer

theorem swanepoelW28_concreteFields_exactly_concreteW23Components :
    Nonempty SwanepoelW28CutSideCardPayForCutConcreteFields <->
      Nonempty
        Swanepoel.SideCardPayForCutSourceW28.ConcreteW23Components :=
  Swanepoel.SideCardPayForCutSourceW28.nonempty_concreteFields_iff_concreteW23Components

theorem swanepoelW28_pointwiseFields_blocker_exact :
    Not (Nonempty SwanepoelW28PointwiseSideCardPayForCutFields) <->
      Swanepoel.SideCardPayForCutSourceW28.MinimalCutVertexBlockerExists :=
  Swanepoel.SideCardPayForCutSourceW28.not_nonempty_pointwiseFields_iff_blocker

end Verified
end ErdosProblems1066
