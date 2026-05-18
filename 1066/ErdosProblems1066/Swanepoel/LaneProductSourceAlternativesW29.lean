import ErdosProblems1066.Swanepoel.LaneProductFinalSourceW28
import ErdosProblems1066.Swanepoel.SwanepoelW28FinalAssembly
import ErdosProblems1066.Swanepoel.PointwiseProductSourceW28
import ErdosProblems1066.Swanepoel.SelectedFaceWitnessConstructionW28
import ErdosProblems1066.Swanepoel.FigureExactAngleSourceW28
import ErdosProblems1066.Swanepoel.NoCutSourceConstructionW28
import ErdosProblems1066.Swanepoel.Lemma9NoEarlySourceRowsW28

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W29 lane-product source alternatives

This worker sharpens the W28 lane-product final-source boundary by routing the
W28 pointwise product blockers, selected-topology witnesses, and exact Figure
source blockers into the existing lane-product final source package.

No endpoint is used to manufacture a source: every lower-bound result below
passes first through a `LaneProductFinalSourceW28.LaneProductFinalSource` or the
W28 honest final-source package.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LaneProductSourceAlternativesW29

noncomputable section

abbrev Target : Prop :=
  LaneProductFinalSourceW28.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  LaneProductFinalSourceW28.LowerBoundAt n C

abbrev LaneProduct : Type 1 :=
  LaneProductFinalSourceW28.LaneProduct

abbrev LaneProductFinalSource : Type 1 :=
  LaneProductFinalSourceW28.LaneProductFinalSource

abbrev W27FinalSourcePackage : Type 1 :=
  LaneProductFinalSourceW28.W27FinalSourcePackage

abbrev W27PointwiseSourcePackage : Type 1 :=
  LaneProductFinalSourceW28.PointwiseSourcePackage

abbrev ConcreteTailFields : Prop :=
  LaneProductFinalSourceW28.ConcreteTailFields

abbrev RemainingLaneProductFinalSourceBlocker : Prop :=
  LaneProductFinalSourceW28.RemainingLaneProductFinalSourceBlocker

abbrev HonestFinalSourcePackage : Type 1 :=
  SwanepoelW28FinalAssembly.HonestFinalSourcePackage

abbrev PointwiseProductBlocker : Type 1 :=
  PointwiseProductSourceW28.PointwiseProductBlocker.{0}

abbrev PointwiseW26Product : Type 1 :=
  PointwiseProductSourceW28.W26Product.{0}

abbrev NoCutDependency : Prop :=
  PointwiseProductSourceW28.NoCutDependency

abbrev BoundaryFamily : Type 1 :=
  PointwiseProductSourceW28.BoundaryFamily.{0}

abbrev FramePositiveRows
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily) : Type 1 :=
  PointwiseProductSourceW28.FramePositiveRows.{0} noCut boundary

abbrev NoEarlySourceFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily}
    (lemma8 : FramePositiveRows noCut boundary) : Type 1 :=
  PointwiseProductSourceW28.NoEarlySourceFamily.{0} lemma8

abbrev FigureExactDataFamily
    {noCut : NoCutDependency} {boundary : BoundaryFamily}
    (lemma8 : FramePositiveRows noCut boundary) : Type 1 :=
  PointwiseProductSourceW28.FigureExactDataFamily.{0} lemma8

abbrev GeometrySourceFamily
    (noCut : NoCutDependency)
    (boundary : BoundaryFamily) : Type 1 :=
  PointwiseProductSourceW28.GeometrySourceFamily.{0} noCut boundary

abbrev ExtractedWitnessFamily : Type 1 :=
  SelectedFaceWitnessConstructionW28.ExtractedWitnessFamily.{0}

/-! ## Pointwise blockers as lane-product final sources -/

def pointwiseSourcePackageOfPointwiseProductBlocker
    (P : PointwiseProductBlocker) :
    W27PointwiseSourcePackage :=
  P.toPointwiseSourceFamilyFields

def w27FinalSourceOfPointwiseProductBlocker
    (P : PointwiseProductBlocker) :
    W27FinalSourcePackage :=
  LaneProductFinalSourceW28.w27FinalSourceOfPointwiseSourcePackage
    (pointwiseSourcePackageOfPointwiseProductBlocker P)

def laneProductFinalSourceOfPointwiseProductBlocker
    (P : PointwiseProductBlocker) :
    LaneProductFinalSource :=
  LaneProductFinalSourceW28.LaneProductFinalSource.w27Final
    (w27FinalSourceOfPointwiseProductBlocker P)

def honestFinalSourcePackageOfPointwiseProductBlocker
    (P : PointwiseProductBlocker) :
    HonestFinalSourcePackage :=
  SwanepoelW28FinalAssembly.HonestFinalSourcePackage.pointwiseProduct
    P.toW26Product

theorem nonempty_pointwiseW26Product_iff_pointwiseProductBlocker :
    Nonempty PointwiseW26Product <->
      Nonempty PointwiseProductBlocker :=
  PointwiseProductSourceW28.nonempty_w26Product_iff_pointwiseProductBlocker

theorem pointwiseSourcePackage_nonempty_of_pointwiseProductBlocker
    (h : Nonempty PointwiseProductBlocker) :
    Nonempty W27PointwiseSourcePackage := by
  cases h with
  | intro P =>
      exact Nonempty.intro (pointwiseSourcePackageOfPointwiseProductBlocker P)

theorem w27FinalSource_nonempty_of_pointwiseProductBlocker
    (h : Nonempty PointwiseProductBlocker) :
    Nonempty W27FinalSourcePackage := by
  cases h with
  | intro P =>
      exact Nonempty.intro (w27FinalSourceOfPointwiseProductBlocker P)

theorem laneProductFinalSource_nonempty_of_pointwiseProductBlocker
    (h : Nonempty PointwiseProductBlocker) :
    Nonempty LaneProductFinalSource := by
  cases h with
  | intro P =>
      exact Nonempty.intro (laneProductFinalSourceOfPointwiseProductBlocker P)

/-! ## Sharpened W28 source alternatives -/

abbrev HonestSourceAlternatives : Prop :=
  ConcreteTailFields \/
    Nonempty W27PointwiseSourcePackage \/
      Nonempty LaneProduct \/
        Nonempty PointwiseProductBlocker

theorem nonempty_honestFinalSourcePackage_iff_sourceAlternatives :
    Nonempty HonestFinalSourcePackage <-> HonestSourceAlternatives := by
  constructor
  case mp =>
    intro h
    cases
        (SwanepoelW28FinalAssembly.nonempty_honestFinalSourcePackage_iff_sourceAlternatives).1
          h with
    | inl hTail =>
        exact Or.inl hTail
    | inr hRest =>
        cases hRest with
        | inl hPointwise =>
            exact Or.inr (Or.inl hPointwise)
        | inr hRest2 =>
            cases hRest2 with
            | inl hLane =>
                exact Or.inr (Or.inr (Or.inl hLane))
            | inr hProduct =>
                exact Or.inr
                  (Or.inr
                    (Or.inr
                      ((nonempty_pointwiseW26Product_iff_pointwiseProductBlocker).1
                        hProduct)))
  case mpr =>
    intro h
    apply
      (SwanepoelW28FinalAssembly.nonempty_honestFinalSourcePackage_iff_sourceAlternatives).2
    cases h with
    | inl hTail =>
        exact Or.inl hTail
    | inr hRest =>
        cases hRest with
        | inl hPointwise =>
            exact Or.inr (Or.inl hPointwise)
        | inr hRest2 =>
            cases hRest2 with
            | inl hLane =>
                exact Or.inr (Or.inr (Or.inl hLane))
            | inr hBlocker =>
                exact Or.inr
                  (Or.inr
                    (Or.inr
                      ((nonempty_pointwiseW26Product_iff_pointwiseProductBlocker).2
                        hBlocker)))

abbrev LaneProductSourceAlternatives : Prop :=
  Nonempty LaneProduct \/ ConcreteTailFields \/ Nonempty PointwiseProductBlocker

theorem laneProductSourceAlternatives_to_remainingBlocker
    (h : LaneProductSourceAlternatives) :
    RemainingLaneProductFinalSourceBlocker := by
  cases h with
  | inl hLane =>
      exact Or.inl hLane
  | inr hRest =>
      cases hRest with
      | inl hTail =>
          exact Or.inr (Or.inl hTail)
      | inr hPointwise =>
          exact Or.inr
            (Or.inr
              (pointwiseSourcePackage_nonempty_of_pointwiseProductBlocker
                hPointwise))

theorem laneProductFinalSource_nonempty_of_sourceAlternatives
    (h : LaneProductSourceAlternatives) :
    Nonempty LaneProductFinalSource := by
  cases h with
  | inl hLane =>
      cases hLane with
      | intro P =>
          exact
            Nonempty.intro
              (LaneProductFinalSourceW28.LaneProductFinalSource.laneProduct P)
  | inr hRest =>
      cases hRest with
      | inl hTail =>
          cases
              (SwanepoelW27FinalAssembly.concreteFinalSourcePackage_nonempty_of_tailFields
                hTail) with
          | intro P =>
              exact
                Nonempty.intro
                  (LaneProductFinalSourceW28.LaneProductFinalSource.w27Final P)
      | inr hPointwise =>
          exact
            laneProductFinalSource_nonempty_of_pointwiseProductBlocker
              hPointwise

theorem targetLowerBoundEightThirtyOne_of_sourceAlternatives
    (h : LaneProductSourceAlternatives) :
    Target :=
  LaneProductFinalSourceW28.targetLowerBoundEightThirtyOne_of_remainingBlocker
    (laneProductSourceAlternatives_to_remainingBlocker h)

theorem lower_bound_eight_thirty_one_of_sourceAlternatives
    (h : LaneProductSourceAlternatives)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_sourceAlternatives h n C

/-! ## Topology and Figure source composites feeding the pointwise product -/

def boundaryFamilyOfExtractedWitnessFamily
    (F : ExtractedWitnessFamily) :
    BoundaryFamily :=
  SelectedFaceWitnessConstructionW28.boundaryRemainingComponentFamilyOfExtracted
    F

def figureExactDataFamilyOfExactSourceBlocker
    {noCut : NoCutDependency} {boundary : BoundaryFamily}
    {lemma8 : FramePositiveRows noCut boundary}
    (h :
      FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{0}
        (PointwiseProductSourceW28.PayForCutOfNoCut noCut)
        (PointwiseProductSourceW28.TopologyArcOfBoundary boundary)
        (PointwiseProductSourceW28.Lemma8ConcreteOfRows lemma8)) :
    FigureExactDataFamily lemma8 := by
  exact (Classical.choice h).toLocalExactAngleDataFamily

structure ExtractedTopologyPointwiseSources : Type 1 where
  noCut : NoCutDependency
  topology : ExtractedWitnessFamily
  lemma8 :
    FramePositiveRows noCut
      (boundaryFamilyOfExtractedWitnessFamily topology)
  lemma9 : NoEarlySourceFamily lemma8
  figures : FigureExactDataFamily lemma8

namespace ExtractedTopologyPointwiseSources

def boundary
    (S : ExtractedTopologyPointwiseSources) :
    BoundaryFamily :=
  boundaryFamilyOfExtractedWitnessFamily S.topology

def toPointwiseProductBlocker
    (S : ExtractedTopologyPointwiseSources) :
    PointwiseProductBlocker :=
  PointwiseProductSourceW28.pointwiseProductBlockerOfComponents
    S.noCut S.boundary S.lemma8 S.lemma9 S.figures

def toLaneProductFinalSource
    (S : ExtractedTopologyPointwiseSources) :
    LaneProductFinalSource :=
  laneProductFinalSourceOfPointwiseProductBlocker
    S.toPointwiseProductBlocker

theorem laneProductFinalSource_nonempty
    (S : ExtractedTopologyPointwiseSources) :
    Nonempty LaneProductFinalSource :=
  Nonempty.intro S.toLaneProductFinalSource

end ExtractedTopologyPointwiseSources

structure ExactFigurePointwiseSources : Type 1 where
  noCut : NoCutDependency
  boundary : BoundaryFamily
  lemma8 : FramePositiveRows noCut boundary
  lemma9 : NoEarlySourceFamily lemma8
  figures :
    FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{0}
      (PointwiseProductSourceW28.PayForCutOfNoCut noCut)
      (PointwiseProductSourceW28.TopologyArcOfBoundary boundary)
      (PointwiseProductSourceW28.Lemma8ConcreteOfRows lemma8)

namespace ExactFigurePointwiseSources

def figureExactData
    (S : ExactFigurePointwiseSources) :
    FigureExactDataFamily S.lemma8 :=
  figureExactDataFamilyOfExactSourceBlocker S.figures

def toPointwiseProductBlocker
    (S : ExactFigurePointwiseSources) :
    PointwiseProductBlocker :=
  PointwiseProductSourceW28.pointwiseProductBlockerOfComponents
    S.noCut S.boundary S.lemma8 S.lemma9 S.figureExactData

def toLaneProductFinalSource
    (S : ExactFigurePointwiseSources) :
    LaneProductFinalSource :=
  laneProductFinalSourceOfPointwiseProductBlocker
    S.toPointwiseProductBlocker

theorem laneProductFinalSource_nonempty
    (S : ExactFigurePointwiseSources) :
    Nonempty LaneProductFinalSource :=
  Nonempty.intro S.toLaneProductFinalSource

end ExactFigurePointwiseSources

structure ExtractedTopologyGeometryRouteFigureSources : Type 1 where
  noCut : NoCutDependency
  topology : ExtractedWitnessFamily
  lemma8Geometry :
    GeometrySourceFamily noCut
      (boundaryFamilyOfExtractedWitnessFamily topology)
  lemma9Route :
    Lemma9NoEarlySourceRowsW28.M8NoEarlyRouteFamilyData.{0}
      (PointwiseProductSourceW28.PayForCutOfNoCut noCut)
      (PointwiseProductSourceW28.TopologyArcOfBoundary
        (boundaryFamilyOfExtractedWitnessFamily topology))
      (PointwiseProductSourceW28.Lemma8ConcreteOfRows
        (PointwiseProductSourceW28.lemma8RowsOfGeometrySourceFamily
          lemma8Geometry))
  figures :
    FigureExactAngleSourceW28.ExactE22E23SourceBlocker.{0}
      (PointwiseProductSourceW28.PayForCutOfNoCut noCut)
      (PointwiseProductSourceW28.TopologyArcOfBoundary
        (boundaryFamilyOfExtractedWitnessFamily topology))
      (PointwiseProductSourceW28.Lemma8ConcreteOfRows
        (PointwiseProductSourceW28.lemma8RowsOfGeometrySourceFamily
          lemma8Geometry))

namespace ExtractedTopologyGeometryRouteFigureSources

def boundary
    (S : ExtractedTopologyGeometryRouteFigureSources) :
    BoundaryFamily :=
  boundaryFamilyOfExtractedWitnessFamily S.topology

def lemma8Rows
    (S : ExtractedTopologyGeometryRouteFigureSources) :
    FramePositiveRows S.noCut S.boundary :=
  PointwiseProductSourceW28.lemma8RowsOfGeometrySourceFamily
    S.lemma8Geometry

def lemma9
    (S : ExtractedTopologyGeometryRouteFigureSources) :
    NoEarlySourceFamily S.lemma8Rows :=
  S.lemma9Route.toW25SourceFamily

def figureExactData
    (S : ExtractedTopologyGeometryRouteFigureSources) :
    FigureExactDataFamily S.lemma8Rows :=
  figureExactDataFamilyOfExactSourceBlocker S.figures

def toPointwiseProductBlocker
    (S : ExtractedTopologyGeometryRouteFigureSources) :
    PointwiseProductBlocker :=
  PointwiseProductSourceW28.pointwiseProductBlockerOfComponents
    S.noCut S.boundary S.lemma8Rows S.lemma9 S.figureExactData

def toLaneProductFinalSource
    (S : ExtractedTopologyGeometryRouteFigureSources) :
    LaneProductFinalSource :=
  laneProductFinalSourceOfPointwiseProductBlocker
    S.toPointwiseProductBlocker

def toHonestFinalSourcePackage
    (S : ExtractedTopologyGeometryRouteFigureSources) :
    HonestFinalSourcePackage :=
  honestFinalSourcePackageOfPointwiseProductBlocker
    S.toPointwiseProductBlocker

theorem laneProductFinalSource_nonempty
    (S : ExtractedTopologyGeometryRouteFigureSources) :
    Nonempty LaneProductFinalSource :=
  Nonempty.intro S.toLaneProductFinalSource

theorem honestFinalSourcePackage_nonempty
    (S : ExtractedTopologyGeometryRouteFigureSources) :
    Nonempty HonestFinalSourcePackage :=
  Nonempty.intro S.toHonestFinalSourcePackage

end ExtractedTopologyGeometryRouteFigureSources

/-! ## No-cut W28 pointwise product already feeds the lane-product source -/

def laneProductFinalSourceOfBlockerDegreeDeletionPointwiseW27Product
    (P : NoCutSourceConstructionW28.BlockerDegreeDeletionPointwiseW27Product) :
    LaneProductFinalSource :=
  LaneProductFinalSourceW28.LaneProductFinalSource.w27Final
    P.toConcreteFinalSourcePackage

theorem laneProductFinalSource_nonempty_of_blockerDegreeDeletionPointwiseW27Product
    (P : NoCutSourceConstructionW28.BlockerDegreeDeletionPointwiseW27Product) :
    Nonempty LaneProductFinalSource :=
  Nonempty.intro
    (laneProductFinalSourceOfBlockerDegreeDeletionPointwiseW27Product P)

end

end LaneProductSourceAlternativesW29
end Swanepoel
end ErdosProblems1066
