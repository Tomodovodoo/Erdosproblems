import ErdosProblems1066.PachToth.SquaredOrbitClosureSourceW28
import ErdosProblems1066.PachToth.GeneratedClosureMetricSourceW28

set_option autoImplicit false

/-!
# W29 completion-row source for generated orbit skeletons

This file identifies the actual source rows needed after W28.  A W25/W28
generated-closure metric row package already supplies the three row families
needed by `GeneratedOrbitSkeleton.CompletionRows`:

* algebraic cyclic displacement closure,
* global square-distance separation, and
* square-distance same-block unit rows.

The final section also records the exact source-field obstruction for an
arbitrary skeleton, without routing through a final Pach--Toth target.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CompletionRowsSourceW29

open FiniteGraph

noncomputable section

abbrev GeneratedOrbitSkeleton : Type :=
  SquaredOrbitClosureSourceW28.GeneratedOrbitSkeleton

abbrev SquaredOrbitClosureSourceRows : Type :=
  SquaredOrbitClosureSourceW28.SquaredOrbitClosureSourceRows

abbrev GeneratedClosureMetricRowPackage : Type :=
  GeneratedClosureMetricSourceW28.GeneratedClosureMetricRowPackage

/-- The generated-closure metric package determines the W28 skeleton by
forgetting its closure and metric rows. -/
def skeletonOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    GeneratedOrbitSkeleton where
  O := P.family.O
  base := P.family.base
  orientation := P.family.orientation

@[simp]
theorem skeletonOfGeneratedClosureMetricRowPackage_O
    (P : GeneratedClosureMetricRowPackage)
    (k : Nat) (hk : 0 < k) :
    (skeletonOfGeneratedClosureMetricRowPackage P).O k hk =
      P.family.O k hk :=
  rfl

@[simp]
theorem skeletonOfGeneratedClosureMetricRowPackage_base
    (P : GeneratedClosureMetricRowPackage)
    (k : Nat) (hk : 0 < k) :
    (skeletonOfGeneratedClosureMetricRowPackage P).base k hk =
      P.family.base k hk :=
  rfl

@[simp]
theorem skeletonOfGeneratedClosureMetricRowPackage_orientation
    (P : GeneratedClosureMetricRowPackage)
    (k : Nat) (hk : 0 < k) :
    (skeletonOfGeneratedClosureMetricRowPackage P).orientation k hk =
      P.family.orientation k hk :=
  rfl

@[simp]
theorem skeletonOfGeneratedClosureMetricRowPackage_point
    (P : GeneratedClosureMetricRowPackage)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (skeletonOfGeneratedClosureMetricRowPackage P).point k hk i v =
      GeneratedClosedChain.generatedPoint
        (P.family.O k hk) hk (P.family.base k hk)
        (P.family.orientation k hk) i v :=
  rfl

/-- The closure source in the generated-closure metric package is exactly the
cyclic displacement-closure row family required by the W28 skeleton. -/
def displacementClosureRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    (skeletonOfGeneratedClosureMetricRowPackage P).DisplacementClosureRows :=
  P.closureSource.toGeneratedChainFamilyClosures

/-- Euclidean generated separation from the reduced metric package gives the
W28 square-distance separation rows. -/
def separationRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    (skeletonOfGeneratedClosureMetricRowPackage P).SeparationRows := by
  intro k hk i u j v hne
  simpa [SquaredOrbitClosureSourceW28.GeneratedOrbitSkeleton.point,
    SquaredOrbitClosureSourceW28.sqDist]
    using
      CrossBlockDistanceSqReduction.one_le_sqDist_of_one_le_root_eucDist
        (P.reducedMetric.separated k hk i u j v hne)

/-- Reduced same-block metric data gives the same-block unit rows in
square-distance form. -/
def sameBlockUnitRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    (skeletonOfGeneratedClosureMetricRowPackage P).SameBlockUnitRows := by
  intro k hk i u v huv hadj
  have hroot :
      _root_.eucDist
          (GeneratedClosedChain.generatedPoint
            (P.family.O k hk) hk (P.family.base k hk)
            (P.family.orientation k hk) i u)
          (GeneratedClosedChain.generatedPoint
            (P.family.O k hk) hk (P.family.base k hk)
            (P.family.orientation k hk) i v) =
        1 :=
    (ReducedMetricHypothesesProducerW20.sameBlockUnitEdgeCertificateOfReducedMetric
      P.reducedMetric.toReducedMetricHypotheses k hk).unit_edges
      i u v huv hadj
  simpa [SquaredOrbitClosureSourceW28.GeneratedOrbitSkeleton.point,
    SquaredOrbitClosureSourceW28.sqDist]
    using
      ClosedPlacementConcreteConstructionW27.sqDist_eq_one_of_root_eucDist_eq_one
        hroot

/-- The generated-closure metric package constructs the W28 completion rows
for its underlying skeleton. -/
def completionRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    (skeletonOfGeneratedClosureMetricRowPackage P).CompletionRows where
  closure := displacementClosureRowsOfGeneratedClosureMetricRowPackage P
  separated_sq := separationRowsOfGeneratedClosureMetricRowPackage P
  same_block_edges_sq_unit :=
    sameBlockUnitRowsOfGeneratedClosureMetricRowPackage P

/-- The same package gives the W28 source-row package. -/
def squaredOrbitClosureSourceRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    SquaredOrbitClosureSourceRows where
  skeleton := skeletonOfGeneratedClosureMetricRowPackage P
  rows := completionRowsOfGeneratedClosureMetricRowPackage P

@[simp]
theorem squaredOrbitClosureSourceRowsOfGeneratedClosureMetricRowPackage_skeleton
    (P : GeneratedClosureMetricRowPackage) :
    (squaredOrbitClosureSourceRowsOfGeneratedClosureMetricRowPackage
      P).skeleton =
      skeletonOfGeneratedClosureMetricRowPackage P :=
  rfl

theorem nonempty_completionRows_of_generatedClosureMetricRowPackage :
    Nonempty GeneratedClosureMetricRowPackage ->
      Exists fun G : GeneratedOrbitSkeleton => Nonempty G.CompletionRows := by
  intro h
  cases h with
  | intro P =>
      exact
        Exists.intro (skeletonOfGeneratedClosureMetricRowPackage P)
          (Nonempty.intro
            (completionRowsOfGeneratedClosureMetricRowPackage P))

theorem nonempty_squaredOrbitClosureSourceRows_of_generatedClosureMetricRowPackage :
    Nonempty GeneratedClosureMetricRowPackage ->
      Nonempty SquaredOrbitClosureSourceRows := by
  intro h
  cases h with
  | intro P =>
      exact
        Nonempty.intro
          (squaredOrbitClosureSourceRowsOfGeneratedClosureMetricRowPackage P)

theorem nonempty_squaredMinimalFieldsWithOrbitClosure_of_generatedClosureMetricRowPackage :
    Nonempty GeneratedClosureMetricRowPackage ->
      Nonempty
        SquaredOrbitClosureSourceW28.SquaredMinimalFieldsWithOrbitClosure := by
  intro h
  exact
    SquaredOrbitClosureSourceW28.nonempty_squaredMinimalFieldsWithOrbitClosure_of_sourceRows
      (nonempty_squaredOrbitClosureSourceRows_of_generatedClosureMetricRowPackage h)

/-! ## Exact source-field blockers for arbitrary skeletons -/

theorem completionRows_nonempty_iff_source_rows
    (G : GeneratedOrbitSkeleton) :
    Nonempty G.CompletionRows <->
      G.DisplacementClosureRows /\
        G.SeparationRows /\
          G.SameBlockUnitRows := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact
          And.intro R.closure
            (And.intro R.separated_sq R.same_block_edges_sq_unit)
  case mpr =>
    intro h
    exact
      Nonempty.intro
        { closure := h.1
          separated_sq := h.2.1
          same_block_edges_sq_unit := h.2.2 }

theorem no_completionRows_iff_missing_source_row
    (G : GeneratedOrbitSkeleton) :
    Not (Nonempty G.CompletionRows) <->
      Not
        (G.DisplacementClosureRows /\
          G.SeparationRows /\
            G.SameBlockUnitRows) := by
  constructor
  case mp =>
    intro h hrows
    exact h ((completionRows_nonempty_iff_source_rows G).2 hrows)
  case mpr =>
    intro h hcompletion
    exact h ((completionRows_nonempty_iff_source_rows G).1 hcompletion)

/-- Missing same-block square unit rows are a third source-only blocker for
W28 completion rows, alongside the two blocker structures already named in
`SquaredOrbitClosureSourceW28`. -/
structure MissingSameBlockUnitRows
    (G : GeneratedOrbitSkeleton) where
  no_rows : Not G.SameBlockUnitRows

namespace MissingSameBlockUnitRows

theorem no_completionRows
    {G : GeneratedOrbitSkeleton}
    (B : MissingSameBlockUnitRows G) :
    Not (Nonempty G.CompletionRows) := by
  intro h
  cases h with
  | intro R =>
      exact B.no_rows R.same_block_edges_sq_unit

end MissingSameBlockUnitRows

end

end CompletionRowsSourceW29
end PachToth

namespace Verified

abbrev PachTothW29CompletionRowsSourceRows : Type :=
  PachToth.CompletionRowsSourceW29.SquaredOrbitClosureSourceRows

theorem pachtoth_w29_sourceRows_of_generatedClosureMetricRowPackage :
    Nonempty
        PachToth.CompletionRowsSourceW29.GeneratedClosureMetricRowPackage ->
      Nonempty PachTothW29CompletionRowsSourceRows :=
  PachToth.CompletionRowsSourceW29.nonempty_squaredOrbitClosureSourceRows_of_generatedClosureMetricRowPackage

theorem pachtoth_w29_completionRows_iff_source_rows
    (G : PachToth.CompletionRowsSourceW29.GeneratedOrbitSkeleton) :
    Nonempty G.CompletionRows <->
      G.DisplacementClosureRows /\
        G.SeparationRows /\
          G.SameBlockUnitRows :=
  PachToth.CompletionRowsSourceW29.completionRows_nonempty_iff_source_rows G

end Verified
end ErdosProblems1066
