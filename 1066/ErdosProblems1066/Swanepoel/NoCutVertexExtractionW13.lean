import ErdosProblems1066.Swanepoel.CutVertexSlackW12

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutVertexExtractionW13

open CutVertexInterface
open CutVertexSlackFromDeletion

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}

def NoCutVertexExtractionInput
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Prop :=
  Or (CutVertexDeletionMissingArithmetic hmin)
    (Or (CutVertexDeletionCombinedImageBoundFact hmin)
      (Or (CutVertexDeletionSideCardExactFact hmin)
        (Or (CutVertexDeletionSideCardPaperFact hmin)
          (Or (CutVertexDeletionSlackFact C)
            (Nonempty (CutVertexFinal.RemainingNoCutSlackFact C))))))

def NoCutVertexExtractionAllInputs
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Prop :=
  And (CutVertexDeletionMissingArithmetic hmin)
    (And (CutVertexDeletionCombinedImageBoundFact hmin)
      (And (CutVertexDeletionSideCardExactFact hmin)
        (And (CutVertexDeletionSideCardPaperFact hmin)
          (And (CutVertexDeletionSlackFact C)
            (Nonempty (CutVertexFinal.RemainingNoCutSlackFact C))))))

theorem sideCardExactFact_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionSideCardExactFact hmin <-> NoCutVertex C :=
  _root_.ErdosProblems1066.Swanepoel.CutVertexSlackW12.cutVertexDeletionSideCardExactFact_iff_noCutVertex_of_minimalFailure
    hmin

theorem missingArithmetic_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionMissingArithmetic hmin <-> NoCutVertex C :=
  (sideCardExactFact_iff_missingArithmetic hmin).symm.trans
    (sideCardExactFact_iff_noCutVertex_of_minimalFailure hmin)

theorem combinedImageBoundFact_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionCombinedImageBoundFact hmin <-> NoCutVertex C :=
  (sideCardExactFact_iff_combinedImageBoundFact hmin).symm.trans
    (sideCardExactFact_iff_noCutVertex_of_minimalFailure hmin)

theorem sideCardPaperFact_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionSideCardPaperFact hmin <-> NoCutVertex C :=
  (sideCardExactFact_iff_sideCardPaperFact hmin).symm.trans
    (sideCardExactFact_iff_noCutVertex_of_minimalFailure hmin)

theorem deletionSlackFact_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionSlackFact C <-> NoCutVertex C :=
  _root_.ErdosProblems1066.Swanepoel.CutVertexSlackW12.cutVertexDeletionSlackFact_iff_noCutVertex_of_minimalFailure
    hmin

theorem remainingNoCutSlackFact_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (CutVertexFinal.RemainingNoCutSlackFact C) <-> NoCutVertex C :=
  _root_.ErdosProblems1066.Swanepoel.CutVertexSlackW12.remainingNoCutSlackFact_nonempty_iff_noCutVertex_of_minimalFailure
    hmin

theorem noCutVertexExtractionInput_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    NoCutVertexExtractionInput hmin <-> NoCutVertex C := by
  unfold NoCutVertexExtractionInput
  constructor
  case mp =>
    intro H
    exact H.elim
      (fun hmissing =>
        (missingArithmetic_iff_noCutVertex_of_minimalFailure hmin).1
          hmissing)
      (fun Hcombined =>
        Hcombined.elim
          (fun hcombined =>
            (combinedImageBoundFact_iff_noCutVertex_of_minimalFailure hmin).1
              hcombined)
          (fun Hside =>
            Hside.elim
              (fun hside =>
                (sideCardExactFact_iff_noCutVertex_of_minimalFailure hmin).1
                  hside)
              (fun Hpaper =>
                Hpaper.elim
                  (fun hpaper =>
                    (sideCardPaperFact_iff_noCutVertex_of_minimalFailure
                      hmin).1 hpaper)
                  (fun Hdeletion =>
                    Hdeletion.elim
                      (fun hdeletion =>
                        (deletionSlackFact_iff_noCutVertex_of_minimalFailure
                          hmin).1 hdeletion)
                      (fun hremaining =>
                        (remainingNoCutSlackFact_iff_noCutVertex_of_minimalFailure
                          hmin).1 hremaining)))))
  case mpr =>
    intro hno
    exact Or.inl
      ((missingArithmetic_iff_noCutVertex_of_minimalFailure hmin).2 hno)

theorem noCutVertexExtractionAllInputs_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    NoCutVertexExtractionAllInputs hmin <-> NoCutVertex C := by
  unfold NoCutVertexExtractionAllInputs
  constructor
  case mp =>
    intro H
    exact (missingArithmetic_iff_noCutVertex_of_minimalFailure hmin).1 H.1
  case mpr =>
    intro hno
    exact And.intro
      ((missingArithmetic_iff_noCutVertex_of_minimalFailure hmin).2 hno)
      (And.intro
        ((combinedImageBoundFact_iff_noCutVertex_of_minimalFailure hmin).2
          hno)
        (And.intro
          ((sideCardExactFact_iff_noCutVertex_of_minimalFailure hmin).2 hno)
          (And.intro
            ((sideCardPaperFact_iff_noCutVertex_of_minimalFailure hmin).2
              hno)
            (And.intro
              ((deletionSlackFact_iff_noCutVertex_of_minimalFailure hmin).2
                hno)
              ((remainingNoCutSlackFact_iff_noCutVertex_of_minimalFailure
                hmin).2 hno)))))

theorem cutVertexPartition_obstructs_extractionInput_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (NoCutVertexExtractionInput hmin) := by
  intro H
  exact
    (noCutVertexExtractionInput_iff_noCutVertex_of_minimalFailure hmin).1 H
      (Nonempty.intro P)

theorem cutVertexPartition_obstructs_all_extraction_inputs_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    And (Not (CutVertexDeletionMissingArithmetic hmin))
      (And (Not (CutVertexDeletionCombinedImageBoundFact hmin))
        (And (Not (CutVertexDeletionSideCardExactFact hmin))
          (And (Not (CutVertexDeletionSideCardPaperFact hmin))
            (And (Not (CutVertexDeletionSlackFact C))
              (Not
                (Nonempty (CutVertexFinal.RemainingNoCutSlackFact C))))))) := by
  exact And.intro
    (not_missingArithmetic_of_minimalFailure_partition hmin P)
    (And.intro
      (fun hcombined =>
        not_sideCardExactFact_of_minimalFailure_partition hmin P
          ((sideCardExactFact_iff_combinedImageBoundFact hmin).2 hcombined))
      (And.intro
        (not_sideCardExactFact_of_minimalFailure_partition hmin P)
        (And.intro
          (fun hpaper =>
            not_sideCardExactFact_of_minimalFailure_partition hmin P
              ((sideCardExactFact_iff_sideCardPaperFact hmin).2 hpaper))
          (And.intro
            (not_deletionSlackFact_of_minimalFailure_partition hmin P)
            (fun hremaining =>
              (remainingNoCutSlackFact_iff_noCutVertex_of_minimalFailure
                hmin).1 hremaining (Nonempty.intro P))))))

end

end NoCutVertexExtractionW13
end Swanepoel
end ErdosProblems1066
