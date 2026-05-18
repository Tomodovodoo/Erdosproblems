import ErdosProblems1066.Swanepoel.CommonNeighborGeometry
import ErdosProblems1066.Swanepoel.InducedSubconfiguration
import ErdosProblems1066.Swanepoel.LocalExclusions
import ErdosProblems1066.Swanepoel.MinimalGraphFacts

/-!
# Local exclusions for minimal cleared failures

This module closes a small logical gap without proving any new Euclidean
geometry.  A minimal cleared failure does not, by itself, exclude a local
pattern such as `K_{2,3}`.  What is kernel-checked here is the conditional
closure principle: if a local pattern supplies honest degree-controlled
deletion data, then that pattern cannot occur in a minimal cleared failure.

The downstream common-neighbor cap is then routed from the already-checked
`LocalExclusions` lemmas.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureLocalExclusions

open CounterexamplePipeline
open DegreePipeline
open GraphBridge
open InducedSubconfiguration
open LocalConfigurations
open MinimalCounterexample
open MinimalGraphFacts

noncomputable section

universe u

/-! ## Local deletion certificates independent of the smaller set -/

/-- Degree-controlled deletion data whose distance-preservation field is
uniform in the eventual smaller-side independent set.

Minimality only gives an existential smaller independent set.  This package is
therefore stronger than `DegreeHypotheses`: it contains all deletion data
except the smaller set, and proves distance preservation for every possible
smaller set. -/
structure DegreeLocalDeletionCertificate {n nSmall : Nat}
    (C : _root_.UDConfig n) (Csmall : _root_.UDConfig nSmall) where
  kept : Fin nSmall -> Fin n
  deleted : Finset (Fin n)
  reinsertion : Finset (Fin n)
  keptInjective : Function.Injective kept
  keptDeletedDisjoint :
    Disjoint ((Finset.univ.image kept) : Finset (Fin n)) deleted
  cover : ((Finset.univ.image kept) : Finset (Fin n)) ∪ deleted =
    Finset.univ
  closedNeighborhood : IsClosedNeighborhood C reinsertion deleted
  deletedSubsetClosedUnitNeighborhood :
    Exists fun center : Fin n => deleted <= closedUnitNeighborhood C center
  reinsertionCardLower : 2 <= reinsertion.card
  reinsertionCardUpper : reinsertion.card <= 8
  reinsertionIndep : C.IsIndep reinsertion
  preservesDistances :
    forall small : Finset (Fin nSmall),
      PreservesDistancesOn Csmall C kept small

namespace DegreeLocalDeletionCertificate

variable {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}

/-- Attach a chosen smaller independent set to a local deletion certificate. -/
def data (K : DegreeLocalDeletionCertificate C Csmall)
    (small : Finset (Fin nSmall)) :
    DeletionReinsertionData C Csmall where
  kept := K.kept
  deleted := K.deleted
  reinsertion := K.reinsertion
  small := small

/-- A local deletion certificate gives the degree-pipeline hypotheses for any
chosen smaller-side set. -/
lemma degreeHypotheses (K : DegreeLocalDeletionCertificate C Csmall)
    (small : Finset (Fin nSmall)) :
    DegreeHypotheses (K.data small) where
  keptInjective := K.keptInjective
  keptDeletedDisjoint := K.keptDeletedDisjoint
  cover := K.cover
  closedNeighborhood := K.closedNeighborhood
  deletedSubsetClosedUnitNeighborhood := K.deletedSubsetClosedUnitNeighborhood
  reinsertionCardLower := K.reinsertionCardLower
  reinsertionCardUpper := K.reinsertionCardUpper
  reinsertionIndep := K.reinsertionIndep
  preservesDistances := K.preservesDistances small

end DegreeLocalDeletionCertificate

/-! ## General local deletion certificates with direct cardinal control -/

/-- Local deletion data with the deletion-cardinality inequality supplied
directly instead of derived from a single closed unit neighborhood.

This interface is useful for singleton and other small local-deletion rules:
the caller supplies the actual cardinal arithmetic
`deleted.card <= 4 * reinsertion.card - 1`, while the induced/subconfiguration
machinery can still be used separately to provide the kept-side metric data. -/
structure LocalDeletionCertificate {n nSmall : Nat}
    (C : _root_.UDConfig n) (Csmall : _root_.UDConfig nSmall) where
  kept : Fin nSmall -> Fin n
  deleted : Finset (Fin n)
  reinsertion : Finset (Fin n)
  keptInjective : Function.Injective kept
  keptDeletedDisjoint :
    Disjoint ((Finset.univ.image kept) : Finset (Fin n)) deleted
  cover :
    Union.union ((Finset.univ.image kept) : Finset (Fin n)) deleted =
      Finset.univ
  closedNeighborhood : IsClosedNeighborhood C reinsertion deleted
  deletedCard : (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1
  reinsertionNonempty : reinsertion.Nonempty
  reinsertionCardUpper : reinsertion.card <= 8
  reinsertionIndep : C.IsIndep reinsertion
  preservesDistances :
    forall small : Finset (Fin nSmall),
      PreservesDistancesOn Csmall C kept small

namespace LocalDeletionCertificate

variable {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}

/-- Attach a chosen smaller independent set to a general local deletion
certificate. -/
def data (K : LocalDeletionCertificate C Csmall)
    (small : Finset (Fin nSmall)) :
    DeletionReinsertionData C Csmall where
  kept := K.kept
  deleted := K.deleted
  reinsertion := K.reinsertion
  small := small

/-- A general local deletion certificate gives the counterexample-pipeline
hypotheses for any chosen smaller-side set. -/
lemma hypotheses (K : LocalDeletionCertificate C Csmall)
    (small : Finset (Fin nSmall)) :
    (K.data small).Hypotheses where
  keptInjective := K.keptInjective
  keptDeletedDisjoint := K.keptDeletedDisjoint
  cover := K.cover
  closedNeighborhood := K.closedNeighborhood
  deletedCard := K.deletedCard
  reinsertionCard := K.reinsertionCardUpper
  reinsertionIndep := K.reinsertionIndep
  preservesDistances := K.preservesDistances small

/-- The deleted side is nonempty whenever the reinsertion side is nonempty and
forms a closed neighborhood. -/
lemma deleted_nonempty (K : LocalDeletionCertificate C Csmall) :
    K.deleted.Nonempty :=
  deleted_nonempty_of_center_nonempty K.closedNeighborhood
    K.reinsertionNonempty

/-- A general local deletion certificate in a minimal cleared failure clears
the original configuration. -/
theorem hasCleared_of_minimalFailure
    (hmin : IsMinimalClearedFailure C)
    (K : LocalDeletionCertificate C Csmall) :
    HasClearedEightThirtyOneIndependentSet C := by
  classical
  let Dempty := K.data (Finset.empty : Finset (Fin nSmall))
  have hDempty : Dempty.Hypotheses := K.hypotheses Finset.empty
  have hlt : nSmall < n :=
    nSmall_lt_original_of_deleted_nonempty Dempty hDempty K.deleted_nonempty
  match smaller_hasCleared_of_minimalClearedFailure hmin Csmall hlt with
  | Exists.intro small hrest =>
      let D := K.data small
      have hD : D.Hypotheses := K.hypotheses small
      have hsmall : D.SmallerBound := by
        exact
          { smallIndep := hrest.1
            smallBound := hrest.2 }
      exact D.hasCleared_of_deletionReinsertion hD hsmall

/-- Equivalently, a minimal cleared failure cannot carry a general local
deletion certificate. -/
theorem false_of_minimalFailure
    (hmin : IsMinimalClearedFailure C)
    (K : LocalDeletionCertificate C Csmall) :
    False :=
  not_hasCleared_of_minimalClearedFailure hmin
    (hasCleared_of_minimalFailure hmin K)

/-- Nonempty form of the general local-deletion impossibility statement. -/
theorem not_nonempty_localDeletionCertificate_of_minimalFailure
    (hmin : IsMinimalClearedFailure C) :
    Not (Nonempty (LocalDeletionCertificate C Csmall)) := by
  rintro ⟨K⟩
  exact false_of_minimalFailure hmin K

end LocalDeletionCertificate

/-! ## Minimal-failure closure for certified local deletions -/

/-- A certified local deletion in a minimal cleared failure would clear the
original configuration. -/
theorem hasCleared_of_minimalFailure_and_degreeLocalDeletionCertificate
    {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}
    (hmin : IsMinimalClearedFailure C)
    (K : DegreeLocalDeletionCertificate C Csmall) :
    HasClearedEightThirtyOneIndependentSet C := by
  classical
  let Dempty := K.data (∅ : Finset (Fin nSmall))
  have hDemptyDegree : DegreeHypotheses Dempty :=
    K.degreeHypotheses ∅
  have hDempty : Dempty.Hypotheses :=
    hypotheses_of_degreeHypotheses Dempty hDemptyDegree
  have hlt : nSmall < n :=
    nSmall_lt_original_of_two_le_reinsertion Dempty hDempty
      hDemptyDegree.reinsertionCardLower
  rcases smaller_hasCleared_of_minimalClearedFailure hmin Csmall hlt with
    ⟨small, hsmallIndep, hsmallBound⟩
  let D := K.data small
  have hDdegree : DegreeHypotheses D := K.degreeHypotheses small
  have hsmall : D.SmallerBound := by
    exact
      { smallIndep := hsmallIndep
        smallBound := hsmallBound }
  exact hasCleared_of_degreeDeletionReinsertion D hDdegree hsmall

/-- Equivalently, a minimal cleared failure has no certified local
degree-deletion. -/
theorem false_of_minimalFailure_and_degreeLocalDeletionCertificate
    {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}
    (hmin : IsMinimalClearedFailure C)
    (K : DegreeLocalDeletionCertificate C Csmall) :
    False := by
  exact not_hasCleared_of_minimalClearedFailure hmin
    (hasCleared_of_minimalFailure_and_degreeLocalDeletionCertificate hmin K)

/-- Nonempty form of the previous impossibility statement. -/
theorem not_nonempty_degreeLocalDeletionCertificate_of_minimalFailure
    {n nSmall : Nat} {C : _root_.UDConfig n}
    {Csmall : _root_.UDConfig nSmall}
    (hmin : IsMinimalClearedFailure C) :
    ¬ Nonempty (DegreeLocalDeletionCertificate C Csmall) := by
  rintro ⟨K⟩
  exact false_of_minimalFailure_and_degreeLocalDeletionCertificate hmin K

/-! ## Constructing certificates from local deletion data -/

/-- The kept vertices after deleting a local closed-neighborhood candidate. -/
def keptAfterDeletion {n : Nat} (deleted : Finset (Fin n)) :
    Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)) \ deleted

lemma keptAfterDeletion_disjoint {n : Nat} (deleted : Finset (Fin n)) :
    Disjoint (keptAfterDeletion deleted) deleted := by
  rw [Finset.disjoint_left]
  intro v hv hdel
  exact (Finset.mem_sdiff.mp hv).2 hdel

lemma keptAfterDeletion_union_deleted {n : Nat} (deleted : Finset (Fin n)) :
    keptAfterDeletion deleted ∪ deleted = (Finset.univ : Finset (Fin n)) := by
  ext v
  simp [keptAfterDeletion]

/-- A local deletion/reinsertion package with no explicit smaller
configuration.  The smaller induced configuration is reconstructed from
`deleted`. -/
structure LocalClosedNeighborhoodDeletion {n : Nat}
    (C : _root_.UDConfig n) where
  deleted : Finset (Fin n)
  reinsertion : Finset (Fin n)
  closedNeighborhood : IsClosedNeighborhood C reinsertion deleted
  deletedSubsetClosedUnitNeighborhood :
    Exists fun center : Fin n => deleted <= closedUnitNeighborhood C center
  reinsertionCardLower : 2 <= reinsertion.card
  reinsertionCardUpper : reinsertion.card <= 8
  reinsertionIndep : C.IsIndep reinsertion

namespace LocalClosedNeighborhoodDeletion

variable {n : Nat} {C : _root_.UDConfig n}

/-- The induced smaller configuration on the vertices outside the deleted
closed-neighborhood candidate. -/
def induced (L : LocalClosedNeighborhoodDeletion C) :
    InducedSubconfiguration.Induced
      (m := (keptAfterDeletion L.deleted).card)
      C (keptAfterDeletion L.deleted) :=
  InducedSubconfiguration.ofFinset C (keptAfterDeletion L.deleted)

/-- Build the degree-local deletion certificate consumed by the
minimal-failure closure from only the local deletion/reinsertion data. -/
def toDegreeLocalDeletionCertificate
    (L : LocalClosedNeighborhoodDeletion C) :
    DegreeLocalDeletionCertificate C L.induced.config where
  kept := L.induced.embed
  deleted := L.deleted
  reinsertion := L.reinsertion
  keptInjective := L.induced.embed_injective
  keptDeletedDisjoint := by
    rw [L.induced.image_univ]
    exact keptAfterDeletion_disjoint L.deleted
  cover := by
    rw [L.induced.image_univ]
    exact keptAfterDeletion_union_deleted L.deleted
  closedNeighborhood := L.closedNeighborhood
  deletedSubsetClosedUnitNeighborhood := L.deletedSubsetClosedUnitNeighborhood
  reinsertionCardLower := L.reinsertionCardLower
  reinsertionCardUpper := L.reinsertionCardUpper
  reinsertionIndep := L.reinsertionIndep
  preservesDistances := by
    intro small
    exact L.induced.preservesDistancesOn small

/-- Existence form for downstream pattern reducers. -/
theorem exists_degreeLocalDeletionCertificate
    (L : LocalClosedNeighborhoodDeletion C) :
    Exists fun nSmall : Nat =>
      Exists fun Csmall : _root_.UDConfig nSmall =>
        Nonempty (DegreeLocalDeletionCertificate C Csmall) := by
  exact ⟨(keptAfterDeletion L.deleted).card, L.induced.config,
    ⟨L.toDegreeLocalDeletionCertificate⟩⟩

/-- The deleted side of a local closed-neighborhood deletion is nonempty:
the reinsertion set has at least two vertices and is contained in the deleted
closed neighborhood. -/
lemma deleted_nonempty (L : LocalClosedNeighborhoodDeletion C) :
    L.deleted.Nonempty := by
  have hreinsertion_card_pos : 0 < L.reinsertion.card := by
    exact lt_of_lt_of_le (by norm_num : 0 < 2) L.reinsertionCardLower
  exact deleted_nonempty_of_center_nonempty L.closedNeighborhood
    (Finset.card_pos.mp hreinsertion_card_pos)

/-- The kept-after-deletion set and the deleted set partition all vertices. -/
lemma keptAfterDeletion_card_add_deleted_card
    (L : LocalClosedNeighborhoodDeletion C) :
    (keptAfterDeletion L.deleted).card + L.deleted.card = n := by
  have hsubset : L.deleted <= (Finset.univ : Finset (Fin n)) := by
    intro v _
    simp
  have h := Finset.card_sdiff_add_card_eq_card hsubset
  simpa [keptAfterDeletion, Finset.card_univ, Fintype.card_fin] using h

/-- The induced smaller configuration attached to a local deletion really has
strictly fewer vertices than the original configuration. -/
theorem induced_card_lt_original
    (L : LocalClosedNeighborhoodDeletion C) :
    (keptAfterDeletion L.deleted).card < n := by
  have hpartition := L.keptAfterDeletion_card_add_deleted_card
  have hpos : 0 < L.deleted.card := Finset.card_pos.mpr L.deleted_nonempty
  omega

/-- In a minimal cleared failure, the induced configuration attached to a
local deletion is available to the minimality hypothesis directly. -/
theorem induced_hasCleared_of_minimalFailure
    (hmin : IsMinimalClearedFailure C)
    (L : LocalClosedNeighborhoodDeletion C) :
    HasClearedEightThirtyOneIndependentSet L.induced.config :=
  smaller_hasCleared_of_minimalClearedFailure hmin L.induced.config
    L.induced_card_lt_original

/-- A local closed-neighborhood deletion in a minimal cleared failure would
clear the original configuration.  This direct route uses the induced
configuration's strict smaller-cardinality fact before attaching the smaller
independent set to the deletion certificate. -/
theorem hasCleared_of_minimalFailure
    (hmin : IsMinimalClearedFailure C)
    (L : LocalClosedNeighborhoodDeletion C) :
    HasClearedEightThirtyOneIndependentSet C := by
  classical
  match induced_hasCleared_of_minimalFailure hmin L with
  | Exists.intro small hrest =>
      let K := L.toDegreeLocalDeletionCertificate
      let D := K.data small
      have hDdegree : DegreeHypotheses D := K.degreeHypotheses small
      have hsmall : D.SmallerBound := by
        exact
          { smallIndep := hrest.1
            smallBound := hrest.2 }
      exact hasCleared_of_degreeDeletionReinsertion D hDdegree hsmall

/-- Equivalently, a minimal cleared failure cannot carry local
closed-neighborhood deletion data. -/
theorem false_of_minimalFailure
    (hmin : IsMinimalClearedFailure C)
    (L : LocalClosedNeighborhoodDeletion C) :
    False :=
  not_hasCleared_of_minimalClearedFailure hmin
    (hasCleared_of_minimalFailure hmin L)

end LocalClosedNeighborhoodDeletion

/-! ## Pattern reducers -/

/-- A proposition-valued local pattern is degree-reducible if every occurrence
of it supplies a certified local deletion. -/
def PatternDegreeReducible {n : Nat} (C : _root_.UDConfig n)
    (pattern : Prop) : Prop :=
  pattern ->
    Exists fun nSmall : Nat =>
      Exists fun Csmall : _root_.UDConfig nSmall =>
        Nonempty (DegreeLocalDeletionCertificate C Csmall)

/-- Generic reducer constructor: a local pattern reducer only has to supply
the deletion/reinsertion sets.  The smaller induced configuration is rebuilt
by `LocalClosedNeighborhoodDeletion`. -/
theorem patternDegreeReducible_of_localClosedNeighborhoodDeletion
    {n : Nat} {C : _root_.UDConfig n} {pattern : Prop}
    (hdel : pattern -> LocalClosedNeighborhoodDeletion C) :
    PatternDegreeReducible C pattern := by
  intro hpattern
  exact (hdel hpattern).exists_degreeLocalDeletionCertificate

/-- Any degree-reducible local pattern is absent from a minimal cleared
failure. -/
theorem not_pattern_of_minimalFailure_and_patternDegreeReducible
    {n : Nat} {C : _root_.UDConfig n} {pattern : Prop}
    (hmin : IsMinimalClearedFailure C)
    (hred : PatternDegreeReducible C pattern) :
    ¬ pattern := by
  intro hpattern
  rcases hred hpattern with ⟨nSmall, Csmall, hK⟩
  exact not_nonempty_degreeLocalDeletionCertificate_of_minimalFailure
    (Csmall := Csmall) hmin hK

/-- The `K_{2,3}`-specific reducer used by the local exclusion route. -/
def K23DegreeReducible {n : Nat} (C : _root_.UDConfig n) : Prop :=
  forall _P : K23Pattern (GraphBridge.unitDistanceLocalGraph C),
    Exists fun nSmall : Nat =>
      Exists fun Csmall : _root_.UDConfig nSmall =>
        Nonempty (DegreeLocalDeletionCertificate C Csmall)

/-- A local `K_{2,3}` deletion rule only has to provide the deleted and
reinserted sets.  The induced smaller configuration and all distance
preservation data are constructed automatically. -/
theorem K23DegreeReducible_of_localClosedNeighborhoodDeletion
    {n : Nat} {C : _root_.UDConfig n}
    (hdel :
      forall _P : K23Pattern (GraphBridge.unitDistanceLocalGraph C),
        LocalClosedNeighborhoodDeletion C) :
    K23DegreeReducible C := by
  intro P
  exact (hdel P).exists_degreeLocalDeletionCertificate

/-- Tupled-input variant of
`K23DegreeReducible_of_localClosedNeighborhoodDeletion`, convenient for
workers proving a concrete local rule. -/
theorem K23DegreeReducible_of_localClosedNeighborhoodK23Deletion
    {n : Nat} {C : _root_.UDConfig n}
    (hdel :
      forall _P : K23Pattern (GraphBridge.unitDistanceLocalGraph C),
        Exists fun deleted : Finset (Fin n) =>
        Exists fun reinsertion : Finset (Fin n) =>
          IsClosedNeighborhood C reinsertion deleted /\
          (Exists fun center : Fin n =>
            deleted <= closedUnitNeighborhood C center) /\
          2 <= reinsertion.card /\
          reinsertion.card <= 8 /\
          C.IsIndep reinsertion) :
    K23DegreeReducible C := by
  intro P
  rcases hdel P with
    ⟨deleted, reinsertion, hclosed, hsubset, hlower, hupper, hindep⟩
  let L : LocalClosedNeighborhoodDeletion C :=
    { deleted := deleted
      reinsertion := reinsertion
      closedNeighborhood := hclosed
      deletedSubsetClosedUnitNeighborhood := hsubset
      reinsertionCardLower := hlower
      reinsertionCardUpper := hupper
      reinsertionIndep := hindep }
  exact L.exists_degreeLocalDeletionCertificate

/-- If every local `K_{2,3}` pattern is degree-reducible, then a minimal
cleared failure has no local `K_{2,3}`. -/
theorem not_hasK23_of_minimalFailure_and_K23DegreeReducible
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (hred : K23DegreeReducible C) :
    ¬ HasK23 (GraphBridge.unitDistanceLocalGraph C) := by
  rintro ⟨P⟩
  rcases hred P with ⟨nSmall, Csmall, hK⟩
  exact not_nonempty_degreeLocalDeletionCertificate_of_minimalFailure
    (Csmall := Csmall) hmin hK

/-! ## Downstream finite local-exclusion package -/

/-- Finite local exclusions in the form needed by common-neighbor arguments:
no `K_{2,3}`, plus the resulting two-common-neighbor cap. -/
structure FiniteLocalExclusionPackage {V : Type u}
    (G : LocalGraph V) [Fintype V] [DecidableEq V] : Prop where
  noK23 : ¬ HasK23 G
  commonNeighborCard_le_two :
    forall {a b : V}, a ≠ b ->
      (LocalExclusions.LocalGraph.commonNeighborFinset G a b).card <= 2

namespace FiniteLocalExclusionPackage

variable {V : Type u} {G : LocalGraph V} [Fintype V] [DecidableEq V]

/-- Route an explicit no-`K_{2,3}` assumption into the finite common-neighbor
package. -/
lemma of_not_hasK23 (hno : ¬ HasK23 G) :
    FiniteLocalExclusionPackage G where
  noK23 := hno
  commonNeighborCard_le_two := by
    intro a b hab
    exact LocalExclusions.LocalGraph.commonNeighborFinset_card_le_two_of_not_hasK23
      G hno hab

end FiniteLocalExclusionPackage

/-- The finite local-exclusion package for a minimal cleared failure, assuming
honest degree reductions for all local `K_{2,3}` patterns. -/
theorem finiteLocalExclusionPackage_of_minimalFailure_and_K23DegreeReducible
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (hred : K23DegreeReducible C) :
    FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C) := by
  classical
  exact FiniteLocalExclusionPackage.of_not_hasK23
    (not_hasK23_of_minimalFailure_and_K23DegreeReducible hmin hred)

/-- The geometric two-circle argument gives the finite local-exclusion package
for every separated unit-distance configuration, with no minimal-failure or
local-deletion assumption. -/
theorem finiteLocalExclusionPackage_of_unitDistanceConfig
    {n : Nat} (C : _root_.UDConfig n) :
    FiniteLocalExclusionPackage (GraphBridge.unitDistanceLocalGraph C) where
  noK23 := CommonNeighborGeometry.not_hasK23_unitDistanceLocalGraph C
  commonNeighborCard_le_two := by
    intro a b hab
    exact CommonNeighborGeometry.unitDistance_commonNeighborFinset_card_le_two
      C hab

/-- Common-neighbor cap for any separated unit-distance configuration. -/
theorem commonNeighborFinset_card_le_two_of_unitDistanceConfig
    {n : Nat} (C : _root_.UDConfig n) {a b : Fin n} (hab : a ≠ b) :
    (LocalExclusions.LocalGraph.commonNeighborFinset
      (GraphBridge.unitDistanceLocalGraph C) a b).card <= 2 := by
  exact (finiteLocalExclusionPackage_of_unitDistanceConfig C).commonNeighborCard_le_two hab

/-- Common-neighbor cap for the unit-distance graph of a minimal cleared
failure, conditional on honest `K_{2,3}` reductions. -/
theorem commonNeighborFinset_card_le_two_of_minimalFailure_and_K23DegreeReducible
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (hred : K23DegreeReducible C) {a b : Fin n} (hab : a ≠ b) :
    (LocalExclusions.LocalGraph.commonNeighborFinset
      (GraphBridge.unitDistanceLocalGraph C) a b).card <= 2 := by
  classical
  exact (finiteLocalExclusionPackage_of_minimalFailure_and_K23DegreeReducible
    hmin hred).commonNeighborCard_le_two hab

/-- Three distinct common neighbors would produce a forbidden `K_{2,3}` under
the same conditional minimal-failure closure. -/
theorem no_three_commonNeighbors_of_minimalFailure_and_K23DegreeReducible
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (hred : K23DegreeReducible C) {a b : Fin n} (hab : a ≠ b) :
    ¬ (∃ x y z : Fin n,
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor a b x ∧
        (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor a b y ∧
        (GraphBridge.unitDistanceLocalGraph C).CommonNeighbor a b z) := by
  exact LocalExclusions.LocalGraph.no_three_commonNeighbors_of_not_hasK23
    (GraphBridge.unitDistanceLocalGraph C)
    (not_hasK23_of_minimalFailure_and_K23DegreeReducible hmin hred) hab

end

end MinimalFailureLocalExclusions
end Swanepoel
end ErdosProblems1066
