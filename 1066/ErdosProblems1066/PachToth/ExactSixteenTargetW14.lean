import ErdosProblems1066.PachToth.ExactBlockCertificateW13
import ErdosProblems1066.PachToth.FiniteCertificateInstantiationW13
import ErdosProblems1066.PachToth.NonConnectorInstantiationW13
import ErdosProblems1066.PachToth.TargetReduction

set_option autoImplicit false

/-!
# W14 exact `16 * k` target facade

This file records the strongest exact-multiple Pach-Toth target currently
available from the W13 certificate surfaces.  The all-positive theorem below
keeps the remaining finite certificate data as explicit fields: one period
word and its `Fin 16` equations for every positive block count, together with
the upper-triangle non-connector value inequalities.

The restricted exact-block certificate is kept separate: it proves only the
one-block target at `16`, because its remaining closure field is one-block
data and does not supply an all-positive family.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactSixteenTargetW14

noncomputable section

abbrev ExactSixteenBlockTarget (k : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt (16 * k)

abbrev PeriodEquationFields :=
  FiniteCertificateInstantiationW13.W12.PeriodEquationFields

abbrev AllPositiveNonConnectorFields :=
  FiniteCertificateInstantiationW13.W12.AllPositiveNonConnectorFields

abbrev TableFamilyPackage :=
  FiniteCertificateInstantiationW13.W12.TableFamilyPackage

abbrev VectorPackage :=
  FiniteCertificateInstantiationW13.W12.VectorPackage

abbrev ListPackage :=
  FiniteCertificateInstantiationW13.W12.ListPackage

abbrev LocalVertexIndex :=
  FiniteCertificateObligationsW12.LocalVertexIndex

/-- Explicit W14 certificate fields for the exact `16 * k` theorem.

This is intentionally just the finite data still needed by the W13 route. -/
structure ExplicitAllPositiveCertificate where
  period : PeriodEquationFields
  value :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  value_eq_polynomial_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (CrossBlockSqTableSearch.IndexedCyclicConnectorPair
            hk i u j v) ->
            value k hk i u j v =
              CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
                period.toRoleHingedPeriodSearchFamily hk i u j v
  value_ge_one_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (CrossBlockSqTableSearch.IndexedCyclicConnectorPair
            hk i u j v) ->
            1 <= value k hk i u j v

namespace ExplicitAllPositiveCertificate

/-- Repackage the explicit W14 fields in the W13 all-positive facade. -/
def toAllPositiveNonConnectorFields
    (C : ExplicitAllPositiveCertificate) :
    AllPositiveNonConnectorFields where
  period := C.period
  value := C.value
  value_eq_polynomial_lt := C.value_eq_polynomial_lt
  value_ge_one_lt := C.value_ge_one_lt

/-- Exact block target for one chosen positive block count. -/
theorem targetUpperConstructionFiveSixteenAt
    (C : ExplicitAllPositiveCertificate)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k :=
  C.toAllPositiveNonConnectorFields
    |>.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact `16 * k` target for every positive block count, conditional on the
explicit all-positive finite certificate fields above. -/
theorem targetUpperConstructionFiveSixteen
    (C : ExplicitAllPositiveCertificate) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toAllPositiveNonConnectorFields.targetUpperConstructionFiveSixteen

end ExplicitAllPositiveCertificate

/-- Exact block target from the W13 raw all-positive field package. -/
theorem targetUpperConstructionFiveSixteenAt_of_allPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k :=
  C.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact block target from a W13 native non-connector table package. -/
theorem targetUpperConstructionFiveSixteenAt_of_tableFamilyPackage
    (P : TableFamilyPackage)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k :=
  P.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact block target from a W13 vector-backed non-connector table package. -/
theorem targetUpperConstructionFiveSixteenAt_of_vectorPackage
    (P : VectorPackage)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k :=
  P.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact block target from a W13 list-backed non-connector table package. -/
theorem targetUpperConstructionFiveSixteenAt_of_listPackage
    (P : ListPackage)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k :=
  P.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact block target from the concrete value-matrix W13 instantiation. -/
theorem targetUpperConstructionFiveSixteenAt_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k := by
  let fields :=
    FiniteCertificateInstantiationW13.fieldsOfConcreteValueMatrixFamily C
  exact fields.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact block target from the candidate value-matrix W13 instantiation. -/
theorem targetUpperConstructionFiveSixteenAt_of_candidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k := by
  let fields :=
    FiniteCertificateInstantiationW13.fieldsOfCandidateValueMatrixFamily C
  exact fields.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact block target from raw indexed non-connector square-distance fields
over a period-search family. -/
theorem targetUpperConstructionFiveSixteenAt_of_indexedSqDistanceFields
    {F : NonConnectorInstantiationW13.RoleHingedPeriodSearchFamily}
    (D : NonConnectorInstantiationW13.IndexedSqDistanceFields F)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k :=
  let G : GeneratedMetricClosure.RoleHingedGeneratedClosureData k hk :=
    { transitions := F.transitions
      orientation := F.orientation k hk
      closure := (F.period k hk).toGeneratedClosureEquation
      separated := D.separated k hk }
  G.targetUpperConstructionFiveSixteenAt_exactBlock

/-- Exact block target from raw indexed non-connector value fields over a
period-search family. -/
theorem targetUpperConstructionFiveSixteenAt_of_indexedValueFields
    {F : NonConnectorInstantiationW13.RoleHingedPeriodSearchFamily}
    (D : NonConnectorInstantiationW13.IndexedValueFields F)
    (k : Nat) (hk : 0 < k) :
    ExactSixteenBlockTarget k :=
  targetUpperConstructionFiveSixteenAt_of_indexedSqDistanceFields
    D.toSqDistanceFields k hk

/-- The restricted one-block exact certificate proves only the `16` target. -/
theorem targetUpperConstructionFiveSixteenAt_sixteen_of_concreteOneBlockCertificate
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (C : ExactBlockCertificateW13.ConcreteOneBlockCertificate orientation) :
    targetUpperConstructionFiveSixteenAt 16 :=
  ExactBlockCertificateW13.targetUpperConstructionFiveSixteenAt_of_concreteOneBlockCertificate
    C

/-- The checked target reduction remains available as a separate exact-target
route from indexed-chain realizations. -/
theorem exactTarget_of_indexedChainRealizations
    (H :
      forall (k : Nat) (hk : 0 < k),
        IndexedChain.IndexedChainRealization k hk) :
    PachToth.targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_indexedChainRealizations H

end

end ExactSixteenTargetW14
end PachToth
end ErdosProblems1066
