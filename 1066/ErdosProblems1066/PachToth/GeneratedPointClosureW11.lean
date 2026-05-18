import ErdosProblems1066.PachToth.GeneratedPointCertificateW11
import ErdosProblems1066.PachToth.CrossBlockInequalityLedgerW11
import ErdosProblems1066.PachToth.FlexibleCandidateAssemblyW11
import ErdosProblems1066.PachToth.PachTothW10ClosureMatrix

set_option autoImplicit false

/-!
# W11 generated-point closure package

This module is a target-facing closure facade for generated-point data.  It
adds no numeric certificate entries: normalized polynomial fields,
normalized value fields, raw lower-bound fields, row-grouped cross-block
ledger fields, and candidate-assembly fields all remain visible inputs.

The only new work here is routing those input packages to the exact block
form, the fixed-`n` facade, the eventual facade, and the arbitrary-`n` facade.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedPointClosureW11

noncomputable section

universe u

abbrev RoleHingedPeriodSearchFamily :=
  GeneratedPointCertificateW11.RoleHingedPeriodSearchFamily

abbrev NormalizedPolynomialFields
    (F : RoleHingedPeriodSearchFamily) :=
  GeneratedPointCertificateW11.NormalizedPolynomialFields F

abbrev NormalizedValueFields
    (F : RoleHingedPeriodSearchFamily) :=
  GeneratedPointCertificateW11.NormalizedValueFields F

abbrev LowerBoundFields
    (F : RoleHingedPeriodSearchFamily) :=
  GeneratedPointCertificateW11.LowerBoundFields F

abbrev CrossBlockPeriodSearchFamily :=
  CrossBlockInequalityLedgerW11.RoleHingedPeriodSearchFamily

abbrev CrossBlockInequalityLedger
    (F : CrossBlockPeriodSearchFamily) :=
  CrossBlockInequalityLedgerW11.CrossBlockInequalityLedger F

abbrev FlexibleCandidateAssemblyFields :=
  FlexibleCandidateAssemblyW11.FlexibleCandidateAssemblyFields

abbrev W10CandidatePackedInequalities :=
  PachTothW10ClosureMatrix.W10CandidatePackedInequalities

/-- Exact, fixed, eventual, and arbitrary Pach--Toth projections from one
explicit input package. -/
structure GeneratedPointTargetRow (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

namespace GeneratedPointTargetRow

/-- An arbitrary-`n` target gives the source-faithful eventual target with
threshold zero. -/
theorem eventualTarget_of_arbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

/-- Build the full projection row once exact and arbitrary targets are known. -/
def ofExactAndArbitrary
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    GeneratedPointTargetRow alpha where
  exactTarget := exactTarget
  fixedTarget := fun A n => arbitraryTarget A n
  eventualTarget := fun A => eventualTarget_of_arbitrary (arbitraryTarget A)
  arbitraryTarget := arbitraryTarget

/-- Forget a W10 exact/arbitrary row into the W11 generated-point target row. -/
def ofW10TargetProjectionRow
    {alpha : Sort u}
    (R : PachTothW10ClosureMatrix.TargetProjectionRow alpha) :
    GeneratedPointTargetRow alpha :=
  ofExactAndArbitrary R.exactTarget R.arbitraryTarget

/-- Reuse the W11 candidate assembly row, which already exposes all four
target projections. -/
def ofCandidateProjectionRow
    {alpha : Type}
    (R : FlexibleCandidateAssemblyW11.CandidateProjectionRow alpha) :
    GeneratedPointTargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

end GeneratedPointTargetRow

/-! ## Generated-point field rows -/

/-- Normalized generated-point polynomial fields close the exact, eventual,
and arbitrary target facades. -/
def normalizedPolynomialFieldsRow
    (F : RoleHingedPeriodSearchFamily) :
    GeneratedPointTargetRow (NormalizedPolynomialFields F) :=
  GeneratedPointTargetRow.ofExactAndArbitrary
    (fun C => C.targetUpperConstructionFiveSixteen)
    (fun C => C.targetUpperConstructionFiveSixteenArbitrary)

/-- Normalized generated-point value/equality fields close the exact,
eventual, and arbitrary target facades. -/
def normalizedValueFieldsRow
    (F : RoleHingedPeriodSearchFamily) :
    GeneratedPointTargetRow (NormalizedValueFields F) :=
  GeneratedPointTargetRow.ofExactAndArbitrary
    (fun C => C.targetUpperConstructionFiveSixteen)
    (fun C => C.targetUpperConstructionFiveSixteenArbitrary)

/-- Raw cross-block lower-bound fields close the exact, eventual, and
arbitrary target facades. -/
def lowerBoundFieldsRow
    (F : RoleHingedPeriodSearchFamily) :
    GeneratedPointTargetRow (LowerBoundFields F) :=
  GeneratedPointTargetRow.ofExactAndArbitrary
    (fun C => C.targetUpperConstructionFiveSixteen)
    (fun C => C.targetUpperConstructionFiveSixteenArbitrary)

/-! ## Supporting row-grouped and candidate rows -/

/-- Row-grouped cross-block ledger fields close the same targets after
projection to the lower-table family. -/
def crossBlockInequalityLedgerRow
    (F : CrossBlockPeriodSearchFamily) :
    GeneratedPointTargetRow (CrossBlockInequalityLedger F) :=
  GeneratedPointTargetRow.ofExactAndArbitrary
    (fun L =>
      L.toNonConnectorLowerTableFamily.targetUpperConstructionFiveSixteen)
    (fun L =>
      (L.toNonConnectorLowerTableFamily).targetUpperConstructionFiveSixteenArbitrary)

/-- The candidate assembly row, normalized to this module's row shape. -/
def flexibleCandidateAssemblyFieldsRow :
    GeneratedPointTargetRow FlexibleCandidateAssemblyFields :=
  GeneratedPointTargetRow.ofCandidateProjectionRow
    FlexibleCandidateAssemblyW11.matrix.candidateFields

/-- The inherited W10 packed-inequality row, normalized to this module's row
shape. -/
def w10CandidatePackedInequalitiesRow :
    GeneratedPointTargetRow W10CandidatePackedInequalities :=
  GeneratedPointTargetRow.ofW10TargetProjectionRow
    PachTothW10ClosureMatrix.matrix.w10PackedCrossBlockInequalities

/-! ## Field-shape ledger and closure matrix -/

/-- The visible data packages consumed by this generated-point closure layer.
These entries are field shapes, not solved data. -/
structure ExplicitFieldShapes where
  normalizedPolynomialFields : RoleHingedPeriodSearchFamily -> Prop
  normalizedValueFields : RoleHingedPeriodSearchFamily -> Type
  lowerBoundFields : RoleHingedPeriodSearchFamily -> Type
  crossBlockInequalityLedgers : CrossBlockPeriodSearchFamily -> Type
  flexibleCandidateAssemblyFields : Type
  w10CandidatePackedInequalities : Type

/-- Public ledger of the explicit generated-point data still required by
each route. -/
def explicitFieldShapes : ExplicitFieldShapes where
  normalizedPolynomialFields := NormalizedPolynomialFields
  normalizedValueFields := NormalizedValueFields
  lowerBoundFields := LowerBoundFields
  crossBlockInequalityLedgers := CrossBlockInequalityLedger
  flexibleCandidateAssemblyFields := FlexibleCandidateAssemblyFields
  w10CandidatePackedInequalities := W10CandidatePackedInequalities

/-- The checked generated-point closure matrix. -/
structure Matrix where
  fields : ExplicitFieldShapes
  normalizedPolynomial :
    forall F : RoleHingedPeriodSearchFamily,
      GeneratedPointTargetRow (NormalizedPolynomialFields F)
  normalizedValue :
    forall F : RoleHingedPeriodSearchFamily,
      GeneratedPointTargetRow (NormalizedValueFields F)
  lowerBound :
    forall F : RoleHingedPeriodSearchFamily,
      GeneratedPointTargetRow (LowerBoundFields F)
  crossBlockLedger :
    forall F : CrossBlockPeriodSearchFamily,
      GeneratedPointTargetRow (CrossBlockInequalityLedger F)
  flexibleCandidateAssembly :
    GeneratedPointTargetRow FlexibleCandidateAssemblyFields
  w10CandidatePackedInequalities :
    GeneratedPointTargetRow W10CandidatePackedInequalities

/-- The generated-point closure package assembled from the W11 certificate
facade, cross-block ledger, W11 candidate assembly, and W10 closure matrix. -/
def matrix : Matrix where
  fields := explicitFieldShapes
  normalizedPolynomial := normalizedPolynomialFieldsRow
  normalizedValue := normalizedValueFieldsRow
  lowerBound := lowerBoundFieldsRow
  crossBlockLedger := crossBlockInequalityLedgerRow
  flexibleCandidateAssembly := flexibleCandidateAssemblyFieldsRow
  w10CandidatePackedInequalities := w10CandidatePackedInequalitiesRow

/-! ## Public normalized polynomial projections -/

theorem targetUpperConstructionFiveSixteen_of_normalizedPolynomialFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.normalizedPolynomial F).exactTarget C

theorem targetUpperConstructionFiveSixteenAt_of_normalizedPolynomialFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedPolynomialFields F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.normalizedPolynomial F).fixedTarget C n

theorem targetUpperConstructionFiveSixteenEventually_of_normalizedPolynomialFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.normalizedPolynomial F).eventualTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_normalizedPolynomialFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.normalizedPolynomial F).arbitraryTarget C

/-! ## Public normalized value projections -/

theorem targetUpperConstructionFiveSixteen_of_normalizedValueFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.normalizedValue F).exactTarget C

theorem targetUpperConstructionFiveSixteenAt_of_normalizedValueFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedValueFields F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.normalizedValue F).fixedTarget C n

theorem targetUpperConstructionFiveSixteenEventually_of_normalizedValueFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.normalizedValue F).eventualTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_normalizedValueFields
    {F : RoleHingedPeriodSearchFamily}
    (C : NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.normalizedValue F).arbitraryTarget C

/-! ## Public raw lower-bound projections -/

theorem targetUpperConstructionFiveSixteen_of_lowerBoundFields
    {F : RoleHingedPeriodSearchFamily}
    (C : LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.lowerBound F).exactTarget C

theorem targetUpperConstructionFiveSixteenAt_of_lowerBoundFields
    {F : RoleHingedPeriodSearchFamily}
    (C : LowerBoundFields F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.lowerBound F).fixedTarget C n

theorem targetUpperConstructionFiveSixteenEventually_of_lowerBoundFields
    {F : RoleHingedPeriodSearchFamily}
    (C : LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.lowerBound F).eventualTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_lowerBoundFields
    {F : RoleHingedPeriodSearchFamily}
    (C : LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.lowerBound F).arbitraryTarget C

/-! ## Public supporting projections -/

theorem targetUpperConstructionFiveSixteen_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.crossBlockLedger F).exactTarget L

theorem targetUpperConstructionFiveSixteenEventually_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.crossBlockLedger F).eventualTarget L

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockInequalityLedger
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockLedger F).arbitraryTarget L

theorem targetUpperConstructionFiveSixteen_of_flexibleCandidateAssemblyFields
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.flexibleCandidateAssembly.exactTarget F

theorem targetUpperConstructionFiveSixteenEventually_of_flexibleCandidateAssemblyFields
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.flexibleCandidateAssembly.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_flexibleCandidateAssemblyFields
    (F : FlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.flexibleCandidateAssembly.arbitraryTarget F

theorem targetUpperConstructionFiveSixteen_of_w10CandidatePackedInequalities
    (C : W10CandidatePackedInequalities) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.w10CandidatePackedInequalities.exactTarget C

theorem targetUpperConstructionFiveSixteenEventually_of_w10CandidatePackedInequalities
    (C : W10CandidatePackedInequalities) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.w10CandidatePackedInequalities.eventualTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_w10CandidatePackedInequalities
    (C : W10CandidatePackedInequalities) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w10CandidatePackedInequalities.arbitraryTarget C

end

end GeneratedPointClosureW11
end PachToth
end ErdosProblems1066
