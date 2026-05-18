import ErdosProblems1066.PachToth.ExactFamilyClosure

set_option autoImplicit false

/-!
# Cross-block lower-bound interface

This module isolates the last quantitative separation obligations in the
role-hinged generated-family route.  Period-search data is bundled once, and
the remaining cross-block work is kept as explicit inequalities: a lower table
that is at least one on distinct blocks and is bounded above by the actual
generated cross-block distances.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockLowerBoundsInterface

open ExactFamilyClosure
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev LocalVertexIndex := Fin 16

/-- Encode a local vertex by the checked finite `Fin 16` index. -/
def localVertexIndex (u : LocalVertex) : LocalVertexIndex :=
  BlockPartition.localVertexEquivFin16 u

/-- Decode a checked finite `Fin 16` index to a local vertex. -/
def localVertexOfIndex (a : LocalVertexIndex) : LocalVertex :=
  BlockPartition.localVertexEquivFin16.symm a

@[simp]
theorem localVertexOfIndex_localVertexIndex (u : LocalVertex) :
    localVertexOfIndex (localVertexIndex u) = u :=
  BlockPartition.localVertexEquivFin16.left_inv u

@[simp]
theorem localVertexIndex_localVertexOfIndex (a : LocalVertexIndex) :
    localVertexIndex (localVertexOfIndex a) = a :=
  BlockPartition.localVertexEquivFin16.right_inv a

/-- Role-hinged period-search data before adding the remaining cross-block
lower-bound inequalities. -/
structure RoleHingedPeriodSearchFamily where
  transitions : GeneratedMetricClosure.RoleHingeTransitions
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  period :
    forall (k : Nat) (hk : 0 < k),
      PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (ExactFamilyClosure.finiteOrientationWord k hk (orientation k hk))

/-- The generated point addressed by finite local indices. -/
def indexedGeneratedPoint
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex) : R2 :=
  GeneratedClosedChain.generatedPoint
    F.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase
    (F.orientation k hk) i (localVertexOfIndex u)

/-- A finite-index cross-block lower table for one block count.

For fixed `k`, this is a table over `Fin k x Fin 16 x Fin k x Fin 16`.
The fields are exactly the remaining numeric inequalities: the table entries
are at least one on distinct blocks, and they are lower bounds for the
corresponding generated distances. -/
structure IndexedCrossBlockLowerTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  lower : Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  lower_ge_one :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j -> 1 <= lower i u j v
  lower_bound :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j ->
          lower i u j v <=
            _root_.eucDist
              (indexedGeneratedPoint F hk i u)
              (indexedGeneratedPoint F hk j v)

namespace IndexedCrossBlockLowerTable

/-- Interpret a finite-index lower table as a local-vertex lower table. -/
def toLocalLower
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedCrossBlockLowerTable F k hk) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real :=
  fun i u j v => T.lower i (localVertexIndex u) j (localVertexIndex v)

/-- The finite-index `>= 1` inequalities project to the generated far-apart
cross-block table predicate. -/
theorem toLocalLower_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedCrossBlockLowerTable F k hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      T.toLocalLower := by
  intro i u j v hij
  exact T.lower_ge_one i (localVertexIndex u) j (localVertexIndex v) hij

/-- The finite-index metric inequalities project to the generated far-apart
cross-block distance predicate. -/
theorem toLocalLower_bound
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedCrossBlockLowerTable F k hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      T.toLocalLower := by
  intro i u j v hij
  simpa [toLocalLower, indexedGeneratedPoint] using
    T.lower_bound i (localVertexIndex u) j (localVertexIndex v) hij

/-- A finite-index table supplies generated global separation for one block
count, using the generated far-apart metric wrapper and the checked same-block
metric facts. -/
theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedCrossBlockLowerTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) := by
  exact
    GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
      (GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
        F.transitions)
      T.toLocalLower T.toLocalLower_ge_one T.toLocalLower_bound

end IndexedCrossBlockLowerTable

/-- A family of finite-index cross-block lower tables, one for each positive
block count required by the period-search family.  The remaining facts are
still explicit fields of the per-`k` tables; this structure only says where
to find them. -/
structure IndexedCrossBlockLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      IndexedCrossBlockLowerTable F k hk

namespace IndexedCrossBlockLowerTableFamily

/-- The local-vertex lower table induced by the finite-index table family. -/
def lower
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real :=
  (T.table k hk).toLocalLower

/-- Project a table family to the generated far-apart `>= 1` predicate. -/
theorem lower_ge_one
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      (T.lower k hk) :=
  (T.table k hk).toLocalLower_ge_one

/-- Project a table family to the generated far-apart metric lower-bound
predicate. -/
theorem lower_bound
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      (T.lower k hk) :=
  (T.table k hk).toLocalLower_bound

end IndexedCrossBlockLowerTableFamily

/-- The minimal remaining cross-block lower-bound family over fixed
role-hinged period-search data.

The two hypotheses are deliberately stated as the concrete inequalities, not
as already-packaged global separation: same-block separation is supplied by
the checked exact base block downstream. -/
structure CrossBlockLowerBounds
    (F : RoleHingedPeriodSearchFamily) where
  lower :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j -> 1 <= lower k hk i u j v
  lower_bound :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j ->
          lower k hk i u j v <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint
                F.transitions.toFigure2TransitionObligations hk
                BaseTransitionRealization.exactBase
                (F.orientation k hk) i u)
              (GeneratedClosedChain.generatedPoint
                F.transitions.toFigure2TransitionObligations hk
                BaseTransitionRealization.exactBase
                (F.orientation k hk) j v)

/-- Build the downstream cross-block lower-bound facade from a family of
finite-index tables. -/
def CrossBlockLowerBounds.ofIndexedTables
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F) :
    CrossBlockLowerBounds F where
  lower := T.lower
  lower_ge_one := by
    intro k hk i u j v hij
    exact T.lower_ge_one k hk i u j v hij
  lower_bound := by
    intro k hk i u j v hij
    exact T.lower_bound k hk i u j v hij

namespace CrossBlockLowerBounds

/-- Project the explicit lower-bound inequalities to the named
`GeneratedSeparationFarApart` lower-bound table predicate. -/
def toLowerBoundsAtLeastOne
    {F : RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBounds F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      (H.lower k hk) :=
  H.lower_ge_one k hk

/-- Project the explicit lower-bound inequalities to the named
`GeneratedSeparationFarApart` cross-block distance predicate. -/
def toDistanceLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBounds F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      (H.lower k hk) :=
  H.lower_bound k hk

/-- The generated far-apart wrapper turns the explicit cross-block lower table
into global separation, with same-block separation supplied by the exact base
and role-hinged transition metric facts. -/
theorem toGeneratedGlobalSeparation_direct
    {F : RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBounds F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) := by
  exact
    GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
      (GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
        F.transitions)
      (H.lower k hk) (H.toLowerBoundsAtLeastOne k hk)
      (H.toDistanceLowerBounds k hk)

/-- Reassemble the period-search family and explicit cross-block inequalities
into the final facade package from `ExactFamilyClosure`. -/
def toExactFamilyClosure
    {F : RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBounds F) :
    ExactFamilyClosure.RoleHingedPeriodSearchCrossBlockFamily where
  transitions := F.transitions
  orientation := F.orientation
  period := F.period
  lower := H.lower
  lower_ge_one := H.toLowerBoundsAtLeastOne
  lower_bound := H.toDistanceLowerBounds

/-- The generated global separation projected from the explicit cross-block
inequalities and the exact-base same-block facts. -/
def separated
    {F : RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBounds F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  H.toExactFamilyClosure.separated k hk

/-- The direct far-apart projection agrees propositionally with the separation
obtained through the exact-family closure facade. -/
theorem separated_eq_direct
    {F : RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBounds F)
    (k : Nat) (hk : 0 < k) :
    H.separated k hk = H.toGeneratedGlobalSeparation_direct k hk :=
  rfl

/-- A finite-index table family gives generated separation at every positive
block count. -/
theorem separated_ofIndexedTables
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    (CrossBlockLowerBounds.ofIndexedTables T).separated k hk =
      (T.table k hk).generatedGlobalSeparation :=
  rfl

/-- Forget the lower-bound interface to the role-hinged generated-closure
family used by the exact target facade. -/
def toRoleHingedGeneratedClosureFamily
    {F : RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBounds F) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily :=
  H.toExactFamilyClosure.toRoleHingedGeneratedClosureFamily

/-- Final exact Pach-Toth target from period-search data plus explicit
cross-block lower-bound inequalities. -/
theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBounds F) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_periodSearch_crossBlockLowerBounds
      H.toExactFamilyClosure

/-- Final arbitrary-`n` Pach-Toth target from period-search data plus explicit
cross-block lower-bound inequalities and the checked small cases from
`ExactFamilyClosure`. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBounds F) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_periodSearch_crossBlockLowerBounds
      H.toExactFamilyClosure

end CrossBlockLowerBounds

end

end CrossBlockLowerBoundsInterface
end PachToth
end ErdosProblems1066
