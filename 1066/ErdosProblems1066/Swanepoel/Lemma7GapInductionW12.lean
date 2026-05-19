import ErdosProblems1066.Swanepoel.NonconcaveArcAngleFacts

set_option autoImplicit false

/-!
# Lemma 7 degree-three gap induction

This file isolates the checked finite induction in Swanepoel's Lemma 7/E15.
The geometric step is still the project-local Lemma 6 certificate from
`NonconcaveArcAngleFacts`: whenever equality in the prefix count exposes an
empty gap, Lemma 6 forces the next negative/nontriangle event, and that event
increments the next prefix count.

The result is intentionally count-level.  Downstream boundary files can plug in
their concrete cyclic intervals, negative-element counts, and long-arc counts
without redoing the induction.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma7GapInductionW12

open NonconcaveArcAngleFacts

universe u

variable {n : Nat}

/--
Input data for the Lemma 7 prefix induction over consecutive degree-three
gaps.

`count s` is the combined prefix count `N + A` after `s` gap steps from the
chosen initial gap.  The fields say:

* prefix counts are monotone as the interval grows;
* equality `count s = s` exposes the `s`-th empty gap;
* the Lemma 6 certificate turns that gap into the forced conclusion; and
* the forced conclusion contributes the next prefix increment.
-/
structure DegreeThreeGapInductionData
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) where
  length : Nat
  count : Nat -> Nat
  gapAt : Nat -> Prop
  forcedAt : Nat -> Prop
  count_mono_step :
    forall s : Nat, s < length -> count s <= count (s + 1)
  equality_gives_gap :
    forall s : Nat, s < length -> count s = s -> gapAt s
  lemma6_gap_forces_forced :
    forall s : Nat, s < length ->
      Lemma6GapToNegativeCertificate D (gapAt s) (forcedAt s)
  forced_increments_count :
    forall s : Nat, s < length -> forcedAt s -> s + 1 <= count (s + 1)

namespace DegreeThreeGapInductionData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}

/-- Equality in a prefix count exposes a gap, and Lemma 6 supplies the forced
negative/nontriangle conclusion for that gap. -/
theorem forcedAt_of_count_eq
    (C : DegreeThreeGapInductionData D) {s : Nat}
    (hs : s < C.length) (hcount : C.count s = s) :
    C.forcedAt s :=
  (C.lemma6_gap_forces_forced s hs).negative_of_gap
    (C.equality_gives_gap s hs hcount)

/-- One induction step: if the current prefix count has reached `s`, then the
next prefix count reaches `s + 1`.  The equality case is exactly where Lemma 6
is invoked. -/
theorem count_succ_lower_bound
    (C : DegreeThreeGapInductionData D) {s : Nat}
    (hs : s < C.length) (hprev : s <= C.count s) :
    s + 1 <= C.count (s + 1) := by
  if hcount : C.count s = s then
    exact
      C.forced_increments_count s hs
        (C.forcedAt_of_count_eq hs hcount)
  else
    have hmono : C.count s <= C.count (s + 1) :=
      C.count_mono_step s hs
    have hne : Not (s = C.count s) := by
      intro hs_eq
      exact hcount hs_eq.symm
    have hstrict : s < C.count s :=
      Nat.lt_of_le_of_ne hprev hne
    exact Nat.succ_le_of_lt (lt_of_lt_of_le hstrict hmono)

/-- Lemma 7 prefix lower bound: after `s` degree-three gap steps, at least `s`
negative/long-arc events have been counted. -/
theorem count_lower_bound
    (C : DegreeThreeGapInductionData D) :
    forall s : Nat, s <= C.length -> s <= C.count s := by
  intro s hs
  induction s with
  | zero =>
      exact Nat.zero_le _
  | succ s ih =>
      have hslt : s < C.length := Nat.lt_of_succ_le hs
      exact
        C.count_succ_lower_bound hslt
          (ih (Nat.le_of_lt hslt))

/-- The lower bound at the terminal prefix. -/
theorem terminal_count_lower_bound
    (C : DegreeThreeGapInductionData D) :
    C.length <= C.count C.length :=
  C.count_lower_bound C.length le_rfl

end DegreeThreeGapInductionData

/--
The cyclic final-gap data used in the last line of Lemma 7/E16.

If terminal equality held, the final wrap-around gap would again be empty; the
Lemma 6 certificate would then force a negative/nontriangle event in the
initial gap, contradicting the chosen initial empty gap.
-/
structure TerminalGapExclusion
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
    (C : DegreeThreeGapInductionData D) where
  terminalGap : Prop
  terminalForced : Prop
  terminal_equality_gives_gap :
    C.count C.length = C.length -> terminalGap
  terminal_lemma6_gap_forces_forced :
    Lemma6GapToNegativeCertificate D terminalGap terminalForced
  terminal_count_ne_length :
    C.count C.length ≠ C.length

namespace TerminalGapExclusion

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G}
variable {C : DegreeThreeGapInductionData D}

/-- Terminal equality would trigger the final Lemma 6 gap conclusion. -/
theorem terminalForced_of_count_eq
    (T : TerminalGapExclusion C)
    (hcount : C.count C.length = C.length) :
    T.terminalForced :=
  T.terminal_lemma6_gap_forces_forced.negative_of_gap
    (T.terminal_equality_gives_gap hcount)

/-- The terminal count is strictly larger than the number of completed gap
steps, because equality would force an event in the initially empty gap. -/
theorem terminal_count_strict_lower_bound
    (T : TerminalGapExclusion C) :
    C.length < C.count C.length := by
  have hle : C.length <= C.count C.length :=
    C.terminal_count_lower_bound
  have hne : Not (C.length = C.count C.length) := by
    intro hlength
    exact T.terminal_count_ne_length hlength.symm
  exact Nat.lt_of_le_of_ne hle hne

/-- Nat form of the strict terminal conclusion, ready to use as the
`d_3 <= N + A` coverage inequality when `length + 1` is the number of
degree-three boundary vertices. -/
theorem terminal_count_succ_lower_bound
    (T : TerminalGapExclusion C) :
    C.length + 1 <= C.count C.length :=
  Nat.succ_le_of_lt T.terminal_count_strict_lower_bound

end TerminalGapExclusion

end Lemma7GapInductionW12
end Swanepoel
end ErdosProblems1066
