import ErdosProblems1066.Swanepoel.SwanepoelW30FinalAssembly
import ErdosProblems1066.Swanepoel.SwanepoelW30RouteAudit

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W31 final Swanepoel conditional assembly

This file is the W31 final conditional surface for the Swanepoel `8 / 31`
route.  It routes honest W30/W31-facing source packages and audit gates into
the existing W30 final source gate, and from there into the W29 final source
gate.  It does not manufacture an unconditional final source inhabitant.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW31FinalAssembly

noncomputable section

abbrev Target : Prop :=
  SwanepoelW30FinalAssembly.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelW30FinalAssembly.LowerBoundAt n C

abbrev W30FinalSourcePackage : Type 1 :=
  SwanepoelW30FinalAssembly.FinalSourcePackage

abbrev W30FinalSourceGate : Prop :=
  SwanepoelW30FinalAssembly.FinalSourceGate

abbrev W30PointwiseProductSourceData : Type 1 :=
  SwanepoelW30FinalAssembly.PointwiseProductSourceData

abbrev W30StrongestPointwiseRouteSource : Type 1 :=
  SwanepoelW30RouteAudit.StrongestRoute.StrongestPointwiseRouteSource.{0}

abbrev W30StrongestRouteComponents : Prop :=
  SwanepoelW30RouteAudit.StrongestRoute.StrongestRouteComponents.{0}

/-! ## Routing W31-facing gates into the W30 final gate -/

theorem w30FinalSourceGate_of_w30FinalSourcePackage
    (h : Nonempty W30FinalSourcePackage) :
    W30FinalSourceGate :=
  (SwanepoelW30FinalAssembly.nonempty_finalSourcePackage_iff_finalSourceGate).1
    h

theorem w30FinalSourceGate_of_pointwiseProductSourceData
    (h : Nonempty W30PointwiseProductSourceData) :
    W30FinalSourceGate :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem pointwiseProductSourceData_nonempty_of_strongestRouteSource
    (h : Nonempty W30StrongestPointwiseRouteSource) :
    Nonempty W30PointwiseProductSourceData := by
  cases h with
  | intro S =>
      exact Nonempty.intro S.toPointwiseProductSourceData

theorem strongestRouteSource_nonempty_of_components
    (h : W30StrongestRouteComponents) :
    Nonempty W30StrongestPointwiseRouteSource :=
  (SwanepoelW30RouteAudit.StrongestRoute.strongestRouteSource_nonempty_iff_components).2
    h

theorem w30FinalSourceGate_of_strongestRouteSource
    (h : Nonempty W30StrongestPointwiseRouteSource) :
    W30FinalSourceGate :=
  w30FinalSourceGate_of_pointwiseProductSourceData
    (pointwiseProductSourceData_nonempty_of_strongestRouteSource h)

theorem w30FinalSourceGate_of_strongestRouteComponents
    (h : W30StrongestRouteComponents) :
    W30FinalSourceGate :=
  w30FinalSourceGate_of_strongestRouteSource
    (strongestRouteSource_nonempty_of_components h)

abbrev FinalSourceGate : Prop :=
  Nonempty W30FinalSourcePackage \/
    W30FinalSourceGate \/
      Nonempty W30StrongestPointwiseRouteSource \/
        W30StrongestRouteComponents

theorem w30FinalSourceGate_of_finalSourceGate
    (h : FinalSourceGate) :
    W30FinalSourceGate := by
  cases h with
  | inl hPkg =>
      exact w30FinalSourceGate_of_w30FinalSourcePackage hPkg
  | inr hRest =>
      cases hRest with
      | inl hGate =>
          exact hGate
      | inr hRest2 =>
          cases hRest2 with
          | inl hStrongest =>
              exact w30FinalSourceGate_of_strongestRouteSource hStrongest
          | inr hComponents =>
              exact w30FinalSourceGate_of_strongestRouteComponents hComponents

/-! ## W31 final source package -/

inductive FinalSourcePackage : Type 1 where
  | w30FinalSourcePackage :
      W30FinalSourcePackage -> FinalSourcePackage
  | w30FinalSourceGate :
      W30FinalSourceGate -> FinalSourcePackage
  | strongestRouteSource :
      W30StrongestPointwiseRouteSource -> FinalSourcePackage
  | strongestRouteComponents :
      W30StrongestRouteComponents -> FinalSourcePackage

namespace FinalSourcePackage

def toFinalSourceGate
    (P : FinalSourcePackage) :
    FinalSourceGate :=
  match P with
  | w30FinalSourcePackage Q => Or.inl (Nonempty.intro Q)
  | w30FinalSourceGate h => Or.inr (Or.inl h)
  | strongestRouteSource S =>
      Or.inr (Or.inr (Or.inl (Nonempty.intro S)))
  | strongestRouteComponents h =>
      Or.inr (Or.inr (Or.inr h))

def toW30FinalSourceGate
    (P : FinalSourcePackage) :
    W30FinalSourceGate :=
  w30FinalSourceGate_of_finalSourceGate P.toFinalSourceGate

theorem targetLowerBoundEightThirtyOne
    (P : FinalSourcePackage) :
    Target :=
  SwanepoelW30FinalAssembly.targetLowerBoundEightThirtyOne_of_finalSourceGate
    P.toW30FinalSourceGate

end FinalSourcePackage

/-! ## Conditional endpoints -/

theorem nonempty_finalSourcePackage_iff_finalSourceGate :
    Nonempty FinalSourcePackage <-> FinalSourceGate := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact P.toFinalSourceGate
  case mpr =>
    intro h
    cases h with
    | inl hPkg =>
        cases hPkg with
        | intro P =>
            exact
              Nonempty.intro
                (FinalSourcePackage.w30FinalSourcePackage P)
    | inr hRest =>
        cases hRest with
        | inl hGate =>
            exact
              Nonempty.intro
                (FinalSourcePackage.w30FinalSourceGate hGate)
        | inr hRest2 =>
            cases hRest2 with
            | inl hStrongest =>
                cases hStrongest with
                | intro S =>
                    exact
                      Nonempty.intro
                        (FinalSourcePackage.strongestRouteSource S)
            | inr hComponents =>
                exact
                  Nonempty.intro
                    (FinalSourcePackage.strongestRouteComponents hComponents)

theorem targetLowerBoundEightThirtyOne_of_finalSourcePackage
    (P : FinalSourcePackage) :
    Target :=
  P.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_finalSourcePackage
    (P : FinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_finalSourcePackage P n C

theorem targetLowerBoundEightThirtyOne_of_nonempty_finalSourcePackage
    (h : Nonempty FinalSourcePackage) :
    Target := by
  cases h with
  | intro P =>
      exact targetLowerBoundEightThirtyOne_of_finalSourcePackage P

theorem lower_bound_eight_thirty_one_of_nonempty_finalSourcePackage
    (h : Nonempty FinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_nonempty_finalSourcePackage h n C

theorem targetLowerBoundEightThirtyOne_of_finalSourceGate
    (h : FinalSourceGate) :
    Target :=
  SwanepoelW30FinalAssembly.targetLowerBoundEightThirtyOne_of_finalSourceGate
    (w30FinalSourceGate_of_finalSourceGate h)

theorem lower_bound_eight_thirty_one_of_finalSourceGate
    (h : FinalSourceGate)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate h n C

theorem targetLowerBoundEightThirtyOne_of_strongestRouteSource
    (h : Nonempty W30StrongestPointwiseRouteSource) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (Or.inr (Or.inr (Or.inl h)))

theorem lower_bound_eight_thirty_one_of_strongestRouteSource
    (h : Nonempty W30StrongestPointwiseRouteSource)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_strongestRouteSource h n C

theorem targetLowerBoundEightThirtyOne_of_strongestRouteComponents
    (h : W30StrongestRouteComponents) :
    Target :=
  targetLowerBoundEightThirtyOne_of_finalSourceGate
    (Or.inr (Or.inr (Or.inr h)))

theorem lower_bound_eight_thirty_one_of_strongestRouteComponents
    (h : W30StrongestRouteComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  targetLowerBoundEightThirtyOne_of_strongestRouteComponents h n C

/-! ## Exact remaining blocker surface -/

theorem not_finalSourcePackage_iff_not_finalSourceGate :
    Not (Nonempty FinalSourcePackage) <-> Not FinalSourceGate := by
  constructor
  case mp =>
    intro h hGate
    exact h ((nonempty_finalSourcePackage_iff_finalSourceGate).2 hGate)
  case mpr =>
    intro h hPkg
    exact h ((nonempty_finalSourcePackage_iff_finalSourceGate).1 hPkg)

theorem not_finalSourceGate_iff_not_each_gate :
    Not FinalSourceGate <->
      Not (Nonempty W30FinalSourcePackage) /\
        Not W30FinalSourceGate /\
          Not (Nonempty W30StrongestPointwiseRouteSource) /\
            Not W30StrongestRouteComponents := by
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      intro hPkg
      exact h (Or.inl hPkg)
    constructor
    case left =>
      intro hGate
      exact h (Or.inr (Or.inl hGate))
    constructor
    case left =>
      intro hStrongest
      exact h (Or.inr (Or.inr (Or.inl hStrongest)))
    case right =>
      intro hComponents
      exact h (Or.inr (Or.inr (Or.inr hComponents)))
  case mpr =>
    intro h hGate
    cases hGate with
    | inl hPkg =>
        exact h.1 hPkg
    | inr hRest =>
        cases hRest with
        | inl hW30 =>
            exact h.2.1 hW30
        | inr hRest2 =>
            cases hRest2 with
            | inl hStrongest =>
                exact h.2.2.1 hStrongest
            | inr hComponents =>
                exact h.2.2.2 hComponents

theorem not_finalSourcePackage_iff_not_each_gate :
    Not (Nonempty FinalSourcePackage) <->
      Not (Nonempty W30FinalSourcePackage) /\
        Not W30FinalSourceGate /\
          Not (Nonempty W30StrongestPointwiseRouteSource) /\
            Not W30StrongestRouteComponents :=
  Iff.trans not_finalSourcePackage_iff_not_finalSourceGate
    not_finalSourceGate_iff_not_each_gate

theorem finalStatus :
    (FinalSourceGate -> Target) /\
      (Nonempty FinalSourcePackage <-> FinalSourceGate) /\
        (Not (Nonempty FinalSourcePackage) <->
          Not (Nonempty W30FinalSourcePackage) /\
            Not W30FinalSourceGate /\
              Not (Nonempty W30StrongestPointwiseRouteSource) /\
                Not W30StrongestRouteComponents) :=
  And.intro targetLowerBoundEightThirtyOne_of_finalSourceGate
    (And.intro nonempty_finalSourcePackage_iff_finalSourceGate
      not_finalSourcePackage_iff_not_each_gate)

end

end SwanepoelW31FinalAssembly
end Swanepoel

namespace Verified

abbrev SwanepoelW31FinalSourcePackage : Type 1 :=
  Swanepoel.SwanepoelW31FinalAssembly.FinalSourcePackage

abbrev SwanepoelW31FinalSourceGate : Prop :=
  Swanepoel.SwanepoelW31FinalAssembly.FinalSourceGate

abbrev SwanepoelW31StrongestPointwiseRouteSource : Type 1 :=
  Swanepoel.SwanepoelW31FinalAssembly.W30StrongestPointwiseRouteSource

abbrev SwanepoelW31StrongestRouteComponents : Prop :=
  Swanepoel.SwanepoelW31FinalAssembly.W30StrongestRouteComponents

theorem swanepoelW31_finalSource_nonempty_iff_finalSourceGate :
    Nonempty SwanepoelW31FinalSourcePackage <->
      SwanepoelW31FinalSourceGate :=
  Swanepoel.SwanepoelW31FinalAssembly.nonempty_finalSourcePackage_iff_finalSourceGate

theorem swanepoelW31_not_finalSource_iff_not_each_gate :
    Not (Nonempty SwanepoelW31FinalSourcePackage) <->
      Not
          (Nonempty
            Swanepoel.SwanepoelW31FinalAssembly.W30FinalSourcePackage) /\
        Not Swanepoel.SwanepoelW31FinalAssembly.W30FinalSourceGate /\
          Not (Nonempty SwanepoelW31StrongestPointwiseRouteSource) /\
            Not SwanepoelW31StrongestRouteComponents :=
  Swanepoel.SwanepoelW31FinalAssembly.not_finalSourcePackage_iff_not_each_gate

theorem lower_bound_eight_thirty_one_of_swanepoelW31_finalSource
    (h : Nonempty SwanepoelW31FinalSourcePackage)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW31FinalAssembly.lower_bound_eight_thirty_one_of_nonempty_finalSourcePackage
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW31_finalSourceGate
    (h : SwanepoelW31FinalSourceGate)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW31FinalAssembly.lower_bound_eight_thirty_one_of_finalSourceGate
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW31_strongestRouteSource
    (h : Nonempty SwanepoelW31StrongestPointwiseRouteSource)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW31FinalAssembly.lower_bound_eight_thirty_one_of_strongestRouteSource
    h n C

theorem lower_bound_eight_thirty_one_of_swanepoelW31_strongestRouteComponents
    (h : SwanepoelW31StrongestRouteComponents)
    (n : Nat) (C : _root_.UDConfig n) :
    Exists fun s : Finset (Fin n) =>
      C.IsIndep s /\ 31 * s.card >= 8 * n :=
  Swanepoel.SwanepoelW31FinalAssembly.lower_bound_eight_thirty_one_of_strongestRouteComponents
    h n C

end Verified
end ErdosProblems1066
