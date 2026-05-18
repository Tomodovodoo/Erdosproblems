import ErdosProblems1066.PachToth.ConnectorEquationConcrete

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace TranslatedEquationObstruction

noncomputable section

abbrev FourEquationTranslatedRoute : Type :=
  EquationTransitionClosure.EquationTransitionData

abbrev SameOppositeFourEquationTranslatedRoute : Type :=
  EquationTransitionClosure.SameOppositeEquationTransitionData

abbrev FinalProofUsesOnlyFourEquationTranslatedRoute : Prop :=
  Nonempty SameOppositeFourEquationTranslatedRoute

abbrev FinalProofUsesNonRigidOrAlternativeTransitionInterface : Prop :=
  Not FinalProofUsesOnlyFourEquationTranslatedRoute

abbrev FourEquationTranslatedRouteUninhabited : Prop :=
  IsEmpty FourEquationTranslatedRoute

abbrev SameOppositeFourEquationTranslatedRouteUninhabited : Prop :=
  IsEmpty SameOppositeFourEquationTranslatedRoute

theorem false_of_fourEquationTranslatedRoute
    (T : FourEquationTranslatedRoute) :
    False :=
  ConnectorEquationConcrete.false_of_equationTransitionData T

theorem false_of_sameOppositeFourEquationTranslatedRoute
    (T : SameOppositeFourEquationTranslatedRoute) :
    False :=
  ConnectorEquationConcrete.false_of_sameOppositeEquationTransitionData T

theorem fourEquationTranslatedRoute_isEmpty :
    FourEquationTranslatedRouteUninhabited :=
  ⟨false_of_fourEquationTranslatedRoute⟩

theorem sameOppositeFourEquationTranslatedRoute_isEmpty :
    SameOppositeFourEquationTranslatedRouteUninhabited :=
  ⟨false_of_sameOppositeFourEquationTranslatedRoute⟩

theorem no_fourEquationTranslatedRoute :
    Not (Nonempty FourEquationTranslatedRoute) := by
  rintro ⟨T⟩
  exact false_of_fourEquationTranslatedRoute T

theorem no_sameOppositeFourEquationTranslatedRoute :
    Not (Nonempty SameOppositeFourEquationTranslatedRoute) := by
  rintro ⟨T⟩
  exact false_of_sameOppositeFourEquationTranslatedRoute T

theorem no_finalProofUsesOnlyFourEquationTranslatedRoute :
    Not FinalProofUsesOnlyFourEquationTranslatedRoute :=
  no_sameOppositeFourEquationTranslatedRoute

theorem finalProof_uses_nonRigidOrAlternativeTransitionInterface :
    FinalProofUsesNonRigidOrAlternativeTransitionInterface :=
  no_finalProofUsesOnlyFourEquationTranslatedRoute

end

end TranslatedEquationObstruction
end PachToth
end ErdosProblems1066
