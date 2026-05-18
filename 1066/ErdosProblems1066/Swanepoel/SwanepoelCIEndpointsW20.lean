import ErdosProblems1066.Swanepoel.PointwiseAssemblyClosureW19
import ErdosProblems1066.Swanepoel.SwanepoelFinalClosureW19

set_option autoImplicit false

/-!
# W20 Swanepoel CI endpoint aliases

This file is an audit-facing alias surface over the compiled W19 Swanepoel
producer-family closure and final conditional closure.  It introduces no new
root-facing theorem and keeps the W20 names conditional on the same explicit
families as W19.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelCIEndpointsW20

noncomputable section

abbrev W19PointwiseProducerFamilyFields : Type 1 :=
  PointwiseAssemblyClosureW19.PointwiseProducerFamilyFields.{0}

abbrev W20PointwiseProducerFamilyFields : Type 1 :=
  W19PointwiseProducerFamilyFields

abbrev W19PointwiseW16AssemblyFamily : Type 1 :=
  SwanepoelFinalClosureW19.PointwiseW16AssemblyFamily

abbrev W20PointwiseW16AssemblyFamily : Type 1 :=
  W19PointwiseW16AssemblyFamily

abbrev W19ConcreteBlockerInputFamily : Type 1 :=
  SwanepoelFinalClosureW19.ConcreteBlockerInputFamily

abbrev W20ConcreteBlockerInputFamily : Type 1 :=
  W19ConcreteBlockerInputFamily

abbrev Target : Prop :=
  SwanepoelFinalClosureW19.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  SwanepoelFinalClosureW19.LowerBoundAt n C

theorem w19_pointwiseProducerFamily_nonempty
    (P : W19PointwiseProducerFamilyFields) :
    Nonempty W19PointwiseW16AssemblyFamily :=
  PointwiseAssemblyClosureW19.PointwiseProducerFamilyFields.toPointwiseW16AssemblyFamily_nonempty
    P

theorem w20_pointwiseProducerFamily_nonempty
    (P : W20PointwiseProducerFamilyFields) :
    Nonempty W20PointwiseW16AssemblyFamily :=
  w19_pointwiseProducerFamily_nonempty P

theorem w19_targetLowerBoundEightThirtyOne_of_pointwiseProducerFamily
    (P : W19PointwiseProducerFamilyFields) :
    Target :=
  PointwiseAssemblyClosureW19.PointwiseProducerFamilyFields.targetLowerBoundEightThirtyOne
    P

theorem w20_targetLowerBoundEightThirtyOne_of_pointwiseProducerFamily
    (P : W20PointwiseProducerFamilyFields) :
    Target :=
  w19_targetLowerBoundEightThirtyOne_of_pointwiseProducerFamily P

theorem w19_lower_bound_eight_thirty_one_of_pointwiseProducerFamily
    (P : W19PointwiseProducerFamilyFields)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  SwanepoelFinalClosureW19.lower_bound_eight_thirty_one_of_pointwiseW16AssemblyFamily
    P.toPointwiseW16AssemblyFamily n C

theorem w20_lower_bound_eight_thirty_one_of_pointwiseProducerFamily
    (P : W20PointwiseProducerFamilyFields)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  w19_lower_bound_eight_thirty_one_of_pointwiseProducerFamily P n C

theorem w19_targetLowerBoundEightThirtyOne_of_pointwiseW16AssemblyFamily
    (F : W19PointwiseW16AssemblyFamily) :
    Target :=
  SwanepoelFinalClosureW19.targetLowerBoundEightThirtyOne_of_pointwiseW16AssemblyFamily
    F

theorem w20_targetLowerBoundEightThirtyOne_of_pointwiseW16AssemblyFamily
    (F : W20PointwiseW16AssemblyFamily) :
    Target :=
  w19_targetLowerBoundEightThirtyOne_of_pointwiseW16AssemblyFamily F

theorem w19_lower_bound_eight_thirty_one_of_pointwiseW16AssemblyFamily
    (F : W19PointwiseW16AssemblyFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  SwanepoelFinalClosureW19.lower_bound_eight_thirty_one_of_pointwiseW16AssemblyFamily
    F n C

theorem w20_lower_bound_eight_thirty_one_of_pointwiseW16AssemblyFamily
    (F : W20PointwiseW16AssemblyFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  w19_lower_bound_eight_thirty_one_of_pointwiseW16AssemblyFamily F n C

theorem w19_targetLowerBoundEightThirtyOne_of_concreteBlockerInputFamily
    (F : W19ConcreteBlockerInputFamily) :
    Target :=
  SwanepoelFinalClosureW19.targetLowerBoundEightThirtyOne_of_concreteBlockerInputFamily
    F

theorem w20_targetLowerBoundEightThirtyOne_of_concreteBlockerInputFamily
    (F : W20ConcreteBlockerInputFamily) :
    Target :=
  w19_targetLowerBoundEightThirtyOne_of_concreteBlockerInputFamily F

theorem w19_lower_bound_eight_thirty_one_of_concreteBlockerInputFamily
    (F : W19ConcreteBlockerInputFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  SwanepoelFinalClosureW19.lower_bound_eight_thirty_one_of_concreteBlockerInputFamily
    F n C

theorem w20_lower_bound_eight_thirty_one_of_concreteBlockerInputFamily
    (F : W20ConcreteBlockerInputFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  w19_lower_bound_eight_thirty_one_of_concreteBlockerInputFamily F n C

end

end SwanepoelCIEndpointsW20
end Swanepoel

namespace Verified

abbrev SwanepoelW20PointwiseProducerFamilyFields : Type 1 :=
  Swanepoel.SwanepoelCIEndpointsW20.W20PointwiseProducerFamilyFields

abbrev SwanepoelW20PointwiseW16AssemblyFamily : Type 1 :=
  Swanepoel.SwanepoelCIEndpointsW20.W20PointwiseW16AssemblyFamily

abbrev SwanepoelW20ConcreteBlockerInputFamily : Type 1 :=
  Swanepoel.SwanepoelCIEndpointsW20.W20ConcreteBlockerInputFamily

theorem lower_bound_eight_thirty_one_of_swanepoel_w20_pointwiseProducerFamily
    (P : SwanepoelW20PointwiseProducerFamilyFields)
    (n : Nat) (C : _root_.UDConfig n) :
    Swanepoel.SwanepoelCIEndpointsW20.LowerBoundAt n C :=
  Swanepoel.SwanepoelCIEndpointsW20.w20_lower_bound_eight_thirty_one_of_pointwiseProducerFamily
    P n C

theorem lower_bound_eight_thirty_one_of_swanepoel_w20_pointwiseW16AssemblyFamily
    (F : SwanepoelW20PointwiseW16AssemblyFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    Swanepoel.SwanepoelCIEndpointsW20.LowerBoundAt n C :=
  Swanepoel.SwanepoelCIEndpointsW20.w20_lower_bound_eight_thirty_one_of_pointwiseW16AssemblyFamily
    F n C

theorem lower_bound_eight_thirty_one_of_swanepoel_w20_concreteBlockerInputFamily
    (F : SwanepoelW20ConcreteBlockerInputFamily)
    (n : Nat) (C : _root_.UDConfig n) :
    Swanepoel.SwanepoelCIEndpointsW20.LowerBoundAt n C :=
  Swanepoel.SwanepoelCIEndpointsW20.w20_lower_bound_eight_thirty_one_of_concreteBlockerInputFamily
    F n C

end Verified
end ErdosProblems1066
