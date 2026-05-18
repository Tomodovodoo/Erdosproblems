import ErdosProblems1066.Swanepoel.PointwiseFamilyProducerW18
import ErdosProblems1066.Swanepoel.TopologyArcClosureW19

set_option autoImplicit false

/-!
# W20 topology arc producer family

This file is the adapter from the W19 topology-arc closure surface to the
W18 pointwise producer-family field
`PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyArcProducerFamilyW20

open PointwiseFamilyProducerW18
open TopologyArcClosureW19

universe u

noncomputable section

abbrev ActualTopologyArcInputs {n : Nat} (C : _root_.UDConfig n) :=
  TopologyArcClosureW19.ActualTopologyArcInputs.{u} C

abbrev W18TopologyArcConcreteProducerFamily :=
  PointwiseFamilyProducerW18.TopologyArcConcreteProducerFamily

abbrev MinimalFailureActualTopologyArcInputsFamily :=
  TopologyArcClosureW19.MinimalFailureActualTopologyArcInputsFamily

abbrev MinimalFailureTopologyArcSourceFields
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  TopologyArcClosureW19.MinimalFailureTopologyArcSourceFields.{u} C hmin

abbrev MinimalFailureTopologyArcSourceFamily :=
  TopologyArcClosureW19.MinimalFailureTopologyArcSourceFamily

abbrev W18TopologyArcSourceFamily :=
  TopologyArcClosureW19.W18TopologyArcSourceFamily

/-- Forget a W19 family of actual topology-arc inputs to the W18 pointwise
producer-family field. -/
def topologyArcConcreteProducerFamilyOfActualInputsFamily
    (F : MinimalFailureActualTopologyArcInputsFamily.{u}) :
    W18TopologyArcConcreteProducerFamily.{u} where
  row := fun C hmin => F.inputsFor C hmin

namespace MinimalFailureActualTopologyArcInputsFamily

/-- W19 actual-input families are already the W18 topology-arc producer rows. -/
def toTopologyArcConcreteProducerFamily
    (F : MinimalFailureActualTopologyArcInputsFamily.{u}) :
    W18TopologyArcConcreteProducerFamily.{u} :=
  topologyArcConcreteProducerFamilyOfActualInputsFamily F

theorem nonempty_topologyArcConcreteProducerFamily
    (F : MinimalFailureActualTopologyArcInputsFamily.{u}) :
    Nonempty W18TopologyArcConcreteProducerFamily.{u} :=
  Nonempty.intro (toTopologyArcConcreteProducerFamily F)

@[simp]
theorem toTopologyArcConcreteProducerFamily_row
    (F : MinimalFailureActualTopologyArcInputsFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (toTopologyArcConcreteProducerFamily F).row C hmin =
      F.inputsFor C hmin :=
  rfl

end MinimalFailureActualTopologyArcInputsFamily

/-- Convert one minimal source row into the W18 actual topology-arc input. -/
def actualTopologyArcInputsOfSourceFields
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    ActualTopologyArcInputs.{u} C :=
  P.toActualTopologyArcInputs

/-- A W19 source family supplies the W18 pointwise topology-arc producer. -/
def topologyArcConcreteProducerFamilyOfSourceFamily
    (F : MinimalFailureTopologyArcSourceFamily.{u}) :
    W18TopologyArcConcreteProducerFamily.{u} where
  row := fun C hmin => F.inputsFor C hmin

namespace MinimalFailureTopologyArcSourceFields

theorem nonempty_actualTopologyArcInputs
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    Nonempty (ActualTopologyArcInputs.{u} C) :=
  TopologyArcClosureW19.MinimalFailureTopologyArcSourceFields.nonempty_actualTopologyArcInputs
    P

@[simp]
theorem actualTopologyArcInputsOfSourceFields_eq
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : MinimalFailureTopologyArcSourceFields.{u} C hmin) :
    actualTopologyArcInputsOfSourceFields P = P.toActualTopologyArcInputs :=
  rfl

end MinimalFailureTopologyArcSourceFields

namespace MinimalFailureTopologyArcSourceFamily

/-- Source-family rows convert directly to the W18 pointwise topology-arc
producer family. -/
def toTopologyArcConcreteProducerFamily
    (F : MinimalFailureTopologyArcSourceFamily.{u}) :
    W18TopologyArcConcreteProducerFamily.{u} :=
  topologyArcConcreteProducerFamilyOfSourceFamily F

theorem nonempty_topologyArcConcreteProducerFamily
    (F : MinimalFailureTopologyArcSourceFamily.{u}) :
    Nonempty W18TopologyArcConcreteProducerFamily.{u} :=
  Nonempty.intro (toTopologyArcConcreteProducerFamily F)

@[simp]
theorem toTopologyArcConcreteProducerFamily_row
    (F : MinimalFailureTopologyArcSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (toTopologyArcConcreteProducerFamily F).row C hmin =
      (F.row C hmin).toActualTopologyArcInputs :=
  rfl

@[simp]
theorem toTopologyArcConcreteProducerFamily_row_inputsFor
    (F : MinimalFailureTopologyArcSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (toTopologyArcConcreteProducerFamily F).row C hmin =
      F.inputsFor C hmin :=
  rfl

end MinimalFailureTopologyArcSourceFamily

/-- The W18 source-family surface can also be forgotten directly to the
pointwise topology-arc producer family. -/
def topologyArcConcreteProducerFamilyOfW18SourceFamily
    (F : W18TopologyArcSourceFamily.{u}) :
    W18TopologyArcConcreteProducerFamily.{u} where
  row := fun C hmin => F.inputsFor C hmin

namespace W18TopologyArcSourceFamily

def toTopologyArcConcreteProducerFamily
    (F : W18TopologyArcSourceFamily.{u}) :
    W18TopologyArcConcreteProducerFamily.{u} :=
  topologyArcConcreteProducerFamilyOfW18SourceFamily F

theorem nonempty_topologyArcConcreteProducerFamily
    (F : W18TopologyArcSourceFamily.{u}) :
    Nonempty W18TopologyArcConcreteProducerFamily.{u} :=
  Nonempty.intro (toTopologyArcConcreteProducerFamily F)

@[simp]
theorem toTopologyArcConcreteProducerFamily_row
    (F : W18TopologyArcSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (toTopologyArcConcreteProducerFamily F).row C hmin =
      F.inputsFor C hmin :=
  rfl

end W18TopologyArcSourceFamily

theorem topologyArcConcreteProducerFamily_nonempty_of_actualInputsFamily
    (F : MinimalFailureActualTopologyArcInputsFamily.{u}) :
    Nonempty W18TopologyArcConcreteProducerFamily.{u} :=
  MinimalFailureActualTopologyArcInputsFamily.nonempty_topologyArcConcreteProducerFamily
    F

theorem topologyArcConcreteProducerFamily_nonempty_of_sourceFamily
    (F : MinimalFailureTopologyArcSourceFamily.{u}) :
    Nonempty W18TopologyArcConcreteProducerFamily.{u} :=
  MinimalFailureTopologyArcSourceFamily.nonempty_topologyArcConcreteProducerFamily
    F

theorem topologyArcConcreteProducerFamily_nonempty_of_w18SourceFamily
    (F : W18TopologyArcSourceFamily.{u}) :
    Nonempty W18TopologyArcConcreteProducerFamily.{u} :=
  W18TopologyArcSourceFamily.nonempty_topologyArcConcreteProducerFamily F

end

end TopologyArcProducerFamilyW20

namespace Verified

universe u

abbrev SwanepoelW20TopologyArcSourceFields
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : Swanepoel.MinimalGraphFacts.IsMinimalClearedFailure C) :=
  Swanepoel.TopologyArcProducerFamilyW20.MinimalFailureTopologyArcSourceFields.{u}
    C hmin

abbrev SwanepoelW20TopologyArcSourceFamily :=
  Swanepoel.TopologyArcProducerFamilyW20.MinimalFailureTopologyArcSourceFamily

abbrev SwanepoelW20TopologyArcConcreteProducerFamily :=
  Swanepoel.TopologyArcProducerFamilyW20.W18TopologyArcConcreteProducerFamily

theorem swanepoelW20TopologyArcConcreteProducerFamily_nonempty_of_sourceFamily
    (F : SwanepoelW20TopologyArcSourceFamily.{u}) :
    Nonempty SwanepoelW20TopologyArcConcreteProducerFamily.{u} :=
  Swanepoel.TopologyArcProducerFamilyW20.topologyArcConcreteProducerFamily_nonempty_of_sourceFamily
    F

end Verified
end Swanepoel
end ErdosProblems1066
