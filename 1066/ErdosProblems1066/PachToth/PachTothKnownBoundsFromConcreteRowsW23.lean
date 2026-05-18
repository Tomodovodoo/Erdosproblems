import ErdosProblems1066.PachToth.ConcreteValueMatrixFamilyInhabitationW22

set_option autoImplicit false

/-!
# W23 Pach-Toth known-bounds endpoints from value-matrix rows

This module records the strongest source-row endpoints currently available
from the W22 value-matrix row packages.  The public-style bounds below always
take either a concrete row package, a candidate row package, or a nonempty
row-package hypothesis as input.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothKnownBoundsFromConcreteRowsW23

noncomputable section

abbrev ConcreteValueMatrixRowPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage

abbrev CandidateValueMatrixRowPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.CandidateValueMatrixRowPackage

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixFamily

abbrev CandidateValueMatrixFamily : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.CandidateValueMatrixFamily

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev ExactBlockBound (k : Nat) : Prop :=
  Exists fun C : _root_.UDConfig (16 * k) =>
    forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k

abbrev ArbitraryBound (n : Nat) : Prop :=
  Exists fun C : _root_.UDConfig n =>
    forall s : Finset (Fin n), C.IsIndep s ->
      s.card <= Arithmetic.ceilDiv (5 * n) 16

/-! ## Concrete value-matrix row package route -/

def inputPackageOfConcreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    ConcreteValueMatrixFamilyInhabitationW22.W21InputPackage :=
  P.toInputPackage

theorem targetUpperConstructionFiveSixteen_of_concreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    ExactTarget :=
  P.toInputPackage.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    ArbitraryTarget :=
  P.toInputPackage.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenAt_of_concreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) (n : Nat) :
    FixedTarget n :=
  targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixRowPackage
    P n

theorem upper_bound_five_sixteen_exact_of_concreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  targetUpperConstructionFiveSixteen_of_concreteValueMatrixRowPackage P k hk

theorem upper_bound_five_sixteen_arbitrary_of_concreteValueMatrixRowPackage
    (P : ConcreteValueMatrixRowPackage) (n : Nat) :
    ArbitraryBound n :=
  targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixRowPackage
    P n

theorem targetUpperConstructionFiveSixteen_of_nonempty_concreteValueMatrixRowPackage
    (H : Nonempty ConcreteValueMatrixRowPackage) :
    ExactTarget := by
  cases H with
  | intro P =>
      exact targetUpperConstructionFiveSixteen_of_concreteValueMatrixRowPackage
        P

theorem targetUpperConstructionFiveSixteenArbitrary_of_nonempty_concreteValueMatrixRowPackage
    (H : Nonempty ConcreteValueMatrixRowPackage) :
    ArbitraryTarget := by
  cases H with
  | intro P =>
      exact
        targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixRowPackage
          P

theorem upper_bound_five_sixteen_exact_of_nonempty_concreteValueMatrixRowPackage
    (H : Nonempty ConcreteValueMatrixRowPackage)
    (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  targetUpperConstructionFiveSixteen_of_nonempty_concreteValueMatrixRowPackage
    H k hk

theorem upper_bound_five_sixteen_arbitrary_of_nonempty_concreteValueMatrixRowPackage
    (H : Nonempty ConcreteValueMatrixRowPackage) (n : Nat) :
    ArbitraryBound n :=
  targetUpperConstructionFiveSixteenArbitrary_of_nonempty_concreteValueMatrixRowPackage
    H n

/-! ## Candidate value-matrix row package route -/

def candidateValueMatrixFamilyOfCandidateValueMatrixRowPackage
    (P : CandidateValueMatrixRowPackage) :
    CandidateValueMatrixFamily :=
  P.toCandidateValueMatrixFamily

theorem targetUpperConstructionFiveSixteen_of_candidateValueMatrixRowPackage
    (P : CandidateValueMatrixRowPackage) :
    ExactTarget :=
  P.toCandidateValueMatrixFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixRowPackage
    (P : CandidateValueMatrixRowPackage) :
    ArbitraryTarget :=
  P.toCandidateValueMatrixFamily.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenAt_of_candidateValueMatrixRowPackage
    (P : CandidateValueMatrixRowPackage) (n : Nat) :
    FixedTarget n :=
  targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixRowPackage
    P n

theorem upper_bound_five_sixteen_exact_of_candidateValueMatrixRowPackage
    (P : CandidateValueMatrixRowPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  targetUpperConstructionFiveSixteen_of_candidateValueMatrixRowPackage P k hk

theorem upper_bound_five_sixteen_arbitrary_of_candidateValueMatrixRowPackage
    (P : CandidateValueMatrixRowPackage) (n : Nat) :
    ArbitraryBound n :=
  targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixRowPackage
    P n

theorem targetUpperConstructionFiveSixteen_of_nonempty_candidateValueMatrixRowPackage
    (H : Nonempty CandidateValueMatrixRowPackage) :
    ExactTarget := by
  cases H with
  | intro P =>
      exact targetUpperConstructionFiveSixteen_of_candidateValueMatrixRowPackage
        P

theorem targetUpperConstructionFiveSixteenArbitrary_of_nonempty_candidateValueMatrixRowPackage
    (H : Nonempty CandidateValueMatrixRowPackage) :
    ArbitraryTarget := by
  cases H with
  | intro P =>
      exact
        targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixRowPackage
          P

theorem upper_bound_five_sixteen_exact_of_nonempty_candidateValueMatrixRowPackage
    (H : Nonempty CandidateValueMatrixRowPackage)
    (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  targetUpperConstructionFiveSixteen_of_nonempty_candidateValueMatrixRowPackage
    H k hk

theorem upper_bound_five_sixteen_arbitrary_of_nonempty_candidateValueMatrixRowPackage
    (H : Nonempty CandidateValueMatrixRowPackage) (n : Nat) :
    ArbitraryBound n :=
  targetUpperConstructionFiveSixteenArbitrary_of_nonempty_candidateValueMatrixRowPackage
    H n

/-! ## Endpoint packages and exact row-package gates -/

structure ConcreteRowsEndpointPackage where
  rows : ConcreteValueMatrixRowPackage
  exactTarget : ExactTarget
  arbitraryTarget : ArbitraryTarget

namespace ConcreteRowsEndpointPackage

theorem upper_bound_five_sixteen_exact
    (E : ConcreteRowsEndpointPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  E.exactTarget k hk

theorem upper_bound_five_sixteen_arbitrary
    (E : ConcreteRowsEndpointPackage) (n : Nat) :
    ArbitraryBound n :=
  E.arbitraryTarget n

end ConcreteRowsEndpointPackage

def concreteRowsEndpointPackage
    (P : ConcreteValueMatrixRowPackage) :
    ConcreteRowsEndpointPackage where
  rows := P
  exactTarget :=
    targetUpperConstructionFiveSixteen_of_concreteValueMatrixRowPackage P
  arbitraryTarget :=
    targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixRowPackage
      P

theorem nonempty_concreteRowsEndpointPackage_iff_rowPackage :
    Nonempty ConcreteRowsEndpointPackage <->
      Nonempty ConcreteValueMatrixRowPackage := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro E =>
        exact Nonempty.intro E.rows
  case mpr =>
    intro H
    cases H with
    | intro P =>
        exact Nonempty.intro (concreteRowsEndpointPackage P)

structure CandidateRowsEndpointPackage where
  rows : CandidateValueMatrixRowPackage
  exactTarget : ExactTarget
  arbitraryTarget : ArbitraryTarget

namespace CandidateRowsEndpointPackage

theorem upper_bound_five_sixteen_exact
    (E : CandidateRowsEndpointPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockBound k :=
  E.exactTarget k hk

theorem upper_bound_five_sixteen_arbitrary
    (E : CandidateRowsEndpointPackage) (n : Nat) :
    ArbitraryBound n :=
  E.arbitraryTarget n

end CandidateRowsEndpointPackage

def candidateRowsEndpointPackage
    (P : CandidateValueMatrixRowPackage) :
    CandidateRowsEndpointPackage where
  rows := P
  exactTarget :=
    targetUpperConstructionFiveSixteen_of_candidateValueMatrixRowPackage P
  arbitraryTarget :=
    targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixRowPackage
      P

theorem nonempty_candidateRowsEndpointPackage_iff_rowPackage :
    Nonempty CandidateRowsEndpointPackage <->
      Nonempty CandidateValueMatrixRowPackage := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro E =>
        exact Nonempty.intro E.rows
  case mpr =>
    intro H
    cases H with
    | intro P =>
        exact Nonempty.intro (candidateRowsEndpointPackage P)

theorem nonempty_concreteValueMatrixFamily_iff_rowPackage :
    Nonempty ConcreteValueMatrixFamily <->
      Nonempty ConcreteValueMatrixRowPackage :=
  ConcreteValueMatrixFamilyInhabitationW22.nonempty_concreteValueMatrixFamily_iff_rowPackage

theorem nonempty_candidateValueMatrixFamily_iff_rowPackage :
    Nonempty CandidateValueMatrixFamily <->
      Nonempty CandidateValueMatrixRowPackage :=
  ConcreteValueMatrixFamilyInhabitationW22.nonempty_candidateValueMatrixFamily_iff_rowPackage

end

end PachTothKnownBoundsFromConcreteRowsW23

/-! ## Source-specific conditional aliases -/

theorem upper_bound_five_sixteen_exact_of_w23_concreteValueMatrixRowPackage
    (P :
      PachTothKnownBoundsFromConcreteRowsW23.ConcreteValueMatrixRowPackage)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachTothKnownBoundsFromConcreteRowsW23.upper_bound_five_sixteen_exact_of_concreteValueMatrixRowPackage
    P k hk

theorem upper_bound_five_sixteen_arbitrary_of_w23_concreteValueMatrixRowPackage
    (P :
      PachTothKnownBoundsFromConcreteRowsW23.ConcreteValueMatrixRowPackage)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  PachTothKnownBoundsFromConcreteRowsW23.upper_bound_five_sixteen_arbitrary_of_concreteValueMatrixRowPackage
    P n

theorem upper_bound_five_sixteen_exact_of_w23_candidateValueMatrixRowPackage
    (P :
      PachTothKnownBoundsFromConcreteRowsW23.CandidateValueMatrixRowPackage)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachTothKnownBoundsFromConcreteRowsW23.upper_bound_five_sixteen_exact_of_candidateValueMatrixRowPackage
    P k hk

theorem upper_bound_five_sixteen_arbitrary_of_w23_candidateValueMatrixRowPackage
    (P :
      PachTothKnownBoundsFromConcreteRowsW23.CandidateValueMatrixRowPackage)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  PachTothKnownBoundsFromConcreteRowsW23.upper_bound_five_sixteen_arbitrary_of_candidateValueMatrixRowPackage
    P n

end PachToth

namespace Verified

abbrev PachTothW23ConcreteValueMatrixRowPackage : Type :=
  PachToth.PachTothKnownBoundsFromConcreteRowsW23.ConcreteValueMatrixRowPackage

abbrev PachTothW23CandidateValueMatrixRowPackage : Type :=
  PachToth.PachTothKnownBoundsFromConcreteRowsW23.CandidateValueMatrixRowPackage

abbrev PachTothW23ConcreteRowsEndpointPackage : Type :=
  PachToth.PachTothKnownBoundsFromConcreteRowsW23.ConcreteRowsEndpointPackage

abbrev PachTothW23CandidateRowsEndpointPackage : Type :=
  PachToth.PachTothKnownBoundsFromConcreteRowsW23.CandidateRowsEndpointPackage

theorem pachtoth_w23_concreteRowsEndpointPackage_iff_rowPackage :
    Nonempty PachTothW23ConcreteRowsEndpointPackage <->
      Nonempty PachTothW23ConcreteValueMatrixRowPackage :=
  PachToth.PachTothKnownBoundsFromConcreteRowsW23.nonempty_concreteRowsEndpointPackage_iff_rowPackage

theorem pachtoth_w23_candidateRowsEndpointPackage_iff_rowPackage :
    Nonempty PachTothW23CandidateRowsEndpointPackage <->
      Nonempty PachTothW23CandidateValueMatrixRowPackage :=
  PachToth.PachTothKnownBoundsFromConcreteRowsW23.nonempty_candidateRowsEndpointPackage_iff_rowPackage

theorem upper_bound_five_sixteen_exact_of_pachtoth_w23_concreteValueMatrixRowPackage
    (P : PachTothW23ConcreteValueMatrixRowPackage)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.upper_bound_five_sixteen_exact_of_w23_concreteValueMatrixRowPackage
    P k hk

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w23_concreteValueMatrixRowPackage
    (P : PachTothW23ConcreteValueMatrixRowPackage) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w23_concreteValueMatrixRowPackage
    P n

theorem upper_bound_five_sixteen_exact_of_pachtoth_w23_candidateValueMatrixRowPackage
    (P : PachTothW23CandidateValueMatrixRowPackage)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.upper_bound_five_sixteen_exact_of_w23_candidateValueMatrixRowPackage
    P k hk

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w23_candidateValueMatrixRowPackage
    (P : PachTothW23CandidateValueMatrixRowPackage) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w23_candidateValueMatrixRowPackage
    P n

end Verified
end ErdosProblems1066
