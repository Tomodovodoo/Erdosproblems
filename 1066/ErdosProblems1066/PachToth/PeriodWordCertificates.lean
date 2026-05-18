import ErdosProblems1066.PachToth.OrientationWord
import ErdosProblems1066.PachToth.PeriodSearchInterface

set_option autoImplicit false

/-!
# Period-word certificates

This module packages finite orientation words as `PeriodSearchInterface`
certificates.  The constructors keep the algebraic period equations as
explicit fields: a finite word supplies the indexing data, while a caller
supplies the exact `Fin 16` family of local-vertex equations.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodWordCertificates

open FiniteGraph

noncomputable section

abbrev Orientation := OrientationWord.Orientation
abbrev R2 := Prod Real Real
abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations
abbrev FiniteOrientationWord :=
  PeriodSearchInterface.FiniteOrientationWord

/-- Repackage an `OrientationWord.Word` as the finite word expected by the
period-search interface. -/
def finiteOrientationWordOfWord {k : Nat} (hk : 0 < k)
    (W : OrientationWord.Word k) : FiniteOrientationWord where
  length := k
  positive_length := hk
  letter := W.toFin

@[simp]
theorem finiteOrientationWordOfWord_length {k : Nat} (hk : 0 < k)
    (W : OrientationWord.Word k) :
    (finiteOrientationWordOfWord hk W).length = k :=
  rfl

@[simp]
theorem finiteOrientationWordOfWord_letter {k : Nat} (hk : 0 < k)
    (W : OrientationWord.Word k) (i : Fin k) :
    (finiteOrientationWordOfWord hk W).letter i = W i :=
  rfl

/-- Repackage `SearchData` as the finite word expected by the period-search
interface. -/
def finiteOrientationWordOfSearchData
    (D : OrientationWord.SearchData) : FiniteOrientationWord where
  length := D.k
  positive_length := D.hk
  letter := D.orientation

@[simp]
theorem finiteOrientationWordOfSearchData_length
    (D : OrientationWord.SearchData) :
    (finiteOrientationWordOfSearchData D).length = D.k :=
  rfl

@[simp]
theorem finiteOrientationWordOfSearchData_letter
    (D : OrientationWord.SearchData) (i : Fin D.k) :
    (finiteOrientationWordOfSearchData D).letter i = D.orientation i :=
  rfl

/-- Exact algebraic period-equation fields for an orientation word. -/
abbrev AlgebraicEquationsForWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k) : Prop :=
  forall i : Fin 16,
    PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
      (finiteOrientationWordOfWord hk W)
      (BlockPartition.localVertexEquivFin16.symm i)

/-- Exact algebraic period-equation fields for bundled search data. -/
abbrev AlgebraicEquationsForSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData) : Prop :=
  forall i : Fin 16,
    PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
      (finiteOrientationWordOfSearchData D)
      (BlockPartition.localVertexEquivFin16.symm i)

/-- Build the indexed algebraic certificate for an orientation word from exact
local-vertex equations. -/
def indexedAlgebraicCertificateOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation : AlgebraicEquationsForWord O hk base W) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate O base
      (finiteOrientationWordOfWord hk W) where
  equation := equation

/-- Build the indexed algebraic certificate for bundled search data from exact
local-vertex equations. -/
def indexedAlgebraicCertificateOfSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation : AlgebraicEquationsForSearchData O base D) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate O base
      (finiteOrientationWordOfSearchData D) where
  equation := equation

/-- A full period-search certificate built from an orientation word and exact
indexed algebraic equations. -/
def periodSearchCertificateOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation : AlgebraicEquationsForWord O hk base W) :
    PeriodSearchInterface.PeriodSearchCertificate O base where
  word := finiteOrientationWordOfWord hk W
  period := indexedAlgebraicCertificateOfWord O hk base W equation

/-- A full period-search certificate built from bundled search data and exact
indexed algebraic equations. -/
def periodSearchCertificateOfSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation : AlgebraicEquationsForSearchData O base D) :
    PeriodSearchInterface.PeriodSearchCertificate O base where
  word := finiteOrientationWordOfSearchData D
  period := indexedAlgebraicCertificateOfSearchData O base D equation

@[simp]
theorem periodSearchCertificateOfWord_word
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation : AlgebraicEquationsForWord O hk base W) :
    (periodSearchCertificateOfWord O hk base W equation).word =
      finiteOrientationWordOfWord hk W :=
  rfl

@[simp]
theorem periodSearchCertificateOfSearchData_word
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation : AlgebraicEquationsForSearchData O base D) :
    (periodSearchCertificateOfSearchData O base D equation).word =
      finiteOrientationWordOfSearchData D :=
  rfl

/-- The exact algebraic equations for a word imply the generated closure
equation for that word. -/
theorem generatedClosureEquationOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation : AlgebraicEquationsForWord O hk base W) :
    PeriodInterface.GeneratedClosureEquation O hk base W.toFin :=
  (indexedAlgebraicCertificateOfWord O hk base W equation)
    |>.toGeneratedClosureEquation

/-- The exact algebraic equations for bundled search data imply the generated
closure equation for the stored orientation function. -/
theorem generatedClosureEquationOfSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation : AlgebraicEquationsForSearchData O base D) :
    PeriodInterface.GeneratedClosureEquation O D.hk base D.orientation :=
  (indexedAlgebraicCertificateOfSearchData O base D equation)
    |>.toGeneratedClosureEquation

/-- The exact algebraic equations for a word imply the generated final-block
period equation for that word. -/
theorem generatedPeriodEquationOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation : AlgebraicEquationsForWord O hk base W) :
    PeriodInterface.GeneratedPeriodEquation O hk base W.toFin :=
  (periodSearchCertificateOfWord O hk base W equation)
    |>.toGeneratedPeriodEquation

/-- The exact algebraic equations for bundled search data imply the generated
final-block period equation for the stored orientation function. -/
theorem generatedPeriodEquationOfSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation : AlgebraicEquationsForSearchData O base D) :
    PeriodInterface.GeneratedPeriodEquation O D.hk base D.orientation :=
  (periodSearchCertificateOfSearchData O base D equation)
    |>.toGeneratedPeriodEquation

/-- The downstream generated-period hypothesis obtained from exact algebraic
equations for a word. -/
theorem generatedPeriodOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation : AlgebraicEquationsForWord O hk base W) :
    GeneratedSeparationInterface.GeneratedPeriod O hk base W.toFin :=
  (periodSearchCertificateOfWord O hk base W equation)
    |>.toGeneratedPeriod

/-- The downstream generated-period hypothesis obtained from exact algebraic
equations for bundled search data. -/
theorem generatedPeriodOfSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation : AlgebraicEquationsForSearchData O base D) :
    GeneratedSeparationInterface.GeneratedPeriod O D.hk base D.orientation :=
  (periodSearchCertificateOfSearchData O base D equation)
    |>.toGeneratedPeriod

/-! ## All-positive and thresholded finite-word families -/

/-- A finite period-word package for every positive block count.

This is the upstream word/equation core of the all-positive rows exposed by
the route matrix: each member is an actual finite word together with its
exact `Fin 16` algebraic period equations. -/
structure AllPositivePeriodWordFamily
    (O : TransitionObligations)
    (base : LocalVertex -> R2) where
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hk : 0 < k),
      AlgebraicEquationsForWord O hk base (word k hk)

namespace AllPositivePeriodWordFamily

/-- The raw orientation function carried by one finite family member. -/
def orientation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    Fin k -> Orientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i :=
  rfl

/-- The concrete period-search word for one positive block count. -/
def finiteWord
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    FiniteOrientationWord :=
  finiteOrientationWordOfWord hk (F.word k hk)

@[simp]
theorem finiteWord_length
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    (F.finiteWord k hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    (F.finiteWord k hk).letter i = F.orientation k hk i :=
  rfl

/-- One indexed algebraic equation projected from the stored finite family. -/
theorem indexedEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) (i : Fin 16) :
    PeriodSearchInterface.AlgebraicVertexPeriodEquation
      O base (F.finiteWord k hk)
      (BlockPartition.localVertexEquivFin16.symm i) :=
  F.equation k hk i

/-- The indexed algebraic certificate for one positive block count. -/
def indexedAlgebraicCertificate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      O base (F.finiteWord k hk) :=
  indexedAlgebraicCertificateOfWord
    O hk base (F.word k hk) (F.equation k hk)

/-- The full period-search certificate for one positive block count. -/
def periodSearchCertificate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.PeriodSearchCertificate O base :=
  periodSearchCertificateOfWord
    O hk base (F.word k hk) (F.equation k hk)

@[simp]
theorem periodSearchCertificate_word
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    (F.periodSearchCertificate k hk).word = F.finiteWord k hk :=
  rfl

/-- The generated closure equation for one positive finite word. -/
theorem generatedClosureEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      O hk base (F.orientation k hk) :=
  generatedClosureEquationOfWord
    O hk base (F.word k hk) (F.equation k hk)

/-- The generated final-block period equation for one positive finite word. -/
theorem generatedPeriodEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      O hk base (F.orientation k hk) :=
  generatedPeriodEquationOfWord
    O hk base (F.word k hk) (F.equation k hk)

/-- The downstream generated-period hypothesis for one positive finite word. -/
theorem generatedPeriod
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      O hk base (F.orientation k hk) :=
  generatedPeriodOfWord
    O hk base (F.word k hk) (F.equation k hk)

/-- The generated-period hypotheses for every positive block count. -/
theorem generatedPeriodFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base) :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedPeriod
        O hk base (F.orientation k hk) :=
  fun k hk => F.generatedPeriod k hk

/-- Forget an all-positive period-word family to the generated-chain family
interface consumed by downstream closed-placement wrappers. -/
def toGeneratedChainFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _ _ => O
  base := fun _ _ => base
  orientation := F.orientation

@[simp]
theorem toGeneratedChainFamily_O
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.O k hk = O :=
  rfl

@[simp]
theorem toGeneratedChainFamily_base
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.base k hk = base :=
  rfl

@[simp]
theorem toGeneratedChainFamily_orientation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.orientation k hk = F.orientation k hk :=
  rfl

/-- Period hypotheses for the generated-chain family obtained from an
all-positive period-word family. -/
theorem generatedPeriods
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base) :
    F.toGeneratedChainFamily.Periods :=
  F.generatedPeriodFamily

/-- View an all-positive period-word family as an eventual generated-chain
family for any threshold. -/
def toEventualGeneratedChainFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (K0 : Nat) :
    GeneratedSeparationInterface.EventualGeneratedChainFamily K0 where
  O := fun _ _ _ => O
  base := fun _ _ _ => base
  orientation := fun k _hK hk => F.orientation k hk

@[simp]
theorem toEventualGeneratedChainFamily_O
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (K0 k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    (F.toEventualGeneratedChainFamily K0).O k hK hk = O :=
  rfl

@[simp]
theorem toEventualGeneratedChainFamily_base
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (K0 k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    (F.toEventualGeneratedChainFamily K0).base k hK hk = base :=
  rfl

@[simp]
theorem toEventualGeneratedChainFamily_orientation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (K0 k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    (F.toEventualGeneratedChainFamily K0).orientation k hK hk =
      F.orientation k hk :=
  rfl

/-- Eventual period hypotheses obtained by forgetting an all-positive
period-word family above any threshold. -/
theorem eventualGeneratedPeriods
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base)
    (K0 : Nat) :
    (F.toEventualGeneratedChainFamily K0).Periods :=
  fun k _hK hk => F.generatedPeriod k hk

end AllPositivePeriodWordFamily

/-- A thresholded finite period-word package.

This is the word/equation core of the eventual route-matrix rows: finite
words and exact `Fin 16` algebraic period equations are supplied from the
block threshold `K0` onward. -/
structure ThresholdPeriodWordFamily
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (K0 : Nat) where
  word :
    forall (k : Nat), K0 <= k -> 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      AlgebraicEquationsForWord O hk base (word k hK hk)

namespace ThresholdPeriodWordFamily

/-- The raw orientation function carried by one thresholded family member. -/
def orientation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    Fin k -> Orientation :=
  (F.word k hK hk).toFin

@[simp]
theorem orientation_apply
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) (i : Fin k) :
    F.orientation k hK hk i = F.word k hK hk i :=
  rfl

/-- The concrete period-search word for one thresholded block count. -/
def finiteWord
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    FiniteOrientationWord :=
  finiteOrientationWordOfWord hk (F.word k hK hk)

@[simp]
theorem finiteWord_length
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    (F.finiteWord k hK hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) (i : Fin k) :
    (F.finiteWord k hK hk).letter i =
      F.orientation k hK hk i :=
  rfl

/-- One indexed algebraic equation projected from the thresholded family. -/
theorem indexedEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) (i : Fin 16) :
    PeriodSearchInterface.AlgebraicVertexPeriodEquation
      O base (F.finiteWord k hK hk)
      (BlockPartition.localVertexEquivFin16.symm i) :=
  F.equation k hK hk i

/-- The indexed algebraic certificate for one thresholded block count. -/
def indexedAlgebraicCertificate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      O base (F.finiteWord k hK hk) :=
  indexedAlgebraicCertificateOfWord
    O hk base (F.word k hK hk) (F.equation k hK hk)

/-- The full period-search certificate for one thresholded block count. -/
def periodSearchCertificate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodSearchInterface.PeriodSearchCertificate O base :=
  periodSearchCertificateOfWord
    O hk base (F.word k hK hk) (F.equation k hK hk)

@[simp]
theorem periodSearchCertificate_word
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    (F.periodSearchCertificate k hK hk).word = F.finiteWord k hK hk :=
  rfl

/-- The generated closure equation for one thresholded finite word. -/
theorem generatedClosureEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      O hk base (F.orientation k hK hk) :=
  generatedClosureEquationOfWord
    O hk base (F.word k hK hk) (F.equation k hK hk)

/-- The generated final-block period equation for one thresholded finite
word. -/
theorem generatedPeriodEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      O hk base (F.orientation k hK hk) :=
  generatedPeriodEquationOfWord
    O hk base (F.word k hK hk) (F.equation k hK hk)

/-- The downstream generated-period hypothesis for one thresholded finite
word. -/
theorem generatedPeriod
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      O hk base (F.orientation k hK hk) :=
  generatedPeriodOfWord
    O hk base (F.word k hK hk) (F.equation k hK hk)

/-- The generated-period hypotheses for every block count from the threshold
onward. -/
theorem generatedPeriodFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0) :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedPeriod
        O hk base (F.orientation k hK hk) :=
  fun k hK hk => F.generatedPeriod k hK hk

/-- Forget a thresholded period-word family to the eventual generated-chain
family interface. -/
def toEventualGeneratedChainFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0) :
    GeneratedSeparationInterface.EventualGeneratedChainFamily K0 where
  O := fun _ _ _ => O
  base := fun _ _ _ => base
  orientation := F.orientation

@[simp]
theorem toEventualGeneratedChainFamily_O
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    F.toEventualGeneratedChainFamily.O k hK hk = O :=
  rfl

@[simp]
theorem toEventualGeneratedChainFamily_base
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    F.toEventualGeneratedChainFamily.base k hK hk = base :=
  rfl

@[simp]
theorem toEventualGeneratedChainFamily_orientation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    F.toEventualGeneratedChainFamily.orientation k hK hk =
      F.orientation k hK hk :=
  rfl

/-- Period hypotheses for the eventual generated-chain family obtained from a
thresholded period-word family. -/
theorem generatedPeriods
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0) :
    F.toEventualGeneratedChainFamily.Periods :=
  F.generatedPeriodFamily

/-- If the block threshold is at most one, a thresholded finite family is
available for every positive block count. -/
def toAllPositive
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (hK0 : K0 <= 1) :
    AllPositivePeriodWordFamily O base where
  word := fun k hk =>
    F.word k (le_trans hK0 (Nat.succ_le_of_lt hk)) hk
  equation := fun k hk =>
    F.equation k (le_trans hK0 (Nat.succ_le_of_lt hk)) hk

@[simp]
theorem toAllPositive_word
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (hK0 : K0 <= 1)
    (k : Nat) (hk : 0 < k) :
    (F.toAllPositive hK0).word k hk =
      F.word k (le_trans hK0 (Nat.succ_le_of_lt hk)) hk :=
  rfl

/-- Generated period for every positive block count when the threshold is at
most one. -/
theorem generatedPeriod_allPositive
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (hK0 : K0 <= 1)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      O hk base ((F.toAllPositive hK0).orientation k hk) :=
  (F.toAllPositive hK0).generatedPeriod k hk

/-- Generated-period family hypotheses for every positive block count when
the threshold is at most one. -/
theorem generatedPeriods_allPositive
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (hK0 : K0 <= 1) :
    (F.toAllPositive hK0).toGeneratedChainFamily.Periods :=
  (F.toAllPositive hK0).generatedPeriods

/-- Generated period equation for every positive block count when the
threshold is at most one. -/
theorem generatedPeriodEquation_allPositive
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {K0 : Nat}
    (F : ThresholdPeriodWordFamily O base K0)
    (hK0 : K0 <= 1)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      O hk base ((F.toAllPositive hK0).orientation k hk) :=
  (F.toAllPositive hK0).generatedPeriodEquation k hk

end ThresholdPeriodWordFamily

namespace Examples

def onePositive : 0 < 1 :=
  Nat.zero_lt_succ 0

def twoPositive : 0 < 2 :=
  Nat.zero_lt_succ 1

/-- The one-letter same-orientation word. -/
def sameOneWord : OrientationWord.Word 1 :=
  OrientationWord.Word.ofFin fun _ =>
    OrientationData.BlockOrientation.same

/-- Conditional certificate shape for the one-letter word. -/
def sameOnePeriodSearchCertificate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation : AlgebraicEquationsForWord O onePositive base sameOneWord) :
    PeriodSearchInterface.PeriodSearchCertificate O base :=
  periodSearchCertificateOfWord O onePositive base sameOneWord equation

/-- Conditional generated closure equation for the one-letter word. -/
theorem sameOneGeneratedClosureEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation : AlgebraicEquationsForWord O onePositive base sameOneWord) :
    PeriodInterface.GeneratedClosureEquation O onePositive base
      sameOneWord.toFin :=
  generatedClosureEquationOfWord O onePositive base sameOneWord equation

/-- Conditional generated final-block period equation for the one-letter
word. -/
theorem sameOneGeneratedPeriodEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation : AlgebraicEquationsForWord O onePositive base sameOneWord) :
    PeriodInterface.GeneratedPeriodEquation O onePositive base
      sameOneWord.toFin :=
  generatedPeriodEquationOfWord O onePositive base sameOneWord equation

/-- The two-letter same/opposite word. -/
def sameOppositeTwoWord : OrientationWord.Word 2 :=
  OrientationWord.Word.ofFin fun i =>
    if i = (0 : Fin 2) then
      OrientationData.BlockOrientation.same
    else
      OrientationData.BlockOrientation.opposite

/-- Conditional certificate shape for the two-letter same/opposite word. -/
def sameOppositeTwoPeriodSearchCertificate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation :
      AlgebraicEquationsForWord O twoPositive base sameOppositeTwoWord) :
    PeriodSearchInterface.PeriodSearchCertificate O base :=
  periodSearchCertificateOfWord O twoPositive base sameOppositeTwoWord equation

/-- Conditional generated closure equation for the two-letter same/opposite
word. -/
theorem sameOppositeTwoGeneratedClosureEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation :
      AlgebraicEquationsForWord O twoPositive base sameOppositeTwoWord) :
    PeriodInterface.GeneratedClosureEquation O twoPositive base
      sameOppositeTwoWord.toFin :=
  generatedClosureEquationOfWord O twoPositive base sameOppositeTwoWord
    equation

/-- Conditional generated final-block period equation for the two-letter
same/opposite word. -/
theorem sameOppositeTwoGeneratedPeriodEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation :
      AlgebraicEquationsForWord O twoPositive base sameOppositeTwoWord) :
    PeriodInterface.GeneratedPeriodEquation O twoPositive base
      sameOppositeTwoWord.toFin :=
  generatedPeriodEquationOfWord O twoPositive base sameOppositeTwoWord
    equation

end Examples

end

end PeriodWordCertificates
end PachToth
end ErdosProblems1066
