import ErdosProblems1066.Swanepoel.NoCutPointwiseBridgeW32
import ErdosProblems1066.Swanepoel.FrameCyclicOrderAssemblyW32
import ErdosProblems1066.Swanepoel.SwanepoelW32RouteAudit
import ErdosProblems1066.Swanepoel.K23ObstructionConcrete
import ErdosProblems1066.Swanepoel.LateTriplesInterface
import ErdosProblems1066.Swanepoel.NoEarlyTripleConcrete
import ErdosProblems1066.Swanepoel.NoEarlyRouteCoverageClosureW32

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W34 common-neighbor route coverage source

This file supplies the checked source bridge for the W32 no-early
`commonNeighbor` branch.  The geometric input still needed from the selected
boundary-label configuration is the explicit five-start
three-common-neighbor obstruction row.  Once that row is available, the
graph-theoretic conversion below builds the common-neighbor-card obstruction
rows and therefore actual W32 route coverage data.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace CommonNeighborRouteCoverageSourceW34

open K23ObstructionConcrete
open GraphBridge
open K23NoEarlyClosure
open Lemma10Bridge
open LateTriplesInterface
open Lemma9ProducerFamilyW20
open Lemma9SourceFamilyConcreteW27
open LocalExclusions
open LocalConfigurations
open FrameCyclicOrderAssemblyW32
open NoCutPointwiseBridgeW32
open NoEarlyTripleConcrete
open NoEarlyRouteCoverageClosureW32

universe u

variable {V : Type u} {G : LocalConfigurations.LocalGraph V}

/-! ## Three-common-neighbor witnesses feed card witnesses -/

variable [Fintype V] [DecidableEq V]

/-- Three explicit common neighbors give the card-lower-bound witness used by
the common-neighbor-card route. -/
def commonNeighborCardLowerWitnessOfThreeCommonNeighbor
    (W : ThreeCommonNeighborWitness G) :
    CommonNeighborCardLowerWitness G where
  left0 := W.left0
  left1 := W.left1
  left_ne := W.left_ne
  card_ge_three := by
    classical
    have hsubset :
        ({W.right0, W.right1, W.right2} : Finset V) ⊆
          LocalGraph.commonNeighborFinset G W.left0 W.left1 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simpa using
          (LocalGraph.mem_commonNeighborFinset
            G W.left0 W.left1 W.right0).2 W.right0_common
      · simpa using
          (LocalGraph.mem_commonNeighborFinset
            G W.left0 W.left1 W.right1).2 W.right1_common
      · simpa using
          (LocalGraph.mem_commonNeighborFinset
            G W.left0 W.left1 W.right2).2 W.right2_common
    have hcard :
        ({W.right0, W.right1, W.right2} : Finset V).card = 3 := by
      simp [W.right01_ne, W.right02_ne, W.right12_ne]
    have hle := Finset.card_le_card hsubset
    simpa [hcard] using hle

variable {P : BrokenLatticePredicates G 8}

/-- Lower a five-start three-common-neighbor obstruction package to the
common-neighbor-card obstruction package. -/
def commonNeighborCardObstructionInputsOfThreeCommonNeighbor
    (H : M8ConcreteThreeCommonNeighborObstructionInputs P) :
    M8ConcreteCommonNeighborCardObstructionInputs P where
  witness_start1 h :=
    commonNeighborCardLowerWitnessOfThreeCommonNeighbor (H.witness_start1 h)
  witness_start2 h :=
    commonNeighborCardLowerWitnessOfThreeCommonNeighbor (H.witness_start2 h)
  witness_start3 h :=
    commonNeighborCardLowerWitnessOfThreeCommonNeighbor (H.witness_start3 h)
  witness_start4 h :=
    commonNeighborCardLowerWitnessOfThreeCommonNeighbor (H.witness_start4 h)
  witness_start5 h :=
    commonNeighborCardLowerWitnessOfThreeCommonNeighbor (H.witness_start5 h)

/-- A card-lower-bound witness determines explicit three common neighbors by
extracting the labelled `K_{2,3}` supplied by the finite common-neighbor
lower-bound theorem. -/
def threeCommonNeighborWitnessOfCommonNeighborCardLowerWitness
    (W : CommonNeighborCardLowerWitness G) :
    ThreeCommonNeighborWitness G :=
  ThreeCommonNeighborWitness.ofHasK23 W.hasK23

/-- Raise a five-start common-neighbor-card obstruction package to explicit
three-common-neighbor witnesses. -/
def threeCommonNeighborObstructionInputsOfCommonNeighborCard
    (H : M8ConcreteCommonNeighborCardObstructionInputs P) :
    M8ConcreteThreeCommonNeighborObstructionInputs P where
  witness_start1 h :=
    threeCommonNeighborWitnessOfCommonNeighborCardLowerWitness
      (H.witness_start1 h)
  witness_start2 h :=
    threeCommonNeighborWitnessOfCommonNeighborCardLowerWitness
      (H.witness_start2 h)
  witness_start3 h :=
    threeCommonNeighborWitnessOfCommonNeighborCardLowerWitness
      (H.witness_start3 h)
  witness_start4 h :=
    threeCommonNeighborWitnessOfCommonNeighborCardLowerWitness
      (H.witness_start4 h)
  witness_start5 h :=
    threeCommonNeighborWitnessOfCommonNeighborCardLowerWitness
      (H.witness_start5 h)

/-! ## Explicit incidence rows feed witness rows -/

/-- A concrete incidence row for three common neighbors of one fixed pair.

The two `standard` witnesses are the already-known common neighbors.  The
`third` witness is supplied by two explicit adjacency rows to the same left
pair. -/
structure ThreeCommonNeighborIncidenceDatum
    {V : Type u} (G : LocalGraph V) where
  left0 : V
  left1 : V
  standard0 : V
  standard1 : V
  third : V
  left_ne : Not (left0 = left1)
  standard01_ne : Not (standard0 = standard1)
  standard0_ne_third : Not (standard0 = third)
  standard1_ne_third : Not (standard1 = third)
  standard0_common : G.CommonNeighbor left0 left1 standard0
  standard1_common : G.CommonNeighbor left0 left1 standard1
  third_adj_left0 : G.Adj third left0
  third_adj_left1 : G.Adj third left1

namespace ThreeCommonNeighborIncidenceDatum

/-- Forget the provenance of the incidence row and produce the explicit
three-common-neighbor witness used downstream. -/
def toThreeCommonNeighborWitness
    {V : Type u} {G : LocalGraph V}
    (D : ThreeCommonNeighborIncidenceDatum G) :
    ThreeCommonNeighborWitness G where
  left0 := D.left0
  left1 := D.left1
  right0 := D.standard0
  right1 := D.standard1
  right2 := D.third
  left_ne := D.left_ne
  right01_ne := D.standard01_ne
  right02_ne := D.standard0_ne_third
  right12_ne := D.standard1_ne_third
  right0_common := D.standard0_common
  right1_common := D.standard1_common
  right2_common := And.intro D.third_adj_left0 D.third_adj_left1

/-- The same incidence row gives the finite common-neighbor-card lower-bound
witness. -/
def toCommonNeighborCardLowerWitness
    {V : Type u} {G : LocalGraph V} [Fintype V] [DecidableEq V]
    (D : ThreeCommonNeighborIncidenceDatum G) :
    CommonNeighborCardLowerWitness G :=
  commonNeighborCardLowerWitnessOfThreeCommonNeighbor
    D.toThreeCommonNeighborWitness

/-- The third incidence, oriented from the first left endpoint to the third
common neighbor.  In the selected boundary-label application this is the
route-facing bad-adjacency row `Adj q_i s_{i+1}`. -/
theorem left0_adj_third
    {V : Type u} {G : LocalGraph V}
    (D : ThreeCommonNeighborIncidenceDatum G) :
    G.Adj D.left0 D.third :=
  G.symm D.third_adj_left0

/-- The third incidence, oriented from the second left endpoint to the third
common neighbor. -/
theorem left1_adj_third
    {V : Type u} {G : LocalGraph V}
    (D : ThreeCommonNeighborIncidenceDatum G) :
    G.Adj D.left1 D.third :=
  G.symm D.third_adj_left1

end ThreeCommonNeighborIncidenceDatum

/-- Five explicit incidence rows kept at the incidence level before they are
forgotten to three-common-neighbor or common-neighbor-card witnesses.

For the selected K23 bad-adjacency route, the projections
`start1_left0_adj_third` through `start5_left0_adj_third` are exactly the five
route-facing incidences `Adj q_1 s_2`, ..., `Adj q_5 s_6` after the local
labels are identified with `left0` and `third`. -/
structure M8ConcreteThreeCommonNeighborIncidenceInputs
    {V : Type u} {G : LocalGraph V}
    (P : BrokenLatticePredicates G 8) where
  witness_start1 :
    P.tripleEquality start1 -> ThreeCommonNeighborIncidenceDatum G
  witness_start2 :
    P.tripleEquality start2 -> ThreeCommonNeighborIncidenceDatum G
  witness_start3 :
    P.tripleEquality start3 -> ThreeCommonNeighborIncidenceDatum G
  witness_start4 :
    P.tripleEquality start4 -> ThreeCommonNeighborIncidenceDatum G
  witness_start5 :
    P.tripleEquality start5 -> ThreeCommonNeighborIncidenceDatum G

namespace M8ConcreteThreeCommonNeighborIncidenceInputs

variable {P : BrokenLatticePredicates G 8}

/-- Constructor form for the five concrete incidence rows, keeping the
incidence data available before any witness projection is applied. -/
def ofWitnessStarts
    (witness_start1 :
      P.tripleEquality start1 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start2 :
      P.tripleEquality start2 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start3 :
      P.tripleEquality start3 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start4 :
      P.tripleEquality start4 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start5 :
      P.tripleEquality start5 -> ThreeCommonNeighborIncidenceDatum G) :
    M8ConcreteThreeCommonNeighborIncidenceInputs P where
  witness_start1 := witness_start1
  witness_start2 := witness_start2
  witness_start3 := witness_start3
  witness_start4 := witness_start4
  witness_start5 := witness_start5

/-- Forget the five incidence rows to the existing explicit
three-common-neighbor obstruction inputs. -/
def toThreeCommonNeighborObstructionInputs
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P) :
    M8ConcreteThreeCommonNeighborObstructionInputs P where
  witness_start1 h := (H.witness_start1 h).toThreeCommonNeighborWitness
  witness_start2 h := (H.witness_start2 h).toThreeCommonNeighborWitness
  witness_start3 h := (H.witness_start3 h).toThreeCommonNeighborWitness
  witness_start4 h := (H.witness_start4 h).toThreeCommonNeighborWitness
  witness_start5 h := (H.witness_start5 h).toThreeCommonNeighborWitness

/-- Forget the five incidence rows all the way to the concrete labelled
`K_{2,3}` obstruction inputs. -/
def toK23ObstructionInputs
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P) :
    NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs P :=
  H.toThreeCommonNeighborObstructionInputs.toK23ObstructionInputs

/-- Forget the five incidence rows to the existing common-neighbor-card
obstruction inputs. -/
def toCommonNeighborObstructionInputs
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P) :
    M8ConcreteCommonNeighborCardObstructionInputs P where
  witness_start1 h := (H.witness_start1 h).toCommonNeighborCardLowerWitness
  witness_start2 h := (H.witness_start2 h).toCommonNeighborCardLowerWitness
  witness_start3 h := (H.witness_start3 h).toCommonNeighborCardLowerWitness
  witness_start4 h := (H.witness_start4 h).toCommonNeighborCardLowerWitness
  witness_start5 h := (H.witness_start5 h).toCommonNeighborCardLowerWitness

/- First selected bad-adjacency incidence, exposed before forgetting the
incidence row to a common-neighbor witness. -/
omit [Fintype V] [DecidableEq V] in
lemma start1_left0_adj_third
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P)
    (h : P.tripleEquality start1) :
    G.Adj (H.witness_start1 h).left0 (H.witness_start1 h).third :=
  (H.witness_start1 h).left0_adj_third

/- First selected second-left incidence, exposed before forgetting the
incidence row to a common-neighbor witness. -/
omit [Fintype V] [DecidableEq V] in
lemma start1_left1_adj_third
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P)
    (h : P.tripleEquality start1) :
    G.Adj (H.witness_start1 h).left1 (H.witness_start1 h).third :=
  (H.witness_start1 h).left1_adj_third

/- Second selected bad-adjacency incidence, exposed before forgetting the
incidence row to a common-neighbor witness. -/
omit [Fintype V] [DecidableEq V] in
lemma start2_left0_adj_third
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P)
    (h : P.tripleEquality start2) :
    G.Adj (H.witness_start2 h).left0 (H.witness_start2 h).third :=
  (H.witness_start2 h).left0_adj_third

/- Second selected second-left incidence, exposed before forgetting the
incidence row to a common-neighbor witness. -/
omit [Fintype V] [DecidableEq V] in
lemma start2_left1_adj_third
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P)
    (h : P.tripleEquality start2) :
    G.Adj (H.witness_start2 h).left1 (H.witness_start2 h).third :=
  (H.witness_start2 h).left1_adj_third

/- Third selected bad-adjacency incidence, exposed before forgetting the
incidence row to a common-neighbor witness. -/
omit [Fintype V] [DecidableEq V] in
lemma start3_left0_adj_third
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P)
    (h : P.tripleEquality start3) :
    G.Adj (H.witness_start3 h).left0 (H.witness_start3 h).third :=
  (H.witness_start3 h).left0_adj_third

/- Third selected second-left incidence, exposed before forgetting the
incidence row to a common-neighbor witness. -/
omit [Fintype V] [DecidableEq V] in
lemma start3_left1_adj_third
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P)
    (h : P.tripleEquality start3) :
    G.Adj (H.witness_start3 h).left1 (H.witness_start3 h).third :=
  (H.witness_start3 h).left1_adj_third

/- Fourth selected bad-adjacency incidence, exposed before forgetting the
incidence row to a common-neighbor witness. -/
omit [Fintype V] [DecidableEq V] in
lemma start4_left0_adj_third
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P)
    (h : P.tripleEquality start4) :
    G.Adj (H.witness_start4 h).left0 (H.witness_start4 h).third :=
  (H.witness_start4 h).left0_adj_third

/- Fourth selected second-left incidence, exposed before forgetting the
incidence row to a common-neighbor witness. -/
omit [Fintype V] [DecidableEq V] in
lemma start4_left1_adj_third
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P)
    (h : P.tripleEquality start4) :
    G.Adj (H.witness_start4 h).left1 (H.witness_start4 h).third :=
  (H.witness_start4 h).left1_adj_third

/- Fifth selected bad-adjacency incidence, exposed before forgetting the
incidence row to a common-neighbor witness. -/
omit [Fintype V] [DecidableEq V] in
lemma start5_left0_adj_third
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P)
    (h : P.tripleEquality start5) :
    G.Adj (H.witness_start5 h).left0 (H.witness_start5 h).third :=
  (H.witness_start5 h).left0_adj_third

/- Fifth selected second-left incidence, exposed before forgetting the
incidence row to a common-neighbor witness. -/
omit [Fintype V] [DecidableEq V] in
lemma start5_left1_adj_third
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P)
    (h : P.tripleEquality start5) :
    G.Adj (H.witness_start5 h).left1 (H.witness_start5 h).third :=
  (H.witness_start5 h).left1_adj_third

end M8ConcreteThreeCommonNeighborIncidenceInputs

/-! ## Bad-adjacency cross rows feed incidence rows -/

/-- The right `q_{i+1}` label used by the bad-adjacency row beginning at `i`. -/
def m8BadAdjacencyRightTriangleIndexOfNat
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    TriangleIndex 8 :=
  Subtype.mk (i + 1) (by
    omega)

@[simp]
theorem m8BadAdjacencyRightTriangleIndexOfNat_val
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    (m8BadAdjacencyRightTriangleIndexOfNat i hi hi10).1 = i + 1 :=
  rfl

/-- All standard data for one bad-adjacency common-neighbor row except the
cross adjacency `Adj q_i s_{i+1}` itself.

The named K23 cross rows supply the missing incidence from the third common
neighbor to the first left endpoint; this package supplies the two standard
common neighbors, distinctness rows, and the companion incidence to
`q_{i+1}`. -/
structure BadAdjacencyCommonNeighborStandardDatumAt
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8)
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    Type where
  standard0 : Fin n
  standard1 : Fin n
  left_ne :
    Not
      (labels.q (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10) =
        labels.q (m8BadAdjacencyRightTriangleIndexOfNat i hi hi10))
  standard01_ne : Not (standard0 = standard1)
  standard0_ne_third :
    Not
      (standard0 =
        labels.s (m8BadAdjacencyRightExtraIndexOfNat i hi hi10))
  standard1_ne_third :
    Not
      (standard1 =
        labels.s (m8BadAdjacencyRightExtraIndexOfNat i hi hi10))
  standard0_common :
    (unitDistanceLocalGraph C).CommonNeighbor
      (labels.q (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10))
      (labels.q (m8BadAdjacencyRightTriangleIndexOfNat i hi hi10))
      standard0
  standard1_common :
    (unitDistanceLocalGraph C).CommonNeighbor
      (labels.q (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10))
      (labels.q (m8BadAdjacencyRightTriangleIndexOfNat i hi hi10))
      standard1
  third_adj_left1 :
    (unitDistanceLocalGraph C).Adj
      (labels.s (m8BadAdjacencyRightExtraIndexOfNat i hi hi10))
      (labels.q (m8BadAdjacencyRightTriangleIndexOfNat i hi hi10))

namespace BadAdjacencyCommonNeighborStandardDatumAt

/-- Combine the standard part of a bad-adjacency common-neighbor datum with
the named cross adjacency row `Adj q_i s_{i+1}`. -/
def toThreeCommonNeighborIncidenceDatumOfCrossAdjacencyRowAt
    {n : Nat} {C : _root_.UDConfig n}
    {labels : BrokenLatticeLabels (Fin n) 8}
    {i : Nat} {hi : 1 <= i} {hi10 : i <= 10}
    (D : BadAdjacencyCommonNeighborStandardDatumAt C labels i hi hi10)
    (hcross : M8BadAdjacencyCrossAdjacencyRowAt C labels i hi hi10) :
    ThreeCommonNeighborIncidenceDatum (unitDistanceLocalGraph C) where
  left0 := labels.q (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10)
  left1 := labels.q (m8BadAdjacencyRightTriangleIndexOfNat i hi hi10)
  standard0 := D.standard0
  standard1 := D.standard1
  third := labels.s (m8BadAdjacencyRightExtraIndexOfNat i hi hi10)
  left_ne := D.left_ne
  standard01_ne := D.standard01_ne
  standard0_ne_third := D.standard0_ne_third
  standard1_ne_third := D.standard1_ne_third
  standard0_common := D.standard0_common
  standard1_common := D.standard1_common
  third_adj_left0 := (unitDistanceLocalGraph C).symm hcross
  third_adj_left1 := D.third_adj_left1

/-- Combine the standard part of a bad-adjacency common-neighbor datum with
the named cross distance row `|q_i s_{i+1}| = 1`. -/
def toThreeCommonNeighborIncidenceDatumOfCrossDistanceRowAt
    {n : Nat} {C : _root_.UDConfig n}
    {labels : BrokenLatticeLabels (Fin n) 8}
    {i : Nat} {hi : 1 <= i} {hi10 : i <= 10}
    (D : BadAdjacencyCommonNeighborStandardDatumAt C labels i hi hi10)
    (hcross : M8BadAdjacencyCrossDistanceRowAt C labels i hi hi10) :
    ThreeCommonNeighborIncidenceDatum (unitDistanceLocalGraph C) :=
  D.toThreeCommonNeighborIncidenceDatumOfCrossAdjacencyRowAt
    ((m8BadAdjacencyCrossAdjacencyRowAt_iff_distanceRowAt
      C labels i hi hi10).2 hcross)

end BadAdjacencyCommonNeighborStandardDatumAt

/-- Five standard bad-adjacency common-neighbor rows, before the named K23
cross adjacency or distance rows supply the missing third-neighbor incidence.
-/
structure M8BadAdjacencyCommonNeighborStandardRows
    {n : Nat} (C : _root_.UDConfig n)
    (P : BrokenLatticePredicates (unitDistanceLocalGraph C) 8) :
    Type where
  witness_start1 :
    P.tripleEquality start1 ->
      BadAdjacencyCommonNeighborStandardDatumAt
        C P.labels 1 (by omega) (by omega)
  witness_start2 :
    P.tripleEquality start2 ->
      BadAdjacencyCommonNeighborStandardDatumAt
        C P.labels 2 (by omega) (by omega)
  witness_start3 :
    P.tripleEquality start3 ->
      BadAdjacencyCommonNeighborStandardDatumAt
        C P.labels 3 (by omega) (by omega)
  witness_start4 :
    P.tripleEquality start4 ->
      BadAdjacencyCommonNeighborStandardDatumAt
        C P.labels 4 (by omega) (by omega)
  witness_start5 :
    P.tripleEquality start5 ->
      BadAdjacencyCommonNeighborStandardDatumAt
        C P.labels 5 (by omega) (by omega)

namespace M8BadAdjacencyCommonNeighborStandardRows

variable {n : Nat} {C : _root_.UDConfig n}
variable {P : BrokenLatticePredicates (unitDistanceLocalGraph C) 8}

/-- Five standard common-neighbor rows plus the named K23 cross adjacencies
produce the generic five-start incidence package. -/
def toThreeCommonNeighborIncidenceInputsOfCrossAdjacencyRows
    (B : M8BadAdjacencyCommonNeighborStandardRows C P)
    (H : M8BadAdjacencyCrossAdjacencyRows C P.labels) :
    M8ConcreteThreeCommonNeighborIncidenceInputs P where
  witness_start1 h :=
    (B.witness_start1 h).toThreeCommonNeighborIncidenceDatumOfCrossAdjacencyRowAt
      H.adj_q1_s2
  witness_start2 h :=
    (B.witness_start2 h).toThreeCommonNeighborIncidenceDatumOfCrossAdjacencyRowAt
      H.adj_q2_s3
  witness_start3 h :=
    (B.witness_start3 h).toThreeCommonNeighborIncidenceDatumOfCrossAdjacencyRowAt
      H.adj_q3_s4
  witness_start4 h :=
    (B.witness_start4 h).toThreeCommonNeighborIncidenceDatumOfCrossAdjacencyRowAt
      H.adj_q4_s5
  witness_start5 h :=
    (B.witness_start5 h).toThreeCommonNeighborIncidenceDatumOfCrossAdjacencyRowAt
      H.adj_q5_s6

/-- Five standard common-neighbor rows plus the named K23 cross distance rows
produce the generic five-start incidence package. -/
def toThreeCommonNeighborIncidenceInputsOfCrossDistanceRows
    (B : M8BadAdjacencyCommonNeighborStandardRows C P)
    (H : M8BadAdjacencyCrossDistanceRows C P.labels) :
    M8ConcreteThreeCommonNeighborIncidenceInputs P :=
  B.toThreeCommonNeighborIncidenceInputsOfCrossAdjacencyRows H.toAdjacencyRows

/-- Five standard rows plus K23 cross adjacencies feed the explicit
three-common-neighbor obstruction inputs. -/
def toThreeCommonNeighborObstructionInputsOfCrossAdjacencyRows
    (B : M8BadAdjacencyCommonNeighborStandardRows C P)
    (H : M8BadAdjacencyCrossAdjacencyRows C P.labels) :
    M8ConcreteThreeCommonNeighborObstructionInputs P :=
  (B.toThreeCommonNeighborIncidenceInputsOfCrossAdjacencyRows H).toThreeCommonNeighborObstructionInputs

/-- Five standard rows plus K23 cross distance rows feed the explicit
three-common-neighbor obstruction inputs. -/
def toThreeCommonNeighborObstructionInputsOfCrossDistanceRows
    (B : M8BadAdjacencyCommonNeighborStandardRows C P)
    (H : M8BadAdjacencyCrossDistanceRows C P.labels) :
    M8ConcreteThreeCommonNeighborObstructionInputs P :=
  (B.toThreeCommonNeighborIncidenceInputsOfCrossDistanceRows H).toThreeCommonNeighborObstructionInputs

/-- Five standard rows plus K23 cross adjacencies feed the common-neighbor-card
obstruction inputs. -/
def toCommonNeighborObstructionInputsOfCrossAdjacencyRows
    (B : M8BadAdjacencyCommonNeighborStandardRows C P)
    (H : M8BadAdjacencyCrossAdjacencyRows C P.labels) :
    M8ConcreteCommonNeighborCardObstructionInputs P :=
  (B.toThreeCommonNeighborIncidenceInputsOfCrossAdjacencyRows H).toCommonNeighborObstructionInputs

/-- Five standard rows plus K23 cross distance rows feed the common-neighbor-card
obstruction inputs. -/
def toCommonNeighborObstructionInputsOfCrossDistanceRows
    (B : M8BadAdjacencyCommonNeighborStandardRows C P)
    (H : M8BadAdjacencyCrossDistanceRows C P.labels) :
    M8ConcreteCommonNeighborCardObstructionInputs P :=
  (B.toThreeCommonNeighborIncidenceInputsOfCrossDistanceRows H).toCommonNeighborObstructionInputs

end M8BadAdjacencyCommonNeighborStandardRows

/-- Five explicit incidence rows feed the concrete five-start
three-common-neighbor obstruction inputs. -/
def threeCommonNeighborObstructionInputsOfIncidenceRows
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8}
    (witness_start1 :
      P.tripleEquality start1 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start2 :
      P.tripleEquality start2 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start3 :
      P.tripleEquality start3 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start4 :
      P.tripleEquality start4 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start5 :
      P.tripleEquality start5 -> ThreeCommonNeighborIncidenceDatum G) :
    M8ConcreteThreeCommonNeighborObstructionInputs P where
  witness_start1 h := (witness_start1 h).toThreeCommonNeighborWitness
  witness_start2 h := (witness_start2 h).toThreeCommonNeighborWitness
  witness_start3 h := (witness_start3 h).toThreeCommonNeighborWitness
  witness_start4 h := (witness_start4 h).toThreeCommonNeighborWitness
  witness_start5 h := (witness_start5 h).toThreeCommonNeighborWitness

/-- Five explicit incidence rows also feed the concrete five-start
common-neighbor-card obstruction inputs. -/
def commonNeighborObstructionInputsOfIncidenceRows
    {V : Type u} {G : LocalGraph V} [Fintype V] [DecidableEq V]
    {P : BrokenLatticePredicates G 8}
    (witness_start1 :
      P.tripleEquality start1 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start2 :
      P.tripleEquality start2 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start3 :
      P.tripleEquality start3 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start4 :
      P.tripleEquality start4 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start5 :
      P.tripleEquality start5 -> ThreeCommonNeighborIncidenceDatum G) :
    M8ConcreteCommonNeighborCardObstructionInputs P where
  witness_start1 h := (witness_start1 h).toCommonNeighborCardLowerWitness
  witness_start2 h := (witness_start2 h).toCommonNeighborCardLowerWitness
  witness_start3 h := (witness_start3 h).toCommonNeighborCardLowerWitness
  witness_start4 h := (witness_start4 h).toCommonNeighborCardLowerWitness
  witness_start5 h := (witness_start5 h).toCommonNeighborCardLowerWitness

/-- Five explicit incidence rows feed the concrete labelled `K_{2,3}`
obstruction inputs without passing through the card route. -/
def k23ObstructionInputsOfIncidenceRows
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8}
    (witness_start1 :
      P.tripleEquality start1 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start2 :
      P.tripleEquality start2 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start3 :
      P.tripleEquality start3 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start4 :
      P.tripleEquality start4 -> ThreeCommonNeighborIncidenceDatum G)
    (witness_start5 :
      P.tripleEquality start5 -> ThreeCommonNeighborIncidenceDatum G) :
    NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs P :=
  (M8ConcreteThreeCommonNeighborIncidenceInputs.ofWitnessStarts
    witness_start1 witness_start2 witness_start3 witness_start4
    witness_start5).toK23ObstructionInputs

/-- Structured version of `threeCommonNeighborObstructionInputsOfIncidenceRows`.
It is useful when the five bad-adjacency incidences need to remain available
as named projections before the downstream witness conversion. -/
def threeCommonNeighborObstructionInputsOfIncidenceInputs
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8}
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P) :
    M8ConcreteThreeCommonNeighborObstructionInputs P :=
  H.toThreeCommonNeighborObstructionInputs

/-- Structured labelled `K_{2,3}` projection of the same five incidence rows. -/
def k23ObstructionInputsOfIncidenceInputs
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8}
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P) :
    NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs P :=
  H.toK23ObstructionInputs

/-- Structured version of `commonNeighborObstructionInputsOfIncidenceRows`.
It keeps the same incidence package available for the route-facing adjacency
projections while producing the common-neighbor-card input surface. -/
def commonNeighborObstructionInputsOfIncidenceInputs
    {V : Type u} {G : LocalGraph V} [Fintype V] [DecidableEq V]
    {P : BrokenLatticePredicates G 8}
    (H : M8ConcreteThreeCommonNeighborIncidenceInputs P) :
    M8ConcreteCommonNeighborCardObstructionInputs P :=
  H.toCommonNeighborObstructionInputs

/-- Select the common-neighbor-card witness attached to any early start. -/
def commonNeighborCardWitnessOfEarlyTriple
    (H : M8ConcreteCommonNeighborCardObstructionInputs P)
    {a : M8TripleStartIndex}
    (hearly : M8TripleStartEarly a)
    (htriple : P.tripleEquality a) :
    CommonNeighborCardLowerWitness G := by
  classical
  by_cases h1 : a.1 = 1
  · have ha : a = start1 := by
      apply Subtype.ext
      simpa [start1, m8TripleStartIndexOfNat] using h1
    cases ha
    exact H.witness_start1 htriple
  by_cases h2 : a.1 = 2
  · have ha : a = start2 := by
      apply Subtype.ext
      simpa [start2, m8TripleStartIndexOfNat] using h2
    cases ha
    exact H.witness_start2 htriple
  by_cases h3 : a.1 = 3
  · have ha : a = start3 := by
      apply Subtype.ext
      simpa [start3, m8TripleStartIndexOfNat] using h3
    cases ha
    exact H.witness_start3 htriple
  by_cases h4 : a.1 = 4
  · have ha : a = start4 := by
      apply Subtype.ext
      simpa [start4, m8TripleStartIndexOfNat] using h4
    cases ha
    exact H.witness_start4 htriple
  have h5 : a.1 = 5 := by
    have hbounds := m8TripleStartIndex_bounds a
    unfold M8TripleStartEarly at hearly
    omega
  have ha : a = start5 := by
    apply Subtype.ext
    simpa [start5, m8TripleStartIndexOfNat] using h5
  cases ha
  exact H.witness_start5 htriple

/-- Indexed early three-common-neighbor witnesses also provide the concrete
five-start common-neighbor-card witnesses. -/
def commonNeighborCardObstructionInputsOfEarlyThreeCommonNeighbor
    (H : M8EarlyThreeCommonNeighborObstructionInputs P) :
    M8ConcreteCommonNeighborCardObstructionInputs P :=
  commonNeighborCardObstructionInputsOfThreeCommonNeighbor H.toConcrete

/-- Raise common-neighbor-card obstruction rows to explicit
three-common-neighbor obstruction rows, row by row. -/
def threeCommonNeighborObstructionFamilyOfCommonNeighbor
    {noCut : SwanepoelW32RouteAudit.ActualRouteSource.NoCutDependency}
    {components : SwanepoelW32RouteAudit.ActualRouteSource.ComponentFamily.{u}}
    {rows : SwanepoelW32RouteAudit.ActualRouteSource.FrameCyclicRows.{u}
      noCut components}
    (H :
      SwanepoelW32RouteAudit.ActualRouteSource.CommonNeighborObstructionFamily
        rows) :
    SwanepoelW32RouteAudit.ActualRouteSource.ThreeCommonNeighborObstructionFamily
      rows where
  row := fun C hmin =>
    threeCommonNeighborObstructionInputsOfCommonNeighborCard
      (H.row C hmin)

/-! ## Uniform W32 source-family conversions -/

variable {payForCut : W18PayForCutConcreteProducerFamily}
variable {topologyArc : W18TopologyArcConcreteProducerFamily.{u}}
variable {lemma8 : W18Lemma8ConcreteProducerFamily.{u}
  payForCut topologyArc}

/-- The exact selected-geometry theorem still needed for this route: every
minimal-failure row's five early triple equalities produce explicit
three-common-neighbor witnesses for the assembled boundary labels. -/
abbrev SelectedThreeCommonNeighborGeometryTheorem : Type (u + 1) :=
  ThreeCommonNeighborObstructionFamily.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

/-- The common-neighbor-card obstruction family required by W32. -/
abbrev SelectedCommonNeighborCardObstructionRows : Type (u + 1) :=
  CommonNeighborObstructionFamily.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

/-- Convert selected three-common-neighbor geometry rows into the
common-neighbor-card obstruction rows. -/
def commonNeighborObstructionFamilyOfThreeCommonNeighbor
    (H : SelectedThreeCommonNeighborGeometryTheorem.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8)) :
    SelectedCommonNeighborCardObstructionRows.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) where
  row := fun C hmin =>
    commonNeighborCardObstructionInputsOfThreeCommonNeighbor (H.row C hmin)

theorem nonempty_commonNeighborObstructionFamily_of_threeCommonNeighbor
    (h :
      Nonempty
        (SelectedThreeCommonNeighborGeometryTheorem.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    Nonempty
      (SelectedCommonNeighborCardObstructionRows.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) := by
  cases h with
  | intro H =>
      exact Nonempty.intro
        (commonNeighborObstructionFamilyOfThreeCommonNeighbor H)

/-- Coverage plus the selected three-common-neighbor geometry rows feed the
W32 `commonNeighbor` branch. -/
def commonNeighborRouteCoverageDataOfCoverageAndThreeCommonNeighbor
    (coverage :
      NoEarlyCoverageFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8))
    (geometry :
      SelectedThreeCommonNeighborGeometryTheorem.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    CommonNeighborRouteCoverageData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  commonNeighborRouteCoverageDataOfCoverageAndObstruction
    coverage
    (commonNeighborObstructionFamilyOfThreeCommonNeighbor geometry)

theorem commonNeighbor_routeCoverage_of_coverage_and_threeCommonNeighbor
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))
    (hgeometry :
      Nonempty
        (SelectedThreeCommonNeighborGeometryTheorem.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyCommonNeighborRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  And.intro hcoverage
    (nonempty_commonNeighborObstructionFamily_of_threeCommonNeighbor
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) hgeometry)

/-! ## Uniform standard bad-adjacency row conversions -/

/-- Uniform standard bad-adjacency common-neighbor rows, paired with the
route-facing cross-adjacency rows that provide the third-neighbor incidence.

This is the import-local source surface available in this file.  The
selected-frame source theorem itself is declared downstream in
`K23RouteCoverageSourceW34`, so that theorem cannot be named here without
creating an import cycle. -/
structure M8BadAdjacencyCommonNeighborStandardRowFamily
    (payForCut : W18PayForCutConcreteProducerFamily)
    (topologyArc : W18TopologyArcConcreteProducerFamily.{u})
    (lemma8 : W18Lemma8ConcreteProducerFamily.{u}
      payForCut topologyArc) : Type (u + 1) where
  standardRows :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        M8BadAdjacencyCommonNeighborStandardRows C
          (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
            payForCut topologyArc lemma8 C hmin)
  crossAdjacencyRows :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        M8BadAdjacencyCrossAdjacencyRows C
          (Lemma9NoEarlyObstructionInhabitationW25.RowPredicates
            payForCut topologyArc lemma8 C hmin).labels

namespace M8BadAdjacencyCommonNeighborStandardRowFamily

/-- Standard bad-adjacency rows plus cross adjacencies give uniform
three-common-neighbor witness rows. -/
def toThreeCommonNeighborObstructionFamily
    (H :
      M8BadAdjacencyCommonNeighborStandardRowFamily.{u}
        payForCut topologyArc lemma8) :
    ThreeCommonNeighborObstructionFamily.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) where
  row := fun C hmin =>
    (H.standardRows C hmin).toThreeCommonNeighborObstructionInputsOfCrossAdjacencyRows
      (H.crossAdjacencyRows C hmin)

/-- Standard bad-adjacency rows plus cross adjacencies give uniform
common-neighbor-card witness rows. -/
def toCommonNeighborObstructionFamily
    (H :
      M8BadAdjacencyCommonNeighborStandardRowFamily.{u}
        payForCut topologyArc lemma8) :
    CommonNeighborObstructionFamily.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) where
  row := fun C hmin =>
    (H.standardRows C hmin).toCommonNeighborObstructionInputsOfCrossAdjacencyRows
      (H.crossAdjacencyRows C hmin)

/-- Standard bad-adjacency rows plus cross adjacencies inhabit the uniform
three-common-neighbor witness-row family. -/
theorem nonempty_threeCommonNeighborObstructionFamily
    (H :
      M8BadAdjacencyCommonNeighborStandardRowFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (ThreeCommonNeighborObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :=
  Nonempty.intro H.toThreeCommonNeighborObstructionFamily

/-- Standard bad-adjacency rows plus cross adjacencies inhabit the uniform
common-neighbor-card witness-row family. -/
theorem nonempty_commonNeighborObstructionFamily
    (H :
      M8BadAdjacencyCommonNeighborStandardRowFamily.{u}
        payForCut topologyArc lemma8) :
    Nonempty
      (CommonNeighborObstructionFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :=
  Nonempty.intro H.toCommonNeighborObstructionFamily

/-- Coverage plus standard bad-adjacency rows gives the W32 common-neighbor
route data. -/
def toCommonNeighborRouteCoverageData
    (H :
      M8BadAdjacencyCommonNeighborStandardRowFamily.{u}
        payForCut topologyArc lemma8)
    (coverage :
      NoEarlyCoverageFamily.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :
    CommonNeighborRouteCoverageData.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  commonNeighborRouteCoverageDataOfCoverageAndObstruction
    coverage H.toCommonNeighborObstructionFamily

/-- Coverage plus standard bad-adjacency rows gives the W32 common-neighbor
route-coverage predicate. -/
theorem commonNeighborRouteCoverageAvailable
    (H :
      M8BadAdjacencyCommonNeighborStandardRowFamily.{u}
        payForCut topologyArc lemma8)
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyCommonNeighborRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  And.intro hcoverage H.nonempty_commonNeighborObstructionFamily

/-- Coverage plus standard bad-adjacency rows gives the W32 route-coverage
sum through the common-neighbor branch. -/
theorem routeCoverageAvailable
    (H :
      M8BadAdjacencyCommonNeighborStandardRowFamily.{u}
        payForCut topologyArc lemma8)
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  Or.inr (Or.inr (Or.inl
    (H.commonNeighborRouteCoverageAvailable hcoverage)))

end M8BadAdjacencyCommonNeighborStandardRowFamily

theorem routeCoverage_of_coverage_and_threeCommonNeighbor
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))
    (hgeometry :
      Nonempty
        (SelectedThreeCommonNeighborGeometryTheorem.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    NoEarlyRouteCoverageAvailable.{u}
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) :=
  Or.inr (Or.inr (Or.inl
    (commonNeighbor_routeCoverage_of_coverage_and_threeCommonNeighbor
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) hcoverage hgeometry)))

theorem routeData_of_coverage_and_threeCommonNeighbor
    (hcoverage :
      Nonempty
        (NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))
    (hgeometry :
      Nonempty
        (SelectedThreeCommonNeighborGeometryTheorem.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    Nonempty
      (ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :=
  NoEarlyRouteCoverageClosureW32.nonempty_routeData_of_commonNeighbor_routeCoverage
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)
    (commonNeighbor_routeCoverage_of_coverage_and_threeCommonNeighbor
      (payForCut := payForCut) (topologyArc := topologyArc)
      (lemma8 := lemma8) hcoverage hgeometry)

/-! ## No-cut/pointwise bridge adapters -/

namespace NoCutPointwise

variable {noCut : NoCutPointwiseBridgeW32.NoCutDependency}
variable {components : NoCutPointwiseBridgeW32.ExtractedWitnessComponentFamily.{u}}
variable {rows :
  NoCutPointwiseBridgeW32.UniformFrameCyclicOrderRows.{u}
    noCut components}

/-- Selected three-common-neighbor geometry rows, specialized to the
boundary-label rows exposed by `NoCutPointwiseBridgeW32`. -/
abbrev SelectedThreeCommonNeighborGeometryForRows
    {noCut : NoCutPointwiseBridgeW32.NoCutDependency}
    {components : NoCutPointwiseBridgeW32.ExtractedWitnessComponentFamily.{u}}
    (rows :
      NoCutPointwiseBridgeW32.UniformFrameCyclicOrderRows.{u}
        noCut components) : Type (u + 1) :=
  ThreeCommonNeighborObstructionFamily.{u} rows

/-- The exact missing selected geometry theorem if the branch still cannot be
inhabited from current data. -/
abbrev ExactMissingSelectedCommonNeighborGeometryForRows : Prop :=
  Not (Nonempty (SelectedThreeCommonNeighborGeometryForRows.{u} rows))

theorem routeCoverageAvailable_of_coverage_and_threeCommonNeighbor
    (hcoverage : Nonempty (NoEarlyCoverageFamily.{u} rows))
    (hgeometry :
      Nonempty
        (SelectedThreeCommonNeighborGeometryForRows.{u} rows)) :
    RouteCoverageAvailable rows :=
  CommonNeighborRouteCoverageSourceW34.routeCoverage_of_coverage_and_threeCommonNeighbor
    (payForCut := PayForCutOfNoCut noCut)
    (topologyArc := TopologyArcOfComponents components)
    (lemma8 :=
      Lemma8ConcreteOfGeometrySource
        (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    hcoverage hgeometry

theorem routeData_nonempty_of_coverage_and_threeCommonNeighbor
    (hcoverage : Nonempty (NoEarlyCoverageFamily.{u} rows))
    (hgeometry :
      Nonempty
        (SelectedThreeCommonNeighborGeometryForRows.{u} rows)) :
    Nonempty
      (ConcreteNoEarlyRouteData
        (geometrySourceFamilyOfFrameCyclicOrderRows rows)) :=
  (routeData_nonempty_iff_routeCoverageAvailable rows).2
    (routeCoverageAvailable_of_coverage_and_threeCommonNeighbor
      (rows := rows) hcoverage hgeometry)

theorem componentSource_nonempty_of_commonNeighborRoute
    (figureData :
      ExactFigureData (geometrySourceFamilyOfFrameCyclicOrderRows rows))
    (hcoverage : Nonempty (NoEarlyCoverageFamily.{u} rows))
    (hgeometry :
      Nonempty
        (SelectedThreeCommonNeighborGeometryForRows.{u} rows)) :
    Nonempty ComponentFrameNoEarlyFigureSourceData.{u} := by
  cases routeData_nonempty_of_coverage_and_threeCommonNeighbor
      (rows := rows) hcoverage hgeometry with
  | intro routeData =>
      exact Nonempty.intro
        { noCut := noCut
          components := components
          frameCyclicRows := rows
          routeData := routeData
          figureData := figureData }

end NoCutPointwise

end CommonNeighborRouteCoverageSourceW34
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW34SelectedThreeCommonNeighborGeometryTheorem
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc} :=
  Swanepoel.CommonNeighborRouteCoverageSourceW34.SelectedThreeCommonNeighborGeometryTheorem.{u}
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8)

theorem swanepoelW34_routeData_of_selectedThreeCommonNeighborGeometry
    {payForCut :
      Swanepoel.Lemma9ProducerFamilyW20.W18PayForCutConcreteProducerFamily}
    {topologyArc :
      Swanepoel.Lemma9ProducerFamilyW20.W18TopologyArcConcreteProducerFamily.{u}}
    {lemma8 :
      Swanepoel.Lemma9ProducerFamilyW20.W18Lemma8ConcreteProducerFamily.{u}
        payForCut topologyArc}
    (hcoverage :
      Nonempty
        (Swanepoel.NoEarlyRouteCoverageClosureW32.NoEarlyCoverageFamily.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8)))
    (hgeometry :
      Nonempty
        (SwanepoelW34SelectedThreeCommonNeighborGeometryTheorem.{u}
          (payForCut := payForCut) (topologyArc := topologyArc)
          (lemma8 := lemma8))) :
    Nonempty
      (Swanepoel.NoEarlyRouteCoverageClosureW32.ConcreteNoEarlyRouteData.{u}
        (payForCut := payForCut) (topologyArc := topologyArc)
        (lemma8 := lemma8)) :=
  Swanepoel.CommonNeighborRouteCoverageSourceW34.routeData_of_coverage_and_threeCommonNeighbor
    (payForCut := payForCut) (topologyArc := topologyArc)
    (lemma8 := lemma8) hcoverage hgeometry

end Verified
end ErdosProblems1066

end
