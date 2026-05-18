import Mathlib

/-!
# Pach--Toth Figure 2, First-Block Graph Data

This module records the 16-vertex finite graph extracted from the Pach--Toth
Figure 2 first block, and proves the finite independence certificate for that
block.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FiniteGraph

/-- Local vertices in the first Pach--Toth block: one distinguished point `r`
and five shaded triples. -/
inductive LocalVertex where
  | r : LocalVertex
  | tri : Fin 5 -> Fin 3 -> LocalVertex
  deriving DecidableEq, Repr, Fintype

namespace LocalVertex

def T (t : Fin 5) (c : Fin 3) : LocalVertex :=
  tri t c

def T0_0 : LocalVertex := T 0 0
def T0_1 : LocalVertex := T 0 1
def T0_2 : LocalVertex := T 0 2
def T1_0 : LocalVertex := T 1 0
def T1_1 : LocalVertex := T 1 1
def T1_2 : LocalVertex := T 1 2
def T2_0 : LocalVertex := T 2 0
def T2_1 : LocalVertex := T 2 1
def T2_2 : LocalVertex := T 2 2
def T3_0 : LocalVertex := T 3 0
def T3_1 : LocalVertex := T 3 1
def T3_2 : LocalVertex := T 3 2
def T4_0 : LocalVertex := T 4 0
def T4_1 : LocalVertex := T 4 1
def T4_2 : LocalVertex := T 4 2

end LocalVertex

open LocalVertex

/-- There are exactly sixteen local vertices in `B1`. -/
theorem localVertex_card : Fintype.card LocalVertex = 16 := by
  decide

/-- The five shaded triangles are cliques. -/
def shadedCliqueAdj : LocalVertex -> LocalVertex -> Bool
  | .tri t c, .tri t' c' => decide (t = t') && decide (Ne c c')
  | _, _ => false

/-- The non-shaded first-block connector edges between the sixteen `B1`
vertices.  Edges already present from shaded cliques are omitted here. -/
def connectorAdj : LocalVertex -> LocalVertex -> Bool
  | .r, .tri 0 1 => true
  | .tri 0 1, .r => true
  | .r, .tri 0 2 => true
  | .tri 0 2, .r => true
  | .r, .tri 1 0 => true
  | .tri 1 0, .r => true
  | .r, .tri 1 2 => true
  | .tri 1 2, .r => true
  | .tri 0 1, .tri 1 0 => true
  | .tri 1 0, .tri 0 1 => true
  | .tri 0 0, .tri 2 0 => true
  | .tri 2 0, .tri 0 0 => true
  | .tri 0 0, .tri 2 1 => true
  | .tri 2 1, .tri 0 0 => true
  | .tri 4 1, .tri 3 0 => true
  | .tri 3 0, .tri 4 1 => true
  | .tri 4 2, .tri 3 0 => true
  | .tri 3 0, .tri 4 2 => true
  | .tri 3 1, .tri 1 1 => true
  | .tri 1 1, .tri 3 1 => true
  | .tri 3 2, .tri 1 1 => true
  | .tri 1 1, .tri 3 2 => true
  | _, _ => false

/-- Boolean adjacency for the concrete 16-vertex graph `B1`. -/
def adj (u v : LocalVertex) : Bool :=
  shadedCliqueAdj u v || connectorAdj u v

/-- Finset independence for the Boolean graph `B1`. -/
def IsIndependent (s : Finset LocalVertex) : Prop :=
  forall u : LocalVertex, u ∈ s ->
    forall v : LocalVertex, v ∈ s -> Ne u v -> adj u v = false

instance instDecidableIsIndependent (s : Finset LocalVertex) :
    Decidable (IsIndependent s) := by
  unfold IsIndependent
  infer_instance

/-- The independent six-set identified in the source extraction:
`{r, T0.0, T1.1, T2.2, T3.0, T4.0}`. -/
def extractedSixSet : Finset LocalVertex :=
  {.r, T0_0, T1_1, T2_2, T3_0, T4_0}

theorem adj_irrefl : forall v : LocalVertex, adj v v = false := by
  decide

theorem adj_symm : forall u v : LocalVertex, adj u v = adj v u := by
  decide

/-- The six coarse parts: `{r}` and the five shaded triples. -/
def part : LocalVertex -> Fin 6
  | .r => 0
  | .tri t _ =>
      ⟨t.val + 1, by
        have ht := t.isLt
        omega⟩

/-- In the same coarse part, distinct vertices are adjacent. -/
theorem same_part_eq_or_adj :
    forall u v : LocalVertex, part u = part v -> u = v \/ adj u v = true := by
  decide

theorem independent_part_injOn {s : Finset LocalVertex}
    (hs : IsIndependent s) : Set.InjOn part (s : Set LocalVertex) := by
  intro u hu v hv hpart
  rcases same_part_eq_or_adj u v hpart with huv | hadj
  · exact huv
  · by_contra hne
    have hfalse := hs u hu v hv hne
    rw [hadj] at hfalse
    cases hfalse

theorem extractedSixSet_card : extractedSixSet.card = 6 := by
  decide

theorem extractedSixSet_independent : IsIndependent extractedSixSet := by
  decide

theorem part_zero_eq_r : forall v : LocalVertex, part v = 0 -> v = .r := by
  decide

theorem part_one_ne_r : forall v : LocalVertex, part v = 1 -> Ne .r v := by
  decide

theorem part_two_ne_r : forall v : LocalVertex, part v = 2 -> Ne .r v := by
  decide

theorem part_three_ne_T0_0 : forall v : LocalVertex, part v = 3 -> Ne T0_0 v := by
  decide

theorem part_four_ne_T1_1 : forall v : LocalVertex, part v = 4 -> Ne T1_1 v := by
  decide

theorem part_five_ne_T3_0 : forall v : LocalVertex, part v = 5 -> Ne T3_0 v := by
  decide

theorem part_one_forced_by_r :
    forall v : LocalVertex, part v = 1 -> adj .r v = false -> v = T0_0 := by
  decide

theorem part_two_forced_by_r :
    forall v : LocalVertex, part v = 2 -> adj .r v = false -> v = T1_1 := by
  decide

theorem part_three_forced_by_T0_0 :
    forall v : LocalVertex, part v = 3 -> adj T0_0 v = false -> v = T2_2 := by
  decide

theorem part_four_forced_by_T1_1 :
    forall v : LocalVertex, part v = 4 -> adj T1_1 v = false -> v = T3_0 := by
  decide

theorem part_five_forced_by_T3_0 :
    forall v : LocalVertex, part v = 5 -> adj T3_0 v = false -> v = T4_0 := by
  decide

/-- Vertices in the next block made unavailable by selecting the two connector
vertices `T2_2` and `T4_0` in a full previous block. -/
def nextForbidden : Finset LocalVertex :=
  {T1_1, T1_2, T0_0, T0_2}

theorem early_not_forbidden_eq_or_adj :
    forall u v : LocalVertex,
      u ∉ nextForbidden ->
      v ∉ nextForbidden ->
      (part u : Nat) <= 2 ->
      (part v : Nat) <= 2 ->
      u = v \/ adj u v = true := by
  decide

theorem late_part_mem :
    forall v : LocalVertex,
      Not ((part v : Nat) <= 2) ->
      part v ∈ ({(3 : Fin 6), (4 : Fin 6), (5 : Fin 6)} : Finset (Fin 6)) := by
  decide

/-- The first-block graph has independence number at most six. -/
theorem alpha_le_six (s : Finset LocalVertex) (hs : IsIndependent s) :
    s.card <= 6 := by
  have hinj := independent_part_injOn hs
  calc
    s.card = (s.image part).card := (Finset.card_image_of_injOn hinj).symm
    _ <= Fintype.card (Fin 6) := Finset.card_le_univ _
    _ = 6 := by simp

/-- The only independent six-set is
`{r, T0.0, T1.1, T2.2, T3.0, T4.0}`. -/
theorem unique_size_six_independent (s : Finset LocalVertex)
    (hs : IsIndependent s) (hcard : s.card = 6) : s = extractedSixSet := by
  have hinj := independent_part_injOn hs
  have hcard_image : (s.image part).card = 6 := by
    rw [Finset.card_image_of_injOn hinj, hcard]
  have himage : s.image part = Finset.univ :=
    Finset.eq_univ_of_card (s.image part) (by
      simpa [Fintype.card_fin] using hcard_image)
  have hpart_mem (k : Fin 6) : k ∈ s.image part := by
    rw [himage]
    simp
  rcases Finset.mem_image.mp (hpart_mem 0) with ⟨vr, hvr, hvrpart⟩
  have hvr_eq : vr = .r := part_zero_eq_r vr hvrpart
  have hr : .r ∈ s := by
    simpa [hvr_eq] using hvr
  rcases Finset.mem_image.mp (hpart_mem 1) with ⟨v1, hv1, hv1part⟩
  have h1_adj : adj .r v1 = false :=
    hs .r hr v1 hv1 (part_one_ne_r v1 hv1part)
  have hv1_eq : v1 = T0_0 := part_one_forced_by_r v1 hv1part h1_adj
  have hT0 : T0_0 ∈ s := by
    simpa [hv1_eq] using hv1
  rcases Finset.mem_image.mp (hpart_mem 2) with ⟨v2, hv2, hv2part⟩
  have h2_adj : adj .r v2 = false :=
    hs .r hr v2 hv2 (part_two_ne_r v2 hv2part)
  have hv2_eq : v2 = T1_1 := part_two_forced_by_r v2 hv2part h2_adj
  have hT1 : T1_1 ∈ s := by
    simpa [hv2_eq] using hv2
  rcases Finset.mem_image.mp (hpart_mem 3) with ⟨v3, hv3, hv3part⟩
  have h3_adj : adj T0_0 v3 = false :=
    hs T0_0 hT0 v3 hv3 (part_three_ne_T0_0 v3 hv3part)
  have hv3_eq : v3 = T2_2 :=
    part_three_forced_by_T0_0 v3 hv3part h3_adj
  have hT2 : T2_2 ∈ s := by
    simpa [hv3_eq] using hv3
  rcases Finset.mem_image.mp (hpart_mem 4) with ⟨v4, hv4, hv4part⟩
  have h4_adj : adj T1_1 v4 = false :=
    hs T1_1 hT1 v4 hv4 (part_four_ne_T1_1 v4 hv4part)
  have hv4_eq : v4 = T3_0 :=
    part_four_forced_by_T1_1 v4 hv4part h4_adj
  have hT3 : T3_0 ∈ s := by
    simpa [hv4_eq] using hv4
  rcases Finset.mem_image.mp (hpart_mem 5) with ⟨v5, hv5, hv5part⟩
  have h5_adj : adj T3_0 v5 = false :=
    hs T3_0 hT3 v5 hv5 (part_five_ne_T3_0 v5 hv5part)
  have hv5_eq : v5 = T4_0 :=
    part_five_forced_by_T3_0 v5 hv5part h5_adj
  have hT4 : T4_0 ∈ s := by
    simpa [hv5_eq] using hv5
  have hsub : extractedSixSet ⊆ s := by
    intro v hv
    have hv_cases :
        v = .r ∨ v = T0_0 ∨ v = T1_1 ∨ v = T2_2 ∨ v = T3_0 ∨ v = T4_0 := by
      simpa [extractedSixSet] using hv
    rcases hv_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hr
    · exact hT0
    · exact hT1
    · exact hT2
    · exact hT3
    · exact hT4
  exact (Finset.eq_of_subset_of_card_le hsub (by
    rw [hcard, extractedSixSet_card])).symm

theorem extractedSixSet_contains_connectors :
    T2_2 ∈ extractedSixSet /\ T4_0 ∈ extractedSixSet := by
  decide

/-- If a previous full block uses its two connector vertices, then the four
corresponding vertices in this block are unavailable, and every independent set
in this block has size at most four. -/
theorem next_block_after_forbidden_le_four (s : Finset LocalVertex)
    (hs : IsIndependent s)
    (hforbid : forall v : LocalVertex, v ∈ s -> v ∉ nextForbidden) :
    s.card <= 4 := by
  let early : Finset LocalVertex := s.filter fun v => (part v : Nat) <= 2
  let late : Finset LocalVertex := s.filter fun v => Not ((part v : Nat) <= 2)
  have hsplit : early.card + late.card = s.card := by
    simpa [early, late] using
      (Finset.card_filter_add_card_filter_not
        (s := s) (p := fun v : LocalVertex => (part v : Nat) <= 2))
  have hearly : early.card <= 1 := by
    rw [Finset.card_le_one_iff]
    intro u v hu hv
    have hu_s : u ∈ s := (Finset.mem_filter.mp hu).1
    have hv_s : v ∈ s := (Finset.mem_filter.mp hv).1
    have hu_part : (part u : Nat) <= 2 := (Finset.mem_filter.mp hu).2
    have hv_part : (part v : Nat) <= 2 := (Finset.mem_filter.mp hv).2
    rcases early_not_forbidden_eq_or_adj u v
        (hforbid u hu_s) (hforbid v hv_s) hu_part hv_part with huv | hadj
    · exact huv
    · by_contra hne
      have hfalse := hs u hu_s v hv_s hne
      rw [hadj] at hfalse
      cases hfalse
  have hlate : late.card <= 3 := by
    have hinj : Set.InjOn part (late : Set LocalVertex) := by
      intro u hu v hv hpart
      exact independent_part_injOn hs
        (by exact (Finset.mem_filter.mp hu).1)
        (by exact (Finset.mem_filter.mp hv).1)
        hpart
    have hcard : late.card = (late.image part).card :=
      (Finset.card_image_of_injOn hinj).symm
    have hsubset :
        late.image part ⊆ ({(3 : Fin 6), (4 : Fin 6), (5 : Fin 6)} : Finset (Fin 6)) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
      exact late_part_mem v (Finset.mem_filter.mp hv).2
    calc
      late.card = (late.image part).card := hcard
      _ <= ({(3 : Fin 6), (4 : Fin 6), (5 : Fin 6)} : Finset (Fin 6)).card :=
        Finset.card_le_card hsubset
      _ = 3 := by decide
  omega

end FiniteGraph
end PachToth
end ErdosProblems1066
