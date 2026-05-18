import ErdosProblems1066.UnitDistanceBounds

/-!
# Color Classes and Independent Sets

This file collects small finite-set lemmas for turning proper color classes
into independent sets.  The generic statements are parameterized by an
adjacency relation, and the final wrappers specialize them to the unit-distance
adjacency used by `UDConfig`.
-/

namespace ErdosProblems1066
namespace Combinatorics

variable {α β : Type*}

/-- A finite set is independent for `adj` if no two distinct members are
adjacent. -/
def IsIndependentOn (adj : α → α → Prop) (s : Finset α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ¬ adj x y

/-- A coloring is proper on `s` if adjacent distinct vertices in `s` receive
distinct colors. -/
def ProperColoringOn (adj : α → α → Prop) (color : α → β) (s : Finset α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → adj x y → color x ≠ color y

/-- The members of `s` with color `j`. -/
def colorClass [DecidableEq β] (s : Finset α) (color : α → β) (j : β) : Finset α :=
  s.filter fun x => color x = j

@[simp]
theorem mem_colorClass [DecidableEq β] {s : Finset α} {color : α → β} {j : β}
    {x : α} :
    x ∈ colorClass s color j ↔ x ∈ s ∧ color x = j := by
  simp [colorClass]

theorem colorClass_subset [DecidableEq β] {s : Finset α} {color : α → β} {j : β} :
    colorClass s color j ⊆ s := by
  intro x hx
  exact (mem_colorClass.mp hx).1

theorem card_colorClass_le [DecidableEq β] {s : Finset α} {color : α → β} {j : β} :
    (colorClass s color j).card ≤ s.card :=
  Finset.card_le_card colorClass_subset

/-- A color class of a proper coloring is independent. -/
theorem colorClass_isIndependentOn [DecidableEq β] {adj : α → α → Prop}
    {s : Finset α} {color : α → β} {j : β}
    (hproper : ProperColoringOn adj color s) :
    IsIndependentOn adj (colorClass s color j) := by
  intro x hx y hy hxy hAdj
  exact hproper (colorClass_subset hx) (colorClass_subset hy) hxy hAdj
    ((mem_colorClass.mp hx).2.trans (mem_colorClass.mp hy).2.symm)

/-- The image of a color class is independent for the target adjacency when
the coloring is proper for the pulled-back adjacency. -/
theorem image_colorClass_isIndependentOn [DecidableEq β] {γ : Type*} [DecidableEq γ]
    {adj : β → β → Prop}
    {s : Finset α} {f : α → β} {color : α → γ} {j : γ}
    (hproper : ProperColoringOn (fun x y => adj (f x) (f y)) color s) :
    IsIndependentOn adj ((colorClass s color j).image f) := by
  intro x hx y hy hxy hAdj
  rcases Finset.mem_image.mp hx with ⟨x', hx', rfl⟩
  rcases Finset.mem_image.mp hy with ⟨y', hy', rfl⟩
  have hx'y' : x' ≠ y' := by
    intro h
    exact hxy (by simp [h])
  exact hproper (colorClass_subset hx') (colorClass_subset hy') hx'y' hAdj
    ((mem_colorClass.mp hx').2.trans (mem_colorClass.mp hy').2.symm)

theorem card_image_colorClass_of_injOn [DecidableEq β] {γ : Type*} [DecidableEq γ]
    {s : Finset α} {f : α → β}
    {color : α → γ} {j : γ} (hf : Set.InjOn f ↑s) :
    ((colorClass s color j).image f).card = (colorClass s color j).card := by
  rw [Finset.card_image_of_injOn]
  intro x hx y hy hxy
  exact hf (colorClass_subset hx) (colorClass_subset hy) hxy

/-- Pigeonhole principle for finite color classes: one color class has at
least the average size. -/
theorem exists_large_colorClass {k : Nat} (hk : 0 < k)
    (s : Finset α) (color : α → Fin k) :
    ∃ j : Fin k, s.card ≤ k * (colorClass s color j).card := by
  have hsum : (∑ j : Fin k, (colorClass s color j).card) = s.card := by
    simpa only [colorClass, Finset.card_eq_sum_ones] using
      (Finset.sum_fiberwise s color fun _ => (1 : Nat))
  obtain ⟨j, _hj_mem, hj_max⟩ :
      ∃ j ∈ (Finset.univ : Finset (Fin k)),
        ∀ j' ∈ (Finset.univ : Finset (Fin k)),
          (colorClass s color j').card ≤ (colorClass s color j).card :=
    Finset.exists_max_image (Finset.univ : Finset (Fin k))
      (fun j => (colorClass s color j).card) ⟨⟨0, hk⟩, by simp⟩
  refine ⟨j, ?_⟩
  calc
    s.card = ∑ j' : Fin k, (colorClass s color j').card := hsum.symm
    _ ≤ ∑ _j' : Fin k, (colorClass s color j).card := by
      exact Finset.sum_le_sum fun j' _hj' => hj_max j' (by simp)
    _ = k * (colorClass s color j).card := by
      simp [Fintype.card_fin]

theorem exists_large_image_colorClass [DecidableEq β] {k : Nat} (hk : 0 < k)
    {s : Finset α} {f : α → β} (hf : Set.InjOn f ↑s) (color : α → Fin k) :
    ∃ j : Fin k, s.card ≤ k * ((colorClass s color j).image f).card := by
  obtain ⟨j, hj⟩ := exists_large_colorClass hk s color
  refine ⟨j, ?_⟩
  have hcard :=
    card_image_colorClass_of_injOn (s := s) (f := f) (color := color) (j := j) hf
  simpa [hcard] using hj

namespace UDConfig

/-- Unit-distance adjacency for a `UDConfig`. -/
def UnitAdj {n : Nat} (C : _root_.UDConfig n) (i j : Fin n) : Prop :=
  eucDist (C.pts i) (C.pts j) = 1

theorem isIndep_iff_isIndependentOn_unitAdj {n : Nat} (C : _root_.UDConfig n)
    {s : Finset (Fin n)} :
    C.IsIndep s ↔ IsIndependentOn (UnitAdj C) s := by
  rfl

/-- A color class of a proper coloring for unit-distance adjacency is
independent in the `UDConfig` sense. -/
theorem colorClass_isIndep {n k : Nat} (C : _root_.UDConfig n)
    {color : Fin n → Fin k} {j : Fin k}
    (hproper : ProperColoringOn (UnitAdj C) color Finset.univ) :
    C.IsIndep (colorClass (Finset.univ : Finset (Fin n)) color j) := by
  exact (isIndep_iff_isIndependentOn_unitAdj C).2
    (colorClass_isIndependentOn hproper)

/-- A color class of a proper coloring of a reindexed unit-distance graph is
independent after mapping back to the original vertices. -/
theorem image_colorClass_isIndep {m n k : Nat} (C : _root_.UDConfig n)
    (f : Fin m → Fin n) {color : Fin m → Fin k} {j : Fin k}
    (hproper : ProperColoringOn (fun x y => UnitAdj C (f x) (f y)) color
      Finset.univ) :
    C.IsIndep ((colorClass (Finset.univ : Finset (Fin m)) color j).image f) := by
  exact (isIndep_iff_isIndependentOn_unitAdj C).2
    (image_colorClass_isIndependentOn hproper)

theorem equiv_image_colorClass_isIndep {n k : Nat} (C : _root_.UDConfig n)
    (e : Fin n ≃ Fin n) {color : Fin n → Fin k} {j : Fin k}
    (hproper : ProperColoringOn (fun x y => UnitAdj C (e x) (e y)) color
      Finset.univ) :
    C.IsIndep ((colorClass (Finset.univ : Finset (Fin n)) color j).image e) :=
  image_colorClass_isIndep C e hproper

/-- A proper `k`-coloring yields an independent color class of size at least
the average color-class size. -/
theorem exists_large_indep_colorClass_of_proper {n k : Nat} (hk : 0 < k)
    (C : _root_.UDConfig n) {color : Fin n → Fin k}
    (hproper : ProperColoringOn (UnitAdj C) color Finset.univ) :
    ∃ j : Fin k,
      C.IsIndep (colorClass (Finset.univ : Finset (Fin n)) color j) ∧
        n ≤ k * (colorClass (Finset.univ : Finset (Fin n)) color j).card := by
  obtain ⟨j, hj⟩ :=
    exists_large_colorClass hk (Finset.univ : Finset (Fin n)) color
  exact ⟨j, colorClass_isIndep C hproper, by simpa using hj⟩

/-- Reindexed version of `exists_large_indep_colorClass_of_proper`, with
cardinality preserved by an equivalence. -/
theorem exists_large_indep_image_colorClass_of_equiv_proper {n k : Nat}
    (hk : 0 < k) (C : _root_.UDConfig n) (e : Fin n ≃ Fin n)
    {color : Fin n → Fin k}
    (hproper : ProperColoringOn (fun x y => UnitAdj C (e x) (e y)) color
      Finset.univ) :
    ∃ j : Fin k,
      C.IsIndep ((colorClass (Finset.univ : Finset (Fin n)) color j).image e) ∧
        n ≤ k * ((colorClass (Finset.univ : Finset (Fin n)) color j).image e).card := by
  obtain ⟨j, hj⟩ :=
    exists_large_image_colorClass hk
      (s := (Finset.univ : Finset (Fin n))) (f := e)
      (fun x _ y _ hxy => e.injective hxy) color
  exact ⟨j, equiv_image_colorClass_isIndep C e hproper, by simpa using hj⟩

end UDConfig

end Combinatorics
end ErdosProblems1066
