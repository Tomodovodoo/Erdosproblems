import Mathlib

/-!
# Finite Coloring Lemmas

This file contains geometry-free finite coloring facts useful for extracting
large independent sets from finite colorings.
-/

namespace ErdosProblems1066
namespace Combinatorics

/-- Among finitely many colors, one fiber has at least the average size.

The inequality is written without division:
`Fintype.card α ≤ Fintype.card β * fiber.card`. -/
theorem exists_large_fiber {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [Nonempty β] (c : α → β) :
    ∃ b : β, Fintype.card α ≤
      Fintype.card β *
        ((Finset.univ : Finset α).filter fun a : α => c a = b).card := by
  let fiberCard : β → Nat :=
    fun b => ((Finset.univ : Finset α).filter fun a : α => c a = b).card
  have h_sum_card :
      Finset.sum (Finset.univ : Finset β) fiberCard = Fintype.card α := by
    have h_univ :
        Finset.sum (Finset.univ : Finset β) fiberCard =
          (Finset.univ : Finset α).card := by
      calc
        Finset.sum (Finset.univ : Finset β) fiberCard =
            Finset.sum (Finset.univ : Finset β)
              (fun b : β =>
                Finset.sum
                  (((Finset.univ : Finset α).filter fun a : α => c a = b))
                  (fun _ => (1 : Nat))) := by
          apply Finset.sum_congr rfl
          intro b _hb
          dsimp [fiberCard]
          rw [Finset.card_eq_sum_ones]
        _ = Finset.sum (Finset.univ : Finset α) (fun _ : α => (1 : Nat)) := by
          simpa [fiberCard] using
            Finset.sum_fiberwise (Finset.univ : Finset α) c
              (fun _ : α => (1 : Nat))
        _ = (Finset.univ : Finset α).card := by
          rw [Finset.card_eq_sum_ones]
    simpa only [Fintype.card] using h_univ
  let maxData :=
    Finset.exists_max_image (Finset.univ : Finset β) fiberCard
      Finset.univ_nonempty
  let b : β := maxData.choose
  have hbmax :
      ∀ b', b' ∈ (Finset.univ : Finset β) → fiberCard b' ≤ fiberCard b :=
    maxData.choose_spec.2
  refine ⟨b, ?_⟩
  have h_sum_le :
      Finset.sum (Finset.univ : Finset β) fiberCard ≤
        Finset.sum (Finset.univ : Finset β) (fun _ : β => fiberCard b) := by
    exact Finset.sum_le_sum fun b' hb' => hbmax b' hb'
  calc
    Fintype.card α = Finset.sum (Finset.univ : Finset β) fiberCard :=
      h_sum_card.symm
    _ ≤ Finset.sum (Finset.univ : Finset β) (fun _ : β => fiberCard b) :=
      h_sum_le
    _ = Fintype.card β * fiberCard b := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

/-- `Fin n` version of `exists_large_fiber`, matching the form used after a
finite coloring of `n` vertices by `k` colors. -/
theorem exists_large_color_class (n k : Nat) (hk : 0 < k)
    (c : Fin n → Fin k) :
    ∃ j : Fin k, n ≤
      k * ((Finset.univ : Finset (Fin n)).filter fun i : Fin n => c i = j).card := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  simpa using (exists_large_fiber (α := Fin n) (β := Fin k) c)

end Combinatorics
end ErdosProblems1066

