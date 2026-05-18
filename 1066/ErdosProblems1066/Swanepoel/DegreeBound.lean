import ErdosProblems1066.Geometry.Semicircle
import ErdosProblems1066.UnitDistanceBounds

/-!
# Swanepoel degree bound

This module isolates the elementary Euclidean fact behind the maximum degree
bound for separated unit-distance configurations: a vertex has at most six
unit-distance neighbours.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace DegreeBound

abbrev Point : Type := Real × Real

def centeredDot (d p center : Point) : Real :=
  d.1 * (p.1 - center.1) + d.2 * (p.2 - center.2)

lemma semicircle_eucDist_eq_root (p q : Point) :
    Geometry.Semicircle.eucDist p q = _root_.eucDist p q := by
  rfl

lemma point_ne_center_of_on_unit_circle {p center : Point}
    (h : _root_.eucDist p center = 1) :
    p ≠ center := by
  intro hpc
  simp [hpc] at h

lemma exists_large_real_not_in_finset (s : Finset Real) :
    ∃ t : Real, ∀ x ∈ s, x ≠ t := by
  refine ⟨1 + ∑ x ∈ s, |x|, ?_⟩
  intro x hx hxt
  have hx_le_sum : |x| ≤ ∑ y ∈ s, |y| :=
    Finset.single_le_sum (fun y _ => abs_nonneg y) hx
  have hx_abs : x ≤ |x| := le_abs_self x
  linarith

lemma exists_direction_avoiding_centered_points {m : Nat}
    (pts : Fin m → Point) (center : Point)
    (hon_circle : ∀ i, _root_.eucDist (pts i) center = 1) :
    ∃ d : Point, d ≠ (0, 0) ∧ ∀ i, centeredDot d (pts i) center ≠ 0 := by
  classical
  let bad : Finset Real :=
    (Finset.univ : Finset (Fin m)).filter
      (fun i => (pts i).2 - center.2 ≠ 0)
        |>.image (fun i => -((pts i).1 - center.1) / ((pts i).2 - center.2))
  obtain ⟨t, ht⟩ := exists_large_real_not_in_finset bad
  refine ⟨(1, t), by simp, ?_⟩
  intro i hdot
  dsimp [centeredDot] at hdot
  by_cases hy : (pts i).2 - center.2 = 0
  · have hx : (pts i).1 - center.1 = 0 := by simpa [hy] using hdot
    exact point_ne_center_of_on_unit_circle (hon_circle i) (by
      ext <;> linarith)
  · have ht_eq : t = -((pts i).1 - center.1) / ((pts i).2 - center.2) := by
      rw [eq_div_iff hy]
      linarith
    exact ht _ (by
      refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
      simp [hy]) ht_eq.symm

lemma card_le_three_in_open_semicircle {m : Nat}
    (pts : Fin m → Point) (center d : Point) (s : Finset (Fin m))
    (hd : d ≠ (0, 0))
    (hon_circle : ∀ i, _root_.eucDist (pts i) center = 1)
    (hsep : ∀ i j, i ≠ j → 1 ≤ _root_.eucDist (pts i) (pts j))
    (hin_half : ∀ i ∈ s, 0 < centeredDot d (pts i) center) :
    s.card ≤ 3 := by
  let emb : Fin s.card → Fin m := s.orderEmbOfFin rfl
  have h := Geometry.Semicircle.at_most_three_in_open_semicircle
    (fun i : Fin s.card => pts (emb i)) center d hd
  refine h ?_ ?_ ?_
  · intro i
    simpa [semicircle_eucDist_eq_root] using hon_circle (emb i)
  · intro i j hij
    have hne : emb i ≠ emb j := by
      intro hsame
      exact hij ((s.orderEmbOfFin rfl).injective hsame)
    simpa [semicircle_eucDist_eq_root] using hsep (emb i) (emb j) hne
  · intro i
    have hi_mem : emb i ∈ s := Finset.orderEmbOfFin_mem s rfl i
    have hpos := hin_half (emb i) hi_mem
    dsimp [centeredDot] at hpos
    linarith

theorem unit_circle_separated_card_le_six {m : Nat}
    (pts : Fin m → Point) (center : Point)
    (hon_circle : ∀ i, _root_.eucDist (pts i) center = 1)
    (hsep : ∀ i j, i ≠ j → 1 ≤ _root_.eucDist (pts i) (pts j)) :
    m ≤ 6 := by
  classical
  obtain ⟨d, hd_ne, hd_avoid⟩ :=
    exists_direction_avoiding_centered_points pts center hon_circle
  let pos : Fin m → Prop := fun i => 0 < centeredDot d (pts i) center
  let sPos : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter pos
  have hsPos : sPos.card ≤ 3 := by
    refine card_le_three_in_open_semicircle pts center d sPos hd_ne hon_circle hsep ?_
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hsNonpos : ((Finset.univ : Finset (Fin m)).filter (fun i => ¬ pos i)).card ≤ 3 := by
    refine card_le_three_in_open_semicircle pts center (-d.1, -d.2)
      ((Finset.univ : Finset (Fin m)).filter (fun i => ¬ pos i)) ?_ hon_circle hsep ?_
    · intro h
      exact hd_ne (by
        ext <;> linarith [Prod.ext_iff.mp h |>.1, Prod.ext_iff.mp h |>.2])
    · intro i hi
      have hnpos : ¬ pos i := (Finset.mem_filter.mp hi).2
      have hne : centeredDot d (pts i) center ≠ 0 := hd_avoid i
      have hneg : centeredDot d (pts i) center < 0 := by
        exact lt_of_le_of_ne (not_lt.mp hnpos) hne
      dsimp [centeredDot] at hneg ⊢
      linarith
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin m))) (p := pos)
  have hm :
      m = sPos.card + ((Finset.univ : Finset (Fin m)).filter (fun i => ¬ pos i)).card := by
    simpa [sPos, Fintype.card_fin] using hsplit.symm
  omega

theorem UDConfig.unitDistanceNeighborSet_card_le_six {n : Nat}
    (C : _root_.UDConfig n) (center : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter
      (fun j => j ≠ center ∧ _root_.eucDist (C.pts j) (C.pts center) = 1)).card ≤ 6 := by
  classical
  let nbrs : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter
      (fun j => j ≠ center ∧ _root_.eucDist (C.pts j) (C.pts center) = 1)
  let ptsNbr : Fin nbrs.card → Point := fun i => C.pts (nbrs.orderEmbOfFin rfl i)
  have hcircle : ∀ i, _root_.eucDist (ptsNbr i) (C.pts center) = 1 := by
    intro i
    exact (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem nbrs rfl i)).2.2
  have hsep : ∀ i j, i ≠ j → 1 ≤ _root_.eucDist (ptsNbr i) (ptsNbr j) := by
    intro i j hij
    have hne : nbrs.orderEmbOfFin rfl i ≠ nbrs.orderEmbOfFin rfl j := by
      intro hsame
      exact hij ((nbrs.orderEmbOfFin rfl).injective hsame)
    exact C.sep (nbrs.orderEmbOfFin rfl i) (nbrs.orderEmbOfFin rfl j) hne
  simpa [nbrs, ptsNbr] using
    unit_circle_separated_card_le_six ptsNbr (C.pts center) hcircle hsep

end DegreeBound
end Swanepoel
end ErdosProblems1066

end
