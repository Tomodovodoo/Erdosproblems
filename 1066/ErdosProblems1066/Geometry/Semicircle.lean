import Mathlib

/-!
# Open Semicircle Geometry

This file isolates the elementary geometric input used by the Pollack/Pach
unit-distance lower-bound argument: four unit vectors with pairwise dot product
at most `1 / 2` cannot all lie in an open half-plane, and consequently an open
semicircle of a unit circle contains at most three pairwise separated points.
-/

noncomputable section

namespace ErdosProblems1066
namespace Geometry
namespace Semicircle

open Real

/-- Euclidean distance in `ℝ²`, represented as pairs. -/
def eucDist (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

lemma eucDist_nonneg (p q : ℝ × ℝ) : 0 ≤ eucDist p q :=
  Real.sqrt_nonneg _

lemma eucDist_sq (p q : ℝ × ℝ) :
    eucDist p q ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  unfold eucDist
  rw [Real.sq_sqrt]
  positivity

lemma eucDist_eq_one_iff (p q : ℝ × ℝ) :
    eucDist p q = 1 ↔ (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = 1 := by
  constructor
  · intro h
    have hs := congrArg (fun t : ℝ => t ^ 2) h
    simpa [eucDist_sq] using hs
  · intro h
    unfold eucDist
    rw [h]
    norm_num

private lemma unit_upper_half_x_bounds {x y : ℝ}
    (hunit : x ^ 2 + y ^ 2 = 1) (hpos : 0 < y) :
    -1 < x ∧ x < 1 := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hpos
  constructor
  · nlinarith [sq_nonneg (x + 1)]
  · nlinarith [sq_nonneg (x - 1)]

private lemma cos_arccos_sub_of_unit_upper_half
    (x y : Fin 4 → ℝ)
    (hunit : ∀ i, x i ^ 2 + y i ^ 2 = 1)
    (hpos : ∀ i, 0 < y i)
    (i j : Fin 4) :
    Real.cos (Real.arccos (x i) - Real.arccos (x j)) =
      x i * x j + y i * y j := by
  have hxi := unit_upper_half_x_bounds (hunit i) (hpos i)
  have hxj := unit_upper_half_x_bounds (hunit j) (hpos j)
  have hsi : Real.sqrt (1 - x i ^ 2) = y i := by
    have hsq : 1 - x i ^ 2 = y i ^ 2 := by nlinarith [hunit i]
    rw [hsq, Real.sqrt_sq (le_of_lt (hpos i))]
  have hsj : Real.sqrt (1 - x j ^ 2) = y j := by
    have hsq : 1 - x j ^ 2 = y j ^ 2 := by nlinarith [hunit j]
    rw [hsq, Real.sqrt_sq (le_of_lt (hpos j))]
  rw [Real.cos_sub,
    Real.cos_arccos (le_of_lt hxi.1) (le_of_lt hxi.2),
    Real.cos_arccos (le_of_lt hxj.1) (le_of_lt hxj.2),
    Real.sin_arccos, Real.sin_arccos, hsi, hsj]

private lemma four_angles_not_separated_in_open_pi_interval
    (θ : Fin 4 → ℝ)
    (hrange : ∀ i, 0 < θ i ∧ θ i < Real.pi)
    (hsep : ∀ i j, i ≠ j → Real.pi / 3 ≤ |θ i - θ j|) :
    False := by
  let σ := Tuple.sort θ
  let φ : Fin 4 → ℝ := θ ∘ σ
  have hmono : Monotone φ := Tuple.monotone_sort θ
  have h01le : φ 0 ≤ φ 1 := hmono (by decide)
  have h12le : φ 1 ≤ φ 2 := hmono (by decide)
  have h23le : φ 2 ≤ φ 3 := hmono (by decide)
  have hσ01 : σ (0 : Fin 4) ≠ σ 1 := σ.injective.ne (by decide)
  have hσ12 : σ (1 : Fin 4) ≠ σ 2 := σ.injective.ne (by decide)
  have hσ23 : σ (2 : Fin 4) ≠ σ 3 := σ.injective.ne (by decide)
  have hgap01 : Real.pi / 3 ≤ φ 1 - φ 0 := by
    have h := hsep (σ 0) (σ 1) hσ01
    have habs : |θ (σ 0) - θ (σ 1)| = φ 1 - φ 0 := by
      change |φ 0 - φ 1| = φ 1 - φ 0
      rw [abs_of_nonpos (sub_nonpos.mpr h01le)]
      ring
    simpa [habs] using h
  have hgap12 : Real.pi / 3 ≤ φ 2 - φ 1 := by
    have h := hsep (σ 1) (σ 2) hσ12
    have habs : |θ (σ 1) - θ (σ 2)| = φ 2 - φ 1 := by
      change |φ 1 - φ 2| = φ 2 - φ 1
      rw [abs_of_nonpos (sub_nonpos.mpr h12le)]
      ring
    simpa [habs] using h
  have hgap23 : Real.pi / 3 ≤ φ 3 - φ 2 := by
    have h := hsep (σ 2) (σ 3) hσ23
    have habs : |θ (σ 2) - θ (σ 3)| = φ 3 - φ 2 := by
      change |φ 2 - φ 3| = φ 3 - φ 2
      rw [abs_of_nonpos (sub_nonpos.mpr h23le)]
      ring
    simpa [habs] using h
  have hspan_ge : Real.pi ≤ φ 3 - φ 0 := by
    nlinarith [hgap01, hgap12, hgap23]
  have hspan_lt : φ 3 - φ 0 < Real.pi := by
    have h0 : 0 < φ 0 := by simpa [φ] using (hrange (σ 0)).1
    have h3 : φ 3 < Real.pi := by simpa [φ] using (hrange (σ 3)).2
    linarith
  linarith

/--
Four unit vectors in the open upper half-plane cannot have all pairwise dot
products at most `1 / 2`.
-/
theorem no_four_unit_vectors_upper_half
    (x y : Fin 4 → ℝ)
    (hunit : ∀ i, x i ^ 2 + y i ^ 2 = 1)
    (hpos : ∀ i, 0 < y i)
    (hdot : ∀ i j, i ≠ j → x i * x j + y i * y j ≤ 1 / 2) :
    False := by
  let θ : Fin 4 → ℝ := fun i => Real.arccos (x i)
  have hθ_range : ∀ i, 0 < θ i ∧ θ i < Real.pi := by
    intro i
    have hx := unit_upper_half_x_bounds (hunit i) (hpos i)
    exact ⟨Real.arccos_pos.mpr hx.2, Real.arccos_lt_pi.mpr hx.1⟩
  have hθ_sep : ∀ i j, i ≠ j → Real.pi / 3 ≤ |θ i - θ j| := by
    intro i j hij
    by_contra hnot
    have hlt : |θ i - θ j| < Real.pi / 3 := lt_of_not_ge hnot
    have hcos_gt : 1 / 2 < Real.cos |θ i - θ j| := by
      have h :=
        Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (θ i - θ j))
          (by linarith [Real.pi_pos]) hlt
      simpa [Real.cos_pi_div_three] using h
    have hdot_gt : 1 / 2 < x i * x j + y i * y j := by
      calc
        1 / 2 < Real.cos |θ i - θ j| := hcos_gt
        _ = Real.cos (θ i - θ j) := by rw [Real.cos_abs]
        _ = x i * x j + y i * y j := by
          simpa [θ] using cos_arccos_sub_of_unit_upper_half x y hunit hpos i j
    linarith [hdot i j hij]
  exact four_angles_not_separated_in_open_pi_interval θ hθ_range hθ_sep

/--
Four unit vectors in any open half-plane cannot have all pairwise dot products
at most `1 / 2`.
-/
theorem no_four_unit_vectors_in_open_halfplane
    (u v : Fin 4 → ℝ) (d₁ d₂ : ℝ) (hd : (d₁, d₂) ≠ (0, 0))
    (hunit : ∀ i, u i ^ 2 + v i ^ 2 = 1)
    (hdot : ∀ i j, i ≠ j → u i * u j + v i * v j ≤ 1 / 2)
    (hhalf : ∀ i, d₁ * u i + d₂ * v i > 0) :
    False := by
  let N := Real.sqrt (d₁ ^ 2 + d₂ ^ 2)
  have hsum_nonneg : 0 ≤ d₁ ^ 2 + d₂ ^ 2 := by positivity
  have hsum_ne : d₁ ^ 2 + d₂ ^ 2 ≠ 0 := by
    intro h
    have hd₁ : d₁ = 0 := by nlinarith [sq_nonneg d₁, sq_nonneg d₂]
    have hd₂ : d₂ = 0 := by nlinarith [sq_nonneg d₁, sq_nonneg d₂]
    exact hd (by ext <;> assumption)
  have hsum_pos : 0 < d₁ ^ 2 + d₂ ^ 2 :=
    lt_of_le_of_ne hsum_nonneg (Ne.symm hsum_ne)
  have hN_pos : 0 < N := Real.sqrt_pos.2 hsum_pos
  let x' : Fin 4 → ℝ := fun i => (d₂ * u i - d₁ * v i) / N
  let y' : Fin 4 → ℝ := fun i => (d₁ * u i + d₂ * v i) / N
  apply no_four_unit_vectors_upper_half x' y'
  · intro i
    dsimp [x', y', N]
    field_simp [hN_pos.ne']
    rw [Real.sq_sqrt hsum_nonneg]
    nlinarith [hunit i]
  · intro i
    dsimp [y', N]
    exact div_pos (hhalf i) hN_pos
  · intro i j hij
    have hrot :
        x' i * x' j + y' i * y' j = u i * u j + v i * v j := by
      dsimp [x', y', N]
      field_simp [hN_pos.ne']
      rw [Real.sq_sqrt hsum_nonneg]
      ring
    rw [hrot]
    exact hdot i j hij

/--
At most three points can lie on a unit circle inside an open semicircle while
remaining pairwise at distance at least `1`.
-/
theorem at_most_three_in_open_semicircle {m : ℕ}
    (pts : Fin m → ℝ × ℝ) (center : ℝ × ℝ) (d : ℝ × ℝ)
    (hd : d ≠ (0, 0))
    (hon_circle : ∀ i, eucDist (pts i) center = 1)
    (hsep : ∀ i j, i ≠ j → 1 ≤ eucDist (pts i) (pts j))
    (hin_half : ∀ i,
      d.1 * (pts i).1 + d.2 * (pts i).2 >
        d.1 * center.1 + d.2 * center.2) :
    m ≤ 3 := by
  by_contra hm
  have hm4 : 4 ≤ m := by omega
  let idx : Fin 4 → Fin m := fun i => ⟨i, by omega⟩
  let u : Fin 4 → ℝ := fun i => (pts (idx i)).1 - center.1
  let v : Fin 4 → ℝ := fun i => (pts (idx i)).2 - center.2
  have hunit : ∀ i, u i ^ 2 + v i ^ 2 = 1 := by
    intro i
    have h := (eucDist_eq_one_iff (pts (idx i)) center).mp (hon_circle (idx i))
    simpa [u, v] using h
  have hdot : ∀ i j, i ≠ j → u i * u j + v i * v j ≤ 1 / 2 := by
    intro i j hij
    have hidx : idx i ≠ idx j := by
      intro h
      apply hij
      exact Fin.ext (by simpa using congrArg Fin.val h)
    have hdist := hsep (idx i) (idx j) hidx
    have hdist_sq : 1 ≤ ((pts (idx i)).1 - (pts (idx j)).1) ^ 2 +
        ((pts (idx i)).2 - (pts (idx j)).2) ^ 2 := by
      have hsquare : (1 : ℝ) ≤ eucDist (pts (idx i)) (pts (idx j)) ^ 2 := by
        have hnonneg := eucDist_nonneg (pts (idx i)) (pts (idx j))
        nlinarith
      simpa [eucDist_sq] using hsquare
    have hi := hunit i
    have hj := hunit j
    dsimp [u, v] at hi hj ⊢
    nlinarith [hdist_sq, hi, hj]
  have hhalf : ∀ i, d.1 * u i + d.2 * v i > 0 := by
    intro i
    have h := hin_half (idx i)
    dsimp [u, v] at h ⊢
    linarith
  exact no_four_unit_vectors_in_open_halfplane u v d.1 d.2 hd hunit hdot hhalf

end Semicircle
end Geometry
end ErdosProblems1066
