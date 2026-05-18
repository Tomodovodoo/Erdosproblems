import Mathlib

set_option autoImplicit true
set_option linter.style.longLine false
set_option linter.style.induction false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.style.refine false
set_option linter.style.setOption false
set_option linter.style.whitespace false
set_option linter.flexible false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Unit Distance Graphs with Minimum Separation ≥ 1

We study the independence number of "unit distance graphs" on n points in ℝ²,
where all pairwise distances are ≥ 1 and edges connect pairs at distance exactly 1.

Let g(n) be the largest integer such that every such graph has an independent
set of size ≥ g(n). The known bounds are:

- Lower bound: g(n) ≥ ⌈8n/31⌉ (Swanepoel, 2002)
  improving on ⌈9n/35⌉ (Csizmadia, 1998) and ⌈n/4⌉ (Pollack/Pach, 1985)
- Upper bound: g(n) ≤ ⌊5n/16⌋ (Pach–Tóth, 1996)
  improving on ⌊6n/19⌋ (Chung–Graham / Pach) and ⌊n/3⌋ (Erdős)

## Local proof documents

The source papers used for the informal proof record are kept outside the Lean
package in `../Proof_Files/`:

- `../Proof_Files/Po85.pdf`: Pollack/Pach-era `n/4` lower bound and early
  unit-distance graph bounds.
- `../Proof_Files/Cs98.pdf`: Csizmadia's `9n/35` lower-bound improvement.
- `../Proof_Files/Sw02.pdf`: Swanepoel's `8n/31` lower-bound improvement.
- `../Proof_Files/PaTo96.ps`: Pach–Tóth's `5n/16` upper-bound construction.

## What is proved in this file

**Fully proved:**
- `upper_bound_third`: g(n) ≤ ⌈n/3⌉ via explicit equilateral triangle construction
- `lower_bound_quarter`: g(n) ≥ ⌈n/4⌉ via Pach's observation that the unit distance
  graph is 4-colorable (using greedy coloring with a generic direction ordering).
  This uses the key geometric lemma `no_four_unit_vectors_upper_half` showing
  that at most 3 unit-distance neighbors lie in any open half-plane.

**Not yet formalized in Lean:**
- Swanepoel's improved lower bound 8n/31.
- Pach–Tóth's improved upper bound 5n/16.

Those stronger paper results are tracked in `../proof_workings/`, but this file
does not assert them until their proofs are kernel-checked here.
-/

noncomputable section
open Classical Real Finset Function
set_option maxHeartbeats 800000

/-! ## Definitions -/

/-- Euclidean distance in ℝ² -/
def eucDist (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-- A unit distance configuration: n labeled points in ℝ² with pairwise distance ≥ 1 -/
structure UDConfig (n : ℕ) where
  pts : Fin n → ℝ × ℝ
  sep : ∀ i j : Fin n, i ≠ j → 1 ≤ eucDist (pts i) (pts j)

/-- An independent set in a UDConfig: a set of vertices with pairwise distance ≠ 1
    (equivalently, > 1 given the separation condition) -/
def UDConfig.IsIndep {n : ℕ} (C : UDConfig n) (s : Finset (Fin n)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → eucDist (C.pts i) (C.pts j) ≠ 1

/-! ## Basic lemmas about eucDist -/

@[simp] lemma eucDist_self (p : ℝ × ℝ) : eucDist p p = 0 := by
  simp [eucDist]

lemma eucDist_comm (p q : ℝ × ℝ) : eucDist p q = eucDist q p := by
  simp [eucDist]; ring_nf

lemma eucDist_nonneg (p q : ℝ × ℝ) : 0 ≤ eucDist p q :=
  Real.sqrt_nonneg _

lemma eucDist_sq (p q : ℝ × ℝ) :
    eucDist p q ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  unfold eucDist
  rw [sq_sqrt]
  positivity

lemma eucDist_eq_one_iff (p q : ℝ × ℝ) :
    eucDist p q = 1 ↔ (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = 1 := by
  constructor
  · intro h; have := congr_arg (· ^ 2) h; simp [eucDist_sq] at this; linarith
  · intro h; unfold eucDist; rw [h]; simp

lemma eucDist_ne_zero_of_ne {p q : ℝ × ℝ} (h : p ≠ q) : eucDist p q ≠ 0 := by
  intro heq
  apply h
  unfold eucDist at heq
  have hnn : 0 ≤ (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by positivity
  have hsq : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = 0 := by
    rwa [Real.sqrt_eq_zero hnn] at heq
  have h1 : p.1 = q.1 := by nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  have h2 : p.2 = q.2 := by nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  exact Prod.ext h1 h2

lemma eucDist_ge_one_iff (p q : ℝ × ℝ) :
    1 ≤ eucDist p q ↔ 1 ≤ (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  rw [← eucDist_sq]
  constructor
  · intro h; nlinarith [eucDist_nonneg p q]
  · intro h
    have hnn := eucDist_nonneg p q
    nlinarith [sq_nonneg (eucDist p q - 1)]

/-! ## Upper Bound: g(n) ≤ ⌈n/3⌉ via equilateral triangles -/

/-- Construction: k copies of equilateral triangles with side length 1,
    placed far apart. This gives a 3k-point configuration where the
    maximum independent set has size k.

    Reference: the early upper-bound context is documented in
    `../Proof_Files/Po85.pdf`. -/
theorem upper_bound_third (k : ℕ) (_hk : 0 < k) :
    ∃ C : UDConfig (3 * k),
      ∀ s : Finset (Fin (3 * k)), C.IsIndep s → s.card ≤ k := by
  by_contra hcontr
  set v : Fin (3 * k) → ℝ × ℝ := fun i =>
    (10 * (i / 3 : ℕ) + if i.val % 3 = 0 then 0 else if i.val % 3 = 1 then 1 else 1 / 2,
     if i.val % 3 = 0 then 0 else if i.val % 3 = 1 then 0 else Real.sqrt 3 / 2)
  refine' hcontr ⟨⟨v, _⟩, _⟩ <;> norm_num [UDConfig.IsIndep]
  · intro i j hij; unfold eucDist; norm_num [v]
    by_cases hi : (i : ℕ) / 3 = (j : ℕ) / 3 <;> simp_all +decide [Fin.ext_iff]
    · have := Nat.mod_add_div i 3; have := Nat.mod_add_div j 3
      norm_num at *; split_ifs <;> ring_nf <;> norm_num <;> omega
    · have h_diff_x : |(10 * (i / 3 : ℕ) : ℝ) - (10 * (j / 3 : ℕ) : ℝ)| ≥ 10 := by
        norm_cast; grind
      split_ifs <;> norm_num at *
      any_goals linarith [abs_mul_abs_self (10 * (i / 3 : ℕ) - 10 * (j / 3 : ℕ) : ℝ)]
      grind +locals
      · cases abs_cases (10 * (i / 3 : ℕ) - 10 * (j / 3 : ℕ) : ℝ) <;>
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
      · cases abs_cases (10 * (i / 3 : ℕ) + 1 - 10 * (j / 3 : ℕ) : ℝ) <;>
          cases abs_cases (10 * (i / 3 : ℕ) - 10 * (j / 3 : ℕ) : ℝ) <;> linarith
      · cases abs_cases (10 * (i / 3 : ℕ) - 10 * (j / 3 : ℕ) : ℝ) <;>
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
      · cases abs_cases (10 * (i / 3 : ℕ) - 10 * (j / 3 : ℕ) : ℝ) <;>
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three]
      · cases abs_cases (10 * (i / 3 : ℕ) - 10 * (j / 3 : ℕ) : ℝ) <;>
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
  · intro s hs
    have := Finset.card_le_card (show s ⊆ Finset.univ from Finset.subset_univ s)
    simp_all +decide
    have h_dist : ∀ i j : Fin (3 * k), i ∈ s → j ∈ s → i ≠ j →
        (i.val / 3 : ℕ) ≠ (j.val / 3 : ℕ) := by
      intro i j hi hj hij; specialize hs i hi j hj hij
      contrapose! hs; simp_all +decide [eucDist]; grind
    have h_card : Finset.card (Finset.image (fun i : Fin (3 * k) => i.val / 3) s) ≤ k := by
      exact le_trans (Finset.card_le_card <| Finset.image_subset_iff.mpr fun i hi =>
        Finset.mem_range.mpr <| show (i : ℕ) / 3 < k from
          Nat.div_lt_of_lt_mul <| by linarith [Fin.is_lt i]) (by norm_num)
    rwa [Finset.card_image_of_injOn fun i hi j hj hij => by
      contrapose hij; exact h_dist i j hi hj hij] at h_card

/-! ## Geometric lemmas for lower bound -/

/-
4 unit vectors in the upper half-plane cannot have pairwise inner product ≤ 1/2.
-/
theorem no_four_unit_vectors_upper_half
    (x y : Fin 4 → ℝ)
    (hunit : ∀ i, x i ^ 2 + y i ^ 2 = 1)
    (hpos : ∀ i, 0 < y i)
    (hdot : ∀ i j, i ≠ j → x i * x j + y i * y j ≤ 1/2) : False := by
  -- Let θ_i = Real.arccos (x i). Since y i > 0 and x i^2 + y i^2 = 1, we have x i ∈ (-1, 1), so θ_i ∈ (0, π).
  set θ : Fin 4 → ℝ := fun i => Real.arccos (x i)
  have hθ_range : ∀ i, 0 < θ i ∧ θ i < Real.pi := by
    exact fun i => ⟨ Real.arccos_pos.mpr ( by nlinarith only [ hunit i, hpos i ] ), lt_of_le_of_ne ( Real.arccos_le_pi _ ) ( by intro H; have := hunit i; rw [ Real.arccos_eq_pi ] at H; nlinarith [ hpos i ] ) ⟩;
  -- Inner product condition gives cos(θ_i - θ_j) ≤ 1/2, so |θ_i - θ_j| ≥ π/3.
  have hθ_diff : ∀ i j, i ≠ j → |θ i - θ j| ≥ Real.pi / 3 := by
    -- Using the cosine addition formula, we have cos(θ_i - θ_j) = x_i x_j + y_i y_j.
    have h_cos_diff : ∀ i j, Real.cos (θ i - θ j) = x i * x j + y i * y j := by
      intro i j; rw [ Real.cos_sub, Real.cos_arccos, Real.sin_arccos, Real.cos_arccos, Real.sin_arccos ] <;> try nlinarith [ hunit i, hunit j ];
      rw [ show 1 - x i ^ 2 = y i ^ 2 by linarith [ hunit i ], show 1 - x j ^ 2 = y j ^ 2 by linarith [ hunit j ], Real.sqrt_sq ( le_of_lt ( hpos i ) ), Real.sqrt_sq ( le_of_lt ( hpos j ) ) ];
    intros i j hij
    by_contra h_contra
    have h_cos_lt : Real.cos (|θ i - θ j|) > 1 / 2 := by
      exact Real.cos_pi_div_three.symm ▸ Real.cos_lt_cos_of_nonneg_of_le_pi ( abs_nonneg _ ) ( by linarith [ Real.pi_pos ] ) ( by linarith [ Real.pi_pos ] );
    norm_num at * ; linarith [ hdot i j hij, h_cos_diff i j ];
  -- Sort the 4 angles in decreasing order, sum the 3 gaps ≥ π, but θ_max < π and θ_min > 0 gives a contradiction.
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin 4 ≃ Fin 4, θ (σ 0) ≥ θ (σ 1) ∧ θ (σ 1) ≥ θ (σ 2) ∧ θ (σ 2) ≥ θ (σ 3) := by
    -- By definition of permutation, such a σ exists.
    have h_perm : ∃ σ : Fin 4 ≃ Fin 4, ∀ i j, i < j → θ (σ i) ≥ θ (σ j) := by
      have h_exists_max : ∀ (s : Finset (Fin 4)), s.Nonempty → ∃ m ∈ s, ∀ n ∈ s, θ n ≤ θ m := by
        exact fun s hs => Finset.exists_max_image _ _ hs
      -- By repeatedly applying `h_exists_max`, we can construct the permutation `σ`.
      obtain ⟨m0, hm0⟩ : ∃ m0 ∈ Finset.univ, ∀ n ∈ Finset.univ, θ n ≤ θ m0 := h_exists_max Finset.univ (by decide)
      obtain ⟨m1, hm1⟩ : ∃ m1 ∈ Finset.univ \ {m0}, ∀ n ∈ Finset.univ \ {m0}, θ n ≤ θ m1 := h_exists_max (Finset.univ \ {m0}) (by
      fin_cases m0 <;> trivial)
      obtain ⟨m2, hm2⟩ : ∃ m2 ∈ Finset.univ \ {m0, m1}, ∀ n ∈ Finset.univ \ {m0, m1}, θ n ≤ θ m2 := h_exists_max (Finset.univ \ {m0, m1}) (by
      fin_cases m0 <;> fin_cases m1 <;> trivial)
      obtain ⟨m3, hm3⟩ : ∃ m3 ∈ Finset.univ \ {m0, m1, m2}, ∀ n ∈ Finset.univ \ {m0, m1, m2}, θ n ≤ θ m3 := h_exists_max (Finset.univ \ {m0, m1, m2}) (by
      fin_cases m0 <;> fin_cases m1 <;> fin_cases m2 <;> trivial);
      use Equiv.ofBijective (fun i => if i = 0 then m0 else if i = 1 then m1 else if i = 2 then m2 else m3) (by
      have h_distinct : m0 ≠ m1 ∧ m0 ≠ m2 ∧ m0 ≠ m3 ∧ m1 ≠ m2 ∧ m1 ≠ m3 ∧ m2 ≠ m3 := by
        grind;
      fin_cases m0 <;> fin_cases m1 <;> fin_cases m2 <;> fin_cases m3 <;> trivial);
      grind;
    exact ⟨ h_perm.choose, h_perm.choose_spec 0 1 ( by decide ), h_perm.choose_spec 1 2 ( by decide ), h_perm.choose_spec 2 3 ( by decide ) ⟩;
  have := hθ_diff ( σ 0 ) ( σ 1 ) ( by simp +decide ) ; have := hθ_diff ( σ 1 ) ( σ 2 ) ( by simp +decide ) ; have := hθ_diff ( σ 2 ) ( σ 3 ) ( by simp +decide ) ; norm_num at *;
  cases abs_cases ( θ ( σ 0 ) - θ ( σ 1 ) ) <;> cases abs_cases ( θ ( σ 1 ) - θ ( σ 2 ) ) <;> cases abs_cases ( θ ( σ 2 ) - θ ( σ 3 ) ) <;> linarith [ hθ_range ( σ 0 ), hθ_range ( σ 1 ), hθ_range ( σ 2 ), hθ_range ( σ 3 ) ]

/-
Generalization: 4 unit vectors in any open half-plane cannot have
    pairwise inner product ≤ 1/2. Proved by rotation to reduce to upper half.
-/
theorem no_four_unit_vectors_in_open_halfplane
    (u v : Fin 4 → ℝ) (d₁ d₂ : ℝ) (hd : (d₁, d₂) ≠ (0, 0))
    (hunit : ∀ i, u i ^ 2 + v i ^ 2 = 1)
    (hdot : ∀ i j, i ≠ j → u i * u j + v i * v j ≤ 1/2)
    (hhalf : ∀ i, d₁ * u i + d₂ * v i > 0) : False := by
  -- Reduce to no_four_unit_vectors_upper_half by rotation.
  set N := Real.sqrt (d₁^2 + d₂^2)
  have hN_pos : 0 < N := by
    exact Real.sqrt_pos.mpr ( by contrapose! hd; exact Prod.mk_inj.mpr ⟨ by nlinarith, by nlinarith ⟩ )
  set x' : Fin 4 → ℝ := fun i => (d₂ * u i - d₁ * v i) / N
  set y' : Fin 4 → ℝ := fun i => (d₁ * u i + d₂ * v i) / N;
  apply no_four_unit_vectors_upper_half x' y';
  · grind +splitImp;
  · exact fun i => div_pos ( hhalf i ) hN_pos;
  · intro i j hij; rw [ div_mul_div_comm, div_mul_div_comm ] ; rw [ ← add_div, div_le_iff₀ ] <;> try positivity;
    rw [ Real.mul_self_sqrt ( by positivity ) ] ; nlinarith [ hdot i j hij, hhalf i, hhalf j ]

/-
At most 3 points on a unit circle centered at `center`, in an open
    half-plane defined by direction `d`, with pairwise distance ≥ 1.
-/
theorem at_most_three_in_open_semicircle
    (pts : Fin m → ℝ × ℝ) (center : ℝ × ℝ) (d : ℝ × ℝ)
    (hd : d ≠ (0, 0))
    (hon_circle : ∀ i, eucDist (pts i) center = 1)
    (hsep : ∀ i j, i ≠ j → 1 ≤ eucDist (pts i) (pts j))
    (hin_half : ∀ i, d.1 * (pts i).1 + d.2 * (pts i).2 >
                     d.1 * center.1 + d.2 * center.2) :
    m ≤ 3 := by
  contrapose! hd;
  have := no_four_unit_vectors_in_open_halfplane ( fun i : Fin 4 => ( pts ⟨ i, by linarith [ Fin.is_lt i ] ⟩ |>.1 ) - center.1 ) ( fun i : Fin 4 => ( pts ⟨ i, by linarith [ Fin.is_lt i ] ⟩ |>.2 ) - center.2 ) ( d.1 ) ( d.2 ) ?_ ?_ ?_ ?_ <;> simp_all +decide [ Prod.ext_iff ];
  · intro h; specialize hin_half ⟨ 0, by linarith ⟩ ; aesop;
  · exact fun i => by have := hon_circle ⟨ i, by linarith [ Fin.is_lt i ] ⟩ ; rw [ eucDist_eq_one_iff ] at this; linarith;
  · intro i j hij; have := hsep ⟨ i, by linarith [ Fin.is_lt i ] ⟩ ⟨ j, by linarith [ Fin.is_lt j ] ⟩ ( by simpa [ Fin.ext_iff ] using hij ) ; norm_num [ eucDist ] at *;
    linarith [ hon_circle ⟨ i, by linarith [ Fin.is_lt i ] ⟩, hon_circle ⟨ j, by linarith [ Fin.is_lt j ] ⟩ ];
  · exact fun i => by linarith [ hin_half ⟨ i, by linarith [ Fin.is_lt i ] ⟩ ] ;

/-! ## Combinatorial lemmas for lower bound -/

/-
Pigeonhole: among k colors on n vertices, some color class has ≥ n/k elements.
-/
theorem exists_large_color_class (n : ℕ) (k : ℕ) (hk : 0 < k)
    (c : Fin n → Fin k) :
    ∃ j : Fin k, n ≤ k * (Finset.univ.filter (fun i => c i = j)).card := by
  -- The sum of the cardinalities of the preimages is equal to $n$ because each element in $\text{Fin } n$ is mapped to exactly one element in $\text{Fin } k$.
  have h_sum_card : ∑ j : Fin k, (Finset.filter (fun i => c i = j) Finset.univ).card = Finset.card (Finset.univ : Finset (Fin n)) := by
    simp +decide only [card_eq_sum_ones, sum_fiberwise];
  norm_num +zetaDelta at *;
  have h_pigeonhole : ∃ j : Fin k, ∀ i : Fin k, (Finset.filter (fun x => c x = i) Finset.univ).card ≤ (Finset.filter (fun x => c x = j) Finset.univ).card := by
    simpa using Finset.exists_max_image Finset.univ ( fun i => Finset.card ( Finset.filter ( fun x => c x = i ) Finset.univ ) ) ⟨ ⟨ 0, hk ⟩, Finset.mem_univ _ ⟩;
  exact ⟨ h_pigeonhole.choose, by simpa [ ← h_sum_card ] using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h_pigeonhole.choose_spec i ⟩

/-
Greedy coloring: if each vertex has ≤ k predecessors (neighbors with
    smaller index), then the graph is (k+1)-colorable.
-/
theorem greedy_coloring (n : ℕ) (k : ℕ)
    (adj : Fin n → Fin n → Prop)
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬adj i i)
    (hbd : ∀ i : Fin n,
      (Finset.univ.filter (fun j : Fin n =>
        adj i j ∧ (j : ℕ) < (i : ℕ))).card ≤ k) :
    ∃ c : Fin n → Fin (k + 1), ∀ i j, adj i j → c i ≠ c j := by
  induction' n with n ihirr;
  · simp +zetaDelta at *;
  · obtain ⟨ c, hc ⟩ := ihirr ( fun i j => adj i.castSucc j.castSucc ) ( fun i j hij => hsymm _ _ hij ) ( fun i => hirr _ ) ( fun i => by
      convert hbd ( Fin.castSucc i ) using 1;
      nontriviality;
      refine' Finset.card_bij ( fun j hj => Fin.castSucc j ) _ _ _ <;> simp +decide [ Fin.ext_iff ];
      exact fun j hj₁ hj₂ => ⟨ ⟨ j, by linarith [ Fin.is_lt j, Fin.is_lt i ] ⟩, ⟨ hj₁, hj₂ ⟩, rfl ⟩ );
    -- Let's define the coloring function $c$ for the graph with $n+1$ vertices by extending the coloring function $c$ for the graph with $n$ vertices.
    obtain ⟨c', hc'⟩ : ∃ c' : Fin (k + 1), ∀ i : Fin n, adj (Fin.last n) (Fin.castSucc i) → c' ≠ c i := by
      have h_card : Finset.card (Finset.image c (Finset.filter (fun i : Fin n => adj (Fin.last n) (Fin.castSucc i)) Finset.univ)) ≤ k := by
        refine' le_trans ( Finset.card_image_le ) _;
        convert hbd ( Fin.last n ) using 1;
        refine' Finset.card_bij ( fun i hi => Fin.castSucc i ) _ _ _ <;> simp +decide [ Fin.ext_iff ];
        exact fun i hi hi' => ⟨ ⟨ i, hi' ⟩, hi, rfl ⟩;
      contrapose! h_card;
      rw [ show Finset.image c { i : Fin n | adj ( Fin.last n ) i.castSucc } = Finset.univ from Finset.eq_univ_of_forall fun x => by obtain ⟨ i, hi, rfl ⟩ := h_card x; exact Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hi ⟩ ) ] ; simp +decide [ Finset.card_univ ] ;
    use Fin.snoc c c';
    intro i j hij; induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp +decide [ * ] at hij ⊢;
    exact Ne.symm ( hc' _ ( hsymm _ _ hij ) )

/-! ## Lower Bound: g(n) ≥ ⌈n/4⌉ -/

/-
Lower bound (Pollack/Pach): every UDConfig has an independent set of size ≥ ⌈n/4⌉.

Reference: `../Proof_Files/Po85.pdf`.

Proof sketch: Choose a direction d not perpendicular to any edge.
Order vertices by d-projection. Each vertex has ≤ 3 earlier unit-distance
neighbors (by `no_four_unit_vectors_in_open_halfplane`). Greedy 4-color,
then take the largest color class.
-/
theorem lower_bound_quarter (n : ℕ) (C : UDConfig n) :
    ∃ s : Finset (Fin n), C.IsIndep s ∧ 4 * s.card ≥ n := by
  -- Let `d` be a direction not perpendicular to any edge. Order vertices by `d`-projection.
  obtain ⟨d, hd⟩ : ∃ d : (ℝ × ℝ), d ≠ (0, 0) ∧ (∀ i j : Fin n, i ≠ j → (d.1 * (C.pts i).1 + d.2 * (C.pts i).2) > (d.1 * (C.pts j).1 + d.2 * (C.pts j).2) ∨ (d.1 * (C.pts i).1 + d.2 * (C.pts i).2) < (d.1 * (C.pts j).1 + d.2 * (C.pts j).2)) := by
    by_contra h_contra;
    -- For each pair of points $(p_i, p_j)$, the set of directions $d$ such that $d \cdot (p_i - p_j) = 0$ is a line through the origin.
    have h_line : ∀ i j : Fin n, i ≠ j → ∃ l : ℝ × ℝ, l ≠ (0, 0) ∧ ∀ d : ℝ × ℝ, d.1 * ((C.pts i).1 - (C.pts j).1) + d.2 * ((C.pts i).2 - (C.pts j).2) = 0 ↔ ∃ t : ℝ, d = t • l := by
      intro i j hij
      use ((C.pts i).2 - (C.pts j).2, -(C.pts i).1 + (C.pts j).1);
      have := C.sep i j hij; simp_all +decide [ Prod.ext_iff, eucDist ];
      constructor;
      · intro h; nlinarith;
      · intro a b; constructor <;> intro h;
        · by_cases h_cases : (C.pts i).2 - (C.pts j).2 = 0;
          · simp_all +decide [ sub_eq_iff_eq_add ];
            cases h <;> simp_all +decide [ sub_eq_iff_eq_add ];
            · exact ⟨ b / ( - ( C.pts i |>.1 ) + ( C.pts j |>.1 ) ), by rw [ div_mul_cancel₀ _ ( by cases abs_cases ( ( C.pts i |>.1 ) - ( C.pts j |>.1 ) ) <;> linarith ) ] ⟩;
            · linarith;
          · use a / ((C.pts i).2 - (C.pts j).2);
            grind;
        · rcases h with ⟨ t, rfl, rfl ⟩ ; ring;
    choose! l hl hl' using h_line;
    -- The union of these lines is a countable set of lines through the origin, which has measure zero.
    have h_union_measure_zero : MeasureTheory.volume (⋃ (i : Fin n) (j : Fin n), ⋃ (h : i ≠ j), {d : ℝ × ℝ | ∃ t : ℝ, d = t • l i j}) = 0 := by
      have h_union_measure_zero : ∀ i j : Fin n, i ≠ j → MeasureTheory.volume {d : ℝ × ℝ | ∃ t : ℝ, d = t • l i j} = 0 := by
        intro i j hij; specialize hl i j hij; simp_all +decide [ Set.setOf_exists ] ;
        rcases eq_or_ne ( l i j |>.1 ) 0 with ha | ha <;> rcases eq_or_ne ( l i j |>.2 ) 0 with hb | hb <;> simp_all +decide [ Prod.ext_iff ];
        · erw [ show ( Set.range fun x : ℝ => x • l i j ) = { x : ℝ × ℝ | x.1 = 0 } from ?_ ];
          · erw [ show { x : ℝ × ℝ | x.1 = 0 } = ( { 0 } ×ˢ Set.univ ) by ext ; aesop, MeasureTheory.Measure.prod_prod ] ; norm_num;
          · ext ⟨x, y⟩; simp [ha, hb];
            exact ⟨ fun ⟨ t, ht ⟩ => by simpa [ ha ] using congr_arg Prod.fst ht.symm, fun hx => ⟨ y / ( l i j |>.2 ), by ext <;> simp +decide [ hx, ha, hb, mul_div_cancel₀ ] ⟩ ⟩;
        · erw [ show ( Set.range fun x : ℝ => x • l i j ) = { x : ℝ × ℝ | x.2 = 0 } from ?_ ];
          · erw [ show { x : ℝ × ℝ | x.2 = 0 } = ( Set.univ : Set ℝ ) ×ˢ { 0 } by ext ; aesop, MeasureTheory.Measure.prod_prod ] ; norm_num;
          · ext ⟨ x, y ⟩ ; simp +decide [ ha, hb, Prod.ext_iff ] ;
            exact ⟨ fun h => h.2.symm, fun h => ⟨ ⟨ x / ( l i j |>.1 ), div_mul_cancel₀ _ ha ⟩, h.symm ⟩ ⟩;
        · erw [ show ( Set.range fun x : ℝ => x • l i j ) = ( ℝ ∙ l i j ) by ext; simp +decide [ Submodule.mem_span_singleton ] ] ; erw [ show ( ℝ ∙ l i j : Set ( ℝ × ℝ ) ) = ( Set.range fun x : ℝ => x • l i j ) by ext; simp +decide [ Submodule.mem_span_singleton ] ] ; erw [ MeasureTheory.Measure.prod_apply ] ; ring_nf ;
          · simp +decide [ Set.preimage, ha, hb ];
            rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_zero ];
            filter_upwards [ ] with x ; simp +decide [ Prod.ext_iff, ha, hb ];
            exact MeasureTheory.measure_mono_null ( fun y hy => by obtain ⟨ z, hz₁, hz₂ ⟩ := hy; exact show y = x * ( l i j |>.2 ) / ( l i j |>.1 ) by rw [ eq_div_iff ha ] ; cases lt_or_gt_of_ne ha <;> cases lt_or_gt_of_ne hb <;> nlinarith ) ( MeasureTheory.measure_singleton _ );
          · exact ( by rw [ show ( Set.range fun x : ℝ => x • l i j ) = { x : ℝ × ℝ | x.1 / ( l i j |>.1 ) = x.2 / ( l i j |>.2 ) } from by ext ⟨ x, y ⟩ ; simp +decide [ ha, hb, div_eq_iff, Prod.ext_iff ] ; constructor <;> intros <;> aesop ] ; exact measurableSet_eq_fun ( measurable_fst.div_const _ ) ( measurable_snd.div_const _ ) );
      exact MeasureTheory.measure_iUnion_null fun i => MeasureTheory.measure_iUnion_null fun j => MeasureTheory.measure_iUnion_null fun hij => h_union_measure_zero i j hij;
    -- Since the union of these lines has measure zero, there exists a direction $d$ not in this union.
    obtain ⟨d, hd⟩ : ∃ d : ℝ × ℝ, d ≠ (0, 0) ∧ d ∉ ⋃ (i : Fin n) (j : Fin n), ⋃ (h : i ≠ j), {d : ℝ × ℝ | ∃ t : ℝ, d = t • l i j} := by
      have h_exists_d : ¬(MeasureTheory.volume (Set.univ \ {d : ℝ × ℝ | d = (0, 0)})) = 0 := by
        rw [ MeasureTheory.measure_diff_null ] <;> norm_num;
      contrapose! h_exists_d;
      exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) h_union_measure_zero;
    refine' h_contra ⟨ d, hd.1, fun i j hij => _ ⟩;
    simp_all +decide [ sub_eq_iff_eq_add ];
    exact fun h => hd.2 i j hij ( Classical.choose ( hl' i j hij d.1 d.2 |>.1 ( by linarith ) ) ) ( Classical.choose_spec ( hl' i j hij d.1 d.2 |>.1 ( by linarith ) ) );
  -- Order vertices by `d`-projection.
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin n ≃ Fin n, ∀ i j : Fin n, i < j → d.1 * (C.pts (σ i)).1 + d.2 * (C.pts (σ i)).2 < d.1 * (C.pts (σ j)).1 + d.2 * (C.pts (σ j)).2 := by
    -- Since $d$ is not perpendicular to any edge, the projections of the points onto $d$ are distinct.
    have h_distinct_projections : Function.Injective (fun i : Fin n => d.1 * (C.pts i).1 + d.2 * (C.pts i).2) := by
      exact fun i j hij => Classical.not_not.1 fun hij' => by cases hd.2 i j hij' <;> linarith;
    -- Since the projections are distinct, we can order them.
    have h_ordered_projections : ∃ (p : Fin n → ℝ), (∀ i, p i ∈ Finset.image (fun i : Fin n => d.1 * (C.pts i).1 + d.2 * (C.pts i).2) Finset.univ) ∧ StrictMono p := by
      exact ⟨ fun i => Finset.orderEmbOfFin _ ( by simpa [ Finset.card_image_of_injective _ h_distinct_projections ] ) i, fun i => Finset.orderEmbOfFin_mem _ ( by simpa [ Finset.card_image_of_injective _ h_distinct_projections ] ) _, by simp +decide [ StrictMono ] ⟩;
    obtain ⟨ p, hp₁, hp₂ ⟩ := h_ordered_projections; choose f hf using fun i => Finset.mem_image.mp ( hp₁ i ) ; use Equiv.ofBijective f ( Finite.injective_iff_bijective.mp <| fun i j hij => hp₂.injective <| by have := hf i; have := hf j; aesop ) ; aesop;
  -- Show that each vertex has at most 3 earlier unit-distance neighbors.
  have h_bound : ∀ i : Fin n, (Finset.univ.filter (fun j : Fin n => eucDist (C.pts (σ j)) (C.pts (σ i)) = 1 ∧ j < i)).card ≤ 3 := by
    intro i;
    -- The set of earlier neighbors of σ i is contained in an open half-plane determined by d.
    have h_half_plane : ∀ j : Fin n, eucDist (C.pts (σ j)) (C.pts (σ i)) = 1 ∧ j < i → d.1 * ((C.pts (σ j)).1 - (C.pts (σ i)).1) + d.2 * ((C.pts (σ j)).2 - (C.pts (σ i)).2) < 0 := by
      exact fun j hj => by linarith [ hσ _ _ hj.2 ] ;
    have := @at_most_three_in_open_semicircle;
    contrapose! this;
    obtain ⟨ s, hs ⟩ := Finset.exists_subset_card_eq this;
    refine' ⟨ s.card, fun j => C.pts ( σ ( s.orderEmbOfFin rfl j ) ), C.pts ( σ i ), ( -d.1, -d.2 ), _, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact fun h => by rintro h'; exact hd.1 <| Prod.mk_inj.mpr ⟨ h, h' ⟩ ;
    · intro i j hij; have := C.sep ( σ ( s.orderEmbOfFin rfl i ) ) ( σ ( s.orderEmbOfFin rfl j ) ) ; simp_all +decide [ eucDist ] ;
    · intro j; linarith [ h_half_plane ( s.orderEmbOfFin rfl j ) ( hs.1 ( Finset.orderEmbOfFin_mem _ _ _ ) |>.1 ) ( hs.1 ( Finset.orderEmbOfFin_mem _ _ _ ) |>.2 ) ] ;
  -- Apply greedy coloring with k = 3 and the ordering σ, getting a proper 4-coloring.
  obtain ⟨c, hc⟩ : ∃ c : Fin n → Fin 4, ∀ i j : Fin n, eucDist (C.pts (σ i)) (C.pts (σ j)) = 1 → c i ≠ c j := by
    have := greedy_coloring n 3 (fun i j => eucDist (C.pts (σ i)) (C.pts (σ j)) = 1) (by
    exact fun i j hij => by simpa only [ eucDist_comm ] using hij;) (by
    simp +decide [ eucDist_self ]) (by
    simp_all +decide [ eucDist_comm ]);
    exact this;
  -- Apply exists_large_color_class with k = 4, getting a color class of size ≥ n/4.
  obtain ⟨j, hj⟩ : ∃ j : Fin 4, n ≤ 4 * (Finset.univ.filter (fun i => c i = j)).card := by
    convert exists_large_color_class n 4 ( by decide ) c using 1;
  use Finset.image σ (Finset.univ.filter (fun i => c i = j));
  simp_all +decide [ Finset.card_image_of_injective _ σ.injective ];
  grind +locals

end
