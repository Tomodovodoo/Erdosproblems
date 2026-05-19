# Pollack 1985: Lamport-style Lean proof plan

Source: `../Proof_Files/Po85.pdf`

Paper: R. Pollack, "Increasing the Minimum Distance of a Set of Points",
Journal of Combinatorial Theory, Series A 40, 450 (1985).

Current Lean anchor:
`ErdosProblems1066/UnitDistanceBounds.lean` proves the target theorem as
`lower_bound_quarter`. The proof uses Pach's no-four-color-theorem route
mentioned in Pollack's Remark 2, not Pollack's literal planarity plus
four-color-theorem route.

Verification note:
Current-status note, 2026-05-19: the project already verifies the `1 / 4`
lower bound through the semicircle/greedy-coloring route.  The
planarity-plus-four-color material below is source-faithful historical roadmap
work only.  Current full-root build certification for the whole checkout is
tracked in `../TASK.md`.

## 0. Target theorem

**Theorem P0 (Pollack lower bound in the project setting).**

For every finite planar Euclidean configuration with minimum pairwise distance
at least `1`, there is a subset of at least one quarter of the labels whose
pairwise distances are all different from `1`.

Lean target already proved:

```lean
theorem lower_bound_quarter (n : ℕ) (C : UDConfig n) :
    ∃ s : Finset (Fin n), C.IsIndep s ∧ 4 * s.card ≥ n
```

Optional source-specific wrapper, if a named Pollack theorem is wanted later:

```lean
theorem pollack_lower_bound_quarter (n : ℕ) (C : UDConfig n) :
    ∃ s : Finset (Fin n), C.IsIndep s ∧ 4 * s.card ≥ n := by
  exact lower_bound_quarter n C
```

## 1. Formal setting

**Assumption A1 (configuration).**

```lean
C : UDConfig n
```

Project definition:

```lean
structure UDConfig (n : ℕ) where
  pts : Fin n → ℝ × ℝ
  sep : ∀ i j : Fin n, i ≠ j → 1 ≤ eucDist (pts i) (pts j)
```

**Assumption A2 (Euclidean distance).**

Project definition:

```lean
def eucDist (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)
```

Available project lemmas:

```lean
eucDist_self : eucDist p p = 0
eucDist_comm : eucDist p q = eucDist q p
eucDist_nonneg : 0 ≤ eucDist p q
eucDist_sq :
  eucDist p q ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2
eucDist_eq_one_iff :
  eucDist p q = 1 ↔ (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = 1
```

**Definition D1 (unit-distance independence).**

Project definition:

```lean
def UDConfig.IsIndep {n : ℕ} (C : UDConfig n)
    (s : Finset (Fin n)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → eucDist (C.pts i) (C.pts j) ≠ 1
```

**Definition D2 (unit-distance adjacency, implicit in current Lean proof).**

```lean
Adj C i j := eucDist (C.pts i) (C.pts j) = 1
```

Proof obligations for adjacency:

```lean
lemma unitAdj_symm :
    Adj C i j → Adj C j i

lemma unitAdj_irrefl :
    ¬ Adj C i i
```

Status: both are discharged inline in `lower_bound_quarter` using
`eucDist_comm` and `eucDist_self`.

## 2. Source facts from Pollack's note

**Source fact S1 (problem definition).**

For `n` points in `E^k` with minimum distance `1`, `f(n,k)` is the largest
integer such that every such configuration contains `f(n,k)` points with
minimum mutual distance `> 1`.

Lean translation obligation:

```lean
def HasStrictlyLargerThanUnitDistance
    (C : UDConfig n) (s : Finset (Fin n)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 < eucDist (C.pts i) (C.pts j)
```

Bridge obligation:

```lean
lemma indep_iff_strict_distance_gt_one
    (C : UDConfig n) (s : Finset (Fin n)) :
    C.IsIndep s ↔ HasStrictlyLargerThanUnitDistance C s
```

Proof obligation:
use `C.sep i j hij : 1 ≤ eucDist ...`; combine with
`eucDist ... ≠ 1` to obtain `1 < eucDist ...`.

Status: not needed by the current theorem because `IsIndep` is stated directly
as `distance ≠ 1`.

**Source fact S2 (Pollack lower-bound proof).**

Pollack proves `f(n,2) > n/4` by:

1. proving the distance-`1` graph is planar;
2. applying the four-color theorem;
3. taking the largest color class.

Lean theorem covered:

```lean
lower_bound_quarter :
  ∀ n (C : UDConfig n),
    ∃ s : Finset (Fin n), C.IsIndep s ∧ 4 * s.card ≥ n
```

Note on inequality form:
the Lean theorem proves the integer form `4 * s.card ≥ n`, equivalent to
`s.card ≥ ceil(n / 4)`. This is stronger and cleaner than writing a real-valued
strict inequality.

**Source fact S3 (Pach remark).**

Pollack records that Pach observed the four-color theorem can be avoided by a
direct induction showing that the unit-distance graph is four-colorable.

Lean theorem implementing this route:

```lean
lower_bound_quarter
```

Internal Lean dependencies:

```lean
no_four_unit_vectors_upper_half
no_four_unit_vectors_in_open_halfplane
at_most_three_in_open_semicircle
greedy_coloring
exists_large_color_class
```

## 3. Pollack route: planarity plus four-color theorem

This section is a future source-faithful formalization plan. It is not needed
for the current Lean proof of P0.

### Claim P1. Label collisions are impossible

Statement:

```lean
lemma pts_injective_of_sep (C : UDConfig n) :
    Function.Injective C.pts
```

Proof:

1. Assume `C.pts i = C.pts j`.
2. If `i ≠ j`, then `C.sep i j` gives `1 ≤ eucDist (C.pts i) (C.pts j)`.
3. Rewrite by `C.pts i = C.pts j` and `eucDist_self`; obtain `1 ≤ 0`.
4. Contradiction.
5. Therefore `i = j`.

Dependencies:
`C.sep`, `eucDist_self`.

### Claim P2. Define the explicit unit-distance graph

Statement:

```lean
def unitDistanceGraph (C : UDConfig n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ eucDist (C.pts i) (C.pts j) = 1
```

Proof obligations:

```lean
lemma unitDistanceGraph_symm :
    (unitDistanceGraph C).Adj i j →
    (unitDistanceGraph C).Adj j i

lemma unitDistanceGraph_loopless :
    ¬ (unitDistanceGraph C).Adj i i
```

Dependencies:
`eucDist_comm`, propositional simplification.

Status:
not present as a named definition; current Lean uses the adjacency predicate
directly.

### Claim P3. Crossing unit diagonals force a short side

Statement:

```lean
lemma crossing_unit_segments_force_short_side
    {a b c d : ℝ × ℝ}
    (hcross : SegmentsCrossInterior a b c d)
    (hab : eucDist a b = 1)
    (hcd : eucDist c d = 1) :
    eucDist a c < 1 ∨ eucDist c b < 1 ∨
      eucDist b d < 1 ∨ eucDist d a < 1
```

Definitions required:

```lean
SegmentsCrossInterior a b c d
ConvexQuadrilateral a c b d
SegmentInteriorMembership o a b
```

Proof:

1. Obtain an intersection point `o` from `hcross`.
2. Obtain strict interior facts:
   `o` lies in the relative interior of segment `ab` and of segment `cd`.
3. Prove strict triangle inequalities:

   ```lean
   eucDist a c < eucDist a o + eucDist o c
   eucDist c b < eucDist c o + eucDist o b
   eucDist b d < eucDist b o + eucDist o d
   eucDist d a < eucDist d o + eucDist o a
   ```

4. Add the four strict inequalities:

   ```lean
   eucDist a c + eucDist c b + eucDist b d + eucDist d a
     < 2 * (eucDist a o + eucDist b o + eucDist c o + eucDist d o)
   ```

5. Use interior collinearity on the two diagonals:

   ```lean
   eucDist a o + eucDist o b = eucDist a b
   eucDist c o + eucDist o d = eucDist c d
   ```

6. Rewrite by `hab` and `hcd` to get perimeter `< 4`.
7. If all four side distances were `≥ 1`, the perimeter would be `≥ 4`.
8. Conclude at least one side is `< 1`.

Dependencies:
strict triangle inequality for non-collinear triples, distance additivity for
points between endpoints, linear arithmetic.

Status:
not present in the current project.

### Claim P4. Unit-distance edges do not cross

Statement:

```lean
lemma unit_edges_no_interior_crossing
    (C : UDConfig n)
    {i j k l : Fin n}
    (hij : (unitDistanceGraph C).Adj i j)
    (hkl : (unitDistanceGraph C).Adj k l)
    (hdisjoint :
      i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l) :
    ¬ SegmentsCrossInterior (C.pts i) (C.pts j) (C.pts k) (C.pts l)
```

Proof:

1. Assume the two segments cross in their interiors.
2. Apply Claim P3 to points `C.pts i`, `C.pts j`, `C.pts k`, `C.pts l`.
3. Each resulting short side is a distance between two distinct labels.
4. Use `C.sep` on that pair to get distance `≥ 1`.
5. Contradict the short-side conclusion `< 1`.

Dependencies:
Claim P3, `C.sep`, edge hypotheses.

Status:
not present in the current project.

### Claim P5. The unit-distance graph is planar

Statement:

```lean
lemma unit_distance_graph_planar (C : UDConfig n) :
    Planar (unitDistanceGraph C)
```

Proof:

1. Embed vertex `i` at point `C.pts i`.
2. Use Claim P1 for injectivity of vertex placement.
3. Draw each edge as its straight segment.
4. Use Claim P4 to show no two disjoint edges cross in their interiors.
5. Shared endpoints are allowed graph-embedding intersections.
6. Conclude planarity.

Dependencies:
Claims P1 and P4, a straight-line graph embedding API, graph planarity API.

Status:
not present in the current project.

### Claim P6. Planar graphs are four-colorable

Statement:

```lean
lemma planar_graph_four_colorable
    (G : SimpleGraph V) (hG : Planar G) :
    ∃ c : V → Fin 4, ∀ u v, G.Adj u v → c u ≠ c v
```

Proof:
use a finite graph four-color theorem.

Dependencies:
finite planar graph four-color theorem.

Status:
not present in the current project.

### Claim P7. A largest color class has at least a quarter of the vertices

Statement:

```lean
lemma largest_color_class_ge_quarter
    (c : Fin n → Fin 4) :
    ∃ j : Fin 4,
      n ≤ 4 * (Finset.univ.filter (fun i => c i = j)).card
```

Proof:

1. The four color classes partition `Fin n`.
2. Sum of the four class cardinalities is `n`.
3. Let `j` be a color with maximal class size.
4. Every class size is at most class `j`.
5. Therefore `n ≤ 4 * card(class j)`.

Dependencies:
finite sums over fibers, max element of a finite nonempty set.

Status:
proved in the current project as the special case
`exists_large_color_class n 4`.

### Claim P8. A proper color class is independent

Statement:

```lean
lemma color_class_is_independent
    (C : UDConfig n)
    (c : Fin n → Fin 4)
    (hc : ∀ i j, (unitDistanceGraph C).Adj i j → c i ≠ c j)
    (j : Fin 4) :
    C.IsIndep (Finset.univ.filter (fun i => c i = j))
```

Proof:

1. Let `i` and `j'` be distinct members of the same color class.
2. Assume `eucDist (C.pts i) (C.pts j') = 1`.
3. Then `(unitDistanceGraph C).Adj i j'`.
4. Proper coloring gives `c i ≠ c j'`.
5. Membership in the same color class gives `c i = c j'`.
6. Contradiction.

Dependencies:
Claim P2, proper coloring.

Status:
proved inline at the end of `lower_bound_quarter`, but for the implicit
adjacency and an ordered copy of the vertices.

### Theorem P9. Pollack route closes P0

Statement:

```lean
theorem pollack_lower_bound_via_planarity (n : ℕ) (C : UDConfig n) :
    ∃ s : Finset (Fin n), C.IsIndep s ∧ 4 * s.card ≥ n
```

Proof:

1. Define `G := unitDistanceGraph C`.
2. Apply Claim P5 to get `Planar G`.
3. Apply Claim P6 to get a proper coloring `c : Fin n → Fin 4`.
4. Apply Claim P7 to get a color `j` with
   `n ≤ 4 * card(class j)`.
5. Let `s := Finset.univ.filter (fun i => c i = j)`.
6. Apply Claim P8 to prove `C.IsIndep s`.
7. Return `s`.

Dependencies:
Claims P5, P6, P7, P8.

Status:
not present. This route is source-faithful but requires substantial geometry,
planarity, and four-color dependencies.

## 4. Pach route: current Lean proof of P0

This is the route already implemented by `lower_bound_quarter`.

### Claim Q1. Four separated unit vectors cannot lie in the open upper half-circle

Existing theorem:

```lean
theorem no_four_unit_vectors_upper_half
    (x y : Fin 4 → ℝ)
    (hunit : ∀ i, x i ^ 2 + y i ^ 2 = 1)
    (hpos : ∀ i, 0 < y i)
    (hdot : ∀ i j, i ≠ j → x i * x j + y i * y j ≤ 1 / 2) :
    False
```

Proof:

1. Define `theta i := Real.arccos (x i)`.
2. From `hunit` and `hpos`, prove `0 < theta i ∧ theta i < Real.pi`.
3. Prove
   `Real.cos (theta i - theta j) = x i * x j + y i * y j`.
4. From `hdot`, prove `|theta i - theta j| ≥ Real.pi / 3` for `i ≠ j`.
5. Order the four angles decreasingly.
6. The three adjacent gaps sum to at least `Real.pi`.
7. The total span is strictly less than `Real.pi` because all angles lie in
   `(0, Real.pi)`.
8. Contradiction.

Dependencies:
`Real.arccos`, trigonometric identities, ordering of four finite values,
linear arithmetic.

Status:
proved.

### Claim Q2. Rotate Q1 to any open half-plane

Existing theorem:

```lean
theorem no_four_unit_vectors_in_open_halfplane
    (u v : Fin 4 → ℝ) (d₁ d₂ : ℝ) (hd : (d₁, d₂) ≠ (0, 0))
    (hunit : ∀ i, u i ^ 2 + v i ^ 2 = 1)
    (hdot : ∀ i j, i ≠ j → u i * u j + v i * v j ≤ 1 / 2)
    (hhalf : ∀ i, d₁ * u i + d₂ * v i > 0) :
    False
```

Proof:

1. Let `N := sqrt (d₁^2 + d₂^2)`.
2. Prove `0 < N` from `hd`.
3. Define rotated coordinates
   `x' i := (d₂ * u i - d₁ * v i) / N`,
   `y' i := (d₁ * u i + d₂ * v i) / N`.
4. Prove each `(x' i, y' i)` is a unit vector.
5. Prove `0 < y' i` from `hhalf`.
6. Prove dot products are preserved by rotation.
7. Apply Claim Q1.

Dependencies:
algebra of rotations, `Real.sqrt_pos`, field simplification.

Status:
proved.

### Claim Q3. At most three separated unit-circle points lie in an open semicircle

Existing theorem:

```lean
theorem at_most_three_in_open_semicircle
    (pts : Fin m → ℝ × ℝ) (center : ℝ × ℝ) (d : ℝ × ℝ)
    (hd : d ≠ (0, 0))
    (hon_circle : ∀ i, eucDist (pts i) center = 1)
    (hsep : ∀ i j, i ≠ j → 1 ≤ eucDist (pts i) (pts j))
    (hin_half : ∀ i,
      d.1 * (pts i).1 + d.2 * (pts i).2 >
        d.1 * center.1 + d.2 * center.2) :
    m ≤ 3
```

Proof:

1. Assume `4 ≤ m`.
2. Select four points from `Fin m`.
3. Translate them by subtracting `center`.
4. Use `hon_circle` to prove the translated vectors have squared norm `1`.
5. Use `hsep` and unit norm equations to prove dot products `≤ 1/2`.
6. Use `hin_half` to prove all translated vectors lie in the open half-plane
   with normal `d`.
7. Apply Claim Q2.
8. Contradiction; therefore `m ≤ 3`.

Dependencies:
Claim Q2, `eucDist_eq_one_iff`, `eucDist_sq`, finite subset extraction.

Status:
proved.

### Claim Q4. A generic direction exists

Statement implemented inline:

```lean
lemma exists_generic_direction (C : UDConfig n) :
    ∃ d : ℝ × ℝ,
      d ≠ (0, 0) ∧
      ∀ i j : Fin n, i ≠ j →
        projection d (C.pts i) > projection d (C.pts j) ∨
        projection d (C.pts i) < projection d (C.pts j)
```

where

```lean
projection d p := d.1 * p.1 + d.2 * p.2
```

Proof:

1. For each `i ≠ j`, define the bad set of directions perpendicular to
   `C.pts i - C.pts j`.
2. Prove each bad set is a line through the origin.
3. Prove each such line has Lebesgue measure zero.
4. Prove the finite union of all bad lines has measure zero.
5. Prove the plane minus the origin is not measure zero.
6. Choose `d` outside the finite union and outside the origin.
7. For every `i ≠ j`, projection equality would put `d` in the bad line.
8. Therefore projections are unequal; linear order on `ℝ` gives `<` or `>`.

Dependencies:
measure zero of affine lines through the origin, finite union of null sets,
classical choice.

Status:
proved inline in `lower_bound_quarter`.

### Claim Q5. Vertices can be ordered by increasing projection

Statement implemented inline:

```lean
lemma exists_projection_order
    (C : UDConfig n) (d : ℝ × ℝ)
    (hd : ∀ i j : Fin n, i ≠ j →
      projection d (C.pts i) > projection d (C.pts j) ∨
      projection d (C.pts i) < projection d (C.pts j)) :
    ∃ σ : Fin n ≃ Fin n,
      ∀ i j : Fin n, i < j →
        projection d (C.pts (σ i)) <
        projection d (C.pts (σ j))
```

Proof:

1. Use `hd` to prove the projection map is injective.
2. Use `Finset.orderEmbOfFin` on the image of all projections.
3. Pull each ordered projection value back to its unique label.
4. Assemble the labels into an equivalence `σ`.
5. Prove the strict monotonicity property.

Dependencies:
finite ordering of a finite set of real numbers, injectivity of projection.

Status:
proved inline in `lower_bound_quarter`.

### Claim Q6. Each vertex has at most three earlier unit-neighbors

Statement implemented inline:

```lean
lemma predecessor_unit_neighbor_bound
    (C : UDConfig n) (d : ℝ × ℝ) (σ : Fin n ≃ Fin n)
    (hσ : ∀ i j : Fin n, i < j →
      projection d (C.pts (σ i)) <
      projection d (C.pts (σ j))) :
    ∀ i : Fin n,
      (Finset.univ.filter (fun j : Fin n =>
        eucDist (C.pts (σ j)) (C.pts (σ i)) = 1 ∧ j < i)).card ≤ 3
```

Proof:

1. Fix `i`.
2. Let `S` be the finite set of earlier unit-neighbors of `σ i`.
3. Every point in `S` lies on the unit circle centered at `C.pts (σ i)`.
4. Since `j < i`, `hσ` gives
   `projection d (C.pts (σ j)) < projection d (C.pts (σ i))`.
5. Therefore points in `S` lie in the open half-plane with normal `-d`.
6. The separation condition for `C` gives pairwise distances `≥ 1` inside `S`.
7. Apply Claim Q3 to `S`.
8. Conclude `S.card ≤ 3`.

Dependencies:
Claim Q3, `C.sep`, ordered projection property.

Status:
proved inline in `lower_bound_quarter`.

### Claim Q7. Greedy coloring from predecessor bound

Existing theorem:

```lean
theorem greedy_coloring (n : ℕ) (k : ℕ)
    (adj : Fin n → Fin n → Prop)
    (hsymm : ∀ i j, adj i j → adj j i)
    (hirr : ∀ i, ¬ adj i i)
    (hbd : ∀ i : Fin n,
      (Finset.univ.filter (fun j : Fin n =>
        adj i j ∧ (j : ℕ) < (i : ℕ))).card ≤ k) :
    ∃ c : Fin n → Fin (k + 1),
      ∀ i j, adj i j → c i ≠ c j
```

Proof:

1. Induct on `n`.
2. Color the first `n` vertices by induction.
3. The last vertex has at most `k` colored neighbors.
4. At most `k` colors are forbidden.
5. Choose a color in `Fin (k + 1)` not used by those neighbors.
6. Extend the coloring with `Fin.snoc`.
7. Check edge cases where one or both endpoints are the last vertex.

Dependencies:
finite image cardinality, pigeonhole on `Fin (k+1)`, induction on `Fin`.

Status:
proved.

### Claim Q8. A largest color class has size at least one quarter

Existing theorem:

```lean
theorem exists_large_color_class (n : ℕ) (k : ℕ) (hk : 0 < k)
    (c : Fin n → Fin k) :
    ∃ j : Fin k,
      n ≤ k * (Finset.univ.filter (fun i => c i = j)).card
```

Proof:

1. Express `n` as the sum of the cardinalities of the fibers of `c`.
2. Choose a fiber of maximum cardinality.
3. Bound each fiber cardinality by the maximum.
4. Sum the four inequalities.
5. Specialize to `k = 4`.

Dependencies:
`sum_fiberwise`, finite maximum of cardinalities.

Status:
proved.

### Claim Q9. Pull back the largest color class to the original labels

Statement implemented inline:

```lean
lemma ordered_color_class_independent
    (C : UDConfig n) (σ : Fin n ≃ Fin n)
    (c : Fin n → Fin 4)
    (hc : ∀ i j,
      eucDist (C.pts (σ i)) (C.pts (σ j)) = 1 → c i ≠ c j)
    (color : Fin 4) :
    C.IsIndep (Finset.image σ
      (Finset.univ.filter (fun i => c i = color)))
```

Proof:

1. Let original labels `a` and `b` lie in the image color class.
2. Obtain preimages `i` and `j` with `a = σ i`, `b = σ j`.
3. Membership gives `c i = color` and `c j = color`.
4. If `eucDist (C.pts a) (C.pts b) = 1`, rewrite by the preimage equalities.
5. Apply `hc i j` to get `c i ≠ c j`.
6. Contradiction.

Cardinality obligation:

```lean
(Finset.image σ S).card = S.card
```

Proof:
use `Finset.card_image_of_injective _ σ.injective`.

Status:
proved inline in `lower_bound_quarter`.

### Theorem Q10. Current Lean proof closes P0

Existing theorem:

```lean
theorem lower_bound_quarter (n : ℕ) (C : UDConfig n) :
    ∃ s : Finset (Fin n), C.IsIndep s ∧ 4 * s.card ≥ n
```

Proof:

1. Apply Claim Q4 to choose a generic direction `d`.
2. Apply Claim Q5 to choose an ordering equivalence `σ`.
3. Apply Claim Q6 to get predecessor unit-neighbor bound `≤ 3`.
4. Apply Claim Q7 with `k = 3` to get a proper coloring
   `c : Fin n → Fin 4`.
5. Apply Claim Q8 with `k = 4` to choose a largest color class.
6. Let
   `s := Finset.image σ (Finset.univ.filter (fun i => c i = color))`.
7. Apply Claim Q9 to prove `C.IsIndep s`.
8. Apply the cardinality equality from Claim Q9 and Claim Q8 to prove
   `4 * s.card ≥ n`.
9. Return `s`.

Dependencies:
Claims Q4 through Q9.

Status:
proved.

## 5. Dependency table

| ID | Future Lean object | Needed for | Current status |
| --- | --- | --- | --- |
| P1 | `pts_injective_of_sep` | Pollack planarity route | Not named; easy |
| P2 | `unitDistanceGraph` | Pollack planarity route | Not named |
| P3 | `crossing_unit_segments_force_short_side` | Pollack planarity route | Missing |
| P4 | `unit_edges_no_interior_crossing` | Pollack planarity route | Missing |
| P5 | `unit_distance_graph_planar` | Pollack planarity route | Missing |
| P6 | `planar_graph_four_colorable` | Pollack planarity route | Missing |
| P7 | `largest_color_class_ge_quarter` | Both routes | Proved as `exists_large_color_class` |
| P8 | `color_class_is_independent` | Pollack planarity route | Inline analogue proved |
| Q1 | `no_four_unit_vectors_upper_half` | Pach route | Proved |
| Q2 | `no_four_unit_vectors_in_open_halfplane` | Pach route | Proved |
| Q3 | `at_most_three_in_open_semicircle` | Pach route | Proved |
| Q4 | `exists_generic_direction` | Pach route | Proved inline |
| Q5 | `exists_projection_order` | Pach route | Proved inline |
| Q6 | `predecessor_unit_neighbor_bound` | Pach route | Proved inline |
| Q7 | `greedy_coloring` | Pach route | Proved |
| Q8 | `exists_large_color_class` | Pach route | Proved |
| Q9 | `ordered_color_class_independent` | Pach route | Proved inline |
| Q10 | `lower_bound_quarter` | Target theorem P0 | Proved |

## 6. Lean transcription notes

1. Do not formalize Pollack's literal route unless the goal is a
   source-faithful proof of planarity plus four-coloring. The theorem P0 is
   already proved by Q10.
2. If source naming is required, add only the wrapper
   `pollack_lower_bound_quarter := lower_bound_quarter`.
3. The current proof's weakest maintenance points are Q4 through Q6 because
   they are long inline subproofs. A cleanup pass should extract them as named
   lemmas before changing the proof.
4. The ordinary `lake` and `lean` commands on this machine resolve first to
   `C:\Users\Tom\bin`, whose Lean libdir is invalid. Use the elan-qualified
   command:

   ```text
   elan run leanprover/lean4:v4.28.0 lake build
   ```

5. The theorem P0 has no remaining Lean blocker. The remaining blockers only
   concern Pollack's literal proof route:
   segment-crossing geometry, straight-line planarity, and a finite planar
   four-color theorem interface.
