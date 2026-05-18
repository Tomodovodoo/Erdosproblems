import ErdosProblems1066.Swanepoel.LocalExclusions

set_option autoImplicit false

/-!
# Geometric common-neighbor exclusions

This module proves the Euclidean fact behind the local `K_{2,3}` exclusion:
in a separated unit-distance configuration, two distinct vertices have at most
two common unit-distance neighbors.  Algebraically, the common neighbors are
the intersection of two unit circles.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CommonNeighborGeometry

open GraphBridge
open LocalConfigurations
open LocalExclusions

noncomputable section

abbrev Point : Type := Real × Real

def vsub (p q : Point) : Point :=
  (p.1 - q.1, p.2 - q.2)

def vadd (p q : Point) : Point :=
  (p.1 + q.1, p.2 + q.2)

def dot (p q : Point) : Real :=
  p.1 * q.1 + p.2 * q.2

def normSq (p : Point) : Real :=
  dot p p

@[simp]
lemma vsub_fst (p q : Point) : (vsub p q).1 = p.1 - q.1 :=
  rfl

@[simp]
lemma vsub_snd (p q : Point) : (vsub p q).2 = p.2 - q.2 :=
  rfl

@[simp]
lemma vadd_fst (p q : Point) : (vadd p q).1 = p.1 + q.1 :=
  rfl

@[simp]
lemma vadd_snd (p q : Point) : (vadd p q).2 = p.2 + q.2 :=
  rfl

lemma dot_comm (p q : Point) : dot p q = dot q p := by
  unfold dot
  ring

lemma normSq_eq (p : Point) : normSq p = p.1 ^ 2 + p.2 ^ 2 := by
  unfold normSq dot
  ring

lemma normSq_pos_of_ne_zero {p : Point} (hp : p ≠ (0, 0)) :
    0 < normSq p := by
  rw [normSq_eq]
  have hnonneg : 0 <= p.1 ^ 2 + p.2 ^ 2 := by positivity
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  apply hp
  ext <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]

lemma dot_rel_base_eq_half_normSq_base_of_common_unit
    {A B X : Point}
    (hXA : eucDist X A = 1) (hXB : eucDist X B = 1) :
    dot (vsub X A) (vsub B A) = normSq (vsub B A) / 2 := by
  rw [eucDist_eq_one_iff] at hXA hXB
  simp [dot, normSq, vsub]
  ring_nf at hXA hXB ⊢
  nlinarith

lemma normSq_rel_eq_one_of_unit {A X : Point}
    (hXA : eucDist X A = 1) :
    normSq (vsub X A) = 1 := by
  rw [eucDist_eq_one_iff] at hXA
  simp [normSq, dot, vsub]
  ring_nf at hXA ⊢
  exact hXA

lemma det_ne_zero_of_dot_zero_nonzero {d e : Point}
    (hd : d ≠ (0, 0)) (he : e ≠ (0, 0))
    (horth : dot e d = 0) :
    d.1 * e.2 - d.2 * e.1 ≠ 0 := by
  intro hdet
  have hidentity :
      (d.1 ^ 2 + d.2 ^ 2) * (e.1 ^ 2 + e.2 ^ 2) =
        (d.1 * e.1 + d.2 * e.2) ^ 2 +
          (d.1 * e.2 - d.2 * e.1) ^ 2 := by
    ring
  have hdpos : 0 < d.1 ^ 2 + d.2 ^ 2 := by
    simpa [normSq_eq] using normSq_pos_of_ne_zero hd
  have hepos : 0 < e.1 ^ 2 + e.2 ^ 2 := by
    simpa [normSq_eq] using normSq_pos_of_ne_zero he
  have hdot : d.1 * e.1 + d.2 * e.2 = 0 := by
    simpa [dot, mul_comm, mul_left_comm, mul_assoc] using horth
  nlinarith

lemma eq_zero_of_dot_eq_zero_of_dot_eq_zero {r d e : Point}
    (hdet : d.1 * e.2 - d.2 * e.1 ≠ 0)
    (hrd : dot r d = 0) (hre : dot r e = 0) :
    r = (0, 0) := by
  have hrd' : r.1 * d.1 + r.2 * d.2 = 0 := by
    simpa [dot] using hrd
  have hre' : r.1 * e.1 + r.2 * e.2 = 0 := by
    simpa [dot] using hre
  have hx0 : r.1 * (d.1 * e.2 - d.2 * e.1) = 0 := by
    calc
      r.1 * (d.1 * e.2 - d.2 * e.1) =
          (r.1 * d.1 + r.2 * d.2) * e.2 -
            (r.1 * e.1 + r.2 * e.2) * d.2 := by
        ring
      _ = 0 := by
        rw [hrd', hre']
        ring
  have hy0 : r.2 * (d.1 * e.2 - d.2 * e.1) = 0 := by
    calc
      r.2 * (d.1 * e.2 - d.2 * e.1) =
          (r.1 * e.1 + r.2 * e.2) * d.1 -
            (r.1 * d.1 + r.2 * d.2) * e.1 := by
        ring
      _ = 0 := by
        rw [hrd', hre']
        ring
  have hx : r.1 = 0 := by
    rcases mul_eq_zero.mp hx0 with h | h
    · exact h
    · exact False.elim (hdet h)
  have hy : r.2 = 0 := by
    rcases mul_eq_zero.mp hy0 with h | h
    · exact h
    · exact False.elim (hdet h)
  exact Prod.ext hx hy

lemma vsub_ne_zero_of_ne {u v : Point} (huv : u ≠ v) :
    vsub u v ≠ (0, 0) := by
  intro hzero
  apply huv
  have hx : u.1 - v.1 = 0 := by
    simpa [vsub] using congrArg Prod.fst hzero
  have hy : u.2 - v.2 = 0 := by
    simpa [vsub] using congrArg Prod.snd hzero
  ext <;> linarith

lemma vadd_eq_of_two_common_unit_rel {d u v : Point}
    (hd : d ≠ (0, 0))
    (hu_norm : normSq u = 1) (hv_norm : normSq v = 1)
    (hu_dot : dot u d = normSq d / 2)
    (hv_dot : dot v d = normSq d / 2)
    (huv : u ≠ v) :
    vadd u v = d := by
  let e : Point := vsub u v
  let s : Point := vadd u v
  let r : Point := vsub s d
  have he : e ≠ (0, 0) := by
    exact vsub_ne_zero_of_ne huv
  have hed : dot e d = 0 := by
    have hu_dot' : u.1 * d.1 + u.2 * d.2 =
        (d.1 * d.1 + d.2 * d.2) / 2 := by
      simpa [dot, normSq] using hu_dot
    have hv_dot' : v.1 * d.1 + v.2 * d.2 =
        (d.1 * d.1 + d.2 * d.2) / 2 := by
      simpa [dot, normSq] using hv_dot
    unfold e vsub dot
    ring_nf
    nlinarith
  have hds : dot d e = 0 := by
    simpa [dot_comm] using hed
  have hes : dot e s = 0 := by
    have hu : u.1 * u.1 + u.2 * u.2 = 1 := by
      simpa [normSq, dot] using hu_norm
    have hv : v.1 * v.1 + v.2 * v.2 = 1 := by
      simpa [normSq, dot] using hv_norm
    unfold e s vsub vadd dot
    ring_nf
    nlinarith
  have hse : dot s e = 0 := by
    simpa [dot_comm] using hes
  have hsd : dot s d = normSq d := by
    have hu_dot' : u.1 * d.1 + u.2 * d.2 =
        (d.1 * d.1 + d.2 * d.2) / 2 := by
      simpa [dot, normSq] using hu_dot
    have hv_dot' : v.1 * d.1 + v.2 * d.2 =
        (d.1 * d.1 + d.2 * d.2) / 2 := by
      simpa [dot, normSq] using hv_dot
    simp [s, vadd, dot, normSq]
    ring_nf
    nlinarith
  have hrd : dot r d = 0 := by
    have hsd' : s.1 * d.1 + s.2 * d.2 = d.1 * d.1 + d.2 * d.2 := by
      simpa [dot, normSq] using hsd
    unfold r vsub dot
    ring_nf
    nlinarith
  have hre : dot r e = 0 := by
    have hse' : s.1 * e.1 + s.2 * e.2 = 0 := by
      simpa [dot] using hse
    have hds' : d.1 * e.1 + d.2 * e.2 = 0 := by
      simpa [dot] using hds
    unfold r vsub dot
    ring_nf
    nlinarith
  have hdet : d.1 * e.2 - d.2 * e.1 ≠ 0 :=
    det_ne_zero_of_dot_zero_nonzero hd he hed
  have hr : r = (0, 0) :=
    eq_zero_of_dot_eq_zero_of_dot_eq_zero hdet hrd hre
  have hs_eq : s = d := by
    have hx : s.1 - d.1 = 0 := by
      simpa [r, vsub] using congrArg Prod.fst hr
    have hy : s.2 - d.2 = 0 := by
      simpa [r, vsub] using congrArg Prod.snd hr
    ext <;> linarith
  exact hs_eq

lemma vadd_left_cancel {a b c : Point}
    (h : vadd a b = vadd a c) :
    b = c := by
  have hx : a.1 + b.1 = a.1 + c.1 := by
    simpa [vadd] using congrArg Prod.fst h
  have hy : a.2 + b.2 = a.2 + c.2 := by
    simpa [vadd] using congrArg Prod.snd h
  ext <;> linarith

lemma rel_ne_of_vertex_ne {n : Nat} (C : _root_.UDConfig n)
    {a x y : Fin n} (hxy : x ≠ y) :
    vsub (C.pts x) (C.pts a) ≠ vsub (C.pts y) (C.pts a) := by
  intro hrel
  have hpts : C.pts x = C.pts y := by
    have hx : (C.pts x).1 - (C.pts a).1 =
        (C.pts y).1 - (C.pts a).1 := by
      simpa [vsub] using congrArg Prod.fst hrel
    have hy : (C.pts x).2 - (C.pts a).2 =
        (C.pts y).2 - (C.pts a).2 := by
      simpa [vsub] using congrArg Prod.snd hrel
    ext <;> linarith
  have hsep := C.sep x y hxy
  have hzero : eucDist (C.pts x) (C.pts y) = 0 := by
    rw [hpts, eucDist_self]
  linarith

lemma base_vsub_ne_zero_of_vertex_ne {n : Nat} (C : _root_.UDConfig n)
    {a b : Fin n} (hab : a ≠ b) :
    vsub (C.pts b) (C.pts a) ≠ (0, 0) := by
  intro hzero
  have hpts : C.pts b = C.pts a := by
    have hx : (C.pts b).1 - (C.pts a).1 = 0 := by
      simpa [vsub] using congrArg Prod.fst hzero
    have hy : (C.pts b).2 - (C.pts a).2 = 0 := by
      simpa [vsub] using congrArg Prod.snd hzero
    ext <;> linarith
  have hsep := C.sep a b hab
  have hzero_dist : eucDist (C.pts a) (C.pts b) = 0 := by
    rw [hpts, eucDist_self]
  linarith

lemma unitDistance_commonNeighbor_vertex_data {n : Nat}
    (C : _root_.UDConfig n) {a b x : Fin n}
    (hx : (unitDistanceLocalGraph C).CommonNeighbor a b x) :
    eucDist (C.pts x) (C.pts a) = 1 /\
      eucDist (C.pts x) (C.pts b) = 1 := by
  simpa [unitDistanceLocalGraph_adj] using hx

/-- Two distinct vertices in a separated unit-distance configuration cannot
have three distinct common unit-distance neighbors. -/
theorem no_three_commonNeighbors_unitDistanceLocalGraph {n : Nat}
    (C : _root_.UDConfig n) {a b x y z : Fin n}
    (hab : a ≠ b) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : (unitDistanceLocalGraph C).CommonNeighbor a b x)
    (hy : (unitDistanceLocalGraph C).CommonNeighbor a b y)
    (hz : (unitDistanceLocalGraph C).CommonNeighbor a b z) :
    False := by
  let A : Point := C.pts a
  let B : Point := C.pts b
  let d : Point := vsub B A
  let ux : Point := vsub (C.pts x) A
  let uy : Point := vsub (C.pts y) A
  let uz : Point := vsub (C.pts z) A
  have hd : d ≠ (0, 0) := by
    exact base_vsub_ne_zero_of_vertex_ne C hab
  rcases unitDistance_commonNeighbor_vertex_data C hx with ⟨hxa, hxb⟩
  rcases unitDistance_commonNeighbor_vertex_data C hy with ⟨hya, hyb⟩
  rcases unitDistance_commonNeighbor_vertex_data C hz with ⟨hza, hzb⟩
  have hx_norm : normSq ux = 1 := by
    exact normSq_rel_eq_one_of_unit hxa
  have hy_norm : normSq uy = 1 := by
    exact normSq_rel_eq_one_of_unit hya
  have hz_norm : normSq uz = 1 := by
    exact normSq_rel_eq_one_of_unit hza
  have hx_dot : dot ux d = normSq d / 2 := by
    exact dot_rel_base_eq_half_normSq_base_of_common_unit hxa hxb
  have hy_dot : dot uy d = normSq d / 2 := by
    exact dot_rel_base_eq_half_normSq_base_of_common_unit hya hyb
  have hz_dot : dot uz d = normSq d / 2 := by
    exact dot_rel_base_eq_half_normSq_base_of_common_unit hza hzb
  have huxy : ux ≠ uy := by
    exact rel_ne_of_vertex_ne C (a := a) hxy
  have huxz : ux ≠ uz := by
    exact rel_ne_of_vertex_ne C (a := a) hxz
  have hxy_sum : vadd ux uy = d :=
    vadd_eq_of_two_common_unit_rel hd hx_norm hy_norm hx_dot hy_dot huxy
  have hxz_sum : vadd ux uz = d :=
    vadd_eq_of_two_common_unit_rel hd hx_norm hz_norm hx_dot hz_dot huxz
  have hyz_rel : uy = uz :=
    vadd_left_cancel (hxy_sum.trans hxz_sum.symm)
  have hpts_yz : C.pts y = C.pts z := by
    have hx1 : (C.pts y).1 - (C.pts a).1 =
        (C.pts z).1 - (C.pts a).1 := by
      simpa [uy, uz, A, vsub] using congrArg Prod.fst hyz_rel
    have hx2 : (C.pts y).2 - (C.pts a).2 =
        (C.pts z).2 - (C.pts a).2 := by
      simpa [uy, uz, A, vsub] using congrArg Prod.snd hyz_rel
    ext <;> linarith
  have hsep := C.sep y z hyz
  have hzero : eucDist (C.pts y) (C.pts z) = 0 := by
    rw [hpts_yz, eucDist_self]
  linarith

/-- A direct geometric common-neighbor cap for unit-distance configurations. -/
theorem unitDistance_commonNeighborFinset_card_le_two {n : Nat}
    (C : _root_.UDConfig n) {a b : Fin n} (hab : a ≠ b) :
    (LocalGraph.commonNeighborFinset (unitDistanceLocalGraph C) a b).card <= 2 := by
  classical
  by_contra hle
  have hlt : 2 < (LocalGraph.commonNeighborFinset
      (unitDistanceLocalGraph C) a b).card :=
    Nat.lt_of_not_ge hle
  rcases Finset.two_lt_card.mp hlt with
    ⟨x, hxmem, y, hymem, z, hzmem, hxy, hxz, hyz⟩
  exact no_three_commonNeighbors_unitDistanceLocalGraph C hab hxy hxz hyz
    ((LocalGraph.mem_commonNeighborFinset (unitDistanceLocalGraph C) a b x).1 hxmem)
    ((LocalGraph.mem_commonNeighborFinset (unitDistanceLocalGraph C) a b y).1 hymem)
    ((LocalGraph.mem_commonNeighborFinset (unitDistanceLocalGraph C) a b z).1 hzmem)

/-- The unit-distance local graph of a separated configuration has no labelled
`K_{2,3}` pattern. -/
theorem not_hasK23_unitDistanceLocalGraph {n : Nat} (C : _root_.UDConfig n) :
    Not (HasK23 (unitDistanceLocalGraph C)) := by
  rintro ⟨P⟩
  exact no_three_commonNeighbors_unitDistanceLocalGraph C
    P.left_ne P.right01_ne P.right02_ne P.right12_ne
    P.right0_common P.right1_common P.right2_common

end

end CommonNeighborGeometry
end Swanepoel
end ErdosProblems1066
