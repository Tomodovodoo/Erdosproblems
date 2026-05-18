import ErdosProblems1066.Swanepoel.MinimalCounterexample

/-!
# Induced subconfigurations of `UDConfig`

This module supplies a checked interface for passing from an ambient separated
unit-distance configuration to an induced configuration on a finite set of kept
vertices.  The concrete constructor uses `Finset.orderIsoOfFin`, so the smaller
vertex type is `Fin kept.card`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace InducedSubconfiguration

open MinimalCounterexample

noncomputable section

/-- An induced copy of an ambient `UDConfig` on the vertices listed by `kept`.

The fields deliberately expose the embedding into the ambient configuration and
the exact point equality.  Downstream deletion arguments can therefore obtain
distance preservation and independent-set transfer without making any geometric
assumption beyond the ambient `UDConfig.sep`. -/
structure Induced {n m : Nat} (C : _root_.UDConfig n)
    (kept : Finset (Fin n)) where
  config : _root_.UDConfig m
  embed : Fin m -> Fin n
  embed_injective : Function.Injective embed
  image_univ : ((Finset.univ : Finset (Fin m)).image embed) = kept
  pts_eq : forall i : Fin m, config.pts i = C.pts (embed i)

namespace Induced

variable {n m : Nat} {C : _root_.UDConfig n} {kept : Finset (Fin n)}

@[simp]
lemma pts_eq_apply (I : Induced C kept) (i : Fin m) :
    I.config.pts i = C.pts (I.embed i) :=
  I.pts_eq i

/-- The induced configuration inherits separation from the ambient one. -/
lemma sep_preserved (I : Induced C kept) (i j : Fin m) (hij : i ≠ j) :
    1 <= _root_.eucDist (I.config.pts i) (I.config.pts j) := by
  rw [I.pts_eq i, I.pts_eq j]
  exact C.sep (I.embed i) (I.embed j) (fun h => hij (I.embed_injective h))

/-- Distances in an induced configuration are exactly the ambient distances
between the embedded vertices. -/
lemma dist_eq (I : Induced C kept) (i j : Fin m) :
    _root_.eucDist (I.config.pts i) (I.config.pts j) =
      _root_.eucDist (C.pts (I.embed i)) (C.pts (I.embed j)) := by
  rw [I.pts_eq i, I.pts_eq j]

/-- The induced embedding preserves all distances on every smaller set, in the
form expected by the minimal-counterexample deletion pipeline. -/
lemma preservesDistancesOn (I : Induced C kept) (small : Finset (Fin m)) :
    PreservesDistancesOn I.config C I.embed small := by
  intro i _hi j _hj
  exact (I.dist_eq i j).symm

/-- Push an independent set in the induced configuration to the corresponding
ambient image. -/
lemma image_indep (I : Induced C kept) {s : Finset (Fin m)}
    (hs : I.config.IsIndep s) :
    C.IsIndep (s.image I.embed) := by
  intro x hx y hy hxy hunit
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
  have hij : i ≠ j := by
    intro hij
    exact hxy (by rw [hij])
  exact hs i hi j hj hij ((I.dist_eq i j).trans hunit)

/-- Pull an ambient independent set on an embedded image back to the induced
configuration. -/
lemma preimage_indep_of_image_indep (I : Induced C kept) {s : Finset (Fin m)}
    (hs : C.IsIndep (s.image I.embed)) :
    I.config.IsIndep s := by
  intro i hi j hj hij hunit
  have hi_image : I.embed i ∈ s.image I.embed :=
    Finset.mem_image_of_mem I.embed hi
  have hj_image : I.embed j ∈ s.image I.embed :=
    Finset.mem_image_of_mem I.embed hj
  have hemb_ne : I.embed i ≠ I.embed j := by
    intro h
    exact hij (I.embed_injective h)
  exact hs (I.embed i) hi_image (I.embed j) hj_image hemb_ne
    ((I.dist_eq i j).symm.trans hunit)

/-- Pull back independence from any ambient set containing the embedded smaller
set. -/
lemma preimage_indep_of_subset (I : Induced C kept)
    {s : Finset (Fin m)} {t : Finset (Fin n)}
    (ht : C.IsIndep t)
    (hsub : s.image I.embed ⊆ t) :
    I.config.IsIndep s := by
  refine I.preimage_indep_of_image_indep ?_
  intro x hx y hy hxy hunit
  exact ht x (hsub hx) y (hsub hy) hxy hunit

/-- Independence is equivalent before and after taking the embedded image. -/
lemma image_indep_iff (I : Induced C kept) {s : Finset (Fin m)} :
    C.IsIndep (s.image I.embed) <-> I.config.IsIndep s := by
  constructor
  · exact I.preimage_indep_of_image_indep
  · exact I.image_indep

/-- The embedded vertices are exactly the kept set. -/
lemma mem_kept_iff (I : Induced C kept) (v : Fin n) :
    v ∈ kept <-> Exists fun i : Fin m => I.embed i = v := by
  constructor
  · intro hv
    have hv_image : v ∈ ((Finset.univ : Finset (Fin m)).image I.embed) := by
      simpa [I.image_univ] using hv
    rcases Finset.mem_image.mp hv_image with ⟨i, _hi, h⟩
    exact ⟨i, h⟩
  · rintro ⟨i, rfl⟩
    have hmem : I.embed i ∈ ((Finset.univ : Finset (Fin m)).image I.embed) :=
      Finset.mem_image_of_mem I.embed (Finset.mem_univ i)
    simpa [I.image_univ] using hmem

end Induced

/-- Restrict a `UDConfig` along an injective map whose image is the kept set. -/
def ofEmbedding {n m : Nat} (C : _root_.UDConfig n)
    (kept : Finset (Fin n)) (embed : Fin m -> Fin n)
    (hembed : Function.Injective embed)
    (himage : ((Finset.univ : Finset (Fin m)).image embed) = kept) :
    Induced (m := m) C kept where
  config :=
    { pts := fun i => C.pts (embed i)
      sep := by
        intro i j hij
        exact C.sep (embed i) (embed j) (fun h => hij (hembed h)) }
  embed := embed
  embed_injective := hembed
  image_univ := himage
  pts_eq := fun _ => rfl

/-- The canonical induced subconfiguration on a finite set of kept vertices,
enumerated in the order inherited from `Fin n`. -/
def ofFinset {n : Nat} (C : _root_.UDConfig n) (kept : Finset (Fin n)) :
    Induced (m := kept.card) C kept :=
  ofEmbedding C kept (fun i : Fin kept.card => ((kept.orderIsoOfFin rfl) i : Fin n))
    (by
      intro i j h
      apply (kept.orderIsoOfFin rfl).injective
      exact Subtype.ext h)
    (by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
        exact ((kept.orderIsoOfFin rfl) i).2
      · intro hv
        exact Finset.mem_image.mpr
          ⟨(kept.orderIsoOfFin rfl).symm ⟨v, hv⟩, Finset.mem_univ _, by simp⟩)

@[simp]
lemma ofFinset_config_pts {n : Nat} (C : _root_.UDConfig n)
    (kept : Finset (Fin n)) (i : Fin kept.card) :
    (ofFinset C kept).config.pts i =
      C.pts ((kept.orderIsoOfFin rfl i : kept) : Fin n) :=
  rfl

@[simp]
lemma ofFinset_embed {n : Nat} (C : _root_.UDConfig n)
    (kept : Finset (Fin n)) (i : Fin kept.card) :
    (ofFinset C kept).embed i = ((kept.orderIsoOfFin rfl i : kept) : Fin n) :=
  rfl

end

end InducedSubconfiguration
end Swanepoel
end ErdosProblems1066
