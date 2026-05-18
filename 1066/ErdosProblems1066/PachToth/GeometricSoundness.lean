import ErdosProblems1066.PachToth.IndexedChain

/-!
# Pach--Toth Geometric Edge Soundness

This module is a thin bridge from explicit geometric edge certificates to the
canonical indexed-chain realization interface.  It does not assert that such
certificates exist for the Pach--Toth drawing; it only packages the exact local
and cross-block unit-distance hypotheses needed by `IndexedChainRealization`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeometricSoundness

open Chain
open FiniteGraph
open BlockPartition
open Arithmetic

noncomputable section

/-- The global vertex corresponding to a cyclic block and a local
Pach--Toth vertex under the canonical `BlockPartition` encoding. -/
def globalVertex (k : Nat) (i : Fin k) (v : LocalVertex) : Fin (16 * k) :=
  blockLocalEquiv k (i, v)

/-- Membership in the canonical block selection is exactly membership of the
corresponding encoded global vertex in the original selected set. -/
theorem mem_blockSelection_iff {k : Nat} {s : Finset (Fin (16 * k))}
    {i : Fin k} {v : LocalVertex} :
    v ∈ (blockSelection k s) i ↔ globalVertex k i v ∈ s := by
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨p, hp, hpv⟩
    rcases Finset.mem_filter.mp hp with ⟨hp_indexed, hpi⟩
    rcases Finset.mem_image.mp hp_indexed with ⟨x, hx, hxp⟩
    have hp_eq : p = (i, v) := Prod.ext hpi hpv
    have hx_decode : vertexBlockLocal k x = (i, v) := by
      simpa [hp_eq] using hxp
    have hx_eq : x = globalVertex k i v := by
      calc
        x = blockLocalEquiv k (vertexBlockLocal k x) :=
          ((blockLocalEquiv k).apply_symm_apply x).symm
        _ = globalVertex k i v := by
          simp [globalVertex, hx_decode]
    simpa [hx_eq] using hx
  · intro hv
    unfold blockSelection
    refine Finset.mem_image.mpr ?_
    refine ⟨(i, v), ?_, rfl⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · unfold indexedSelection
      refine Finset.mem_image.mpr ?_
      refine ⟨globalVertex k i v, hv, ?_⟩
      simp [globalVertex, vertexBlockLocal]
    · rfl

/-- Distinct local vertices in encoded blocks give distinct global vertices. -/
theorem globalVertex_ne_of_local_ne {k : Nat} {i j : Fin k}
    {u v : LocalVertex} (huv : u ≠ v) :
    globalVertex k i u ≠ globalVertex k j v := by
  intro h
  have hpairs : (i, u) = (j, v) := (blockLocalEquiv k).injective h
  exact huv (congrArg Prod.snd hpairs)

/-- The finite next-block connector relation never connects a local vertex to
itself. -/
theorem nextConnector_ne {u v : LocalVertex}
    (hconn : CrossBlock.NextConnector u v) : u ≠ v := by
  revert u v
  decide

/-- Explicit geometric soundness for all finite Pach--Toth edges in the
canonical indexed block decomposition. -/
structure ExplicitEdgeSoundness (k : Nat) (hk : 0 < k) where
  config : _root_.UDConfig (16 * k)
  same_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      u ≠ v ->
      adj u v = true ->
      eucDist (config.pts (globalVertex k i u))
        (config.pts (globalVertex k i v)) = 1
  cross_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
      eucDist (config.pts (globalVertex k i u))
        (config.pts (globalVertex k (cyclicSucc hk i) v)) = 1

namespace ExplicitEdgeSoundness

/-- Same-block geometric edge soundness turns every independent global set into
independent finite selections in each canonical block. -/
theorem blocks_independent_of_independent {k : Nat} {hk : 0 < k}
    (G : ExplicitEdgeSoundness k hk) :
    forall s : Finset (Fin (16 * k)), G.config.IsIndep s ->
      BlocksIndependent (blockSelection k s) := by
  intro s hs i u hu v hv huv
  have hgu : globalVertex k i u ∈ s :=
    mem_blockSelection_iff.mp hu
  have hgv : globalVertex k i v ∈ s :=
    mem_blockSelection_iff.mp hv
  by_cases hadj : adj u v = true
  · exact False.elim
      (hs (globalVertex k i u) hgu (globalVertex k i v) hgv
        (globalVertex_ne_of_local_ne huv)
        (G.same_block_edges_unit i u v huv hadj))
  · exact Bool.eq_false_iff.mpr hadj

/-- Cross-block geometric edge soundness turns every independent global set
into cross-independent canonical block selections. -/
theorem cross_independent_of_independent {k : Nat} {hk : 0 < k}
    (G : ExplicitEdgeSoundness k hk) :
    forall s : Finset (Fin (16 * k)), G.config.IsIndep s ->
      CrossBlock.CyclicCrossIndependent hk (blockSelection k s) := by
  intro s hs i u hu v hv hconn
  have hgu : globalVertex k i u ∈ s :=
    mem_blockSelection_iff.mp hu
  have hgv : globalVertex k (cyclicSucc hk i) v ∈ s :=
    mem_blockSelection_iff.mp hv
  exact hs (globalVertex k i u) hgu
    (globalVertex k (cyclicSucc hk i) v) hgv
    (globalVertex_ne_of_local_ne (nextConnector_ne hconn))
    (G.cross_block_edges_unit i u v hconn)

/-- Package explicit edge-soundness hypotheses as an indexed chain
realization. -/
def toIndexedChainRealization {k : Nat} {hk : 0 < k}
    (G : ExplicitEdgeSoundness k hk) :
    IndexedChain.IndexedChainRealization k hk where
  config := G.config
  blocks_independent_of_independent :=
    G.blocks_independent_of_independent
  cross_independent_of_independent :=
    G.cross_independent_of_independent

end ExplicitEdgeSoundness

end

end GeometricSoundness
end PachToth
end ErdosProblems1066
