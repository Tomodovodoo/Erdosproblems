import ErdosProblems1066.PachToth.BlockPartition
import ErdosProblems1066.PachToth.CrossBlock
import ErdosProblems1066.UnitDistanceBounds

/-!
# Pach--Toth Indexed Chain Bridge

This module removes two pieces of bookkeeping from the geometric realization
interface: the global-to-local block split is fixed by `BlockPartition`, and
the cyclic connector rule is derived from the explicit finite connector
relation in `CrossBlock`.

The remaining fields are exactly the geometric soundness obligations: an
independent set in the realized `UDConfig` must restrict to independent local
block selections and must be cross-independent for the intended connector
edges.
-/

namespace ErdosProblems1066
namespace PachToth
namespace IndexedChain

open Chain
open BlockPartition

/-- A `UDConfig (16 * k)` whose canonical indexed block decomposition satisfies
the checked Pach--Toth local and cross-block finite conditions. -/
structure IndexedChainRealization (k : Nat) (hk : 0 < k) where
  config : _root_.UDConfig (16 * k)
  blocks_independent_of_independent :
    forall s : Finset (Fin (16 * k)), config.IsIndep s ->
      BlocksIndependent (blockSelection k s)
  cross_independent_of_independent :
    forall s : Finset (Fin (16 * k)), config.IsIndep s ->
      CrossBlock.CyclicCrossIndependent hk (blockSelection k s)

/-- Every independent set in an indexed Pach--Toth chain realization has at
most `5 * k` vertices. -/
theorem independent_card_le_five_mul {k : Nat} (hk : 0 < k)
    (R : IndexedChainRealization k hk)
    (s : Finset (Fin (16 * k))) (hs : R.config.IsIndep s) :
    s.card <= 5 * k := by
  rw [card_eq_sum_blockSelection k s]
  exact CrossBlock.selected_card_le_five_mul hk (blockSelection k s)
    (R.blocks_independent_of_independent s hs)
    (R.cross_independent_of_independent s hs)

/-- Existence form of the exact-multiple upper bound from an indexed chain
realization. -/
theorem exists_config_with_independent_card_le_five_mul {k : Nat} (hk : 0 < k)
    (R : IndexedChainRealization k hk) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k := by
  exact Exists.intro R.config (independent_card_le_five_mul hk R)

/-- Ratio form of the exact-multiple upper bound from an indexed chain
realization. -/
theorem exists_config_with_independent_card_le_floor_ratio {k : Nat} (hk : 0 < k)
    (R : IndexedChainRealization k hk) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)),
        C.IsIndep s -> s.card <= (5 * (16 * k)) / 16 := by
  refine Exists.intro R.config ?_
  intro s hs
  have hbound := independent_card_le_five_mul hk R s hs
  have hratio : (5 * (16 * k)) / 16 = 5 * k := by
    omega
  simpa [hratio] using hbound

end IndexedChain
end PachToth
end ErdosProblems1066
