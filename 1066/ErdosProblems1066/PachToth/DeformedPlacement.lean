import ErdosProblems1066.PachToth.GeometricSoundness
import ErdosProblems1066.PachToth.TargetReduction

/-!
# Pach--Toth Deformed Placements

This module packages the non-rigid placement interface closest to the
Pach--Toth construction: each block has its own actual point map.  The hard
geometry is kept as explicit fields: global separation, same-block unit edges,
and cyclic cross-connector unit edges.
-/

namespace ErdosProblems1066
namespace PachToth
namespace DeformedPlacement

open BlockPartition
open FiniteGraph
open Arithmetic

noncomputable section

abbrev R2 := Prod Real Real

/-- A closed cyclic Pach--Toth placement with blockwise deformed coordinates.

The fields are exactly the geometric facts consumed by the indexed-chain
soundness layer.  Same-block unit edges are not derived from a rigid local
copy; they are direct obligations about the provided point map. -/
structure ClosedPlacement (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point i u) (point i v) = 1
  cross_connector_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1

namespace ClosedPlacement

/-- Encode a deformed closed placement as the canonical global `UDConfig`. -/
def config {k : Nat} {hk : 0 < k}
    (P : ClosedPlacement k hk) : _root_.UDConfig (16 * k) where
  pts := fun x =>
    let p := vertexBlockLocal k x
    P.point p.1 p.2
  sep := by
    intro x y hxy
    let px := vertexBlockLocal k x
    let py := vertexBlockLocal k y
    have hpair : Ne px py := by
      intro hp
      apply hxy
      calc
        x = blockLocalEquiv k px := by
          change x = blockLocalEquiv k (vertexBlockLocal k x)
          exact ((blockLocalEquiv k).apply_symm_apply x).symm
        _ = blockLocalEquiv k py := by
          rw [hp]
        _ = y := by
          change blockLocalEquiv k (vertexBlockLocal k y) = y
          exact (blockLocalEquiv k).apply_symm_apply y
    exact P.separated px.1 px.2 py.1 py.2 hpair

@[simp]
theorem config_pts_globalVertex {k : Nat} {hk : 0 < k}
    (P : ClosedPlacement k hk) (i : Fin k) (v : LocalVertex) :
    P.config.pts (GeometricSoundness.globalVertex k i v) = P.point i v := by
  simp [config, GeometricSoundness.globalVertex, vertexBlockLocal]

/-- A deformed placement directly supplies the explicit edge-soundness
certificate used by `GeometricSoundness`. -/
def toExplicitEdgeSoundness {k : Nat} {hk : 0 < k}
    (P : ClosedPlacement k hk) :
    GeometricSoundness.ExplicitEdgeSoundness k hk where
  config := P.config
  same_block_edges_unit := by
    intro i u v huv hadj
    rw [config_pts_globalVertex, config_pts_globalVertex]
    exact P.same_block_edges_unit i u v huv hadj
  cross_block_edges_unit := by
    intro i u v hconn
    rw [config_pts_globalVertex, config_pts_globalVertex]
    exact P.cross_connector_edges_unit i u v hconn

/-- A deformed placement gives the canonical indexed-chain realization. -/
def toIndexedChainRealization {k : Nat} {hk : 0 < k}
    (P : ClosedPlacement k hk) :
    IndexedChain.IndexedChainRealization k hk :=
  P.toExplicitEdgeSoundness.toIndexedChainRealization

end ClosedPlacement

/-!
## Length-one obstruction certificate

For a one-block cyclic placement, the successor connector edges return to the
same block.  The finite unit-edge equations then force the first two
equilateral steps into a normalized branch in which the `T2` completion would
need a point unit from both `(3/2, s)` and `(-1, -2*s)`, with `s^2 = 3/4`.
Those two centers have squared distance `13`, so even the first such unit
point is impossible.  This is the checked finite-coordinate obstruction left
by the current geometry interface; it is intentionally not wrapped as another
source package.
-/
theorem lengthOne_forcedBranch_t2Completion_obstruction
    (s x y : Real)
    (_hs : s ^ 2 = (3 : Real) / 4)
    (hfromT0 :
      (x - (3 / 2 : Real)) ^ 2 + (y - s) ^ 2 = 1)
    (hfromT2 :
      (x - (-1 : Real)) ^ 2 + (y - (-2 * s)) ^ 2 = 1) :
    False := by
  nlinarith [_hs, hfromT0, hfromT2]

theorem not_lengthOne_forcedBranch_t2Completion :
    Not
      (Exists fun s : Real =>
        Exists fun x : Real =>
          Exists fun y : Real =>
            s ^ 2 = (3 : Real) / 4 /\
            (x - (3 / 2 : Real)) ^ 2 + (y - s) ^ 2 = 1 /\
            (x - (-1 : Real)) ^ 2 + (y - (-2 * s)) ^ 2 = 1) := by
  intro h
  rcases h with ⟨s, x, y, hs, hfromT0, hfromT2⟩
  exact lengthOne_forcedBranch_t2Completion_obstruction
    s x y hs hfromT0 hfromT2

/-- The Pach--Toth block target follows from deformed closed placements for
every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_deformedPlacements
    (H : forall (k : Nat) (hk : 0 < k), ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteen := by
  apply targetUpperConstructionFiveSixteen_of_indexedChainRealizations
  intro k hk
  exact (H k hk).toIndexedChainRealization

/-! ## The collapsed one-block deformed target -/

theorem lengthOnePositive : 0 < 1 := by
  decide

/-- The exact geometric content of a deformed closed placement when
`k = 1`.  The successor block is the same block, so the four directed
cross-connectors become additional unit-distance requirements on the single
local point map. -/
structure LengthOneGeometry where
  point : LocalVertex -> R2
  separated :
    forall (u v : LocalVertex), Ne u v ->
      1 <= _root_.eucDist (point u) (point v)
  same_block_edges_unit :
    forall (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point u) (point v) = 1
  collapsed_connector_edges_unit :
    forall (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point u) (point v) = 1

namespace LengthOneGeometry

/-- Package the one-block deformed geometry as the general closed-placement
interface. -/
def toClosedPlacement (G : LengthOneGeometry) :
    ClosedPlacement 1 lengthOnePositive where
  point := fun _ v => G.point v
  separated := by
    intro i u j v hne
    have hij : i = j := Subsingleton.elim i j
    have huv : Ne u v := by
      intro huv
      exact hne (by
        cases hij
        cases huv
        rfl)
    simpa using G.separated u v huv
  same_block_edges_unit := by
    intro _ u v huv hadj
    exact G.same_block_edges_unit u v huv hadj
  cross_connector_edges_unit := by
    intro i u v hconn
    have hsucc : cyclicSucc lengthOnePositive i = i :=
      Subsingleton.elim (cyclicSucc lengthOnePositive i) i
    simpa [hsucc] using G.collapsed_connector_edges_unit u v hconn

@[simp]
theorem toClosedPlacement_point
    (G : LengthOneGeometry) (i : Fin 1) (v : LocalVertex) :
    G.toClosedPlacement.point i v = G.point v :=
  rfl

end LengthOneGeometry

/-- Read a `k = 1` closed placement as its collapsed one-block deformed
geometry. -/
def lengthOneGeometryOfClosedPlacement
    {hpos : 0 < 1}
    (P : ClosedPlacement 1 hpos) :
    LengthOneGeometry where
  point := fun v => P.point 0 v
  separated := by
    intro u v huv
    have hpair : Ne ((0 : Fin 1), u) ((0 : Fin 1), v) := by
      intro h
      exact huv (congrArg Prod.snd h)
    exact P.separated 0 u 0 v hpair
  same_block_edges_unit := by
    intro u v huv hadj
    exact P.same_block_edges_unit 0 u v huv hadj
  collapsed_connector_edges_unit := by
    intro u v hconn
    have hunit := P.cross_connector_edges_unit 0 u v hconn
    have hsucc : cyclicSucc hpos (0 : Fin 1) = 0 :=
      Subsingleton.elim (cyclicSucc hpos (0 : Fin 1)) 0
    simpa [hsucc] using hunit

@[simp]
theorem lengthOneGeometryOfClosedPlacement_point
    {hpos : 0 < 1}
    (P : ClosedPlacement 1 hpos) (v : LocalVertex) :
    (lengthOneGeometryOfClosedPlacement P).point v = P.point 0 v :=
  rfl

/-- A checked `k = 1` deformed placement is equivalent to the collapsed
one-block metric rows above.  This names the precise missing geometric
condition for the deformed length-one route. -/
theorem nonempty_closedPlacement_one_iff_lengthOneGeometry
    {hpos : 0 < 1} :
    Nonempty (ClosedPlacement 1 hpos) <-> Nonempty LengthOneGeometry := by
  constructor
  · intro h
    rcases h with ⟨P⟩
    exact ⟨lengthOneGeometryOfClosedPlacement P⟩
  · intro h
    rcases h with ⟨G⟩
    have hproof : hpos = lengthOnePositive := Subsingleton.elim hpos lengthOnePositive
    cases hproof
    exact ⟨G.toClosedPlacement⟩

end

end DeformedPlacement
end PachToth
end ErdosProblems1066
