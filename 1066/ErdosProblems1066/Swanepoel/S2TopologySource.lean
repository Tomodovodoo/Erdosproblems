import ErdosProblems1066.Swanepoel.ExteriorComponentTopology

set_option autoImplicit false

/-!
# S2 topology source reductions

Small topology-only handoffs for the S2 exterior-component route.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ExteriorComponentTopology

open FinitePlaneDrawing
open JordanTopologyFactsConcrete.MinimalFailureTopology

noncomputable section

variable {n : Nat}

/-- Direct frontier-component source for the live point-between topology leaf.

This is the unbundled form of the remaining boundary-bumping content: the
compact connected `T ⊆ K` is used only as the hypothesis under which the two
displayed frontier points must lie in the same connected component of the
selected frontier.  The reducer below packages that frontier component as the
requested compact connected witness. -/
def
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumFrontierComponent :
    Prop :=
  forall (K : Set PlanarInterface.Point) (x : PlanarInterface.Point)
      (T : Set PlanarInterface.Point) (y z : PlanarInterface.Point),
    IsCompact K ->
      x ∈ Kᶜ ->
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x) ->
          IsCompact T ->
            IsConnected T ->
              T ⊆ K ->
                y ∈ T ->
                  z ∈ T ->
                    (hyFrontier :
                      y ∈ frontier (connectedComponentIn Kᶜ x)) ->
                      (hzFrontier :
                        z ∈ frontier (connectedComponentIn Kᶜ x)) ->
                        (⟨z, hzFrontier⟩ :
                            frontier (connectedComponentIn Kᶜ x)) ∈
                          connectedComponent
                            (⟨y, hyFrontier⟩ :
                              frontier (connectedComponentIn Kᶜ x))

/-- A same-frontier-component source supplies the live point-between witness.

The witness is the image in the plane of the connected component of `y` in the
selected frontier.  Compactness comes from the existing compact-frontier lemma
for complement components of compact planar sets. -/
theorem
    planarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween_of_frontierComponent
    (frontier_component :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween := by
  intro K x T y z hcompact hx hunbounded hTcompact hTconnected hTsubset
    hyT hzT hyFrontier hzFrontier
  have hFcompact :
      IsCompact (frontier (connectedComponentIn Kᶜ x)) :=
    planarContinuumUnboundedComplement_frontier_compact
      (K := K) (x := x) hcompact
  haveI :
      CompactSpace (frontier (connectedComponentIn Kᶜ x)) :=
    isCompact_iff_compactSpace.mp hFcompact
  let yF : frontier (connectedComponentIn Kᶜ x) :=
    ⟨y, hyFrontier⟩
  let zF : frontier (connectedComponentIn Kᶜ x) :=
    ⟨z, hzFrontier⟩
  have hz_componentF : zF ∈ connectedComponent yF := by
    simpa [yF, zF] using
      frontier_component K x T y z hcompact hx hunbounded hTcompact
        hTconnected hTsubset hyT hzT hyFrontier hzFrontier
  let S : Set PlanarInterface.Point := Subtype.val '' connectedComponent yF
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  · exact
      isConnected_connectedComponent.image Subtype.val
        continuous_subtype_val.continuousOn
  · intro p hpS
    rcases hpS with ⟨pF, _hp_component, rfl⟩
    exact pF.property
  · exact ⟨yF, mem_connectedComponent, rfl⟩
  · exact ⟨zF, hz_componentF, rfl⟩

/-- Claim `S2-agent-points-between-source-scout-20260521e45`.

The live point-between leaf is strictly reduced to the direct frontier-component
source above.  This route only packages a connected component of the selected
frontier as a compact connected plane set; it does not pass through finite
no-closed-separation, same-`K` components, component avoidance,
no-subcontinuum, crossing-boundedness, or final boundary-cycle assumptions. -/
theorem S2_agent_points_between_source_scout_20260521e45
    (frontier_component :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween :=
  planarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween_of_frontierComponent
    frontier_component

/-- The direct crossing-subcontinuum frontier-component source reduces to the
Janiszewski same-`K` frontier-component theorem already isolated in
`ExteriorComponentTopology`.

The compact connected `T ⊆ K` is used only to put `z` in
`connectedComponentIn K y`; the Janiszewski component theorem then upgrades
that to a component statement inside the selected frontier. -/
theorem
    planarContinuumUnboundedComplementFrontierCrossingSubcontinuumFrontierComponent_of_janiszewskiKComponentFrontierComponent
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumFrontierComponent := by
  intro K x T y z hcompact hx hunbounded _hTcompact hTconnected hTsubset
    hyT hzT hyFrontier hzFrontier
  let U : Set PlanarInterface.Point := connectedComponentIn Kᶜ x
  have hz_componentInK : z ∈ connectedComponentIn K y :=
    hTconnected.isPreconnected.subset_connectedComponentIn hyT hTsubset hzT
  have hz_frontierComponent :
      z ∈ connectedComponentIn (frontier U) y :=
    frontier_component K U y z hcompact ⟨x, hx, rfl⟩ hunbounded
      (by simpa [U] using hyFrontier)
      (by simpa [U] using hzFrontier)
      hz_componentInK
  let yF : frontier U := ⟨y, by simpa [U] using hyFrontier⟩
  let zF : frontier U := ⟨z, by simpa [U] using hzFrontier⟩
  have hz_image :
      z ∈ (Subtype.val '' connectedComponent yF :
        Set PlanarInterface.Point) := by
    rw [connectedComponentIn_eq_image (by simpa [U] using hyFrontier)]
      at hz_frontierComponent
    simpa [yF] using hz_frontierComponent
  rcases hz_image with ⟨w, hw_component, hw_eq⟩
  have hw_eq_zF : w = zF := Subtype.ext hw_eq
  simpa [U, yF, zF, hw_eq_zF] using hw_component

/-- Claim `S2-agent-frontier-component-source-20260521e48` support adapter.

The e45 frontier-component source is lowered to the sharper
Janiszewski same-`K` frontier-component theorem. -/
theorem S2_agent_frontier_component_source_20260521e48_adapter
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumFrontierComponent :=
  planarContinuumUnboundedComplementFrontierCrossingSubcontinuumFrontierComponent_of_janiszewskiKComponentFrontierComponent
    frontier_component

/-- Claim `S2-agent-point-between-honest-source-prover-20260521e54`.

The point-between topology leaf is reduced to the U-indexed
Janiszewski/boundary-bumping subcontinuum theorem. This is the smallest
non-circular planar source currently isolated here: for an unbounded component
`U` of `K`'s complement and a compact connected `T <= K`, two points of
`T` on `frontier U` must be joined by a compact connected subset of
`frontier U`. The reducer only specializes `U` to the selected exterior
component; it does not route through continuous-side, relative-clopen,
same-`K` frontier components, no-subcontinuum, component-avoidance,
crossing-boundedness, finite no-closed-separation, or boundary-cycle rows. -/
theorem S2_agent_point_between_honest_source_prover_20260521e54
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween :=
  planarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween_of_janiszewskiBoundaryBumpingPointsBetween
    points_between

/-- Claim `S2-agent-janiszewski-U-points-between-source-20260521e57`.

The U-indexed point-between source is strictly reduced to the standard
subcontinuum boundary-bumping carrier theorem: a compact connected
`T ⊆ K` meeting `frontier U` has its full frontier trace carried by one compact
connected subset of `frontier U`.  This proof only unwraps that carrier and
does not pass through continuous-side, relative-clopen, same-`K` frontier
component, no-subcontinuum, component-avoidance, crossing-boundedness, finite
no-closed-separation, or boundary-cycle rows. -/
theorem S2_agent_janiszewski_U_points_between_source_20260521e57
    (subcontinuum_carrier :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumCarrier) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween :=
  planarJaniszewskiBoundaryBumpingSubcontinuumPointsBetween_of_subcontinuumCarrier
    subcontinuum_carrier

/-- Claim `S2-agent-point-between-source-20260521k12`.

The selected crossing point-between topology leaf is strictly lowered to the
U-indexed subcontinuum-carrier boundary-bumping theorem.  The composition only
unwraps the carrier to a pointwise compact connected witness and specializes
`U` to `connectedComponentIn Kᶜ x`; it does not use the continuous-side,
relative-clopen, no-compact-crossing, or final-cycle routes. -/
theorem S2_agent_point_between_source_20260521k12
    (subcontinuum_carrier :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumCarrier) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween :=
  S2_agent_point_between_honest_source_prover_20260521e54
    (S2_agent_janiszewski_U_points_between_source_20260521e57
      subcontinuum_carrier)

set_option linter.style.longLine false in
/-- Claim `S2-r14-topology-support-source`.

The planar-continuum no-compact-connected-crossing source used by the selected
raw-orbit no-crossing branch is strictly lowered to the U-indexed
subcontinuum point-between boundary-bumping theorem.  The proof only
specializes `U` to `connectedComponentIn Kᶜ x` and applies the existing
point-between/no-crossing separator; it does not use actual-boundary rows,
carrier rows, sector rows, or W32 consumers. -/
theorem
    planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_janiszewskiSubcontinuumPointsBetween_20260521r14
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_pointsBetween
    (planarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween_of_janiszewskiBoundaryBumpingPointsBetween
      points_between)

set_option linter.style.longLine false in
/-- Named r14 topology-support handoff for the selected raw-orbit no-crossing
branch.  The first remaining topology source is the U-indexed subcontinuum
point-between theorem. -/
theorem S2_r14_topology_support_noCompactConnectedKCrossing_source_20260521r14
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_janiszewskiSubcontinuumPointsBetween_20260521r14
    points_between

/-- U-indexed frontier-component pair source for the live point-between leaf.

This is the compact-witness-free form of the U-indexed boundary-bumping step:
for the displayed compact connected `T <= K`, the two selected frontier points
already lie in the same connected component of `frontier U`. -/
def
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent :
    Prop :=
  forall (K U T : Set PlanarInterface.Point) (y z : PlanarInterface.Point),
    IsCompact K ->
      (Exists fun x : PlanarInterface.Point =>
        x ∈ Kᶜ ∧ U = connectedComponentIn Kᶜ x) ->
        ¬ Bornology.IsBounded U ->
          IsCompact T ->
            IsConnected T ->
              T ⊆ K ->
                y ∈ T ->
                  z ∈ T ->
                    (hyFrontier : y ∈ frontier U) ->
                      (hzFrontier : z ∈ frontier U) ->
                        (⟨z, hzFrontier⟩ : frontier U) ∈
                          connectedComponent
                            (⟨y, hyFrontier⟩ : frontier U)

/-- The U-indexed pair frontier-component source is supplied by the existing
point-between primitive.

The compact connected witness `S ⊆ frontier U` joining the two displayed
frontier points puts `z` in `connectedComponentIn (frontier U) y`; the standard
image description of `connectedComponentIn` translates this back to component
membership in the frontier subtype. -/
theorem
    planarJaniszewskiBoundaryBumpingSubcontinuumPairFrontierComponent_of_subcontinuumPointsBetween
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent := by
  intro K U T y z hcompact hcomponent hunbounded hTcompact hTconnected
    hTsubset hyT hzT hyFrontier hzFrontier
  rcases
      points_between K U T y z hcompact hcomponent hunbounded hTcompact
        hTconnected hTsubset hyT hzT hyFrontier hzFrontier with
    ⟨S, _hScompact, hSconnected, hSsubset, hyS, hzS⟩
  have hz_frontierComponent :
      z ∈ connectedComponentIn (frontier U) y :=
    hSconnected.isPreconnected.subset_connectedComponentIn hyS hSsubset hzS
  let yF : frontier U := ⟨y, hyFrontier⟩
  let zF : frontier U := ⟨z, hzFrontier⟩
  have hz_image :
      z ∈ (Subtype.val '' connectedComponent yF :
        Set PlanarInterface.Point) := by
    simpa [connectedComponentIn_eq_image hyFrontier, yF] using
      hz_frontierComponent
  rcases hz_image with ⟨w, hw_component, hw_eq⟩
  have hw_eq_zF : w = zF := Subtype.ext hw_eq
  simpa [yF, zF, hw_eq_zF] using hw_component

/-- Claim `S2-agent-topology-pair-component-source-20260521k17`.

The current U-indexed pair frontier-component residual is strictly lowered to
the existing U-indexed subcontinuum point-between primitive.  This is the
direct component extraction from the point-between witness, with no
boundary-cycle rows, final S2 rows, W-facing facade, or synthetic enclosure. -/
theorem S2_agent_topology_pair_component_source_20260521k17
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent :=
  planarJaniszewskiBoundaryBumpingSubcontinuumPairFrontierComponent_of_subcontinuumPointsBetween
    points_between

set_option linter.style.longLine false in
/-- The U-indexed pair frontier-component source reduces to the same-`K`
boundary-bumping point theorem.

The compact connected `T <= K` is used only to put `z` in the relative
component of `y` inside `K`; the same-`K` point-between theorem then supplies a
compact connected subset of `frontier U`, and Mathlib connected-component
bookkeeping turns that witness into the required component membership in the
frontier subtype. -/
theorem
    planarJaniszewskiBoundaryBumpingSubcontinuumPairFrontierComponent_of_kComponentPointsBetween
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent := by
  intro K U T y z hcompact hcomponent hunbounded _hTcompact hTconnected
    hTsubset hyT hzT hyFrontier hzFrontier
  have hz_componentInK : z ∈ connectedComponentIn K y :=
    hTconnected.isPreconnected.subset_connectedComponentIn hyT hTsubset hzT
  rcases
      points_between K U y z hcompact hcomponent hunbounded hyFrontier
        hzFrontier hz_componentInK with
    ⟨S, _hScompact, hSconnected, hSsubset, hyS, hzS⟩
  have hz_frontierComponent :
      z ∈ connectedComponentIn (frontier U) y :=
    hSconnected.isPreconnected.subset_connectedComponentIn hyS hSsubset hzS
  let yF : frontier U := ⟨y, hyFrontier⟩
  let zF : frontier U := ⟨z, hzFrontier⟩
  have hz_image :
      z ∈ (Subtype.val '' connectedComponent yF :
        Set PlanarInterface.Point) := by
    simpa [connectedComponentIn_eq_image hyFrontier, yF] using
      hz_frontierComponent
  rcases hz_image with ⟨w, hw_component, hw_eq⟩
  have hw_eq_zF : w = zF := Subtype.ext hw_eq
  simpa [yF, zF, hw_eq_zF] using hw_component

set_option linter.style.longLine false in
/-- Claim `S2-r59-topology-pair-frontier-source-20260521r59`, pair-frontier
side.

The requested pair-frontier source is strictly lowered to the existing topology
theorem
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween`.
No boundary-cycle rows, actual-sector rows, final S2 rows, W/facade consumers,
or finite frontier-cycle rows enter this reducer. -/
theorem S2_r59_pair_frontier_component_of_kComponentPointsBetween_20260521r59
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent :=
  planarJaniszewskiBoundaryBumpingSubcontinuumPairFrontierComponent_of_kComponentPointsBetween
    points_between

/-- A U-indexed frontier-component pair source supplies the point-between
topology leaf by taking the image of the selected frontier component. -/
theorem
    planarJaniszewskiBoundaryBumpingSubcontinuumPointsBetween_of_pairFrontierComponent
    (pair_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween := by
  intro K U T y z hcompact hcomponent hunbounded hTcompact hTconnected hTsubset
    hyT hzT hyFrontier hzFrontier
  have hFcompact : IsCompact (frontier U) := by
    rcases hcomponent with ⟨x, _hx, rfl⟩
    exact
      planarContinuumUnboundedComplement_frontier_compact
        (K := K) (x := x) hcompact
  haveI : CompactSpace (frontier U) := isCompact_iff_compactSpace.mp hFcompact
  let yF : frontier U := ⟨y, hyFrontier⟩
  let zF : frontier U := ⟨z, hzFrontier⟩
  have hz_componentF : zF ∈ connectedComponent yF := by
    simpa [yF, zF] using
      pair_component K U T y z hcompact hcomponent hunbounded hTcompact
        hTconnected hTsubset hyT hzT hyFrontier hzFrontier
  let S : Set PlanarInterface.Point := Subtype.val '' connectedComponent yF
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  · exact
      isConnected_connectedComponent.image Subtype.val
        continuous_subtype_val.continuousOn
  · intro p hpS
    rcases hpS with ⟨pF, _hp_component, rfl⟩
    exact pF.property
  · exact ⟨yF, mem_connectedComponent, rfl⟩
  · exact ⟨zF, hz_componentF, rfl⟩

/-- Claim `S2-main-U-frontier-component-pair-source-20260521e68`.

The U-indexed point-between leaf is reduced to its pure frontier-component
form; this reducer only packages the connected component of the selected
frontier and does not introduce a new S2 facade or boundary-cycle assumption. -/
theorem S2_main_U_frontier_component_pair_source_20260521e68
    (pair_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween :=
  planarJaniszewskiBoundaryBumpingSubcontinuumPointsBetween_of_pairFrontierComponent
    pair_component

/-- The selected crossing point-between source reduces to the U-indexed
subcontinuum pair frontier-component source.

This is the f5 non-circular Janiszewski handoff: the remaining source says
directly that the two displayed points of `T` on `frontier U` lie in the same
component of `frontier U`. The proof only packages that frontier component as
a compact connected witness and specializes `U` to the selected exterior
component; it does not pass through continuous-side, relative-clopen, same-`K`
frontier-component, crossing-boundedness, finite no-closed-separation, or final
S2 rows. -/
theorem
    crossingSubcontinuumPointsBetween_of_U_pairFrontierComponent
    (pair_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween :=
  S2_agent_point_between_honest_source_prover_20260521e54
    (S2_main_U_frontier_component_pair_source_20260521e68 pair_component)

/-- Claim `S2-agent-topology-points-between-source-20260521f5`.

The live point-between topology leaf is strictly reduced to the U-indexed
pair frontier-component source. The residual source is the component-membership
form of Janiszewski boundary bumping for one compact connected `T <= K`, with
no detour through the known circular S2 or same-`K` routes. -/
theorem S2_agent_topology_points_between_source_20260521f5
    (pair_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween :=
  crossingSubcontinuumPointsBetween_of_U_pairFrontierComponent
    pair_component

set_option linter.style.longLine false in
/-- The closed-side frontier-subcontinuum source is strictly lowered to the
same-`K` Janiszewski point-between primitive.

The same-`K` source supplies the U-indexed subcontinuum point-between theorem;
the existing point-level crossing reducer then chooses one point from each
closed side and packages the compact connected frontier witness.  No final S2
boundary rows, cycle rows, actual-sector rows, or carrier rows enter this
handoff. -/
theorem
    planarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum_of_janiszewskiKComponentPointsBetween_20260521current5
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum :=
  planarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum_of_pointsBetween
    (planarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween_of_janiszewskiBoundaryBumpingPointsBetween
      (planarJaniszewskiBoundaryBumpingSubcontinuumPointsBetween_of_kComponentPointsBetween
        points_between))

set_option linter.style.longLine false in
/-- Claim `S2-subagent-frontier-subcontinuum-topology-20260521-current5`.

The requested planar-continuum frontier-subcontinuum source is now reduced to
the same-`K` Janiszewski boundary-bumping point-between theorem. -/
theorem S2_subagent_frontier_subcontinuum_topology_20260521_current5
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum :=
  planarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum_of_janiszewskiKComponentPointsBetween_20260521current5
    points_between

set_option linter.style.longLine false in
/-- The U-indexed pair frontier-component source reduces to the direct
Janiszewski no-subcontinuum obstruction.

If the two displayed frontier points were in different frontier components,
the already checked no-subcontinuum obstruction would supply the contradiction
through its compact-Hausdorff closed split.  We reuse the point-between proof
from that obstruction and translate the compact connected frontier witness into
subtype connected-component membership. -/
theorem
    planarJaniszewskiBoundaryBumpingSubcontinuumPairFrontierComponent_of_noSubcontinuumObstruction
    (no_subcontinuum :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent := by
  intro K U T y z hcompact hcomponent hunbounded hTcompact hTconnected
    hTsubset hyT hzT hyFrontier hzFrontier
  rcases
      planarJaniszewskiBoundaryBumpingSubcontinuumPointsBetween_of_noSubcontinuumObstruction
        no_subcontinuum K U T y z hcompact hcomponent hunbounded hTcompact
        hTconnected hTsubset hyT hzT hyFrontier hzFrontier with
    ⟨S, _hScompact, hSconnected, hSsubset, hyS, hzS⟩
  have hz_frontierComponent :
      z ∈ connectedComponentIn (frontier U) y :=
    hSconnected.isPreconnected.subset_connectedComponentIn hyS hSsubset hzS
  let yF : frontier U := ⟨y, hyFrontier⟩
  let zF : frontier U := ⟨z, hzFrontier⟩
  have hz_image :
      z ∈ (Subtype.val '' connectedComponent yF :
        Set PlanarInterface.Point) := by
    simpa [connectedComponentIn_eq_image hyFrontier, yF] using
      hz_frontierComponent
  rcases hz_image with ⟨w, hw_component, hw_eq⟩
  have hw_eq_zF : w = zF := Subtype.ext hw_eq
  simpa [yF, zF, hw_eq_zF] using hw_component

/-- Claim `S2-agent-U-pair-frontier-component-source-20260521f7`.

The current U-indexed pair frontier-component source is strictly reduced to
the boundedness/crosscut Janiszewski source.  This route goes through the
direct no-subcontinuum obstruction only, and does not use the same-`K`
frontier-component source, continuous-side source, relative-clopen source,
final S2 rows, or finite frontier-cycle rows. -/
theorem S2_agent_U_pair_frontier_component_source_20260521f7
    (subcontinuum_forces_bounded :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent :=
  planarJaniszewskiBoundaryBumpingSubcontinuumPairFrontierComponent_of_noSubcontinuumObstruction
    (planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_subcontinuumForcesBounded
      subcontinuum_forces_bounded)

/-- The U-indexed pair frontier-component source reduces to the same-`K`
frontier-component theorem.

The compact connected `T ⊆ K` is used only to put `z` in
`connectedComponentIn K y`; the same-`K` source then gives membership in
`connectedComponentIn (frontier U) y`, which is translated back to the subtype
connected component of the selected frontier. -/
theorem
    planarJaniszewskiBoundaryBumpingSubcontinuumPairFrontierComponent_of_kComponentFrontierComponent
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent := by
  intro K U T y z hcompact hcomponent hunbounded _hTcompact hTconnected
    hTsubset hyT hzT hyFrontier hzFrontier
  have hz_componentInK : z ∈ connectedComponentIn K y :=
    hTconnected.isPreconnected.subset_connectedComponentIn hyT hTsubset hzT
  have hz_frontierComponent :
      z ∈ connectedComponentIn (frontier U) y :=
    frontier_component K U y z hcompact hcomponent hunbounded hyFrontier
      hzFrontier hz_componentInK
  let yF : frontier U := ⟨y, hyFrontier⟩
  let zF : frontier U := ⟨z, hzFrontier⟩
  have hz_image :
      z ∈ (Subtype.val '' connectedComponent yF :
        Set PlanarInterface.Point) := by
    simpa [connectedComponentIn_eq_image hyFrontier, yF] using
      hz_frontierComponent
  rcases hz_image with ⟨w, hw_component, hw_eq⟩
  have hw_eq_zF : w = zF := Subtype.ext hw_eq
  simpa [yF, zF, hw_eq_zF] using hw_component

/-- Claim `S2-agent-U-pair-source-from-K-component-20260521e69`.

The U-indexed pair-frontier-component source is strictly lowered to the
existing same-`K` frontier-component theorem. -/
theorem S2_agent_U_pair_source_from_K_component_20260521e69
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent :=
  planarJaniszewskiBoundaryBumpingSubcontinuumPairFrontierComponent_of_kComponentFrontierComponent
    frontier_component

set_option linter.style.longLine false in
/-- Claim `S2-k6m-pair-frontier-component-source`.

The live U-indexed pair frontier-component source is strictly lowered to the
Janiszewski component-avoidance row.  If the two displayed frontier points were
in different connected components of `frontier U`, compact-Hausdorff
quasicomponent separation would split that frontier into closed sides `A` and
`B`.  Since `T` is connected inside `K`, the two points lie in the same
component of `K`, contradicting component avoidance for that split. -/
theorem S2_k6m_pair_frontier_component_source
    (component_avoidance :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent := by
  intro K U T y z hcompact hcomponent hunbounded _hTcompact hTconnected
    hTsubset hyT hzT hyFrontier hzFrontier
  have hz_componentInK : z ∈ connectedComponentIn K y :=
    hTconnected.isPreconnected.subset_connectedComponentIn hyT hTsubset hzT
  rcases hcomponent with ⟨x, hx, rfl⟩
  let F : Set PlanarInterface.Point := frontier (connectedComponentIn Kᶜ x)
  have hFcompact : IsCompact F :=
    planarContinuumUnboundedComplement_frontier_compact (K := K) (x := x)
      hcompact
  have hFclosed : IsClosed F := hFcompact.isClosed
  have hfrontier_subset_K : F ⊆ K :=
    planarContinuumUnboundedComplement_frontier_subset
      (K := K) (x := x) hcompact
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hFcompact
  let yF : F := ⟨y, hyFrontier⟩
  let zF : F := ⟨z, hzFrontier⟩
  have hz_componentF : zF ∈ connectedComponent yF := by
    by_contra hz_not_component
    have hex :
        Exists fun t : {t : Set F // IsClopen t ∧ yF ∈ t} =>
          zF ∉ (t : Set F) := by
      by_contra h
      have hall :
          forall t : {t : Set F // IsClopen t ∧ yF ∈ t},
            zF ∈ (t : Set F) := by
        intro t
        by_contra hz_not_t
        exact h ⟨t, hz_not_t⟩
      exact hz_not_component (by
        rw [connectedComponent_eq_iInter_isClopen]
        exact Set.mem_iInter.mpr hall)
    rcases hex with ⟨t, hz_not_t⟩
    let A : Set PlanarInterface.Point := Subtype.val '' (t : Set F)
    let B : Set PlanarInterface.Point := Subtype.val '' ((t : Set F)ᶜ)
    have hAclosed : IsClosed A := by
      exact
        hFclosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp
          t.property.1.isClosed
    have hBclosed : IsClosed B := by
      exact
        hFclosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp
          t.property.1.compl.isClosed
    have hABdisjoint : Disjoint A B := by
      rw [Set.disjoint_left]
      intro p hpA hpB
      rcases hpA with ⟨a, ha, rfl⟩
      rcases hpB with ⟨b, hb, hb_eq⟩
      have hba : b = a := Subtype.ext hb_eq
      exact hb (by simpa [hba] using ha)
    have hcover : F = A ∪ B := by
      ext p
      constructor
      · intro hpF
        let pF : F := ⟨p, hpF⟩
        by_cases hp_t : pF ∈ (t : Set F)
        · exact Or.inl ⟨pF, hp_t, rfl⟩
        · exact Or.inr ⟨pF, hp_t, rfl⟩
      · intro hp
        rcases hp with hpA | hpB
        · rcases hpA with ⟨pF, _hpF, rfl⟩
          exact pF.property
        · rcases hpB with ⟨pF, _hpF, rfl⟩
          exact pF.property
    have hAnonempty : A.Nonempty :=
      ⟨y, ⟨yF, t.property.2, rfl⟩⟩
    have hBnonempty : B.Nonempty :=
      ⟨z, ⟨zF, hz_not_t, rfl⟩⟩
    let yK : K := ⟨y, hfrontier_subset_K hyFrontier⟩
    let zK : K := ⟨z, hfrontier_subset_K hzFrontier⟩
    have hz_componentK : zK ∈ connectedComponent yK := by
      have hz_componentInK' :
          z ∈
            (Subtype.val '' connectedComponent yK : Set PlanarInterface.Point) := by
        simpa [connectedComponentIn_eq_image (hfrontier_subset_K hyFrontier),
          yK] using hz_componentInK
      rcases hz_componentInK' with ⟨w, hw_component, hw_eq⟩
      have hw_eq_zK : w = zK := Subtype.ext hw_eq
      simpa [hw_eq_zK, yK] using hw_component
    have hy_componentK : yK ∈ connectedComponent zK := by
      rw [← connectedComponent_eq hz_componentK]
      exact mem_connectedComponent
    exact
      (component_avoidance K (connectedComponentIn Kᶜ x) A B hcompact
        ⟨x, hx, rfl⟩ hunbounded hAclosed hBclosed hABdisjoint hcover
        hAnonempty hBnonempty zK ⟨zF, hz_not_t, rfl⟩ yK
        ⟨yF, t.property.2, rfl⟩)
        hy_componentK
  simpa [F, yF, zF] using hz_componentF

/-- A same-`K` frontier-component source supplies the stronger subcontinuum
carrier surface.

Choose one point `y` in `T ∩ frontier U`; every other point of that trace lies
in the same relative component of `K` as `y` because `T` is connected and
contained in `K`.  The frontier-component source then puts the whole trace in
the connected component of `y` inside `frontier U`, whose image is the required
compact connected carrier. -/
theorem
    planarJaniszewskiBoundaryBumpingSubcontinuumCarrier_of_kComponentFrontierComponent
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumCarrier := by
  intro K U T hcompact hcomponent hunbounded hTcompact hTconnected hTsubset
    htrace_nonempty
  rcases htrace_nonempty with ⟨y, hyT, hyFrontier⟩
  have hFcompact : IsCompact (frontier U) := by
    rcases hcomponent with ⟨x, _hx, rfl⟩
    exact
      planarContinuumUnboundedComplement_frontier_compact
        (K := K) (x := x) hcompact
  haveI : CompactSpace (frontier U) := isCompact_iff_compactSpace.mp hFcompact
  let yF : frontier U := ⟨y, hyFrontier⟩
  let S : Set PlanarInterface.Point := Subtype.val '' connectedComponent yF
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  · exact
      isConnected_connectedComponent.image Subtype.val
        continuous_subtype_val.continuousOn
  · intro p hpS
    rcases hpS with ⟨pF, _hp_component, rfl⟩
    exact pF.property
  · intro p hpTrace
    rcases hpTrace with ⟨hpT, hpFrontier⟩
    have hp_componentInK : p ∈ connectedComponentIn K y :=
      hTconnected.isPreconnected.subset_connectedComponentIn hyT hTsubset hpT
    have hp_frontierComponent : p ∈ connectedComponentIn (frontier U) y :=
      frontier_component K U y p hcompact hcomponent hunbounded hyFrontier
        hpFrontier hp_componentInK
    have hp_image :
        p ∈ (Subtype.val '' connectedComponent yF :
          Set PlanarInterface.Point) := by
      simpa [connectedComponentIn_eq_image hyFrontier, yF] using
        hp_frontierComponent
    simpa [S] using hp_image

/-- Claim `S2-k6c-topology-subcontinuum-carrier-source`.

The live subcontinuum-carrier topology leaf is strictly lowered to the direct
same-`K` Janiszewski frontier-component theorem.  The adapter only chooses a
trace point and uses the connected component of that point inside the selected
frontier as the carrier; it does not use boundary-cycle, final S2, finite
no-closed-separation, component-avoidance, or crossing-boundedness rows. -/
theorem S2_k6c_topology_subcontinuum_carrier_source
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumCarrier :=
  planarJaniszewskiBoundaryBumpingSubcontinuumCarrier_of_kComponentFrontierComponent
    frontier_component

/-- Claim `S2-agent-subcontinuum-carrier-source-20260521e61`.

The subcontinuum-carrier topology source is strictly lowered to the pointwise
U-indexed subcontinuum boundary-bumping source.  The reducer fixes one trace
point and packages its connected component inside `frontier U`, without using
continuous-side, relative-clopen, same-`K` frontier-component,
no-subcontinuum, component-avoidance, crossing-boundedness, finite
no-closed-separation, or boundary-cycle rows. -/
theorem S2_agent_subcontinuum_carrier_source_20260521e61
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumCarrier :=
  planarJaniszewskiBoundaryBumpingSubcontinuumCarrier_of_subcontinuumPointsBetween
    points_between

/-- The subcontinuum carrier source reduces to the same component-indexed
boundedness/crosscut source already isolated in `ExteriorComponentTopology`.

This route first derives the pointwise U-indexed subcontinuum theorem from the
boundedness obstruction, then packages the trace in one selected frontier
component.  It avoids the nontrivial-relative-clopen route, the same-`K`
frontier-component route, crossing-boundedness aliases, and any use of the
carrier source itself. -/
theorem
    planarJaniszewskiBoundaryBumpingSubcontinuumCarrier_of_subcontinuumForcesBounded
    (subcontinuum_forces_bounded :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumCarrier :=
  planarJaniszewskiBoundaryBumpingSubcontinuumCarrier_of_subcontinuumPointsBetween
    (planarJaniszewskiBoundaryBumpingSubcontinuumPointsBetween_of_subcontinuumForcesBounded
      subcontinuum_forces_bounded)

/-- Claim `S2-k6h-subcontinuum-carrier-source`.

The live subcontinuum-carrier topology source is strictly lowered to the
component-indexed boundedness/crosscut source.  The residual topology source is
exactly
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded`. -/
theorem S2_k6h_subcontinuum_carrier_source
    (subcontinuum_forces_bounded :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumCarrier :=
  planarJaniszewskiBoundaryBumpingSubcontinuumCarrier_of_subcontinuumForcesBounded
    subcontinuum_forces_bounded

set_option linter.style.longLine false in
/-- The U-indexed bounded-subcontinuum source reduces to the x-indexed
compact/frontier no-crossing theorem.

This opens the component witness `U = connectedComponentIn Kᶜ x`: if `U` were
unbounded, the displayed compact connected `T ⊆ K` crossing the two closed
frontier sides would be forbidden by the x-indexed no-crossing source.  The
adapter does not route through the equivalent no-subcontinuum obstruction,
frontier-trace connectedness, component avoidance, crossing-boundedness, or
the carrier source itself. -/
theorem
    planarJaniszewskiBoundaryBumpingSubcontinuumForcesBounded_of_noCompactConnectedKCrossing
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded := by
  intro K U A B T hcompact hcomponent hAclosed hBclosed hABdisjoint hcover
    hTcompact hTconnected hTsubset hTA hTB
  rcases hcomponent with ⟨x, hx, rfl⟩
  by_cases hbounded : Bornology.IsBounded (connectedComponentIn Kᶜ x)
  · exact hbounded
  · exfalso
    exact
      no_crossing K x A B hcompact hx hbounded hAclosed hBclosed
        hABdisjoint hcover T hTcompact hTconnected hTsubset hTA hTB

/-- Claim `S2-k6i-subcontinuum-forces-bounded-source`.

The residual U-indexed bounded-subcontinuum theorem is strictly lowered to the
x-indexed compact/frontier no-crossing source.  The remaining topology source
is exactly
`PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing`. -/
theorem S2_k6i_subcontinuum_forces_bounded_source
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded :=
  planarJaniszewskiBoundaryBumpingSubcontinuumForcesBounded_of_noCompactConnectedKCrossing
    no_crossing

set_option linter.style.longLine false in
/-- The U-indexed bounded-subcontinuum source is strictly lowered to the
aligned closed `K`-split source.

Once the component witness is opened, an unbounded closed split of the selected
frontier gives closed sets `K₁` and `K₂` covering `K`, with the two frontier
sides contained in the two closed pieces.  Any compact connected `T ⊆ K`
meeting both frontier sides is then separated by `T ∩ K₁` and `T ∩ K₂`. -/
theorem
    planarJaniszewskiBoundaryBumpingSubcontinuumForcesBounded_of_alignedKSplit
    (aligned_split :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded := by
  intro K U A B T hcompact hcomponent hAclosed hBclosed hABdisjoint hcover
    hTcompact hTconnected hTsubset hTA hTB
  rcases hcomponent with ⟨x, hx, rfl⟩
  by_cases hbounded : Bornology.IsBounded (connectedComponentIn Kᶜ x)
  · exact hbounded
  · exfalso
    rcases
        aligned_split K x A B hcompact hx hbounded hAclosed hBclosed
          hABdisjoint hcover with
      ⟨K₁, K₂, hK₁closed, hK₂closed, hKdisjoint, hKcover, hAK₁, hBK₂⟩
    have hTclosed : IsClosed T := hTcompact.isClosed
    have hleftClosed : IsClosed (T ∩ K₁) := hTclosed.inter hK₁closed
    have hrightClosed : IsClosed (T ∩ K₂) := hTclosed.inter hK₂closed
    have hdisjoint : Disjoint (T ∩ K₁) (T ∩ K₂) := by
      rw [Set.disjoint_left]
      intro p hpLeft hpRight
      exact (Set.disjoint_left.mp hKdisjoint) hpLeft.2 hpRight.2
    have hTcover : T = (T ∩ K₁) ∪ (T ∩ K₂) := by
      ext p
      constructor
      · intro hpT
        have hpK : p ∈ K := hTsubset hpT
        have hpKsplit : p ∈ K₁ ∪ K₂ := by
          simpa [hKcover] using hpK
        rcases hpKsplit with hpK₁ | hpK₂
        · exact Or.inl ⟨hpT, hpK₁⟩
        · exact Or.inr ⟨hpT, hpK₂⟩
      · intro hp
        rcases hp with hpLeft | hpRight
        · exact hpLeft.1
        · exact hpRight.1
    have hleftNonempty : (T ∩ K₁).Nonempty := by
      rcases hTA with ⟨a, haT, haA⟩
      exact ⟨a, haT, hAK₁ haA⟩
    have hrightNonempty : (T ∩ K₂).Nonempty := by
      rcases hTB with ⟨b, hbT, hbB⟩
      exact ⟨b, hbT, hBK₂ hbB⟩
    exact
      (noClosedSeparation_of_isPreconnected hTconnected.isPreconnected)
        (T ∩ K₁) (T ∩ K₂) hleftClosed hrightClosed hdisjoint hTcover
        hleftNonempty hrightNonempty

set_option linter.style.longLine false in
/-- Claim `S2-r4-subcontinuum-boundedness-aligned-split-20260521r4`.

The component-indexed Janiszewski boundedness leaf is lowered to the aligned
closed `K`-split theorem.  The adapter is topology support only: it opens the
component witness and uses connectedness of the displayed compact subcontinuum
against the induced closed split, without invoking final boundary-cycle rows. -/
theorem S2_r4_subcontinuum_boundedness_aligned_split_20260521r4
    (aligned_split :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded :=
  planarJaniszewskiBoundaryBumpingSubcontinuumForcesBounded_of_alignedKSplit
    aligned_split

set_option linter.style.longLine false in
/-- Claim `S2-r9-aligned-k-split-source-20260521r9`.

The full aligned closed `K`-split source is lowered to the nontrivial
open-cover separation primitive.  The existing topology API first converts
open neighborhoods of the two nonempty frontier pieces into a hard-case
aligned split; the owner-file adapter then handles empty frontier-side cases
without using final boundary-cycle rows. -/
theorem S2_r9_aligned_k_split_source_of_openKCover_20260521r9
    (open_cover :
      PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesOpenKCoverSeparation) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit :=
  planarContinuumUnboundedComplementFrontierAlignedKSplit_of_nontrivialAlignedKSplit
    (planarContinuumUnboundedComplementFrontierNontrivialAlignedKSplit_of_openKCoverSeparation
      open_cover)

set_option linter.style.longLine false in
/-- The U-indexed subcontinuum point-between source is lowered directly to
the x-indexed compact/frontier no-crossing primitive.

The no-crossing theorem rules out any compact connected subset of `K` crossing
a closed split of the selected unbounded component frontier; the existing
boundedness/crosscut adapter turns that into the standard Janiszewski
point-between witness. -/
theorem
    planarJaniszewskiBoundaryBumpingSubcontinuumPointsBetween_of_noCompactConnectedKCrossing_20260521k18
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween :=
  planarJaniszewskiBoundaryBumpingSubcontinuumPointsBetween_of_subcontinuumForcesBounded
    (S2_k6i_subcontinuum_forces_bounded_source no_crossing)

set_option linter.style.longLine false in
/-- Claim `S2-agent-topology-points-between-source-20260521k18`.

The current U-indexed point-between residual is strictly lowered to the
already isolated compact/frontier no-crossing planar-continuum primitive.  No
boundary-cycle rows, synthetic enclosure predicates, W-facing facade, or final
S2 wrapper is introduced. -/
theorem S2_agent_topology_points_between_source_20260521k18
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween :=
  planarJaniszewskiBoundaryBumpingSubcontinuumPointsBetween_of_noCompactConnectedKCrossing_20260521k18
    no_crossing

set_option linter.style.longLine false in
/-- The whole-frontier no-subcontinuum obstruction is exactly the compact
connected no-crossing theorem with the nonempty closed-side hypotheses
retained for the older obstruction surface.

This is the direct source-lowering step: a displayed compact connected
`T ⊆ K` meeting both closed frontier sides is already forbidden by
`PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing`.
The proof uses no relative-clopen side, boundedness alias, finite-drawing
consumer, W-facing facade, or final boundary-cycle row. -/
theorem
    planarContinuumUnboundedComplementFrontierNoSubcontinuumObstruction_of_noCompactConnectedKCrossing
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    _hAnonempty _hBnonempty T hTcompact hTconnected hTsubset hTA hTB
  exact
    no_crossing K x A B hcompact hx hunbounded hAclosed hBclosed
      hABdisjoint hcover T hTcompact hTconnected hTsubset hTA hTB

set_option linter.style.longLine false in
/-- Claim `S2-agent-topology-nosubcontinuum-source-20260521k15`.

The whole-frontier no-subcontinuum source is strictly lowered to the
compact/frontier no-crossing theorem, the residual immediately above the
standard compact-connected frontier point-between argument. -/
theorem S2_agent_topology_nosubcontinuum_source_20260521k15
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction :=
  planarContinuumUnboundedComplementFrontierNoSubcontinuumObstruction_of_noCompactConnectedKCrossing
    no_crossing

set_option linter.style.longLine false in
/-- The whole-frontier no-subcontinuum obstruction supplies the compact
connected `K`-crossing exclusion.

The target has no explicit nonempty-side hypotheses, but a compact connected
`T <= K` meeting both closed sides provides them immediately.  This is the
direct non-facade handoff from the older no-subcontinuum source to the current
no-compact-connected-crossing primitive. -/
theorem
    planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_noSubcontinuumObstruction
    (no_subcontinuum :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    T hTcompact hTconnected hTsubset hTA hTB
  have hAnonempty : A.Nonempty := by
    rcases hTA with ⟨y, _hyT, hyA⟩
    exact ⟨y, hyA⟩
  have hBnonempty : B.Nonempty := by
    rcases hTB with ⟨z, _hzT, hzB⟩
    exact ⟨z, hzB⟩
  exact
    no_subcontinuum K x A B hcompact hx hunbounded hAclosed hBclosed
      hABdisjoint hcover hAnonempty hBnonempty T hTcompact hTconnected
      hTsubset hTA hTB

set_option linter.style.longLine false in
/-- Direct x-indexed no-crossing lowerer from the U-indexed Janiszewski
no-subcontinuum obstruction.

This is the narrow boundary-bumping source for the compact/frontier
no-crossing primitive: after specializing `U` to
`connectedComponentIn Kᶜ x`, the only extra data needed by the Janiszewski
surface is nonemptiness of the two closed frontier sides, supplied by the
displayed compact connected `T ⊆ K` crossing them. -/
theorem
    planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_janiszewskiNoSubcontinuumObstruction_20260521current2
    (no_subcontinuum :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    T hTcompact hTconnected hTsubset hTA hTB
  have hAnonempty : A.Nonempty := by
    rcases hTA with ⟨y, _hyT, hyA⟩
    exact ⟨y, hyA⟩
  have hBnonempty : B.Nonempty := by
    rcases hTB with ⟨z, _hzT, hzB⟩
    exact ⟨z, hzB⟩
  exact
    no_subcontinuum K (connectedComponentIn Kᶜ x) A B hcompact
      ⟨x, hx, rfl⟩ hunbounded hAclosed hBclosed hABdisjoint hcover
      hAnonempty hBnonempty T hTcompact hTconnected hTsubset hTA hTB

set_option linter.style.longLine false in
/-- Claim `S2-subagent-no-compact-crossing-primitive-20260521-current2`.

The compact/frontier no-crossing primitive is strictly lowered to the direct
U-indexed Janiszewski no-subcontinuum boundary-bumping source, without routing
through boundedness, carrier rows, boundary-cycle rows, actual-sector rows, or
W32 consumers. -/
theorem S2_subagent_no_compact_crossing_primitive_20260521_current2
    (no_subcontinuum :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_janiszewskiNoSubcontinuumObstruction_20260521current2
    no_subcontinuum

set_option linter.style.longLine false in
/-- q20 whole-frontier no-subcontinuum source from the same-`K`
Janiszewski point-between primitive.

The composition first applies the checked c6 point-between/no-subcontinuum
reducer, then specializes the U-indexed Janiszewski obstruction to
`connectedComponentIn Kᶜ x`. -/
theorem
    planarContinuumUnboundedComplementFrontierNoSubcontinuumObstruction_of_janiszewskiKComponentPointsBetween_20260522q20
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction :=
  planarContinuumUnboundedComplementFrontierNoSubcontinuumObstruction_of_janiszewskiNoSubcontinuumObstruction
    (planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_kComponentPointsBetween_20260521c6
      points_between)

set_option linter.style.longLine false in
/-- Claim `S2-q20-no-subcontinuum-obstruction-source`.

The planar-continuum whole-frontier no-subcontinuum obstruction is strictly
lowered to
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween`,
with no boundary-cycle, carrier, raw-orbit, actual-sector, or W32 rows. -/
theorem S2_q20_no_subcontinuum_obstruction_source_of_kComponentPointsBetween_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction :=
  planarContinuumUnboundedComplementFrontierNoSubcontinuumObstruction_of_janiszewskiKComponentPointsBetween_20260522q20
    points_between

set_option linter.style.longLine false in
/-- Claim `S2-q21-janiszewski-k-points-source`.

The q20 no-subcontinuum source is pushed one step lower than the same-`K`
point-between surface: the remaining planar topology theorem is the primitive
frontier-component statement saying that two same-`K` frontier points lie in
the same component of the selected frontier.  The only added work is the
Mathlib connected-component/witness-packaging equivalence in
`ExteriorComponentTopology`. -/
theorem S2_q21_no_subcontinuum_obstruction_source_of_kComponentFrontierComponent_20260522
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction :=
  S2_q20_no_subcontinuum_obstruction_source_of_kComponentPointsBetween_20260522
    (planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_frontierComponent
      frontier_component)

set_option linter.style.longLine false in
/-- Claim `S2-q21-janiszewski-k-points-source`, source equivalence form. -/
theorem S2_q21_janiszewski_kComponentPointsBetween_iff_frontierComponent_20260522 :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween ↔
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
  planarJaniszewskiBoundaryBumpingKComponentPointsBetween_iff_frontierComponent_20260522q21

set_option linter.style.longLine false in
/-- Direct Janiszewski bounded-subcontinuum lowerer from the x-indexed
nontrivial relative-clopen `K`-side source.

If the selected complement component were unbounded, the two closed frontier
sides crossed by the compact connected `T <= K` are nonempty.  The
relative-clopen source then supplies a closed `K`-side containing `A` and
disjoint from `B`; intersecting that side and its complement with `T`
separates `T`, contradicting connectedness.  This is a genuine topology
reducer for the boundedness leaf, with no W-facing facade, finite boundary
cycle row, or final S2 assumption. -/
theorem
    planarJaniszewskiBoundaryBumpingSubcontinuumForcesBounded_of_nontrivialRelativeClopenKSide_20260521current3
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded := by
  intro K U A B T hcompact hcomponent hAclosed hBclosed hABdisjoint hcover
    hTcompact hTconnected hTsubset hTA hTB
  by_cases hbounded : Bornology.IsBounded U
  · exact hbounded
  · exfalso
    rcases hcomponent with ⟨x, hx, rfl⟩
    have hAnonempty : A.Nonempty := by
      rcases hTA with ⟨a, _haT, haA⟩
      exact ⟨a, haA⟩
    have hBnonempty : B.Nonempty := by
      rcases hTB with ⟨b, _hbT, hbB⟩
      exact ⟨b, hbB⟩
    rcases
        nontrivial_side K x A B hcompact hx hbounded hAclosed hBclosed
          hABdisjoint hcover hAnonempty hBnonempty with
      ⟨K1, _hK1subset, hK1closed, hKdiffclosed, hAK1, hK1Bdisjoint⟩
    have hTclosed : IsClosed T := hTcompact.isClosed
    have hleftClosed : IsClosed (T ∩ K1) := hTclosed.inter hK1closed
    have hrightClosed : IsClosed (T ∩ (K \ K1)) :=
      hTclosed.inter hKdiffclosed
    have hdisjoint : Disjoint (T ∩ K1) (T ∩ (K \ K1)) := by
      rw [Set.disjoint_left]
      intro p hpLeft hpRight
      exact hpRight.2.2 hpLeft.2
    have hTcover : T = (T ∩ K1) ∪ (T ∩ (K \ K1)) := by
      ext p
      constructor
      · intro hpT
        by_cases hpK1 : p ∈ K1
        · exact Or.inl ⟨hpT, hpK1⟩
        · exact Or.inr ⟨hpT, hTsubset hpT, hpK1⟩
      · intro hp
        rcases hp with hpLeft | hpRight
        · exact hpLeft.1
        · exact hpRight.1
    have hleftNonempty : (T ∩ K1).Nonempty := by
      rcases hTA with ⟨a, haT, haA⟩
      exact ⟨a, haT, hAK1 haA⟩
    have hrightNonempty : (T ∩ (K \ K1)).Nonempty := by
      rcases hTB with ⟨b, hbT, hbB⟩
      exact
        ⟨b, hbT, hTsubset hbT,
          fun hbK1 => (Set.disjoint_left.mp hK1Bdisjoint) hbK1 hbB⟩
    exact
      (noClosedSeparation_of_isPreconnected hTconnected.isPreconnected)
        (T ∩ K1) (T ∩ (K \ K1))
        hleftClosed hrightClosed hdisjoint hTcover hleftNonempty hrightNonempty

set_option linter.style.longLine false in
/-- Claim `S2-subagent-janiszewski-source-20260521-current3`.

The component-indexed Janiszewski bounded-subcontinuum source is strictly
lowered to the x-indexed nontrivial relative-clopen `K`-side primitive.  The
remaining source is
`PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide`. -/
theorem S2_subagent_janiszewski_source_20260521_current3
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded :=
  planarJaniszewskiBoundaryBumpingSubcontinuumForcesBounded_of_nontrivialRelativeClopenKSide_20260521current3
    nontrivial_side

set_option linter.style.longLine false in
/-- Claim `S2-q7-no-compact-connected-K-crossing-source-20260521q2`.

The first remaining topology primitive
`PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing`
is strictly lowered to the component-indexed Janiszewski
crossing-subcontinuum boundedness source.  The composition uses the existing
boundedness-to-no-subcontinuum reducer and the whole-frontier
Janiszewski/no-subcontinuum specialization; it introduces no finite boundary
cycle rows, W32 assumptions, actual-sector rows, or route facade. -/
theorem S2_q7_no_compact_connected_K_crossing_source_20260521q2
    (subcontinuum_forces_bounded :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_noSubcontinuumObstruction
    (S2_codex_20260520_whole_frontier_no_subcontinuum_janiszewski_reducer
      (planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_subcontinuumForcesBounded
        subcontinuum_forces_bounded))

set_option linter.style.longLine false in
/-- Claim `S2-p2o-exterior-component-topology-source-worker-20260521p4`.

The compact/frontier no-crossing source is lowered directly to the existing
nontrivial relative-clopen `K`-side theorem.  Given a compact connected
`T <= K` meeting both frontier sides, the relative-clopen side `K1` separates
`T` into the two closed pieces `T ∩ K1` and `T ∩ (K \ K1)`, contradicting
connectedness of `T`.  This avoids the same-`K` frontier-component route,
finite boundary rows, and W32 composers. -/
theorem S2_p2o_no_compact_connected_K_crossing_source_20260521p4
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    T hTcompact hTconnected hTsubset hTA hTB
  have hAnonempty : A.Nonempty := by
    rcases hTA with ⟨y, _hyT, hyA⟩
    exact ⟨y, hyA⟩
  have hBnonempty : B.Nonempty := by
    rcases hTB with ⟨z, _hzT, hzB⟩
    exact ⟨z, hzB⟩
  rcases
      nontrivial_side K x A B hcompact hx hunbounded hAclosed hBclosed
        hABdisjoint hcover hAnonempty hBnonempty with
    ⟨K1, _hK1subset, hK1closed, hKdiffclosed, hAK1, hK1Bdisjoint⟩
  have hTclosed : IsClosed T := hTcompact.isClosed
  have hleftClosed : IsClosed (T ∩ K1) := hTclosed.inter hK1closed
  have hrightClosed : IsClosed (T ∩ (K \ K1)) := hTclosed.inter hKdiffclosed
  have hdisjoint : Disjoint (T ∩ K1) (T ∩ (K \ K1)) := by
    rw [Set.disjoint_left]
    intro p hpLeft hpRight
    exact hpRight.2.2 hpLeft.2
  have hTcover : T = (T ∩ K1) ∪ (T ∩ (K \ K1)) := by
    ext p
    constructor
    · intro hpT
      by_cases hpK1 : p ∈ K1
      · exact Or.inl ⟨hpT, hpK1⟩
      · exact Or.inr ⟨hpT, hTsubset hpT, hpK1⟩
    · intro hp
      rcases hp with hpLeft | hpRight
      · exact hpLeft.1
      · exact hpRight.1
  have hleftNonempty : (T ∩ K1).Nonempty := by
    rcases hTA with ⟨y, hyT, hyA⟩
    exact ⟨y, hyT, hAK1 hyA⟩
  have hrightNonempty : (T ∩ (K \ K1)).Nonempty := by
    rcases hTB with ⟨z, hzT, hzB⟩
    have hznotK1 : z ∉ K1 := by
      intro hzK1
      exact (Set.disjoint_left.mp hK1Bdisjoint) hzK1 hzB
    exact ⟨z, hzT, hTsubset hzT, hznotK1⟩
  exact
    (noClosedSeparation_of_isPreconnected hTconnected.isPreconnected)
      (T ∩ K1) (T ∩ (K \ K1)) hleftClosed hrightClosed hdisjoint
      hTcover hleftNonempty hrightNonempty

set_option linter.style.longLine false in
/-- Convenience composition of the k6i source from the existing crossing
point-between theorem.

This keeps the no-crossing theorem as the explicit intermediate residual; it
does not use the boundedness/no-subcontinuum equivalence or any downstream W32
consumer. -/
theorem S2_k6i_subcontinuum_forces_bounded_source_of_crossingPointsBetween
    (points_between :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded :=
  S2_k6i_subcontinuum_forces_bounded_source
    (planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_pointsBetween
      points_between)

set_option linter.style.longLine false in
/-- Claim `S2-k6k-relative-clopen-K-side-source`.

The component-witness Janiszewski relative-clopen `K`-side theorem is strictly
lowered to the x-indexed no-compact-connected-crossing source.  The proof
opens no finite-drawing or final-cycle route: no-crossing gives the U-indexed
bounded-subcontinuum theorem, boundedness gives the Janiszewski
no-subcontinuum obstruction, and the existing compact-Hausdorff separator
produces the relative-clopen side.  The exact remaining topology residual is
`PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing`. -/
theorem S2_k6k_relative_clopen_K_side_source
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide :=
  planarJaniszewskiBoundaryBumpingRelativeClopenKSide_of_noSubcontinuumObstruction
    (planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_subcontinuumForcesBounded
      (S2_k6i_subcontinuum_forces_bounded_source no_crossing))

set_option linter.style.longLine false in
/-- Direct x-indexed relative-clopen `K`-side source from the compact/frontier
no-crossing topology primitive.

For a nonempty closed split of the selected unbounded-component frontier, the
frontier-subset lemma places both closed sides inside `K`.  The existing
compact Hausdorff clopen separator
`exists_relative_clopen_separator_of_no_subcontinuum` then applies because the
no-crossing primitive forbids every compact connected subset of `K` from
meeting both sides. -/
theorem
    planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_noCompactConnectedKCrossing_20260521r7b
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    _hAnonempty _hBnonempty
  have hfrontier_subset_K :
      frontier (connectedComponentIn Kᶜ x) ⊆ K :=
    planarContinuumUnboundedComplement_frontier_subset
      (K := K) (x := x) hcompact
  have hAK : A ⊆ K := by
    intro y hyA
    exact hfrontier_subset_K (by
      rw [hcover]
      exact Or.inl hyA)
  have hBK : B ⊆ K := by
    intro y hyB
    exact hfrontier_subset_K (by
      rw [hcover]
      exact Or.inr hyB)
  exact
    exists_relative_clopen_separator_of_no_subcontinuum
      (K := K) (A := A) (B := B)
      hcompact hAclosed hBclosed hAK hBK
      (by
        intro T hTcompact hTconnected hTsubset hTA hTB
        exact
          no_crossing K x A B hcompact hx hunbounded hAclosed hBclosed
            hABdisjoint hcover T hTcompact hTconnected hTsubset hTA hTB)

set_option linter.style.longLine false in
/-- Claim `S2-r7b-relative-clopen-k-side-topology-source`.

The x-indexed nontrivial relative-clopen `K`-side source is strictly lowered to
the already isolated compact/frontier no-crossing topology primitive.  The
checked proof is only frontier containment plus the compact Hausdorff clopen
separator; it uses no boundary-cycle rows, actual-sector rows, W32 consumers,
induced frontier graphs, or arbitrary cycles. -/
theorem S2_r7b_relative_clopen_k_side_topology_source_20260521r7b
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
  planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_noCompactConnectedKCrossing_20260521r7b
    no_crossing

set_option linter.style.longLine false in
/-- Point-between convenience form of `S2_k6k_relative_clopen_K_side_source`.

This keeps the primitive no-crossing theorem visible while recording the
standard way to source it from point-level boundary bumping. -/
theorem S2_k6k_relative_clopen_K_side_source_of_crossingPointsBetween
    (points_between :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide :=
  S2_k6k_relative_clopen_K_side_source
    (planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_pointsBetween
      points_between)

set_option linter.style.longLine false in
/-- The Janiszewski component-avoidance source is strictly lowered to the
x-indexed no-compact-connected-`K`-crossing topology source.

This is the n1 source handoff: the existing k6k reducer gets the
relative-clopen `K`-side from no-crossing, and the checked compact-Hausdorff
component-avoidance adapter consumes that side. -/
theorem
    planarJaniszewskiBoundaryBumpingComponentAvoidance_of_noCompactConnectedKCrossing_20260521n1
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance :=
  planarJaniszewskiBoundaryBumpingComponentAvoidance_of_relativeClopenKSide
    (S2_k6k_relative_clopen_K_side_source no_crossing)

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-component-avoidance-source-20260521n1`.

The live component-avoidance topology leaf is now below the same primitive
no-compact-connected-`K`-crossing source used by the k6k route; no W32 facade,
final boundary-cycle, induced frontier graph, arbitrary cycle, or synthetic
enclosure row is introduced. -/
theorem S2_dynamic_component_avoidance_source_20260521n1
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance :=
  planarJaniszewskiBoundaryBumpingComponentAvoidance_of_noCompactConnectedKCrossing_20260521n1
    no_crossing

set_option linter.style.longLine false in
/-- Claim `S2-k6l-no-compact-connected-K-crossing-source`.

The k6k residual compact/frontier no-crossing theorem is strictly lowered to
the U-indexed pair frontier-component boundary-bumping source.  Given a
compact connected `T <= K` crossing the two closed sides, the source places the
two selected frontier points in the same component of `frontier U`; the image
of that component is a compact connected subset of the frontier meeting both
sides, contradicting the displayed closed separation.  The exact remaining
topology residual is
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent`. -/
theorem S2_k6l_no_compact_connected_K_crossing_source
    (pair_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    T hTcompact hTconnected hTsubset hTA hTB
  rcases hTA with ⟨y, hyT, hyA⟩
  rcases hTB with ⟨z, hzT, hzB⟩
  let U : Set PlanarInterface.Point := connectedComponentIn Kᶜ x
  have hyFrontier : y ∈ frontier U := by
    rw [hcover]
    exact Or.inl hyA
  have hzFrontier : z ∈ frontier U := by
    rw [hcover]
    exact Or.inr hzB
  have hFcompact : IsCompact (frontier U) := by
    dsimp [U]
    exact
      planarContinuumUnboundedComplement_frontier_compact
        (K := K) (x := x) hcompact
  haveI : CompactSpace (frontier U) := isCompact_iff_compactSpace.mp hFcompact
  let yF : frontier U := ⟨y, hyFrontier⟩
  let S : Set PlanarInterface.Point := Subtype.val '' connectedComponent yF
  have hz_component :
      (⟨z, hzFrontier⟩ : frontier U) ∈ connectedComponent yF := by
    simpa [U, yF] using
      pair_component K U T y z hcompact ⟨x, hx, rfl⟩ hunbounded hTcompact
        hTconnected hTsubset hyT hzT hyFrontier hzFrontier
  have hScompact : IsCompact S :=
    isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hSconnected : IsConnected S :=
    isConnected_connectedComponent.image Subtype.val
      continuous_subtype_val.continuousOn
  have hSsubset : S ⊆ frontier U := by
    intro p hpS
    rcases hpS with ⟨pF, _hp_component, rfl⟩
    exact pF.property
  have hyS : y ∈ S := ⟨yF, mem_connectedComponent, rfl⟩
  have hzS : z ∈ S := ⟨⟨z, hzFrontier⟩, hz_component, rfl⟩
  have hSclosed : IsClosed S := hScompact.isClosed
  have hleftClosed : IsClosed (S ∩ A) := hSclosed.inter hAclosed
  have hrightClosed : IsClosed (S ∩ B) := hSclosed.inter hBclosed
  have hdisjoint : Disjoint (S ∩ A) (S ∩ B) := by
    rw [Set.disjoint_left]
    intro p hpLeft hpRight
    exact (Set.disjoint_left.mp hABdisjoint) hpLeft.2 hpRight.2
  have hScover : S = (S ∩ A) ∪ (S ∩ B) := by
    ext p
    constructor
    · intro hpS
      have hpFrontier : p ∈ frontier U := hSsubset hpS
      have hpAB : p ∈ A ∪ B := by
        simpa [U, hcover] using hpFrontier
      rcases hpAB with hpA | hpB
      · exact Or.inl ⟨hpS, hpA⟩
      · exact Or.inr ⟨hpS, hpB⟩
    · intro hp
      rcases hp with hpLeft | hpRight
      · exact hpLeft.1
      · exact hpRight.1
  exact
    (noClosedSeparation_of_isPreconnected hSconnected.isPreconnected)
      (S ∩ A) (S ∩ B) hleftClosed hrightClosed hdisjoint hScover
      ⟨y, hyS, hyA⟩ ⟨z, hzS, hzB⟩

set_option linter.style.longLine false in
/-- Claim `S2-agent-topology-noCompact-source-20260521k16`.

The compact/frontier no-crossing source is strictly lowered to the U-indexed
pair frontier-component topology primitive.  This is just the checked topology
composition through `S2_k6l_no_compact_connected_K_crossing_source`; it does not
use boundary-cycle rows, W-facing facades, or synthetic enclosure predicates. -/
theorem S2_agent_topology_noCompact_source_20260521k16
    (pair_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  S2_k6l_no_compact_connected_K_crossing_source pair_component

set_option linter.style.longLine false in
/-- Claim `S2-agent-topology-noCompact-source-20260521k19`.

The compact/frontier no-crossing source is lowered directly to the U-indexed
subcontinuum pair frontier-component primitive.  A compact connected `T`
crossing a closed frontier split supplies two frontier points in the same
frontier component; the image of that component is compact connected and
crosses the split, contradicting the displayed closed separation. -/
theorem S2_agent_topology_noCompact_source_20260521k19
    (pair_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    T hTcompact hTconnected hTsubset hTA hTB
  rcases hTA with ⟨y, hyT, hyA⟩
  rcases hTB with ⟨z, hzT, hzB⟩
  let U : Set PlanarInterface.Point := connectedComponentIn Kᶜ x
  have hyFrontier : y ∈ frontier U := by
    rw [hcover]
    exact Or.inl hyA
  have hzFrontier : z ∈ frontier U := by
    rw [hcover]
    exact Or.inr hzB
  have hFcompact : IsCompact (frontier U) := by
    dsimp [U]
    exact
      planarContinuumUnboundedComplement_frontier_compact
        (K := K) (x := x) hcompact
  haveI : CompactSpace (frontier U) := isCompact_iff_compactSpace.mp hFcompact
  let yF : frontier U := ⟨y, hyFrontier⟩
  let S : Set PlanarInterface.Point := Subtype.val '' connectedComponent yF
  have hz_component :
      (⟨z, hzFrontier⟩ : frontier U) ∈ connectedComponent yF := by
    simpa [U, yF] using
      pair_component K U T y z hcompact ⟨x, hx, rfl⟩ hunbounded hTcompact
        hTconnected hTsubset hyT hzT hyFrontier hzFrontier
  have hScompact : IsCompact S :=
    isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hSconnected : IsConnected S :=
    isConnected_connectedComponent.image Subtype.val
      continuous_subtype_val.continuousOn
  have hSsubset : S ⊆ frontier U := by
    intro p hpS
    rcases hpS with ⟨pF, _hp_component, rfl⟩
    exact pF.property
  have hyS : y ∈ S := ⟨yF, mem_connectedComponent, rfl⟩
  have hzS : z ∈ S := ⟨⟨z, hzFrontier⟩, hz_component, rfl⟩
  have hSclosed : IsClosed S := hScompact.isClosed
  have hleftClosed : IsClosed (S ∩ A) := hSclosed.inter hAclosed
  have hrightClosed : IsClosed (S ∩ B) := hSclosed.inter hBclosed
  have hdisjoint : Disjoint (S ∩ A) (S ∩ B) := by
    rw [Set.disjoint_left]
    intro p hpLeft hpRight
    exact (Set.disjoint_left.mp hABdisjoint) hpLeft.2 hpRight.2
  have hScover : S = (S ∩ A) ∪ (S ∩ B) := by
    ext p
    constructor
    · intro hpS
      have hpFrontier : p ∈ frontier U := hSsubset hpS
      have hpAB : p ∈ A ∪ B := by
        simpa [U, hcover] using hpFrontier
      rcases hpAB with hpA | hpB
      · exact Or.inl ⟨hpS, hpA⟩
      · exact Or.inr ⟨hpS, hpB⟩
    · intro hp
      rcases hp with hpLeft | hpRight
      · exact hpLeft.1
      · exact hpRight.1
  exact
    (noClosedSeparation_of_isPreconnected hSconnected.isPreconnected)
      (S ∩ A) (S ∩ B) hleftClosed hrightClosed hdisjoint hScover
      ⟨y, hyS, hyA⟩ ⟨z, hzS, hzB⟩

set_option linter.style.longLine false in
/-- The compact/frontier no-crossing source is strictly lowered to the
same-`K` Janiszewski frontier-component theorem.

This composes the existing frontier-component packaging with the checked
point-between-to-no-crossing reducer.  The residual is the direct
Janiszewski same-`K` frontier-component source, not component avoidance,
relative-clopen side data, finite frontier rows, or a final boundary-cycle
consumer. -/
theorem
    planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_janiszewskiKComponentFrontierComponent_20260521n9
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_pointsBetween
    (planarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween_of_frontierComponent
      (planarContinuumUnboundedComplementFrontierCrossingSubcontinuumFrontierComponent_of_janiszewskiKComponentFrontierComponent
        frontier_component))

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-no-compact-crossing-source-20260521n9`.

The live no-compact-connected-`K`-crossing topology leaf is lowered below the
same-`K` Janiszewski frontier-component source. -/
theorem S2_dynamic_no_compact_crossing_source_20260521n9
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_janiszewskiKComponentFrontierComponent_20260521n9
    frontier_component

set_option linter.style.longLine false in
/-- Finite-drawing no-closed-separation from the compact continuum
no-crossing topology leaf.

This is the direct topology-only handoff used by the older local-sector route:
no compact connected `K`-crossing gives frontier preconnectedness, hence no
closed separation, and then specializes to the finite embedded unit-edge
drawing. -/
theorem S2_r5f_local_topology_no_closed_source_20260521r5f
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_planarContinuum
    (planarContinuumUnboundedComplementFrontierNoClosedSeparation_of_preconnected
      (planarContinuumUnboundedComplementFrontierPreconnected_of_noCompactConnectedKCrossing
        no_crossing))

set_option linter.style.longLine false in
/-- Direct finite-drawing boundedness source from compact/frontier no-crossing.

For a nonempty closed split of an unbounded complement-component frontier in
the actual embedded drawing, both split sides lie in `embeddedEdgeSet C`.
Taking the whole embedded drawing as the compact connected subset of `K`
therefore contradicts the no-compact-connected-`K`-crossing theorem.  This
feeds the finite no-closed-separation route through the sharper boundedness
residual instead of the planar preconnectedness adapter. -/
theorem
    finiteDrawingUnboundedComplementFrontierClosedSeparationForcesBounded_of_noCompactConnectedKCrossing_20260521current
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesBounded := by
  intro n C inputs x A B hx hAclosed hBclosed hABdisjoint hcover
    hAnonempty hBnonempty
  by_cases hbounded :
      Bornology.IsBounded (connectedComponentIn (embeddedEdgeSet C)ᶜ x)
  · exact hbounded
  · exfalso
    let K : Set PlanarInterface.Point := embeddedEdgeSet C
    let U : Set PlanarInterface.Point := connectedComponentIn Kᶜ x
    rcases hAnonempty with ⟨a, haA⟩
    rcases hBnonempty with ⟨b, hbB⟩
    have hfrontier_subset_K : frontier U ⊆ K := by
      simpa [K, U] using
        (planarContinuumUnboundedComplement_frontier_subset
          (K := embeddedEdgeSet C) (x := x) (embeddedEdgeSet_compact C))
    have hTA : (K ∩ A).Nonempty := by
      have haFrontier : a ∈ frontier U := by
        simpa [K, U, hcover] using Or.inl haA
      exact ⟨a, hfrontier_subset_K haFrontier, haA⟩
    have hTB : (K ∩ B).Nonempty := by
      have hbFrontier : b ∈ frontier U := by
        simpa [K, U, hcover] using Or.inr hbB
      exact ⟨b, hfrontier_subset_K hbFrontier, hbB⟩
    exact
      no_crossing K x A B
        (embeddedEdgeSet_compact C)
        (by simpa [K] using hx)
        (by simpa [K, U] using hbounded)
        hAclosed hBclosed hABdisjoint
        (by simpa [K, U] using hcover)
        K
        (embeddedEdgeSet_compact C)
        (embeddedEdgeSet_connected_of_inputs inputs)
        subset_rfl
        hTA
        hTB

set_option linter.style.longLine false in
/-- Claim `S2-subagent-topology-source-20260521-current`, finite route.

The finite no-closed-separation leaf feeding the exterior-sector source route
is lowered through the finite boundedness residual, sourced directly from
`PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing`.
No boundary-cycle rows, actual-sector rows, induced frontier graph, W-facing
facade, or final S2 conclusion is used. -/
theorem S2_subagent_topology_source_20260521_current_finiteDrawing_noClosedSeparation_of_noCompactConnectedKCrossing
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_closedSeparationForcesBounded
    (finiteDrawingUnboundedComplementFrontierClosedSeparationForcesBounded_of_noCompactConnectedKCrossing_20260521current
      no_crossing)

set_option linter.style.longLine false in
/-- Finite-drawing frontier preconnectedness from the finite boundedness
residual.

This is the preconnected form of the finite no-closed-separation route: the
boundedness residual rules out nonempty closed splits of an unbounded
complement frontier, and the standard closed-piece criterion converts that to
preconnectedness. -/
theorem finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteClosedSeparationForcesBounded_20260522
    (closed_split_forces_bounded :
      FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesBounded) :
    FiniteDrawingUnboundedComplementFrontierPreconnected :=
  finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
    (finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_closedSeparationForcesBounded
      closed_split_forces_bounded)

set_option linter.style.longLine false in
/-- Claim `S2-r14-frontier-preconnected-topology-source`, finite boundedness
residual.

The finite frontier-preconnectedness leaf is lowered through the same
boundedness-contradiction residual obtained from compact/frontier
no-compact-connected-`K`-crossing.  This stays on the topology support side and
does not use boundary-cycle, actual-sector, carrier, W32, or
induced-frontier-graph rows. -/
theorem S2_r14_finiteDrawing_frontierPreconnected_of_noCompactConnectedKCrossing_20260522
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    FiniteDrawingUnboundedComplementFrontierPreconnected :=
  finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteClosedSeparationForcesBounded_20260522
    (finiteDrawingUnboundedComplementFrontierClosedSeparationForcesBounded_of_noCompactConnectedKCrossing_20260521current
      no_crossing)

set_option linter.style.longLine false in
/-- Finite-drawing no-open-separation from the finite boundedness residual.

This is the open-set form of the same finite topology source used above for
no-closed-separation: a nonempty closed split of an unbounded complement
frontier would force the selected component to be bounded, so the frontier is
preconnected, hence has no open separation. -/
theorem finiteDrawingUnboundedComplementFrontierNoOpenSeparation_of_finiteClosedSeparationForcesBounded_20260522
    (closed_split_forces_bounded :
      FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesBounded) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
  finiteDrawingUnboundedComplementFrontierNoOpenSeparation_of_frontierPreconnected
    (finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
      (finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_closedSeparationForcesBounded
        closed_split_forces_bounded))

set_option linter.style.longLine false in
/-- Claim `S2-r14-no-open-separation-topology-source`, finite boundedness
residual.

The finite no-open-separation leaf is lowered through the finite
boundedness-contradiction residual obtained from compact/frontier
no-compact-connected-`K`-crossing.  This keeps the proof on the topology
support side and introduces no boundary-cycle, actual-sector, carrier, W32, or
induced-frontier-graph row. -/
theorem S2_r14_finiteDrawing_noOpenSeparation_of_noCompactConnectedKCrossing_20260522
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
  finiteDrawingUnboundedComplementFrontierNoOpenSeparation_of_finiteClosedSeparationForcesBounded_20260522
    (finiteDrawingUnboundedComplementFrontierClosedSeparationForcesBounded_of_noCompactConnectedKCrossing_20260521current
      no_crossing)

set_option linter.style.longLine false in
/-- Claim `S2-r53-topology-no-compact-connected-kcrossing-source-20260521r53`.

The finite-drawing no-closed-separation leaf is lowered directly to the
U-indexed subcontinuum pair frontier-component primitive.  For a nonempty
closed split of an unbounded finite-drawing complement frontier, the primitive
puts one point from each side in the same frontier component; the image of that
component is compact connected and is separated by the displayed closed split,
a contradiction.  This uses only finite drawing compactness/connectedness and
frontier-component topology, with no boundary cycle, actual-sector rows, W32
composer, or induced frontier graph. -/
theorem S2_r53_finiteDrawing_noClosedSeparation_of_pairFrontierComponent_20260521r53
    (pair_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation := by
  intro n C inputs x hx hunbounded A B hAclosed hBclosed hABdisjoint hcover
    hAnonempty hBnonempty
  let K : Set PlanarInterface.Point := embeddedEdgeSet C
  let U : Set PlanarInterface.Point := connectedComponentIn Kᶜ x
  rcases hAnonempty with ⟨a, haA⟩
  rcases hBnonempty with ⟨b, hbB⟩
  have hfrontier_subset_K : frontier U ⊆ K := by
    simpa [K, U] using
      finiteDrawingUnboundedComplement_frontier_subset_embeddedEdgeSet C x
  have haFrontier : a ∈ frontier U := by
    simpa [K, U, hcover] using Or.inl haA
  have hbFrontier : b ∈ frontier U := by
    simpa [K, U, hcover] using Or.inr hbB
  have haK : a ∈ K := hfrontier_subset_K haFrontier
  have hbK : b ∈ K := hfrontier_subset_K hbFrontier
  have hFcompact : IsCompact (frontier U) := by
    dsimp [K, U]
    exact
      planarContinuumUnboundedComplement_frontier_compact
        (K := embeddedEdgeSet C) (x := x) (embeddedEdgeSet_compact C)
  haveI : CompactSpace (frontier U) := isCompact_iff_compactSpace.mp hFcompact
  let aF : frontier U := ⟨a, haFrontier⟩
  let S : Set PlanarInterface.Point := Subtype.val '' connectedComponent aF
  have hb_component :
      (⟨b, hbFrontier⟩ : frontier U) ∈ connectedComponent aF := by
    simpa [K, U, aF] using
      pair_component K U K a b (embeddedEdgeSet_compact C)
        ⟨x, by simpa [K] using hx, rfl⟩
        (by simpa [K, U] using hunbounded)
        (embeddedEdgeSet_compact C)
        (embeddedEdgeSet_connected_of_inputs inputs)
        subset_rfl haK hbK haFrontier hbFrontier
  have hScompact : IsCompact S :=
    isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hSconnected : IsConnected S :=
    isConnected_connectedComponent.image Subtype.val
      continuous_subtype_val.continuousOn
  have hSsubset : S ⊆ frontier U := by
    intro p hpS
    rcases hpS with ⟨pF, _hp_component, rfl⟩
    exact pF.property
  have haS : a ∈ S := ⟨aF, mem_connectedComponent, rfl⟩
  have hbS : b ∈ S := ⟨⟨b, hbFrontier⟩, hb_component, rfl⟩
  have hSclosed : IsClosed S := hScompact.isClosed
  have hleftClosed : IsClosed (S ∩ A) := hSclosed.inter hAclosed
  have hrightClosed : IsClosed (S ∩ B) := hSclosed.inter hBclosed
  have hdisjoint : Disjoint (S ∩ A) (S ∩ B) := by
    rw [Set.disjoint_left]
    intro p hpLeft hpRight
    exact (Set.disjoint_left.mp hABdisjoint) hpLeft.2 hpRight.2
  have hScover : S = (S ∩ A) ∪ (S ∩ B) := by
    ext p
    constructor
    · intro hpS
      have hpFrontier : p ∈ frontier U := hSsubset hpS
      have hpAB : p ∈ A ∪ B := by
        simpa [K, U, hcover] using hpFrontier
      rcases hpAB with hpA | hpB
      · exact Or.inl ⟨hpS, hpA⟩
      · exact Or.inr ⟨hpS, hpB⟩
    · intro hp
      rcases hp with hpLeft | hpRight
      · exact hpLeft.1
      · exact hpRight.1
  exact
    (noClosedSeparation_of_isPreconnected hSconnected.isPreconnected)
      (S ∩ A) (S ∩ B) hleftClosed hrightClosed hdisjoint hScover
      ⟨a, haS, haA⟩ ⟨b, hbS, hbB⟩

set_option linter.style.longLine false in
/-- Claim `S2-r59-topology-pair-frontier-source-20260521r59`, finite
no-closed side.

The direct finite-drawing no-closed-separation support source is lowered through
the r59 pair-frontier reducer.  The exact remaining theorem is
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween`;
the proof uses only finite drawing compactness/connectedness and Mathlib
connected-component/no-closed-separation bookkeeping, with no boundary-cycle
rows, actual-sector rows, final S2 rows, W/facade consumers, or induced
frontier graph. -/
theorem S2_r59_finiteDrawing_noClosedSeparation_of_kComponentPointsBetween_20260521r59
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  S2_r53_finiteDrawing_noClosedSeparation_of_pairFrontierComponent_20260521r53
    (S2_r59_pair_frontier_component_of_kComponentPointsBetween_20260521r59
      points_between)

set_option linter.style.longLine false in
/-- Claim `S2-r6z-topology-kcomponent-points-between-source`.

The same-`K` Janiszewski point-between leaf is strictly reduced to the
x-indexed nontrivial relative-clopen `K`-side source.  The checked lowerer in
`ExteriorComponentTopology` opens the complement-component witness and uses
the compact-Hausdorff connected-component/clopen separator
(`connectedComponent_eq_iInter_isClopen`) to turn that side source into the
frontier component carrying the compact connected point-between witness.

This is below Aquinas' finite no-closed-separation and pair-frontier reducers:
it introduces no boundary-cycle rows, actual-sector rows, W32 consumers,
induced frontier graphs, arbitrary cycles, or reverse aliases through finite
frontier conclusions. -/
theorem S2_r6z_topology_kcomponent_points_between_source_20260521r6z
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_nontrivialRelativeClopenKSide
    nontrivial_side

set_option linter.style.longLine false in
/-- Claim `S2-r18-kcomponent-points-between-source`.

The same-`K` Janiszewski point-between leaf is strictly lowered to the
hard-case aligned closed-split planar-continuum source.  The owner reducer in
`ExteriorComponentTopology` turns the aligned `K1/K2` split into the
relative-clopen side and then reuses the checked compact-frontier component
argument for the point-between witness. -/
theorem S2_r18_kcomponent_points_between_source_20260521r18
    (nontrivial_aligned_K_split :
      PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_nontrivialAlignedKSplit
    nontrivial_aligned_K_split

set_option linter.style.longLine false in
/-- Claim `S2-r11-topology-points-between-source`.

The same-`K` Janiszewski point-between leaf is strictly lowered to the direct
no-subcontinuum obstruction.  The connected-component hypothesis inside `K`
is converted into an honest compact connected subcontinuum by taking the image
of the connected component of `y` in the compact subtype `K`; the existing
no-subcontinuum point-between reducer then supplies the frontier witness.

This proof stays inside the topology layer: it does not use boundary-cycle
rows, actual-sector rows, carrier rows, W32 consumers, induced frontier
graphs, arbitrary cycles, or finite no-closed-separation consumers. -/
theorem
    planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_noSubcontinuumObstruction_20260521r11
    (no_subcontinuum :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween := by
  intro K U y z hcompact hcomponent hunbounded hyFrontier hzFrontier
    hz_componentInK
  rcases hcomponent with ⟨x, hx, rfl⟩
  have hfrontier_subset_K :
      frontier (connectedComponentIn Kᶜ x) ⊆ K :=
    planarContinuumUnboundedComplement_frontier_subset
      (K := K) (x := x) hcompact
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let yK : K := ⟨y, hfrontier_subset_K hyFrontier⟩
  let zK : K := ⟨z, hfrontier_subset_K hzFrontier⟩
  have hz_componentK : zK ∈ connectedComponent yK := by
    have hz_image :
        z ∈ (Subtype.val '' connectedComponent yK :
          Set PlanarInterface.Point) := by
      simpa [connectedComponentIn_eq_image
        (hfrontier_subset_K hyFrontier), yK] using hz_componentInK
    rcases hz_image with ⟨w, hw_component, hw_eq⟩
    have hw_eq_zK : w = zK := Subtype.ext hw_eq
    simpa [hw_eq_zK, yK] using hw_component
  let T : Set PlanarInterface.Point := Subtype.val '' connectedComponent yK
  have hTcompact : IsCompact T :=
    isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hTconnected : IsConnected T :=
    isConnected_connectedComponent.image Subtype.val
      continuous_subtype_val.continuousOn
  have hTsubset : T ⊆ K := by
    intro p hpT
    rcases hpT with ⟨pK, _hp_component, rfl⟩
    exact pK.property
  have hyT : y ∈ T := ⟨yK, mem_connectedComponent, rfl⟩
  have hzT : z ∈ T := ⟨zK, hz_componentK, rfl⟩
  exact
    planarJaniszewskiBoundaryBumpingSubcontinuumPointsBetween_of_noSubcontinuumObstruction
      no_subcontinuum K (connectedComponentIn Kᶜ x) T y z hcompact
      ⟨x, hx, rfl⟩ hunbounded hTcompact hTconnected hTsubset hyT hzT
      hyFrontier hzFrontier

set_option linter.style.longLine false in
/-- Named r11 topology support reducer. -/
theorem S2_r11_topology_points_between_source_20260521r11
    (no_subcontinuum :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_noSubcontinuumObstruction_20260521r11
    no_subcontinuum

set_option linter.style.longLine false in
/-- The compact/frontier no-crossing residual is strictly lowered to the
same-`K` Janiszewski boundary-bumping point-between theorem.

This is only a topology eraser: the same-`K` point-between source supplies the
U-indexed subcontinuum point-between witness, which supplies a compact
connected subset of the selected frontier crossing any displayed closed split;
connectedness of that witness contradicts the split.  No boundary-cycle
producer, actual-sector row, carrier row, S2 conclusion, or W32 facade is used. -/
theorem
    planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_janiszewskiKComponentPointsBetween_20260521r7d
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_pointsBetween
    (planarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween_of_janiszewskiBoundaryBumpingPointsBetween
      (planarJaniszewskiBoundaryBumpingSubcontinuumPointsBetween_of_kComponentPointsBetween
        points_between))

set_option linter.style.longLine false in
/-- Claim `S2-r7d-no-compact-connected-crossing-topology-source`.

The current topology residual after r7b is reduced to the sharper named
same-`K` Janiszewski point-between theorem already isolated in the topology
source stack. -/
theorem S2_r7d_no_compact_connected_crossing_topology_source_20260521r7d
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_janiszewskiKComponentPointsBetween_20260521r7d
    points_between

set_option linter.style.longLine false in
/-- Claim `S2-subagent-kcomponent-points-between-topology-20260521-current6`.

The current compact/frontier no-crossing topology source is strictly reduced
to the same-`K` Janiszewski boundary-bumping point-between theorem.  The
composition stays inside the point-between/frontier-subcontinuum topology API
and does not use boundary-sector rows, W32 consumers, induced frontier graphs,
arbitrary cycles, or synthetic enclosures. -/
theorem S2_subagent_kcomponent_points_between_topology_20260521_current6
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_janiszewskiKComponentPointsBetween_20260521r7d
    points_between

set_option linter.style.longLine false in
/-- Claim `S2-r7i-agent-topology-support`.

The compact/frontier no-crossing residual reduces directly to the earlier
planar-continuum frontier-subcontinuum source: a compact connected subset of
`K` crossing the two closed frontier sides would yield a compact connected
subset of the selected frontier crossing the same sides, contradicting the
displayed closed separation.  This proof does not use boundary-cycle rows,
actual exterior-sector rows, carrier rows, W32, or the relative-clopen /
same-`K` component equivalence loop. -/
theorem
    planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_crossingFrontierSubcontinuum_20260521r7i
    (frontier_subcontinuum :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    T hTcompact hTconnected hTsubset hTA hTB
  rcases
      frontier_subcontinuum K x A B T hcompact hx hunbounded hAclosed hBclosed
        hABdisjoint hcover hTcompact hTconnected hTsubset hTA hTB with
    ⟨S, hScompact, hSconnected, hSsubset, hSA, hSB⟩
  have hSclosed : IsClosed S := hScompact.isClosed
  have hleftClosed : IsClosed (S ∩ A) := hSclosed.inter hAclosed
  have hrightClosed : IsClosed (S ∩ B) := hSclosed.inter hBclosed
  have hdisjoint : Disjoint (S ∩ A) (S ∩ B) := by
    rw [Set.disjoint_left]
    intro p hpLeft hpRight
    exact (Set.disjoint_left.mp hABdisjoint) hpLeft.2 hpRight.2
  have hScover : S = (S ∩ A) ∪ (S ∩ B) := by
    ext p
    constructor
    · intro hpS
      have hpFrontier :
          p ∈ frontier (connectedComponentIn Kᶜ x) :=
        hSsubset hpS
      have hpAB : p ∈ A ∪ B := by
        simpa [hcover] using hpFrontier
      rcases hpAB with hpA | hpB
      · exact Or.inl ⟨hpS, hpA⟩
      · exact Or.inr ⟨hpS, hpB⟩
    · intro hp
      rcases hp with hpLeft | hpRight
      · exact hpLeft.1
      · exact hpRight.1
  exact
    (noClosedSeparation_of_isPreconnected hSconnected.isPreconnected)
      (S ∩ A) (S ∩ B) hleftClosed hrightClosed hdisjoint hScover hSA hSB

set_option linter.style.longLine false in
/-- Named r7i topology-support reducer. -/
theorem S2_r7i_agent_topology_support_20260521r7i
    (frontier_subcontinuum :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_crossingFrontierSubcontinuum_20260521r7i
    frontier_subcontinuum

set_option linter.style.longLine false in
/-- Claim `S2-agent-pool7-janiszewski-points-between-source`.

The same-`K` Janiszewski point-between source is strictly lowered to the
planar-continuum frontier-subcontinuum source.  The composition stays in the
topology layer: frontier-subcontinuum gives no compact connected `K` crossing,
the compact Hausdorff separator gives the nontrivial relative-clopen `K` side,
and the checked same-`K` point-between lowerer packages the frontier component
as the compact connected witness.  No boundary-cycle rows, actual-sector rows,
carrier rows, W32 consumers, induced frontier graphs, or arbitrary cycles are
used. -/
theorem S2_agent_pool7_janiszewski_points_between_source_20260521r8h
    (frontier_subcontinuum :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  S2_r6z_topology_kcomponent_points_between_source_20260521r6z
    (S2_r7b_relative_clopen_k_side_topology_source_20260521r7b
      (S2_r7i_agent_topology_support_20260521r7i frontier_subcontinuum))

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-component-avoidance-from-frontier-component-20260521n10`.

The component-avoidance topology leaf is sourced from the same-`K`
Janiszewski frontier-component theorem by composing the checked n9
no-crossing lowerer with the checked n1 component-avoidance lowerer. -/
theorem S2_dynamic_component_avoidance_from_frontier_component_20260521n10
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance :=
  S2_dynamic_component_avoidance_source_20260521n1
    (S2_dynamic_no_compact_crossing_source_20260521n9 frontier_component)

set_option linter.style.longLine false in
/-- Claim `S2-r18-topology-kcomponent-points-between-source`.

The same-`K` Janiszewski point-between source is strictly lowered to the direct
same-`K` frontier-component theorem.  The lowerer only packages the connected
component of the first frontier point inside `frontier U` as the compact
connected witness.  It does not use boundary-cycle rows, actual-sector rows,
carrier rows, W32 consumers, induced frontier graphs, arbitrary cycles,
synthetic enclosures, or convex-hull shortcuts. -/
theorem S2_r18_topology_kcomponent_points_between_source_of_frontierComponent_20260521r18
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_frontierComponent
    frontier_component

set_option linter.style.longLine false in
/-- Claim `S2-janiszewski-kcomponent-points-between-source`.

The same-`K` Janiszewski point-between source is strictly lowered to the direct
same-`K` frontier-component topology theorem.  The proof only packages the
connected component of `y` in `frontier U` as a compact connected plane set,
using the existing compactness of unbounded complement-component frontiers and
Mathlib connected-component image bookkeeping.  It introduces no boundary
cycles, actual-sector rows, carrier rows, W32 facade, induced frontier graph
route, or all-adjacent endpoint premise. -/
theorem S2_janiszewski_kcomponent_points_between_source
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_frontierComponent
    frontier_component

set_option linter.style.longLine false in
/-- Nontrivial-relative-clopen leaf form of
`S2_janiszewski_kcomponent_points_between_source`.

This composes the checked same-`K` frontier-component lowerer with the named
point-between source above, so the exact remaining topology leaf is the
x-indexed nontrivial relative-clopen `K`-side source. -/
theorem S2_janiszewski_kcomponent_points_between_source_of_nontrivialRelativeClopenKSide
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_nontrivialRelativeClopenKSide
    nontrivial_side

/-- The continuous Boolean side source reduces directly to the point-level
crossing-subcontinuum frontier theorem.

Given a compact connected `T ⊆ K` meeting both closed frontier sides, choose
one point on each side.  The point-level source joins those two frontier points
inside the same frontier by a compact connected set `S`, and the displayed
closed split `A ∪ B` then separates `S`, contradiction.  The generic compact
Hausdorff Boolean separator turns this no-crossing fact into the required
continuous side map on `K`. -/
theorem
    planarContinuumUnboundedComplementFrontierContinuousKSide_of_pointsBetween
    (points_between :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    _hAnonempty _hBnonempty
  exact
    exists_continuous_bool_side_of_no_compact_connected_crossing
      (K := K) (A := A) (B := B)
      hcompact hAclosed hBclosed
      (by
        intro T hTcompact hTconnected hTsubset hTA hTB
        rcases hTA with ⟨y, hyT, hyA⟩
        rcases hTB with ⟨z, hzT, hzB⟩
        have hyFrontier :
            y ∈ frontier (connectedComponentIn Kᶜ x) := by
          rw [hcover]
          exact Or.inl hyA
        have hzFrontier :
            z ∈ frontier (connectedComponentIn Kᶜ x) := by
          rw [hcover]
          exact Or.inr hzB
        rcases
            points_between K x T y z hcompact hx hunbounded hTcompact
              hTconnected hTsubset hyT hzT hyFrontier hzFrontier with
          ⟨S, hScompact, hSconnected, hSsubset, hyS, hzS⟩
        have hSclosed : IsClosed S := hScompact.isClosed
        have hleftClosed : IsClosed (S ∩ A) := hSclosed.inter hAclosed
        have hrightClosed : IsClosed (S ∩ B) := hSclosed.inter hBclosed
        have hdisjoint : Disjoint (S ∩ A) (S ∩ B) := by
          rw [Set.disjoint_left]
          intro p hpLeft hpRight
          exact (Set.disjoint_left.mp hABdisjoint) hpLeft.2 hpRight.2
        have hScover : S = (S ∩ A) ∪ (S ∩ B) := by
          ext p
          constructor
          · intro hpS
            have hpFrontier :
                p ∈ frontier (connectedComponentIn Kᶜ x) :=
              hSsubset hpS
            have hpAB : p ∈ A ∪ B := by
              simpa [hcover] using hpFrontier
            rcases hpAB with hpA | hpB
            · exact Or.inl ⟨hpS, hpA⟩
            · exact Or.inr ⟨hpS, hpB⟩
          · intro hp
            rcases hp with hpLeft | hpRight
            · exact hpLeft.1
            · exact hpRight.1
        exact
          (noClosedSeparation_of_isPreconnected hSconnected.isPreconnected)
            (S ∩ A) (S ∩ B) hleftClosed hrightClosed hdisjoint hScover
            ⟨y, hyS, hyA⟩ ⟨z, hzS, hzB⟩)

/-- Claim `S2-agent-continuous-side-source-worker-20260521e42`.

The continuous side-map leaf is strictly reduced to the point-level
crossing-subcontinuum frontier theorem.  This route constructs the Boolean
side map through the compact Hausdorff clopen separator and does not pass
through the open-cover, relative-clopen, no-subcontinuum, component-avoidance,
or crossing-boundedness source aliases. -/
theorem S2_agent_continuous_side_source_worker_20260521e42
    (points_between :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide :=
  planarContinuumUnboundedComplementFrontierContinuousKSide_of_pointsBetween
    points_between

/-- The continuous Boolean side source is strictly lowered to the same-`K`
frontier-component source.

This k6e handoff follows the non-circular topology route
`KComponentFrontierComponent -> crossing frontier component -> crossing
point-between -> no compact connected crossing -> continuous Bool side`.  It
uses only the compact connected frontier-component packaging and the existing
closed-split/no-crossing separator; it does not pass through relative-clopen,
continuous-side reversal, final S2 rows, or boundary-cycle rows. -/
theorem
    planarContinuumUnboundedComplementFrontierContinuousKSide_of_kComponentFrontierComponent
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide :=
  planarContinuumUnboundedComplementFrontierContinuousKSide_of_pointsBetween
    (planarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween_of_frontierComponent
      (planarContinuumUnboundedComplementFrontierCrossingSubcontinuumFrontierComponent_of_janiszewskiKComponentFrontierComponent
        frontier_component))

/-- Claim `S2-k6e-topology-continuous-side-source`.

The nontrivial closed-separation continuous-side topology source is reduced
below the direct Janiszewski same-`K` frontier-component source, along the
compact-connected/no-crossing route above. -/
theorem S2_k6e_topology_continuous_side_source
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide :=
  planarContinuumUnboundedComplementFrontierContinuousKSide_of_kComponentFrontierComponent
    frontier_component

set_option linter.style.longLine false in
/-- Claim `S2-k6j-topology-continuous-K-side-source`.

The continuous Boolean `K`-side source is strictly lowered to the k9
Janiszewski relative-clopen boundary-bumping source.  The residual is exactly
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide`;
the checked composition first turns that source into the x-indexed
crossing-subcontinuum boundedness theorem, then applies the existing compact
Hausdorff no-crossing Boolean separator. -/
theorem S2_k6j_topology_continuous_K_side_source
    (relative_side :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide) :
    PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide :=
  planarContinuumUnboundedComplementFrontierContinuousKSide_of_crossingSubcontinuumForcesBounded
    (planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_janiszewskiRelativeClopenKSide
      relative_side)

/-- Claim `S2-k6g-topology-nontrivial-relative-clopen-source`.

The nontrivial relative-clopen `K`-side topology source is strictly lowered to
the U-indexed subcontinuum-carrier boundary-bumping source.  The route first
uses the carrier to force boundedness for any compact connected crossing of a
closed frontier split, then applies the existing compact-Hausdorff
relative-clopen separator.  It does not pass through the continuous-side
theorem or through a theorem already assuming the relative-clopen source. -/
theorem S2_k6g_topology_nontrivial_relative_clopen_source
    (subcontinuum_carrier :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumCarrier) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
  planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_crossingBounded
    (S2_k6_topology_crossing_subcontinuum subcontinuum_carrier)

/-- Claim `S2-agent-topology-nontrivial-relative-clopen-source-20260521k14`.

The nontrivial relative-clopen `K`-side source is strictly lowered to the
whole-frontier no-subcontinuum obstruction.  This is the compact-Hausdorff
separator step itself: each closed frontier side lies in `K`, and the supplied
obstruction rules out any compact connected subset of `K` crossing both
closed sides. -/
theorem S2_agent_topology_nontrivial_relative_clopen_source_20260521k14
    (no_subcontinuum :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    hAnonempty hBnonempty
  have hfrontier_subset_K :
      frontier (connectedComponentIn Kᶜ x) ⊆ K :=
    planarContinuumUnboundedComplement_frontier_subset
      (K := K) (x := x) hcompact
  have hAK : A ⊆ K := by
    intro y hyA
    exact hfrontier_subset_K (by
      rw [hcover]
      exact Or.inl hyA)
  have hBK : B ⊆ K := by
    intro y hyB
    exact hfrontier_subset_K (by
      rw [hcover]
      exact Or.inr hyB)
  exact
    exists_relative_clopen_separator_of_no_subcontinuum
      (K := K) (A := A) (B := B)
      hcompact hAclosed hBclosed hAK hBK
      (no_subcontinuum K x A B hcompact hx hunbounded hAclosed hBclosed
        hABdisjoint hcover hAnonempty hBnonempty)

set_option linter.style.longLine false in
/-- Claim `S2-q8-relative-clopen-K-side-source-20260521q2`.

The remaining nontrivial relative-clopen `K`-side source is strictly lowered to
the component-indexed Janiszewski bounded-subcontinuum source.  The proof first
specializes that boundedness statement to the selected
`connectedComponentIn Kᶜ x`, then applies the compact-Hausdorff relative
clopen separator already isolated for crossing-boundedness.  It introduces no
final boundary-cycle rows, W32 rows, actual-sector rows, or route facade. -/
theorem S2_q8_relative_clopen_K_side_source_20260521q2
    (subcontinuum_forces_bounded :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
  planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_crossingBounded
    (planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_janiszewskiBoundaryBumping
      subcontinuum_forces_bounded)

set_option linter.style.longLine false in
/-- Claim `S2-agent-q8-topology-nontrivial-side`, same-`K` point-between form.

The q8 nontrivial relative-clopen `K`-side source is strictly reduced to the
current Janiszewski/boundary-bumping same-`K` point-between theorem.  The proof
uses the checked point-between-to-no-crossing reducer and the compact-Hausdorff
relative-clopen separator already isolated in the topology stack; it adds no
boundary-cycle, actual-sector, carrier, or W-facing facade data. -/
theorem S2_agent_q8_topology_nontrivial_side_of_kComponentPointsBetween_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
  S2_r7b_relative_clopen_k_side_topology_source_20260521r7b
    (S2_r7d_no_compact_connected_crossing_topology_source_20260521r7d
      points_between)

set_option linter.style.longLine false in
/-- Claim `S2-agent-q8-topology-nontrivial-side`, frontier-component form.

This sharper q8 handoff lowers the nontrivial relative-clopen `K`-side source
to the direct same-`K` frontier-component theorem used by the current
Janiszewski/boundary-bumping component-topology route. -/
theorem S2_agent_q8_topology_nontrivial_side_of_kComponentFrontierComponent_20260522
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
  S2_r7b_relative_clopen_k_side_topology_source_20260521r7b
    (S2_dynamic_no_compact_crossing_source_20260521n9 frontier_component)

/-- Claim `S2-agent-topology-source-worker-20260521e40`.

The nontrivial relative-clopen `K`-side source reduces directly to the
continuous Boolean side-map source.  The proof only uses the standard
component-frontier containment in `K` and the compact-subspace eraser from a
continuous `Bool` side to a closed disjoint `K₁/K₂` split; it does not pass
through no-subcontinuum, component-avoidance, same-`K` component, or
crossing-boundedness aliases. -/
theorem
    planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_continuousKSide
    (continuous_side :
      PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    hAnonempty hBnonempty
  have hfrontier_subset_K :
      frontier (connectedComponentIn Kᶜ x) ⊆ K :=
    planarContinuumUnboundedComplement_frontier_subset
      (K := K) (x := x) hcompact
  have hAK : A ⊆ K := by
    intro y hyA
    exact hfrontier_subset_K (by
      rw [hcover]
      exact Or.inl hyA)
  have hBK : B ⊆ K := by
    intro y hyB
    exact hfrontier_subset_K (by
      rw [hcover]
      exact Or.inr hyB)
  rcases
      continuous_side K x A B hcompact hx hunbounded hAclosed hBclosed
        hABdisjoint hcover hAnonempty hBnonempty with
    ⟨side, hside, hA_side, hB_side⟩
  rcases
      exists_closed_k_split_of_continuous_bool_side
        (K := K) (A := A) (B := B)
        hcompact hAK hBK side hside hA_side hB_side with
    ⟨K1, K2, hK1closed, hK2closed, hKdisjoint, hKcover, hAK1, hBK2⟩
  refine ⟨K1, ?_, hK1closed, ?_, hAK1, ?_⟩
  · intro y hyK1
    rw [hKcover]
    exact Or.inl hyK1
  · have hdiff_eq : K \ K1 = K2 := by
      ext y
      constructor
      · intro hy
        have hyUnion : y ∈ K1 ∪ K2 := by
          simpa [hKcover] using hy.1
        rcases hyUnion with hyK1 | hyK2
        · exact (hy.2 hyK1).elim
        · exact hyK2
      · intro hyK2
        refine ⟨?_, ?_⟩
        · rw [hKcover]
          exact Or.inr hyK2
        · intro hyK1
          exact (Set.disjoint_left.mp hKdisjoint) hyK1 hyK2
    simpa [hdiff_eq] using hK2closed
  · rw [Set.disjoint_left]
    intro y hyK1 hyB
    exact (Set.disjoint_left.mp hKdisjoint) hyK1 (hBK2 hyB)

/-- Named e40 handoff: the remaining topology source below e38 is reduced to
constructing a continuous Boolean side map on the compactum `K`. -/
theorem S2_agent_topology_source_worker_20260521e40
    (continuous_side :
      PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
  planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_continuousKSide
    continuous_side

set_option linter.style.longLine false in
/-- Claim `S2-subagent-topology-relative-clopen-source-20260521-current4`.

The nontrivial relative-clopen `K`-side source is strictly lowered below the
current Janiszewski/boundary-bumping aliases to the direct
frontier-subcontinuum crossing source.  The checked chain uses only topology
APIs already isolated here: a crossing frontier subcontinuum rules out compact
connected `K`-crossings, the compact Hausdorff Boolean separator gives a
continuous `Bool` side on `K`, and the existing eraser turns that side into
the requested relative-clopen `K`-side. -/
theorem S2_subagent_topology_relative_clopen_source_20260521_current4
    (frontier_subcontinuum :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
  planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_continuousKSide
    (planarContinuumUnboundedComplementFrontierContinuousKSide_of_noCompactConnectedKCrossing
      (planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_crossingFrontierSubcontinuum_20260521r7i
        frontier_subcontinuum))

/-- The same-`K` frontier-component source is lowered to the x-indexed
nontrivial relative-clopen side theorem.

This is the k6d source-lowering handoff for the shortest W32 topology source:
the component witness is opened by the existing Janiszewski relative-clopen
adapter, and the already checked frontier-component reducer does the compact
frontier component argument. -/
theorem
    planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_nontrivialRelativeClopenKSide
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
  planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_relativeClopenKSide
    (janiszewskiBoundaryBumping_of_nontrivialRelativeClopenKSide
      nontrivial_side)

/-- Claim `S2-k6d-frontier-component-source-lowerer`.

The frontier-component topology source is strictly reduced to the existing
x-indexed nontrivial relative-clopen side theorem, without using boundary
cycles, final S2 rows, induced frontier graphs, all-adjacent endpoints,
synthetic enclosures, or identity angular order. -/
theorem S2_k6d_frontier_component_source_lowerer
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
  planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_nontrivialRelativeClopenKSide
    nontrivial_side

set_option linter.style.longLine false in
/-- Claim `S2-agent-janiszewski-frontier-component-source-20260521k13`.

The Janiszewski same-`K` frontier-component source is strictly lowered to the
existing `x`-indexed nontrivial relative-clopen side theorem.  This keeps the
remaining topology leaf below the compact frontier-component packaging used by
the carrier and point-between adapters. -/
theorem S2_agent_janiszewski_frontier_component_source_20260521k13
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
  planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_nontrivialRelativeClopenKSide
    nontrivial_side

set_option linter.style.longLine false in
/-- Claim `S2-topology-kcomponent-frontier-source`.

The same-`K` frontier-component source is strictly lowered to the existing
Janiszewski closed-frontier relative-clopen `K`-side theorem.  The actual
component/quasicomponent separation and frontier-component bookkeeping are the
checked reducer
`planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_relativeClopenKSide`;
this adds no W-facing composer, boundary-cycle row, or route ledger. -/
theorem S2_topology_kcomponent_frontier_source
    (relative_side :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
  planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_relativeClopenKSide
    relative_side

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-topology-frontier-component-lowering-20260521o3`.

The same-`K` Janiszewski frontier-component topology source used by the n9/n10
no-crossing and component-avoidance routes is strictly lowered to the existing
`x`-indexed nontrivial relative-clopen `K`-side theorem.  This is the topology
source itself, not a W-facing route or final boundary-cycle facade. -/
theorem S2_dynamic_topology_frontier_component_lowering_20260521o3
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
  S2_agent_janiszewski_frontier_component_source_20260521k13
    nontrivial_side

set_option linter.style.longLine false in
/-- Trace-preconnected form of the same-`K` frontier-component source.

For each frontier point `y`, the actual Mathlib-sized local obligation is that
the trace of the unbounded-component frontier on the relative component
`connectedComponentIn K y` is preconnected.  This removes the target's
pointwise `z` bookkeeping and leaves a single component/frontier trace theorem.
-/
def
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected :
    Prop :=
  forall (K U : Set PlanarInterface.Point) (y : PlanarInterface.Point),
    IsCompact K ->
      (Exists fun x : PlanarInterface.Point =>
        x ∈ Kᶜ ∧ U = connectedComponentIn Kᶜ x) ->
        ¬ Bornology.IsBounded U ->
          y ∈ frontier U ->
            IsPreconnected (frontier U ∩ connectedComponentIn K y)

set_option linter.style.longLine false in
/-- Closed-separation form of the local same-`K` trace source.

This is the q26-sized topology leaf: for each frontier point `y`, the trace of
the selected unbounded-component frontier on the relative component of `K`
through `y` has no nonempty closed two-piece separation.  The checked reducer
below converts this to trace preconnectedness using only compactness of `K`
and Mathlib's closedness of connected components. -/
def
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation :
    Prop :=
  forall (K U : Set PlanarInterface.Point) (y : PlanarInterface.Point),
    IsCompact K ->
      (Exists fun x : PlanarInterface.Point =>
        x ∈ Kᶜ ∧ U = connectedComponentIn Kᶜ x) ->
        ¬ Bornology.IsBounded U ->
          y ∈ frontier U ->
            NoClosedSeparation (frontier U ∩ connectedComponentIn K y)

set_option linter.style.longLine false in
/-- Generic q37 component-trace conversion.

The remaining same-`K` trace no-closed-separation source is strictly below the
component/frontier trace-preconnectedness theorem: no additional planar,
finite-drawing, boundary-cycle, actual-sector, or W-facing hypotheses are used
after the trace is known preconnected. -/
theorem
    planarJaniszewskiBoundaryBumpingKComponentTraceNoClosedSeparation_of_kComponentTracePreconnected
    (trace_preconnected :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation := by
  intro K U y hcompact hcomponent hunbounded hyFrontier
  exact
    noClosedSeparation_of_isPreconnected
      (trace_preconnected K U y hcompact hcomponent hunbounded hyFrontier)

set_option linter.style.longLine false in
/-- Claim `S2-q37-topology-component-trace-source-worker`.

The q37 topology component-trace source is lowered to the reusable
component/frontier trace-preconnectedness theorem. -/
theorem S2_q37_kComponentTraceNoClosedSeparation_of_kComponentTracePreconnected_20260522q37
    (trace_preconnected :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation :=
  planarJaniszewskiBoundaryBumpingKComponentTraceNoClosedSeparation_of_kComponentTracePreconnected
    trace_preconnected

set_option linter.style.longLine false in
/-- q28 topology trace adapter.

The compatibility trace no-closed-separation theorem over every compact
connected `T ⊆ K` specializes to the live same-`K` component trace by taking
`T = connectedComponentIn K y`.  This is only a strict lowering from the
stronger trace source; it does not assert the stronger source unconditionally. -/
theorem
    planarJaniszewskiBoundaryBumpingKComponentTraceNoClosedSeparation_of_frontierTraceNoClosedSeparation
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceNoClosedSeparation) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation := by
  intro K U y hcompact hcomponent hunbounded hyFrontier
  rcases hcomponent with ⟨x, hx, rfl⟩
  have hfrontier_subset_K :
      frontier (connectedComponentIn Kᶜ x) ⊆ K :=
    planarContinuumUnboundedComplement_frontier_subset
      (K := K) (x := x) hcompact
  have hyK : y ∈ K := hfrontier_subset_K hyFrontier
  have hcomponentClosed : IsClosed (connectedComponentIn K y) := by
    have hKclosed : IsClosed K := hcompact.isClosed
    rw [connectedComponentIn_eq_image hyK]
    exact
      hKclosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp
        isClosed_connectedComponent
  have hTcompact : IsCompact (connectedComponentIn K y) :=
    hcompact.of_isClosed_subset hcomponentClosed (connectedComponentIn_subset K y)
  have hTconnected : IsConnected (connectedComponentIn K y) :=
    isConnected_connectedComponentIn_iff.mpr hyK
  have htraceNonempty :
      (connectedComponentIn K y ∩
          frontier (connectedComponentIn Kᶜ x)).Nonempty :=
    ⟨y, mem_connectedComponentIn hyK, hyFrontier⟩
  have htraceNoClosed :
      NoClosedSeparation
        (connectedComponentIn K y ∩
          frontier (connectedComponentIn Kᶜ x)) :=
    trace_noClosed K (connectedComponentIn Kᶜ x)
      (connectedComponentIn K y)
      hcompact ⟨x, hx, rfl⟩ hunbounded hTcompact hTconnected
      (connectedComponentIn_subset K y) htraceNonempty
  simpa [Set.inter_comm] using htraceNoClosed

set_option linter.style.longLine false in
/-- q28 topology trace adapter, named workboard handoff. -/
theorem S2_q28_kComponentTraceNoClosedSeparation_of_frontierTraceNoClosedSeparation_20260522
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceNoClosedSeparation) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation :=
  planarJaniszewskiBoundaryBumpingKComponentTraceNoClosedSeparation_of_frontierTraceNoClosedSeparation
    trace_noClosed

set_option linter.style.longLine false in
/-- The closed-separation trace source supplies trace preconnectedness.

The only added topology is generic compact-component bookkeeping: the relative
component `connectedComponentIn K y` is closed because `K` is compact, so the
frontier/component trace is closed and the local
`isPreconnected_of_noClosedSeparation` lemma applies. -/
theorem
    planarJaniszewskiBoundaryBumpingKComponentTracePreconnected_of_traceNoClosedSeparation
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected := by
  intro K U y hcompact hcomponent hunbounded hyFrontier
  rcases hcomponent with ⟨x, hx, rfl⟩
  have hfrontier_subset_K :
      frontier (connectedComponentIn Kᶜ x) ⊆ K :=
    planarContinuumUnboundedComplement_frontier_subset
      (K := K) (x := x) hcompact
  have hyK : y ∈ K := hfrontier_subset_K hyFrontier
  have hKclosed : IsClosed K := hcompact.isClosed
  have hcomponentClosed : IsClosed (connectedComponentIn K y) := by
    rw [connectedComponentIn_eq_image hyK]
    exact
      hKclosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp
        isClosed_connectedComponent
  have htraceClosed :
      IsClosed
        (frontier (connectedComponentIn Kᶜ x) ∩
          connectedComponentIn K y) :=
    isClosed_frontier.inter hcomponentClosed
  exact
    isPreconnected_of_noClosedSeparation htraceClosed
      (trace_noClosed K (connectedComponentIn Kᶜ x) y hcompact
        ⟨x, hx, rfl⟩ hunbounded hyFrontier)

set_option linter.style.longLine false in
/-- Claim `S2-agent-q9-topology-frontier-component`.

The live same-`K` Janiszewski frontier-component theorem is strictly reduced to
trace preconnectedness of
`frontier U ∩ connectedComponentIn K y`.  The proof uses only the generic
frontier-subset lemma for compact planar complement components and Mathlib's
`IsPreconnected.subset_connectedComponentIn` component API; it adds no W-facing
facade, cycle row, carrier row, or synthetic enclosure. -/
theorem
    planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_kComponentTracePreconnected
    (trace_preconnected :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent := by
  intro K U y z hcompact hcomponent hunbounded hyFrontier hzFrontier
    hz_componentInK
  rcases hcomponent with ⟨x, hx, rfl⟩
  have hfrontier_subset_K :
      frontier (connectedComponentIn Kᶜ x) ⊆ K :=
    planarContinuumUnboundedComplement_frontier_subset
      (K := K) (x := x) hcompact
  have hyK : y ∈ K := hfrontier_subset_K hyFrontier
  have htrace :
      IsPreconnected
        (frontier (connectedComponentIn Kᶜ x) ∩
          connectedComponentIn K y) :=
    trace_preconnected K (connectedComponentIn Kᶜ x) y hcompact
      ⟨x, hx, rfl⟩ hunbounded hyFrontier
  have hyTrace :
      y ∈ frontier (connectedComponentIn Kᶜ x) ∩
        connectedComponentIn K y :=
    ⟨hyFrontier, mem_connectedComponentIn hyK⟩
  have hzTrace :
      z ∈ frontier (connectedComponentIn Kᶜ x) ∩
        connectedComponentIn K y :=
    ⟨hzFrontier, hz_componentInK⟩
  exact
    htrace.subset_connectedComponentIn hyTrace
      (by
        intro p hp
        exact hp.1)
      hzTrace

set_option linter.style.longLine false in
/-- Claim `S2-agent-q9-topology-frontier-component`, named handoff.

This is the current strict source boundary for the assigned topology task:
prove the trace-preconnected component/frontier theorem above to obtain
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent`. -/
theorem S2_agent_q9_topology_frontier_component_of_kComponentTracePreconnected_20260522
    (trace_preconnected :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
  planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_kComponentTracePreconnected
    trace_preconnected

set_option linter.style.longLine false in
/-- Claim `S2-q26-topology-source`, frontier-component form.

The same-`K` frontier-component source is strictly lowered to the local
closed-separation trace theorem on
`frontier U ∩ connectedComponentIn K y`. -/
theorem S2_q26_kComponentFrontierComponent_of_traceNoClosedSeparation_20260522
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
  S2_agent_q9_topology_frontier_component_of_kComponentTracePreconnected_20260522
    (planarJaniszewskiBoundaryBumpingKComponentTracePreconnected_of_traceNoClosedSeparation
      trace_noClosed)

set_option linter.style.longLine false in
/-- Same-`K` point-between gives the local trace-preconnected component
primitive.

For two points in `frontier U ∩ connectedComponentIn K y`, the point-between
source joins them inside `frontier U`.  Frontier containment in `K` then keeps
that joining subcontinuum in the same relative component of `K` as `y`. -/
theorem
    planarJaniszewskiBoundaryBumpingKComponentTracePreconnected_of_kComponentPointsBetween
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected := by
  intro K U y hcompact hcomponent hunbounded hyFrontier
  have hfrontier_subset_K : frontier U ⊆ K := by
    rcases hcomponent with ⟨x, hx, rfl⟩
    exact
      planarContinuumUnboundedComplement_frontier_subset
        (K := K) (x := x) hcompact
  exact
    isPreconnected_of_forall_pair
      (s := frontier U ∩ connectedComponentIn K y)
      (by
        intro p hp q hq
        have hpFrontier : p ∈ frontier U := hp.1
        have hqFrontier : q ∈ frontier U := hq.1
        have hpComponentY : p ∈ connectedComponentIn K y := hp.2
        have hqComponentY : q ∈ connectedComponentIn K y := hq.2
        have hcomponent_eq :
            connectedComponentIn K y = connectedComponentIn K p :=
          connectedComponentIn_eq hpComponentY
        have hqComponentP : q ∈ connectedComponentIn K p := by
          simpa [hcomponent_eq] using hqComponentY
        rcases
            points_between K U p q hcompact hcomponent hunbounded
              hpFrontier hqFrontier hqComponentP with
          ⟨S, _hScompact, hSconnected, hSsubsetFrontier, hpS, hqS⟩
        have hSsubsetK : S ⊆ K := by
          intro r hrS
          exact hfrontier_subset_K (hSsubsetFrontier hrS)
        have hSsubsetTrace :
            S ⊆ frontier U ∩ connectedComponentIn K y := by
          intro r hrS
          have hrFrontier : r ∈ frontier U := hSsubsetFrontier hrS
          have hrComponentP : r ∈ connectedComponentIn K p :=
            hSconnected.isPreconnected.subset_connectedComponentIn
              hpS hSsubsetK hrS
          have hcomponent_eq' :
              connectedComponentIn K p = connectedComponentIn K y :=
            hcomponent_eq.symm
          have hrComponentY : r ∈ connectedComponentIn K y := by
            simpa [hcomponent_eq'] using hrComponentP
          exact ⟨hrFrontier, hrComponentY⟩
        exact
          ⟨S, hSsubsetTrace, hpS, hqS, hSconnected.isPreconnected⟩)

set_option linter.style.longLine false in
/-- Claim `S2-q43-topology-trace-preconnected-worker`.

The local component/frontier trace-preconnectedness source is strictly lowered
to the existing same-`K` Janiszewski point-between theorem.  This is exactly the
pointwise compact-connected frontier witness route above; it adds no W32-facing
facade, final exterior-cycle/source row, actual-sector premise, or boundary
cycle assumption. -/
theorem S2_q43_kComponentTracePreconnected_of_kComponentPointsBetween_20260522q43
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected :=
  planarJaniszewskiBoundaryBumpingKComponentTracePreconnected_of_kComponentPointsBetween
    points_between

set_option linter.style.longLine false in
/-- Claim `S2-agent-q9-topology-frontier-component`, point-between form.

The local trace-preconnected bridge above feeds the existing q9
frontier-component reducer, so the current frontier-component source is
strictly below the same-`K` point-between primitive. -/
theorem S2_agent_q9_topology_frontier_component_of_kComponentPointsBetween_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
  S2_agent_q9_topology_frontier_component_of_kComponentTracePreconnected_20260522
    (planarJaniszewskiBoundaryBumpingKComponentTracePreconnected_of_kComponentPointsBetween
      points_between)

set_option linter.style.longLine false in
/-- Same-`K` point-between gives the local trace no-closed-separation source.

This composes the point-between-to-trace-preconnected component theorem with
the generic `NoClosedSeparation` conversion above. -/
theorem
    planarJaniszewskiBoundaryBumpingKComponentTraceNoClosedSeparation_of_kComponentPointsBetween
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation :=
  planarJaniszewskiBoundaryBumpingKComponentTraceNoClosedSeparation_of_kComponentTracePreconnected
    (planarJaniszewskiBoundaryBumpingKComponentTracePreconnected_of_kComponentPointsBetween
      points_between)

set_option linter.style.longLine false in
/-- Claim `S2-q37-topology-component-trace-source-worker`, point-between form.

The q37 component-trace no-closed-separation residual is strictly lowered to
the existing same-`K` component point-between source. -/
theorem S2_q37_kComponentTraceNoClosedSeparation_of_kComponentPointsBetween_20260522q37
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation :=
  planarJaniszewskiBoundaryBumpingKComponentTraceNoClosedSeparation_of_kComponentPointsBetween
    points_between

set_option linter.style.longLine false in
/-- Finite-drawing trace-preconnectedness source.

For every unbounded complement component of the actual embedded drawing, the
trace of its frontier on the relative component of any frontier point inside
`embeddedEdgeSet C` is preconnected.  This is the finite, input-facing version
of the q9 same-`K` trace source. -/
def FiniteDrawingUnboundedComplementFrontierKTracePreconnected : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
      (_inputs : FinitePlanarOuterComponentInputs C)
      (x y : PlanarInterface.Point),
    x ∈ (embeddedEdgeSet C)ᶜ ->
      ¬ Bornology.IsBounded
        (connectedComponentIn (embeddedEdgeSet C)ᶜ x) ->
        y ∈ frontier (connectedComponentIn (embeddedEdgeSet C)ᶜ x) ->
          IsPreconnected
            (frontier (connectedComponentIn (embeddedEdgeSet C)ᶜ x) ∩
              connectedComponentIn (embeddedEdgeSet C) y)

set_option linter.style.longLine false in
/-- The finite trace source gives finite frontier preconnectedness.

Connectedness of the embedded drawing puts any two frontier points in the same
relative component of `embeddedEdgeSet C`; the trace row then supplies the
preconnected witness between them. -/
theorem finiteDrawingUnboundedComplementFrontierPreconnected_of_kTracePreconnected
    (trace_preconnected :
      FiniteDrawingUnboundedComplementFrontierKTracePreconnected) :
    FiniteDrawingUnboundedComplementFrontierPreconnected := by
  intro n C inputs x hx hunbounded
  apply isPreconnected_of_forall_pair
  intro y hy z hz
  let K : Set PlanarInterface.Point := embeddedEdgeSet C
  let U : Set PlanarInterface.Point := connectedComponentIn Kᶜ x
  have htrace :
      IsPreconnected (frontier U ∩ connectedComponentIn K y) := by
    simpa [K, U] using
      trace_preconnected C inputs x y hx hunbounded hy
  have hfrontier_subset_K : frontier U ⊆ K := by
    simpa [K, U] using
      finiteDrawingUnboundedComplement_frontier_subset_embeddedEdgeSet C x
  have hyK : y ∈ K := hfrontier_subset_K hy
  have hzK : z ∈ K := hfrontier_subset_K hz
  have hz_component : z ∈ connectedComponentIn K y :=
    (embeddedEdgeSet_connected_of_inputs inputs).isPreconnected
      |>.subset_connectedComponentIn hyK subset_rfl hzK
  refine
    ⟨frontier U ∩ connectedComponentIn K y, ?_, ?_, ?_, htrace⟩
  · intro p hp
    exact hp.1
  · exact ⟨hy, mem_connectedComponentIn hyK⟩
  · exact ⟨hz, hz_component⟩

set_option linter.style.longLine false in
/-- The q9 global trace source specializes to the finite embedded drawing. -/
theorem finiteDrawingUnboundedComplementFrontierKTracePreconnected_of_globalTracePreconnected
    (trace_preconnected :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected) :
    FiniteDrawingUnboundedComplementFrontierKTracePreconnected := by
  intro n C _inputs x y hx hunbounded hy
  exact
    trace_preconnected (embeddedEdgeSet C)
      (connectedComponentIn (embeddedEdgeSet C)ᶜ x) y
      (embeddedEdgeSet_compact C)
      ⟨x, hx, rfl⟩ hunbounded hy

set_option linter.style.longLine false in
/-- Finite-drawing same-`K`-component point-between source.

This is the pointwise source below
`FiniteDrawingUnboundedComplementFrontierKTracePreconnected`: two frontier
points in the same relative component of the embedded drawing are carried by a
compact connected subset of that same unbounded complement frontier. -/
def FiniteDrawingUnboundedComplementFrontierKComponentPointsBetween : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
      (_inputs : FinitePlanarOuterComponentInputs C)
      (x y z : PlanarInterface.Point),
    x ∈ (embeddedEdgeSet C)ᶜ ->
      ¬ Bornology.IsBounded
        (connectedComponentIn (embeddedEdgeSet C)ᶜ x) ->
        y ∈ frontier (connectedComponentIn (embeddedEdgeSet C)ᶜ x) ->
          z ∈ frontier (connectedComponentIn (embeddedEdgeSet C)ᶜ x) ->
            z ∈ connectedComponentIn (embeddedEdgeSet C) y ->
              Exists fun S : Set PlanarInterface.Point =>
                IsCompact S /\
                  IsConnected S /\
                    S ⊆ frontier (connectedComponentIn (embeddedEdgeSet C)ᶜ x) /\
                      y ∈ S /\
                        z ∈ S

set_option linter.style.longLine false in
/-- The finite point-between source proves finite trace preconnectedness.

The only bookkeeping is that a compact connected frontier witness stays in the
same relative component of `embeddedEdgeSet C` because the frontier is carried
by the embedded drawing. -/
theorem finiteDrawingUnboundedComplementFrontierKTracePreconnected_of_kComponentPointsBetween
    (points_between :
      FiniteDrawingUnboundedComplementFrontierKComponentPointsBetween) :
    FiniteDrawingUnboundedComplementFrontierKTracePreconnected := by
  intro n C inputs x y hx hunbounded hy
  let K : Set PlanarInterface.Point := embeddedEdgeSet C
  let U : Set PlanarInterface.Point := connectedComponentIn Kᶜ x
  have hfrontier_subset_K : frontier U ⊆ K := by
    simpa [K, U] using
      finiteDrawingUnboundedComplement_frontier_subset_embeddedEdgeSet C x
  exact
    isPreconnected_of_forall_pair
      (s := frontier U ∩ connectedComponentIn K y)
      (by
        intro p hp q hq
        have hpFrontier : p ∈ frontier U := hp.1
        have hqFrontier : q ∈ frontier U := hq.1
        have hpComponentY : p ∈ connectedComponentIn K y := hp.2
        have hqComponentY : q ∈ connectedComponentIn K y := hq.2
        have hcomponent_eq :
            connectedComponentIn K y = connectedComponentIn K p :=
          connectedComponentIn_eq hpComponentY
        have hqComponentP : q ∈ connectedComponentIn K p := by
          simpa [hcomponent_eq] using hqComponentY
        rcases
            points_between C inputs x p q
              (by simpa [K] using hx)
              (by simpa [K, U] using hunbounded)
              (by simpa [U] using hpFrontier)
              (by simpa [U] using hqFrontier)
              (by simpa [K] using hqComponentP) with
          ⟨S, _hScompact, hSconnected, hSsubsetFrontier, hpS, hqS⟩
        have hSsubsetK : S ⊆ K := by
          intro r hrS
          exact hfrontier_subset_K (hSsubsetFrontier hrS)
        have hSsubsetTrace :
            S ⊆ frontier U ∩ connectedComponentIn K y := by
          intro r hrS
          have hrFrontier : r ∈ frontier U := hSsubsetFrontier hrS
          have hrComponentP : r ∈ connectedComponentIn K p :=
            hSconnected.isPreconnected.subset_connectedComponentIn
              hpS hSsubsetK hrS
          have hcomponent_eq' :
              connectedComponentIn K p = connectedComponentIn K y :=
            hcomponent_eq.symm
          have hrComponentY : r ∈ connectedComponentIn K y := by
            simpa [hcomponent_eq'] using hrComponentP
          exact ⟨hrFrontier, hrComponentY⟩
        exact
          ⟨S, hSsubsetTrace, hpS, hqS, hSconnected.isPreconnected⟩)

set_option linter.style.longLine false in
/-- The global same-`K` point-between source specializes to the finite
embedded drawing point-between source. -/
theorem finiteDrawingUnboundedComplementFrontierKComponentPointsBetween_of_globalKComponentPointsBetween
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    FiniteDrawingUnboundedComplementFrontierKComponentPointsBetween := by
  intro n C _inputs x y z hx hunbounded hy hz hzComponent
  exact
    points_between (embeddedEdgeSet C)
      (connectedComponentIn (embeddedEdgeSet C)ᶜ x) y z
      (embeddedEdgeSet_compact C) ⟨x, hx, rfl⟩ hunbounded hy hz
      hzComponent

set_option linter.style.longLine false in
/-- Claim `S2-agent-q11-topology-trace-accumulation`.

The finite trace-preconnectedness leaf is strictly lowered to the finite
same-component point-between source for the embedded drawing. -/
theorem S2_agent_q11_finiteDrawing_kTracePreconnected_of_kComponentPointsBetween_20260522
    (points_between :
      FiniteDrawingUnboundedComplementFrontierKComponentPointsBetween) :
    FiniteDrawingUnboundedComplementFrontierKTracePreconnected :=
  finiteDrawingUnboundedComplementFrontierKTracePreconnected_of_kComponentPointsBetween
    points_between

set_option linter.style.longLine false in
/-- Claim `S2-agent-q11-topology-trace-accumulation`, global point-between form. -/
theorem S2_agent_q11_finiteDrawing_kTracePreconnected_of_globalKComponentPointsBetween_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    FiniteDrawingUnboundedComplementFrontierKTracePreconnected :=
  finiteDrawingUnboundedComplementFrontierKTracePreconnected_of_kComponentPointsBetween
    (finiteDrawingUnboundedComplementFrontierKComponentPointsBetween_of_globalKComponentPointsBetween
      points_between)

set_option linter.style.longLine false in
/-- Claim `S2-agent-q10-topology-source`, finite separation side.

The finite no-closed/no-open separation leaves are strictly lowered to the
finite trace-preconnectedness source above.  This is source-shaped: it does
not mention boundary cycles, carrier rows, actual-sector rows, W32, or any
synthetic enclosure. -/
theorem S2_agent_q10_finiteDrawing_noClosed_noOpen_of_kTracePreconnected_20260522
    (trace_preconnected :
      FiniteDrawingUnboundedComplementFrontierKTracePreconnected) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation := by
  let frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected :=
    finiteDrawingUnboundedComplementFrontierPreconnected_of_kTracePreconnected
      trace_preconnected
  exact
    ⟨finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_frontierPreconnected
        frontier_preconnected,
      finiteDrawingUnboundedComplementFrontierNoOpenSeparation_of_frontierPreconnected
        frontier_preconnected⟩

set_option linter.style.longLine false in
/-- Claim `S2-agent-q10-topology-source`, q9 trace form.

The q9 same-`K` trace-preconnectedness source now feeds the finite
no-closed/no-open leaves directly through the finite trace theorem, avoiding
the heavier frontier-component and point-between packaging when only finite
drawing separation rows are needed. -/
theorem S2_agent_q10_finiteDrawing_noClosed_noOpen_of_globalTracePreconnected_20260522
    (trace_preconnected :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
  S2_agent_q10_finiteDrawing_noClosed_noOpen_of_kTracePreconnected_20260522
    (finiteDrawingUnboundedComplementFrontierKTracePreconnected_of_globalTracePreconnected
      trace_preconnected)

set_option linter.style.longLine false in
/-- q29 finite topology handoff from the stronger compatibility trace source.

This packages the q28 trace adapter with the existing q10 finite topology
route, yielding both finite no-closed and no-open separation rows. -/
theorem S2_q29_finiteDrawing_noClosed_noOpen_of_frontierTraceNoClosedSeparation_20260522
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceNoClosedSeparation) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
  S2_agent_q10_finiteDrawing_noClosed_noOpen_of_globalTracePreconnected_20260522
    (planarJaniszewskiBoundaryBumpingKComponentTracePreconnected_of_traceNoClosedSeparation
      (S2_q28_kComponentTraceNoClosedSeparation_of_frontierTraceNoClosedSeparation_20260522
        trace_noClosed))

set_option linter.style.longLine false in
/-- Claim `S2-agent-q10-topology-source`, paired finite topology bundle.

The current topology leaf supplying finite no-closed/no-open separation and
the singleton boundary-bumping obstruction is reduced to exactly two source
rows: finite trace-preconnectedness for the embedded drawing and the pointwise
outside-accumulation singleton source. -/
theorem S2_agent_q10_topology_sources_of_kTracePreconnected_outsideAccumulation_20260522
    (trace_preconnected :
      FiniteDrawingUnboundedComplementFrontierKTracePreconnected)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation ∧
        (forall {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C),
            UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
              C inputs) := by
  let hsep :=
    S2_agent_q10_finiteDrawing_noClosed_noOpen_of_kTracePreconnected_20260522
      trace_preconnected
  exact
    ⟨hsep.1, hsep.2,
      fun C inputs =>
        unboundedExteriorSingletonFrontierBoundaryBumpingObstruction_of_outsideAccumulationForcesActualFrontier
          (C := C) (inputs := inputs) (outside_accumulation C inputs)⟩

set_option linter.style.longLine false in
/-- Claim `S2-agent-q10-topology-source`, q9 trace paired bundle.

This is the shortest current source-shaped handoff for the topology side of
the q10 exterior-face route: q9 same-`K` trace preconnectedness supplies the
finite no-closed/no-open separation rows, while the pointwise
outside-accumulation source supplies the singleton boundary-bumping
obstruction. -/
theorem S2_agent_q10_topology_sources_of_globalTracePreconnected_outsideAccumulation_20260522
    (trace_preconnected :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation ∧
        (forall {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C),
            UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
              C inputs) :=
  S2_agent_q10_topology_sources_of_kTracePreconnected_outsideAccumulation_20260522
    (finiteDrawingUnboundedComplementFrontierKTracePreconnected_of_globalTracePreconnected
      trace_preconnected)
    outside_accumulation

set_option linter.style.longLine false in
/-- The subcontinuum-carrier boundary-bumping source reduces to the same lower
nontrivial relative-clopen side theorem, via the direct same-`K`
frontier-component source. -/
theorem
    planarJaniszewskiBoundaryBumpingSubcontinuumCarrier_of_nontrivialRelativeClopenKSide
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumCarrier :=
  planarJaniszewskiBoundaryBumpingSubcontinuumCarrier_of_kComponentFrontierComponent
    (S2_agent_janiszewski_frontier_component_source_20260521k13
      nontrivial_side)

set_option linter.style.longLine false in
/-- The live k12 point-between source is also fed by the lower nontrivial
relative-clopen side theorem, through the subcontinuum carrier route. -/
theorem S2_agent_point_between_source_from_nontrivialRelativeClopenKSide_20260521k13
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween :=
  S2_agent_point_between_source_20260521k12
    (planarJaniszewskiBoundaryBumpingSubcontinuumCarrier_of_nontrivialRelativeClopenKSide
      nontrivial_side)

/-- The lower nontrivial relative-clopen `K`-side source supplies the direct
planar-continuum frontier-preconnectedness theorem. -/
theorem
    planarContinuumUnboundedComplementFrontierPreconnected_of_nontrivialRelativeClopenKSide
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarContinuumUnboundedComplementFrontierPreconnected :=
  planarContinuumUnboundedComplementFrontierPreconnected_of_noClosedSeparation
    (planarContinuumUnboundedComplementFrontierNoClosedSeparation_of_janiszewskiBoundaryBumping
      (janiszewskiBoundaryBumping_of_nontrivialRelativeClopenKSide
        nontrivial_side))

/-- Claim `S2-agent-preconnected-source-20260521k20`.

The planar-continuum frontier-preconnectedness source is strictly lowered to
the current nontrivial relative-clopen `K`-side primitive. -/
theorem S2_agent_preconnected_source_20260521k20
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarContinuumUnboundedComplementFrontierPreconnected :=
  planarContinuumUnboundedComplementFrontierPreconnected_of_nontrivialRelativeClopenKSide
    nontrivial_side

/-- The Janiszewski no-subcontinuum leaf strictly reduces to the lower
`x`-indexed nontrivial relative-clopen `K`-side source.

This route only opens the component witness
`U = connectedComponentIn Kᶜ x`, then uses the direct relative-clopen split
contradiction on a compact connected subcontinuum of `K`.  It does not assume
the no-subcontinuum obstruction, component-avoidance, the same-`K` component
point source, or crossing-boundedness. -/
theorem
    planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_nontrivialRelativeClopenKSide
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction :=
  planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_relativeClopenKSide
    (janiszewskiBoundaryBumping_of_nontrivialRelativeClopenKSide
      nontrivial_side)

/-- Finite-drawing no-closed-separation handoff from the same lower
nontrivial relative-clopen source. -/
theorem
    finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_nontrivialRelativeClopenKSide
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_janiszewskiNoSubcontinuumObstruction
    (planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_nontrivialRelativeClopenKSide
      nontrivial_side)

set_option linter.style.longLine false in
/-- Claim `S2-r5w-topology-leaf-prover-20260521r5w`, finite side.

The finite-drawing no-closed-separation leaf is strictly lowered to the
finite-drawing nontrivial relative-clopen side source, keeping the remaining
topology obligation on the concrete embedded drawing rather than on a final
cycle or induced frontier graph. -/
theorem S2_r5w_finiteDrawing_noClosedSeparation_20260521r5w
    (nontrivial_side :
      FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_finiteDrawing_nontrivialRelativeClopenKSide
    nontrivial_side

set_option linter.style.longLine false in
/-- Claim `S2-r5w-topology-leaf-prover-20260521r5w`, singleton side.

The concrete singleton-frontier boundary-bumping obstruction used by r5q is
reduced to the pointwise outside-accumulation boundary-bumping source.  This
source is exactly the statement that, in the singleton actual-frontier
configuration, an ambient drawing-complement frontier point with arbitrarily
nearby complement points outside the selected unbounded exterior component
must lie on the selected actual frontier. -/
theorem S2_r5w_singleton_boundaryBumping_obstruction_20260521r5w
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (outside_accumulation :
      UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
        C inputs) :
    UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs :=
  unboundedExteriorSingletonFrontierBoundaryBumpingObstruction_of_outsideAccumulationForcesActualFrontier
    (C := C) (inputs := inputs) outside_accumulation

set_option linter.style.longLine false in
/-- The pointwise outside-accumulation source is equivalent, for the singleton
case, to the earlier singleton boundary-bumping obstruction.

If the displayed singleton/outside-accumulation configuration existed, the
obstruction would immediately rule it out, so the requested actual-frontier
membership follows by contradiction.  This is only a source-level adapter; it
does not use boundary-cycle, carrier, actual-sector, synthetic-enclosure, or
W32 rows. -/
theorem
    unboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier_of_boundaryBumpingObstruction_20260522
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
      C inputs := by
  intro q v hqAmbient hqne hfrontier hnear
  exfalso
  exact no_singleton_bumping
    ⟨q, hqAmbient, ⟨v, hqne, hfrontier⟩, hnear⟩

set_option linter.style.longLine false in
/-- Claim `S2-r5w-topology-leaf-prover-20260521r5w`, singleton side,
obstruction form.

The singleton outside-accumulation source can be sourced from the exact
singleton boundary-bumping obstruction already isolated in
`ExteriorComponentTopology`. -/
theorem S2_r5w_outsideAccumulation_forces_actualFrontier_of_boundaryBumpingObstruction_20260522
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
      C inputs :=
  unboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier_of_boundaryBumpingObstruction_20260522
    (C := C) (inputs := inputs) no_singleton_bumping

set_option linter.style.longLine false in
/-- Claim `S2-r5w-topology-leaf-prover-20260521r5w`.

The r5q component-topology input source is lowered through the two r5w leaves:
finite no-closed-separation comes from the finite nontrivial relative-clopen
side source, and the singleton case comes from the pointwise
outside-accumulation boundary-bumping source. -/
theorem S2_r5w_topology_component_input_source_20260521r5w
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (nontrivial_side :
      FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (outside_accumulation :
      UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
        C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_r5q_topology_component_input_source_20260521r5q
    (C := C) inputs
    (S2_r5w_finiteDrawing_noClosedSeparation_20260521r5w
      nontrivial_side)
    (S2_r5w_singleton_boundaryBumping_obstruction_20260521r5w
      (C := C) inputs outside_accumulation)

set_option linter.style.longLine false in
/-- Claim `S2-agent-q7-topology-boundary-bumping`, point-between side.

The same-`K` Janiszewski boundary-bumping point source is strictly reduced to
the x-indexed nontrivial relative-clopen `K`-side source.  This is the
source-facing q7 name over the checked point-between lowerer in
`ExteriorComponentTopology`; it introduces no W-facing rows, boundary-cycle
rows, actual-sector rows, carrier rows, or induced frontier graph shortcut. -/
theorem S2_agent_q7_kcomponent_points_between_source_of_nontrivialRelativeClopen_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_nontrivialRelativeClopenKSide
    nontrivial_side

set_option linter.style.longLine false in
/-- Claim `S2-agent-q7-topology-boundary-bumping`, singleton side.

The concrete singleton boundary-bumping obstruction is sourced directly from
the already-known pointwise outside-accumulation row, uniformly in the finite
drawing inputs. -/
theorem S2_agent_q7_singleton_boundaryBumpingObstruction_family_of_outsideAccumulation_20260522
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
          C inputs :=
  fun C inputs =>
    unboundedExteriorSingletonFrontierBoundaryBumpingObstruction_of_outsideAccumulationForcesActualFrontier
      (C := C) (inputs := inputs) (outside_accumulation C inputs)

set_option linter.style.longLine false in
/-- Paired q7 source handoff for the two boundary-bumping topology leaves.

The global point-between leaf is lowered to the nontrivial relative-clopen
`K`-side primitive, while the singleton obstruction leaf is erased using the
pointwise outside-accumulation source. -/
theorem S2_agent_q7_topology_boundary_bumping_sources_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    And
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs) :=
  And.intro
    (S2_agent_q7_kcomponent_points_between_source_of_nontrivialRelativeClopen_20260522
      nontrivial_side)
    (S2_agent_q7_singleton_boundaryBumpingObstruction_family_of_outsideAccumulation_20260522
      outside_accumulation)

set_option linter.style.longLine false in
/-- Component-frontier graph incidence directly from the finite drawing.

For the concrete unbounded exterior component selected by
`FinitePlanarOuterComponentInputs`, a graph vertex on its frontier has an
incident canonical unit edge.  This is the source-level component wrapper over
`FinitePlaneDrawing.frontier_connectedComponentIn_drawingComplement_graph_vertex_incident`;
it proves only canonical graph incidence, leaving selected
`unboundedFrontierEdgeSet` membership to the later open-edge propagation row. -/
theorem S2_component_frontier_graph_vertex_incident_of_inputs_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    {v : Fin n}
    (hv :
      (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior) :
    Exists fun w : Fin n =>
      (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).Adj v w :=
  (unboundedExteriorComponentRows C inputs).frontier_graph_vertex_incident hv

set_option linter.style.longLine false in
/-- Claim `S2-frontier-open-segment-closure-source`.

The selected graph-vertex open-segment closure source is strictly lowered to
the pointwise punctured accumulation row for the same actual unbounded exterior
frontier.  The checked part is local: punctured accumulation near the graph
vertex supplies an incident canonical edge with one interior frontier point,
and the finite-drawing fixed-side relative-ball closure row propagates closure
to the whole open segment.  The finite input package is used only through the
actual selected exterior component; this route avoids final boundary cycles,
actual-sector rows, induced frontier graphs, all-adjacent endpoint claims,
convex hulls, identity angular rows, and W32 consumers. -/
theorem S2_frontier_open_segment_closure_source_of_puncturedAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (punctured :
      UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs) :
    FrontierVertexIncidentOpenSegmentClosureSource C inputs := by
  intro v hvfrontier
  exact
    incident_openSegment_closure_of_punctured_vertex_and_relative_ball_closure
      (C := C) (inputs := inputs) punctured
      (interiorRelativeBallClosureRow_of_fixed_side_halfballs
        (C := C) (inputs := inputs))
      hvfrontier

set_option linter.style.longLine false in
/-- Claim `S2-punctured-accumulation-source`, actual-frontier form.

The punctured graph-vertex accumulation row is strictly lowered to actual
frontier preconnectedness plus the singleton-frontier boundary-bumping
obstruction.  The proof uses the existing no-singleton reducer only to rule
out the isolated singleton case; it does not use final boundary cycles,
actual-sector rows, W32, carrier rows, induced frontier graphs, or
all-adjacent endpoint rows. -/
theorem S2_puncturedAccumulationSource_of_actualFrontierPreconnected_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (frontier_preconnected :
      UnboundedExteriorActualFrontierPreconnectedSource C inputs)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs :=
  unboundedExteriorFrontierVertexPuncturedAccumulationSource_of_frontierPreconnected_not_singleton
    (C := C) (inputs := inputs)
    (by
      simpa [UnboundedExteriorActualFrontierPreconnectedSource] using
        frontier_preconnected)
    (unboundedExterior_frontier_not_singleton_of_boundaryBumpingObstruction
      (C := C) (inputs := inputs) no_singleton_bumping)

set_option linter.style.longLine false in
/-- Claim `S2-q30-frontier-nontrivial-source`, actual-frontier form.

This exposes the q30 pointwise row in the punctured-accumulation handoff:
singleton boundary-bumping gives actual-frontier nontriviality at each graph
frontier vertex, and actual-frontier preconnectedness upgrades that to
punctured accumulation. -/
theorem S2_q30_puncturedAccumulationSource_of_actualFrontierPreconnected_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (frontier_preconnected :
      UnboundedExteriorActualFrontierPreconnectedSource C inputs)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs :=
  unboundedExteriorFrontierVertexPuncturedAccumulationSource_of_frontierPreconnected_nontrivialAt
    (C := C) (inputs := inputs)
    (by
      simpa [UnboundedExteriorActualFrontierPreconnectedSource] using
        frontier_preconnected)
    (frontier_nontrivialAt_of_unboundedExterior_frontier_not_singleton
      (C := C) (inputs := inputs)
      (unboundedExterior_frontier_not_singleton_of_boundaryBumpingObstruction
        (C := C) (inputs := inputs) no_singleton_bumping))

set_option linter.style.longLine false in
/-- Claim `S2-punctured-accumulation-source`, finite-drawing form.

Finite-drawing frontier preconnectedness specializes to the selected actual
unbounded exterior frontier, and the singleton boundary-bumping obstruction
rules out the only isolated-frontier case.  These are the exact remaining
leaves for the punctured accumulation source in this route. -/
theorem S2_puncturedAccumulationSource_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs :=
  S2_puncturedAccumulationSource_of_actualFrontierPreconnected_boundaryBumping_20260522
    (C := C) (inputs := inputs)
    (actualFrontierPreconnected_of_finiteDrawing_frontierPreconnected
      (C := C) inputs frontier_preconnected)
    no_singleton_bumping

set_option linter.style.longLine false in
/-- Claim `S2-q30-frontier-nontrivial-source`, finite-drawing form.

Finite-drawing frontier preconnectedness supplies the actual-frontier
preconnectedness needed to upgrade the q30 pointwise nontriviality row to the
punctured-accumulation source. -/
theorem S2_q30_puncturedAccumulationSource_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs :=
  S2_q30_puncturedAccumulationSource_of_actualFrontierPreconnected_boundaryBumping_20260522
    (C := C) (inputs := inputs)
    (actualFrontierPreconnected_of_finiteDrawing_frontierPreconnected
      (C := C) inputs frontier_preconnected)
    no_singleton_bumping

set_option linter.style.longLine false in
/-- The recent open-segment-closure consumer fed by the lowered punctured
accumulation source.

This keeps the consumer surface unchanged while exposing the exact local
topology leaves: finite-drawing frontier preconnectedness and the singleton
boundary-bumping obstruction. -/
theorem S2_frontier_open_segment_closure_source_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    FrontierVertexIncidentOpenSegmentClosureSource C inputs :=
  S2_frontier_open_segment_closure_source_of_puncturedAccumulation_20260522
    (C := C) inputs
    (S2_puncturedAccumulationSource_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
      (C := C) inputs frontier_preconnected no_singleton_bumping)

set_option linter.style.longLine false in
/-- Claim `S2-frontier-incident-selected-edge-source`.

The selected-edge endpoint source is strictly lowered to the local
open-segment closure row at frontier graph vertices.  The local row chooses an
incident canonical edge whose whole relative interior lies in the closure of
the selected exterior component; the existing selected-edge definition then
promotes that incident edge to `unboundedFrontierEdgeSet`.  This avoids final
boundary cycles, actual-sector rows, induced frontier graphs, all-adjacent
endpoint claims, convex hulls, identity angular rows, and global outgoing-list
no-between. -/
theorem S2_frontier_incident_selected_edge_source
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (incident_openSegment_closure :
      FrontierVertexIncidentOpenSegmentClosureSource C inputs) :
    FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs :=
  frontierVertexIncidentSource_of_incident_openSegment_closure
    (C := C) (inputs := inputs) incident_openSegment_closure

set_option linter.style.longLine false in
/-- Selected incident-edge source from the pointwise punctured component
frontier row.

This is the source-facing endpoint reducer for
`FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs`: finite component
frontier isolation supplies an incident canonical edge carrying a nearby
non-vertex frontier point, and the fixed-side open-edge propagation promotes
that edge to `unboundedFrontierEdgeSet`. -/
theorem S2_frontier_vertex_incident_source_of_puncturedAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (punctured :
      UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs) :
    FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs :=
  S2_frontier_incident_selected_edge_source
    (C := C) inputs
    (S2_frontier_open_segment_closure_source_of_puncturedAccumulation_20260522
      (C := C) inputs punctured)

set_option linter.style.longLine false in
/-- Claim `S2-q21-frontier-vertex-incident-source`, finite-preconnected form.

Finite-drawing preconnectedness of the actual unbounded exterior frontier plus
the singleton boundary-bumping obstruction supplies punctured accumulation at
each graph-frontier vertex.  The existing finite edge-isolation/open-segment
closure reducer then selects an incident actual `unboundedFrontierEdgeSet`
edge. -/
theorem S2_q21_frontierVertexIncidentSource_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs :=
  S2_frontier_vertex_incident_source_of_puncturedAccumulation_20260522
    (C := C) inputs
    (S2_puncturedAccumulationSource_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
      (C := C) inputs frontier_preconnected no_singleton_bumping)

set_option linter.style.longLine false in
/-- Claim `S2-q21-frontier-vertex-incident-source`, selected-cover form.

The q21 finite-preconnected incident-edge source is exactly the endpoint input
needed by the existing selected frontier-edge cover eraser; interior frontier
points are still handled by the finite fixed-side drawing row. -/
theorem S2_q21_selectedFrontierEdgeCover_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorSelectedFrontierEdgeCover C inputs :=
  unboundedExterior_selectedFrontierEdgeCover_of_frontierVertexIncident
    (C := C) inputs
    (S2_q21_frontierVertexIncidentSource_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
      (C := C) inputs frontier_preconnected no_singleton_bumping)

set_option linter.style.longLine false in
/-- Family form of
`S2_q21_frontierVertexIncidentSource_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522`. -/
theorem S2_q21_frontierVertexIncidentSource_family_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs :=
  fun C inputs =>
    S2_q21_frontierVertexIncidentSource_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
      (C := C) inputs frontier_preconnected (no_singleton_bumping C inputs)

set_option linter.style.longLine false in
/-- Family form of
`S2_q21_selectedFrontierEdgeCover_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522`. -/
theorem S2_q21_selectedFrontierEdgeCover_family_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorSelectedFrontierEdgeCover C inputs :=
  fun C inputs =>
    S2_q21_selectedFrontierEdgeCover_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
      (C := C) inputs frontier_preconnected (no_singleton_bumping C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-r7j-component-topology-input-source-punctured-20260521r7j`.

The component-topology input source can be filled from the finite-drawing
no-closed-separation theorem plus the graph-vertex punctured-accumulation
source.  The finite theorem supplies only actual frontier preconnectedness;
the punctured row supplies selected incident frontier edges through the
fixed-side open-edge propagation reducer.  No final boundary-cycle,
actual-sector, or carrier rows are used. -/
theorem S2_r7j_component_topology_input_source_of_finiteDrawingNoClosedSeparation_puncturedAccumulation_20260521r7j
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (punctured :
      UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_frontierVertexIncident
    (C := C) inputs frontier_noClosedSeparation
    (S2_frontier_vertex_incident_source_of_puncturedAccumulation_20260522
      (C := C) inputs punctured)

set_option linter.style.longLine false in
/-- Component-topology input rows from finite no-closed-separation and the
pointwise punctured component-frontier source.

This restates the r7j handoff at the current component-frontier source
surface: the only endpoint row below the input package is the punctured
same-frontier accumulation at graph vertices. -/
theorem S2_component_topology_input_source_of_finiteDrawingNoClosedSeparation_puncturedAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (punctured :
      UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_r7j_component_topology_input_source_of_finiteDrawingNoClosedSeparation_puncturedAccumulation_20260521r7j
    (C := C) inputs frontier_noClosedSeparation punctured

set_option linter.style.longLine false in
/-- Family form of
`S2_r7j_component_topology_input_source_of_finiteDrawingNoClosedSeparation_puncturedAccumulation_20260521r7j`. -/
theorem S2_r7j_component_topology_input_source_family_of_finiteDrawingNoClosedSeparation_puncturedAccumulation_20260521r7j
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (punctured :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierVertexPuncturedAccumulationSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  fun C inputs =>
    S2_r7j_component_topology_input_source_of_finiteDrawingNoClosedSeparation_puncturedAccumulation_20260521r7j
      (C := C) inputs frontier_noClosedSeparation (punctured C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-r29-component-topology-input-source-20260521r29`.

The input-facing component-topology leaf is reduced to the finite drawing
no-closed-separation topology theorem plus actual carrier neighbour-pair rows.
The topology theorem is used only for frontier preconnectedness; the
neighbour-pair rows give the selected endpoint-incidence field directly. -/
theorem S2_r29_component_topology_input_source_20260521r29
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_frontierVertexIncident
    (C := C) inputs frontier_noClosedSeparation
    (frontierVertexIncidentSource_of_neighborPairRows
      (C := C) (inputs := inputs) neighborRows)

set_option linter.style.longLine false in
/-- Claim `S2-r39-component-topology-input-source-20260521r39`.

The sharp r29 input reducer is composed with the existing topology route from
the current nontrivial relative-clopen `K`-side source to finite-drawing
no-closed-separation.  The only remaining premises are the topology leaf and
the pointwise actual carrier neighbour-pair rows for graph vertices on the
selected unbounded exterior frontier. -/
theorem S2_r39_component_topology_input_source_20260521r39
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_r29_component_topology_input_source_20260521r29
    (C := C) inputs
    (finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_nontrivialRelativeClopenKSide
      nontrivial_side)
    neighborRows

set_option linter.style.longLine false in
/-- Family form of `S2_r39_component_topology_input_source_20260521r39`. -/
theorem S2_r39_component_topology_input_source_family_20260521r39
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  fun C inputs =>
    S2_r39_component_topology_input_source_20260521r39
      (C := C) inputs nontrivial_side (neighborRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-r41-topology-source-leaf-reduction-20260521r41`.

The r39 component-topology input reducer does not need the planar-continuum
nontrivial relative-clopen source when the finite embedded-drawing version is
available.  The finite source directly supplies the finite no-closed-separation
row used for actual-frontier preconnectedness; the pointwise neighbour rows are
kept unchanged as the selected incident-edge source. -/
theorem S2_r41_component_topology_input_source_of_finiteDrawing_nontrivialRelativeClopen_20260521r41
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (nontrivial_side :
      FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (neighborRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierNeighborPairAt inputs a) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_r29_component_topology_input_source_20260521r29
    (C := C) inputs
    (finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_finiteDrawing_nontrivialRelativeClopenKSide
      nontrivial_side)
    neighborRows

set_option linter.style.longLine false in
/-- Family form of
`S2_r41_component_topology_input_source_of_finiteDrawing_nontrivialRelativeClopen_20260521r41`. -/
theorem S2_r41_component_topology_input_source_family_of_finiteDrawing_nontrivialRelativeClopen_20260521r41
    (nontrivial_side :
      FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  fun C inputs =>
    S2_r41_component_topology_input_source_of_finiteDrawing_nontrivialRelativeClopen_20260521r41
      (C := C) inputs nontrivial_side (neighborRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-r6e-component-topology-input-local-sector-reducer-20260521r6e`.

The component-topology input source only needs the finite drawing
no-closed-separation row for actual frontier preconnectedness and the existing
local-sector incident-edge source for the endpoint field.  This avoids the
stronger neighbour-pair premise and does not use actual-sector or final
boundary rows. -/
theorem S2_r6e_component_topology_input_source_of_finiteDrawingNoClosedSeparation_localSectorRows_20260521r6e
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_frontierVertexIncident
    (C := C) inputs frontier_noClosedSeparation
    (frontierVertexIncidentSource_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_r6e_component_topology_input_source_of_finiteDrawingNoClosedSeparation_localSectorRows_20260521r6e`. -/
theorem S2_r6e_component_topology_input_source_family_of_finiteDrawingNoClosedSeparation_localSectorRows_20260521r6e
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  fun C inputs =>
    S2_r6e_component_topology_input_source_of_finiteDrawingNoClosedSeparation_localSectorRows_20260521r6e
      (C := C) inputs frontier_noClosedSeparation (localSectorRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-k6g-component-topology-input-source`.

The component-topology input package is lowered to the live topology leaf plus
actual local-sector rows.  The topology leaf supplies actual frontier
preconnectedness through the finite-drawing no-closed-separation handoff; the
local-sector rows supply the selected incident frontier edge at every actual
frontier carrier vertex. -/
def S2_k6g_component_topology_input_source_of_nontrivialRelativeClopen_localSectorRows
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs where
  frontier_preconnected :=
    actualFrontierPreconnected_of_finiteDrawing_noClosedSeparation
      (C := C) inputs
      (finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_nontrivialRelativeClopenKSide
        nontrivial_side)
  frontier_vertex_incident :=
    frontierVertexIncidentSource_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows

set_option linter.style.longLine false in
/-- Family form of
`S2_k6g_component_topology_input_source_of_nontrivialRelativeClopen_localSectorRows`. -/
theorem S2_k6g_component_topology_input_source_family_of_nontrivialRelativeClopen_localSectorRows
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  fun C inputs =>
    S2_k6g_component_topology_input_source_of_nontrivialRelativeClopen_localSectorRows
      (C := C) inputs nontrivial_side (localSectorRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-r13-component-topology-input-source`, exact input theorem.

The named input source is reduced to the smallest component-topology surface
already isolated in the owner file: finite-drawing no-closed-separation for
the actual embedded drawing, plus the exact selected-edge incidence row at
frontier graph vertices.  The topology premise only supplies
actual-frontier preconnectedness; the incidence field is passed through
unchanged. -/
theorem unboundedExteriorFrontierComponentTopologyInputSourceRows_of_inputs
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (frontier_vertex_incident :
      FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_frontierVertexIncident
    (C := C) inputs frontier_noClosedSeparation frontier_vertex_incident

set_option linter.style.longLine false in
/-- The r13 input source with the finite no-closed-separation topology premise
fed by the Janiszewski/boundary-bumping no-subcontinuum obstruction. -/
theorem S2_r13_component_topology_input_source_of_janiszewskiNoSubcontinuum_vertexIncident_20260521r13
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (no_subcontinuum :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction)
    (frontier_vertex_incident :
      FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  unboundedExteriorFrontierComponentTopologyInputSourceRows_of_inputs
    (C := C) inputs
    (finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_janiszewskiNoSubcontinuumObstruction
      no_subcontinuum)
    frontier_vertex_incident

set_option linter.style.longLine false in
/-- The r13 input source lowered through the current nontrivial relative-clopen
`K`-side topology primitive. -/
theorem S2_r13_component_topology_input_source_of_nontrivialRelativeClopen_vertexIncident_20260521r13
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (frontier_vertex_incident :
      FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_r13_component_topology_input_source_of_janiszewskiNoSubcontinuum_vertexIncident_20260521r13
    (C := C) inputs
    (planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_nontrivialRelativeClopenKSide
      nontrivial_side)
    frontier_vertex_incident

set_option linter.style.longLine false in
/-- Claim `S2-r14-no-open-separation-topology-source`, finite handoff.

The finite-drawing no-open-separation source is strictly lowered to the
already isolated finite-drawing no-closed-separation source.  This is only the
Mathlib conversion from closed-piece nonseparation to preconnectedness and then
to the open-cover criterion; it introduces no boundary cycle, actual-sector
package, carrier row, induced frontier graph, or W32 consumer. -/
theorem S2_r14_finiteDrawing_noOpenSeparation_of_finiteDrawingNoClosedSeparation_20260521r14
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
  finiteDrawingUnboundedComplementFrontierNoOpenSeparation_of_frontierPreconnected
    (finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
      frontier_noClosedSeparation)

set_option linter.style.longLine false in
/-- Claim `S2-r14-no-open-separation-topology-source`, actual component.

Specialize the finite no-open-separation row to the concrete unbounded exterior
component selected by `unboundedExteriorComponentRows C inputs`. -/
theorem S2_r14_noOpenSeparationSource_of_finiteDrawingNoClosedSeparation_20260521r14
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation) :
    UnboundedExteriorFrontierNoOpenSeparationSource C inputs :=
  unboundedExterior_frontier_noOpenSeparation_of_finiteDrawing_continuum
    (C := C) inputs
    (S2_r14_finiteDrawing_noOpenSeparation_of_finiteDrawingNoClosedSeparation_20260521r14
      frontier_noClosedSeparation)

set_option linter.style.longLine false in
/-- Janiszewski/no-subcontinuum source for the r14 finite no-open-separation
row. -/
theorem S2_r14_finiteDrawing_noOpenSeparation_of_janiszewskiNoSubcontinuum_20260521r14
    (no_subcontinuum :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
  S2_r14_finiteDrawing_noOpenSeparation_of_finiteDrawingNoClosedSeparation_20260521r14
    (finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_janiszewskiNoSubcontinuumObstruction
      no_subcontinuum)

set_option linter.style.longLine false in
/-- Janiszewski/no-subcontinuum source for the actual selected exterior
frontier no-open-separation row. -/
theorem S2_r14_noOpenSeparationSource_of_janiszewskiNoSubcontinuum_20260521r14
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (no_subcontinuum :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction) :
    UnboundedExteriorFrontierNoOpenSeparationSource C inputs :=
  S2_r14_noOpenSeparationSource_of_finiteDrawingNoClosedSeparation_20260521r14
    (C := C) inputs
    (finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_janiszewskiNoSubcontinuumObstruction
      no_subcontinuum)

set_option linter.style.longLine false in
/-- Nontrivial relative-clopen `K`-side source for the actual selected exterior
frontier no-open-separation row. -/
theorem S2_r14_noOpenSeparationSource_of_nontrivialRelativeClopen_20260521r14
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    UnboundedExteriorFrontierNoOpenSeparationSource C inputs :=
  S2_r14_noOpenSeparationSource_of_janiszewskiNoSubcontinuum_20260521r14
    (C := C) inputs
    (planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_nontrivialRelativeClopenKSide
      nontrivial_side)

set_option linter.style.longLine false in
/-- Compact-connected no-crossing source for the actual selected exterior
frontier no-open-separation row, routed through the existing finite
no-closed-separation topology source. -/
theorem S2_r14_noOpenSeparationSource_of_noCompactConnectedKCrossing_20260521r14
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    UnboundedExteriorFrontierNoOpenSeparationSource C inputs :=
  S2_r14_noOpenSeparationSource_of_finiteDrawingNoClosedSeparation_20260521r14
    (C := C) inputs
    (S2_subagent_topology_source_20260521_current_finiteDrawing_noClosedSeparation_of_noCompactConnectedKCrossing
      no_crossing)

set_option linter.style.longLine false in
/-- Family form of the r14 no-open-separation source from the compact-connected
no-crossing topology primitive. -/
theorem S2_r14_noOpenSeparationSource_family_of_noCompactConnectedKCrossing_20260521r14
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierNoOpenSeparationSource C inputs :=
  fun C inputs =>
    S2_r14_noOpenSeparationSource_of_noCompactConnectedKCrossing_20260521r14
      (C := C) inputs no_crossing

set_option linter.style.longLine false in
/-- Claim `S2-r17-no-open-topology-source`.

The finite-drawing no-open-separation topology leaf is strictly lowered to the
same-`K` Janiszewski boundary-bumping point-between theorem.  The proof first
uses the already checked r59 finite no-closed reducer, then applies only the
closed-piece/preconnected/no-open topology conversion.  It introduces no
actual-sector rows, boundary-cycle rows, carrier rows derived from final S2,
W32 consumer, or final S2 assumption.

Exact remaining theorem:
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween`. -/
theorem S2_r17_finiteDrawing_noOpenSeparation_of_kComponentPointsBetween_20260521r17
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
  finiteDrawingUnboundedComplementFrontierNoOpenSeparation_of_frontierPreconnected
    (finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
      (S2_r59_finiteDrawing_noClosedSeparation_of_kComponentPointsBetween_20260521r59
        points_between))

set_option linter.style.longLine false in
/-- Claim `S2-r19-topology-noopen-source`.

The finite-drawing no-open-separation topology leaf is strictly lowered to the
sharp same-`K` Janiszewski frontier-component theorem.  This is exactly the
current r18/r17 topology route: r18 packages the frontier component as the
same-`K` point-between source, and r17 converts that source to the finite
no-open-separation row.  It uses no W32 rows, actual-sector rows,
boundary-cycle rows, or carrier rows. -/
theorem S2_r19_finiteDrawing_noOpenSeparation_of_kComponentFrontierComponent_20260521r19
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
  finiteDrawingUnboundedComplementFrontierNoOpenSeparation_of_kComponentFrontierComponent
    frontier_component

set_option linter.style.longLine false in
/-- Claim `S2-r19-topology-frontier-component-source`, finite no-closed side.

The finite-drawing no-closed-separation topology leaf is lowered to the same
direct Janiszewski frontier-component source used by the r19 no-open handoff.
This shares the r18 component-to-point-between packaging and no
boundary-cycle, actual-sector, carrier, W32, or final S2 row. -/
theorem S2_r19_finiteDrawing_noClosedSeparation_of_kComponentFrontierComponent_20260521r19
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_kComponentFrontierComponent
    frontier_component

set_option linter.style.longLine false in
/-- Finite frontier preconnectedness from the same-`K` frontier-component
source.

This lowers `FiniteDrawingUnboundedComplementFrontierPreconnected` through the
checked finite no-closed-separation reducer and Mathlib's closed-piece
preconnectedness criterion, without introducing any finite frontier-cycle or
W-facing route. -/
theorem
    finiteDrawingUnboundedComplementFrontierPreconnected_of_kComponentFrontierComponent_20260522
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    FiniteDrawingUnboundedComplementFrontierPreconnected :=
  finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
    (S2_r19_finiteDrawing_noClosedSeparation_of_kComponentFrontierComponent_20260521r19
      frontier_component)

set_option linter.style.longLine false in
/-- Paired r19 finite no-open/no-closed decomposition from the same
frontier-component source. -/
theorem S2_r19_finiteDrawing_noOpen_noClosed_of_kComponentFrontierComponent_20260521r19
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  ⟨S2_r19_finiteDrawing_noOpenSeparation_of_kComponentFrontierComponent_20260521r19
      frontier_component,
    S2_r19_finiteDrawing_noClosedSeparation_of_kComponentFrontierComponent_20260521r19
      frontier_component⟩

set_option linter.style.longLine false in
/-- Point-between form of the r19 finite no-open/no-closed topology source.

The new q9 local trace bridge supplies the same-`K` frontier-component source
consumed by the existing finite no-open/no-closed handoff. -/
theorem S2_r19_finiteDrawing_noOpen_noClosed_of_kComponentPointsBetween_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  S2_r19_finiteDrawing_noOpen_noClosed_of_kComponentFrontierComponent_20260521r19
    (S2_agent_q9_topology_frontier_component_of_kComponentPointsBetween_20260522
      points_between)

set_option linter.style.longLine false in
/-- Continuous-side lower form of `S2_r19_finiteDrawing_noOpenSeparation_of_kComponentFrontierComponent_20260521r19`. -/
theorem S2_r19_finiteDrawing_noOpenSeparation_of_continuousKSide_20260521r19
    (continuous_side :
      PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
  S2_r19_finiteDrawing_noOpenSeparation_of_kComponentFrontierComponent_20260521r19
    (planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_continuousKSide
      continuous_side)

set_option linter.style.longLine false in
/-- Claim `S2-r19-topology-frontier-component-source`, source lowerer.

The Janiszewski same-`K` frontier-component source needed by the finite
no-open/no-closed handoff is strictly reduced to the hard-case aligned
closed-split planar-continuum source. -/
theorem S2_r19_topology_frontier_component_source_of_nontrivialAlignedKSplit_20260521r19
    (nontrivial_aligned_K_split :
      PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
  planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_nontrivialAlignedKSplit
    nontrivial_aligned_K_split

set_option linter.style.longLine false in
/-- Aligned-split lower form of the r19 finite no-open-separation source. -/
theorem S2_r19_finiteDrawing_noOpenSeparation_of_nontrivialAlignedKSplit_20260521r19
    (nontrivial_aligned_K_split :
      PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
  S2_r19_finiteDrawing_noOpenSeparation_of_kComponentFrontierComponent_20260521r19
    (S2_r19_topology_frontier_component_source_of_nontrivialAlignedKSplit_20260521r19
      nontrivial_aligned_K_split)

set_option linter.style.longLine false in
/-- Aligned-split lower form of the r19 finite no-closed-separation source. -/
theorem S2_r19_finiteDrawing_noClosedSeparation_of_nontrivialAlignedKSplit_20260521r19
    (nontrivial_aligned_K_split :
      PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  S2_r19_finiteDrawing_noClosedSeparation_of_kComponentFrontierComponent_20260521r19
    (S2_r19_topology_frontier_component_source_of_nontrivialAlignedKSplit_20260521r19
      nontrivial_aligned_K_split)

set_option linter.style.longLine false in
/-- Aligned-split lower form of the paired r19 finite no-open/no-closed
decomposition. -/
theorem S2_r19_finiteDrawing_noOpen_noClosed_of_nontrivialAlignedKSplit_20260521r19
    (nontrivial_aligned_K_split :
      PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  S2_r19_finiteDrawing_noOpen_noClosed_of_kComponentFrontierComponent_20260521r19
    (S2_r19_topology_frontier_component_source_of_nontrivialAlignedKSplit_20260521r19
      nontrivial_aligned_K_split)

set_option linter.style.longLine false in
/-- Claim `S2-r20-topology-frontier-component-source`.

The current same-`K` Janiszewski frontier-component topology leaf behind the
finite no-open/no-closed handoff is strictly lowered to the `x`-indexed
nontrivial relative-clopen `K`-side theorem.  The checked owner adapter opens a
hypothetical frontier-component split by compact-Hausdorff clopen separation
and contradicts the displayed same-`K` component relation; this theorem adds
only the r20 name for that topology-only source reduction, with no
boundary-cycle, carrier, actual-sector, W32, induced-graph, or arbitrary-cycle
rows. -/
theorem S2_r20_topology_frontier_component_source_of_nontrivialRelativeClopenKSide_20260521r20
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
  planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_nontrivialRelativeClopenKSide
    nontrivial_side

set_option linter.style.longLine false in
/-- r20 finite no-open handoff using the strictly lowered frontier-component
source. -/
theorem S2_r20_finiteDrawing_noOpenSeparation_of_nontrivialRelativeClopenKSide_20260521r20
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
  S2_r19_finiteDrawing_noOpenSeparation_of_kComponentFrontierComponent_20260521r19
    (S2_r20_topology_frontier_component_source_of_nontrivialRelativeClopenKSide_20260521r20
      nontrivial_side)

set_option linter.style.longLine false in
/-- r20 finite no-closed handoff using the strictly lowered
frontier-component source. -/
theorem S2_r20_finiteDrawing_noClosedSeparation_of_nontrivialRelativeClopenKSide_20260521r20
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  S2_r19_finiteDrawing_noClosedSeparation_of_kComponentFrontierComponent_20260521r19
    (S2_r20_topology_frontier_component_source_of_nontrivialRelativeClopenKSide_20260521r20
      nontrivial_side)

set_option linter.style.longLine false in
/-- Paired r20 finite no-open/no-closed decomposition from the lowered
relative-clopen side source. -/
theorem S2_r20_finiteDrawing_noOpen_noClosed_of_nontrivialRelativeClopenKSide_20260521r20
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  ⟨S2_r20_finiteDrawing_noOpenSeparation_of_nontrivialRelativeClopenKSide_20260521r20
      nontrivial_side,
    S2_r20_finiteDrawing_noClosedSeparation_of_nontrivialRelativeClopenKSide_20260521r20
      nontrivial_side⟩

set_option linter.style.longLine false in
/-- Claim `S2-agent-pool8-topology-no-open-source`, finite drawing.

The finite-drawing no-open-separation leaf is lowered directly through
frontier preconnectedness from the current nontrivial relative-clopen `K`-side
topology source.  This avoids the frontier-component packaging and uses only
the topology-only preconnected/no-open conversion. -/
theorem S2_agent_pool8_finiteDrawing_noOpenSeparation_of_nontrivialRelativeClopenKSide_20260521pool8
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
  finiteDrawingUnboundedComplementFrontierNoOpenSeparation_of_frontierPreconnected
    (finiteDrawingUnboundedComplementFrontierPreconnected_of_planarContinuum
      (planarContinuumUnboundedComplementFrontierPreconnected_of_nontrivialRelativeClopenKSide
        nontrivial_side))

set_option linter.style.longLine false in
/-- Claim `S2-agent-pool8-topology-no-open-source`, actual exterior component.

The same finite topology row specializes to the no-open source for the
frontier of `unboundedExteriorComponentRows C inputs`, with no boundary-cycle,
actual-sector, W32, carrier, induced-frontier-graph, arbitrary-cycle, or
synthetic-enclosure input. -/
theorem S2_agent_pool8_noOpenSeparationSource_of_nontrivialRelativeClopenKSide_20260521pool8
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    UnboundedExteriorFrontierNoOpenSeparationSource C inputs :=
  unboundedExterior_frontier_noOpenSeparation_of_finiteDrawing_continuum
    (C := C) inputs
    (S2_agent_pool8_finiteDrawing_noOpenSeparation_of_nontrivialRelativeClopenKSide_20260521pool8
      nontrivial_side)

set_option linter.style.longLine false in
/-- Claim `S2-r23-no-open-topology-source`, planar-continuum form.

The no-open-separation theorem surface is equivalent to the direct
preconnectedness theorem surface.  This is only Mathlib's
`IsPreconnected`/two-open-set criterion; no boundary cycle, actual-sector row,
carrier row, W32 consumer, or final S2 theorem is used. -/
theorem S2_r23_planarContinuum_noOpenSeparation_iff_preconnected_20260521r23 :
    PlanarContinuumUnboundedComplementFrontierNoOpenSeparation ↔
      PlanarContinuumUnboundedComplementFrontierPreconnected := by
  constructor
  · intro no_open K x hcompact hconnected hx hunbounded
    exact
      isPreconnected_of_noOpenSeparation
        (no_open K x hcompact hconnected hx hunbounded)
  · intro frontier_preconnected
    exact
      planarContinuumUnboundedComplementFrontierNoOpenSeparation_of_preconnected
        frontier_preconnected

set_option linter.style.longLine false in
/-- Claim `S2-r23-no-open-topology-source`, finite drawing forward direction.

The finite-drawing no-open-separation row lowers to the closest topology
primitive: direct preconnectedness of each unbounded complement-component
frontier of the embedded finite drawing. -/
theorem S2_r23_finiteDrawing_frontierPreconnected_of_noOpenSeparation_20260521r23
    (frontier_noOpen :
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation) :
    FiniteDrawingUnboundedComplementFrontierPreconnected := by
  intro m C inputs x hx hunbounded
  exact
    isPreconnected_of_noOpenSeparation
      (frontier_noOpen C inputs x hx hunbounded)

set_option linter.style.longLine false in
/-- Claim `S2-r23-no-open-topology-source`, finite drawing equivalence.

The finite no-open source is just the open-cover presentation of
`FiniteDrawingUnboundedComplementFrontierPreconnected`.  Thus the remaining
finite topology leaf is the preconnectedness theorem, not another
no-open alias. -/
theorem S2_r23_finiteDrawing_noOpenSeparation_iff_frontierPreconnected_20260521r23 :
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation ↔
      FiniteDrawingUnboundedComplementFrontierPreconnected := by
  constructor
  · intro frontier_noOpen
    exact
      S2_r23_finiteDrawing_frontierPreconnected_of_noOpenSeparation_20260521r23
        frontier_noOpen
  · intro frontier_preconnected
    exact
      finiteDrawingUnboundedComplementFrontierNoOpenSeparation_of_frontierPreconnected
        frontier_preconnected

set_option linter.style.longLine false in
/-- Claim `S2-r23-no-open-topology-source`, actual exterior forward direction.

For the selected unbounded exterior component, the current no-open source
lowers exactly to preconnectedness of its actual frontier. -/
theorem S2_r23_actualFrontierPreconnected_of_noOpenSeparationSource_20260521r23
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (source : UnboundedExteriorFrontierNoOpenSeparationSource C inputs) :
    UnboundedExteriorActualFrontierPreconnectedSource C inputs :=
  unboundedExterior_frontier_preconnected_of_noOpenSeparationSource
    (C := C) (inputs := inputs) source

set_option linter.style.longLine false in
/-- Claim `S2-r23-no-open-topology-source`, actual exterior equivalence.

The actual no-open source is exactly the open-cover form of
`UnboundedExteriorActualFrontierPreconnectedSource`. -/
theorem S2_r23_noOpenSeparationSource_iff_actualFrontierPreconnected_20260521r23
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C} :
    UnboundedExteriorFrontierNoOpenSeparationSource C inputs ↔
      UnboundedExteriorActualFrontierPreconnectedSource C inputs := by
  constructor
  · intro source
    exact
      S2_r23_actualFrontierPreconnected_of_noOpenSeparationSource_20260521r23
        (C := C) (inputs := inputs) source
  · intro frontier_preconnected
    exact
      unboundedExterior_frontier_noOpenSeparation_of_actualFrontierPreconnected
        (C := C) (inputs := inputs) frontier_preconnected

set_option linter.style.longLine false in
/-- Claim `S2-r23-no-open-topology-source`, finite-to-actual handoff.

The current actual no-open source can be sourced from the finite-drawing
preconnectedness leaf by specializing to `unboundedExteriorComponentRows`.
This keeps the remaining leaf at the `IsPreconnected` topology primitive. -/
theorem S2_r23_noOpenSeparationSource_of_finiteDrawing_frontierPreconnected_20260521r23
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected) :
    UnboundedExteriorFrontierNoOpenSeparationSource C inputs :=
  unboundedExterior_frontier_noOpenSeparation_of_finiteDrawing_frontierPreconnected
    (C := C) inputs frontier_preconnected

set_option linter.style.longLine false in
/-- Claim `S2-topology-preconnected-leaf`, finite drawing form.

The finite frontier-preconnectedness leaf is strictly lowered to the named
Janiszewski/boundary-bumping relative-clopen primitive.  The reducer stays at
the source-level topology surface: it uses the planar-continuum
preconnectedness theorem and the finite-drawing specialization, with no
boundary-cycle, actual-sector, carrier, W32, synthetic-enclosure, or
identity-order input. -/
theorem S2_topology_preconnected_leaf_finiteDrawing_of_janiszewskiBoundaryBumping_20260521
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide) :
    FiniteDrawingUnboundedComplementFrontierPreconnected :=
  finiteDrawingUnboundedComplementFrontierPreconnected_of_planarContinuum
    (planarContinuumUnboundedComplementFrontierPreconnected_of_janiszewskiRelativeClopenKSide
      boundary_bumping)

set_option linter.style.longLine false in
/-- Claim `S2-topology-preconnected-leaf`, actual exterior form.

The selected unbounded exterior frontier-preconnectedness source is the same
Janiszewski/boundary-bumping topology primitive specialized to
`unboundedExteriorComponentRows C inputs`. -/
theorem S2_topology_preconnected_leaf_actualFrontier_of_janiszewskiBoundaryBumping_20260521
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide) :
    UnboundedExteriorActualFrontierPreconnectedSource C inputs :=
  actualFrontierPreconnected_of_janiszewskiBoundaryBumping
    (C := C) inputs boundary_bumping

set_option linter.style.longLine false in
/-- Claim `S2-topology-preconnected-leaf`.

Paired source-level topology reducer for the two live preconnectedness leaves:
the finite-drawing frontier-preconnectedness theorem and the actual selected
exterior frontier-preconnectedness source both come from the already named
Janiszewski/boundary-bumping relative-clopen primitive. -/
theorem S2_topology_preconnected_leaf_20260521
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide) :
    FiniteDrawingUnboundedComplementFrontierPreconnected /\
      UnboundedExteriorActualFrontierPreconnectedSource C inputs :=
  ⟨S2_topology_preconnected_leaf_finiteDrawing_of_janiszewskiBoundaryBumping_20260521
      boundary_bumping,
    S2_topology_preconnected_leaf_actualFrontier_of_janiszewskiBoundaryBumping_20260521
      (C := C) inputs boundary_bumping⟩

set_option linter.style.longLine false in
/-- Claim `S2-dyn-topology-nontrivial-side`, planar source form.

The x-indexed nontrivial relative-clopen `K`-side source is strictly reduced
to the current U-indexed Janiszewski/boundary-bumping relative-clopen
primitive.  The checked step only specializes the displayed unbounded
component to `connectedComponentIn K^c x`; it does not use final boundary-cycle
rows, actual-sector rows, carrier rows, or W32 consumers. -/
theorem S2_dyn_topology_nontrivial_side_of_janiszewskiBoundaryBumping_20260522
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
  planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_janiszewskiBoundaryBumping
    boundary_bumping

set_option linter.style.longLine false in
/-- Claim `S2-dyn-topology-nontrivial-side`, finite preconnected form.

For the finite S2 compactum, direct frontier preconnectedness already rules out
the nonempty closed frontier split in the nontrivial relative-clopen side
obligation, so no `K`-side chooser has to be imported from downstream
boundary-cycle or actual-sector routes. -/
theorem S2_dyn_topology_finite_nontrivial_side_of_frontierPreconnected_20260522
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected) :
    FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
  finiteDrawingUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_frontierPreconnected
    frontier_preconnected

set_option linter.style.longLine false in
/-- Claim `S2-dyn-topology-nontrivial-side`.

The current dynamic topology side exposes both useful nontrivial-side surfaces:
the planar continuum source comes from the Janiszewski/boundary-bumping
relative-clopen primitive, and the finite drawing source comes from the
preconnectedness leaf sourced by the same primitive. -/
theorem S2_dyn_topology_nontrivial_side_20260522
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide /\
      FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
  And.intro
    (S2_dyn_topology_nontrivial_side_of_janiszewskiBoundaryBumping_20260522
      boundary_bumping)
    (S2_dyn_topology_finite_nontrivial_side_of_frontierPreconnected_20260522
      (S2_topology_preconnected_leaf_finiteDrawing_of_janiszewskiBoundaryBumping_20260521
        boundary_bumping))

set_option linter.style.longLine false in
/-- The x-indexed crossing-subcontinuum boundedness source is exactly the
boundedness form of the older no-compact-connected-`K`-crossing primitive.

If the selected component is already bounded, there is nothing to prove; if it
is unbounded, the no-crossing primitive rules out the displayed compact
connected crossing subcontinuum.  This adapter stays at the topology source
surface and introduces no boundary-cycle, carrier, actual-sector,
synthetic-enclosure, or W32 dependency. -/
theorem
    planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_noCompactConnectedKCrossing_20260522
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded := by
  intro K x A B T hcompact hx hAclosed hBclosed hABdisjoint hcover
    hTcompact hTconnected hTsubset hTA hTB
  by_cases hbounded :
      Bornology.IsBounded (connectedComponentIn (Set.compl K) x)
  case pos =>
    exact hbounded
  case neg =>
    exfalso
    exact no_crossing K x A B hcompact hx hbounded hAclosed hBclosed
      hABdisjoint hcover T hTcompact hTconnected hTsubset hTA hTB

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-topology-source-leaf-20260522`, crossing-bounded side.

The remaining crossing-subcontinuum boundedness predicate is strictly lowered
to the existing no-compact-connected-`K`-crossing topology primitive. -/
theorem S2_dynamic_topology_crossingSubcontinuumForcesBounded_of_noCompactConnectedKCrossing_20260522
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded :=
  planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_noCompactConnectedKCrossing_20260522
    no_crossing

set_option linter.style.longLine false in
/-- Claim `S2-crossing-topology-source`.

The crossing-subcontinuum boundedness topology leaf is strictly lowered to the
same-`K` Janiszewski boundary-bumping point-between theorem.  The checked
composition first turns same-`K` point-between into the no-compact-connected
`K`-crossing exclusion, then applies the boundedness wrapper above.  The exact
remaining topology leaf is
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween`;
no final boundary cycle, actual-sector row, carrier row, W32 facade, induced
frontier graph, all-adjacent endpoint row, or finite no-closed-separation
premise is used. -/
theorem S2_crossing_topology_source_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded :=
  S2_dynamic_topology_crossingSubcontinuumForcesBounded_of_noCompactConnectedKCrossing_20260522
    (planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_janiszewskiKComponentPointsBetween_20260521r7d
      points_between)

set_option linter.style.longLine false in
/-- Post-preconnected topology source leaf.

The compact/frontier no-compact-connected-`K`-crossing theorem is strictly
lowered to the x-indexed crossing-subcontinuum boundedness source.  If a compact
connected subset of `K` crossed the two closed frontier sides while the selected
complement component were unbounded, the boundedness source would give the
forbidden boundedness conclusion directly.  This uses no boundary-cycle,
actual-sector, synthetic-enclosure, or W32 facade dependency. -/
theorem
    planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_crossingSubcontinuumForcesBounded_20260522
    (crossing_forces_bounded :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    T hTcompact hTconnected hTsubset hTA hTB
  exact
    hunbounded
      (crossing_forces_bounded K x A B T hcompact hx hAclosed hBclosed
        hABdisjoint hcover hTcompact hTconnected hTsubset hTA hTB)

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-topology-source-leaf-20260522`, no-compact side.

The remaining theorem for the no-compact-connected-`K`-crossing target is now
exactly
`PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded`. -/
theorem S2_dynamic_topology_noCompactConnectedKCrossing_of_crossingSubcontinuumForcesBounded_20260522
    (crossing_forces_bounded :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_crossingSubcontinuumForcesBounded_20260522
    crossing_forces_bounded

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-topology-source-leaf-20260522`, finite no-closed side.

The same boundedness source also feeds the finite-drawing no-closed-separation
target through the existing no-compact-connected-`K`-crossing handoff. -/
theorem S2_dynamic_topology_finiteDrawing_noClosedSeparation_of_crossingSubcontinuumForcesBounded_20260522
    (crossing_forces_bounded :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  S2_subagent_topology_source_20260521_current_finiteDrawing_noClosedSeparation_of_noCompactConnectedKCrossing
    (S2_dynamic_topology_noCompactConnectedKCrossing_of_crossingSubcontinuumForcesBounded_20260522
      crossing_forces_bounded)

set_option linter.style.longLine false in
/-- Crossing-witness no-closed-separation source for the compact/frontier
no-crossing topology leaf.

This is the no-closed-separation surface with the exact extra data available
in the live no-compact-connected-`K`-crossing target: `K` is only compact, but
it carries a compact connected witness `T <= K` meeting the selected frontier.
For genuine planar continua this is supplied by
`PlanarContinuumUnboundedComplementFrontierNoClosedSeparation`; the remaining
gap is precisely removing global connectedness of `K` in favor of the local
crossing witness. -/
def PlanarContinuumUnboundedComplementFrontierCrossingWitnessNoClosedSeparation :
    Prop :=
  forall (K : Set PlanarInterface.Point) (x : PlanarInterface.Point)
      (T : Set PlanarInterface.Point),
    IsCompact K ->
      x ∈ Kᶜ ->
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x) ->
          IsCompact T ->
            IsConnected T ->
              T ⊆ K ->
                (T ∩ frontier (connectedComponentIn Kᶜ x)).Nonempty ->
                  NoClosedSeparation (frontier (connectedComponentIn Kᶜ x))

set_option linter.style.longLine false in
/-- The crossing-witness no-closed-separation source is enough for the current
compact/frontier no-compact-connected-`K`-crossing primitive.

The proof extracts a frontier point from one crossed side to satisfy the
source's local trace hypothesis, then applies `NoClosedSeparation` to the
displayed closed split `frontier U = A ∪ B`. -/
theorem
    planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_crossingWitnessNoClosedSeparation_20260522q34
    (frontier_noClosed :
      PlanarContinuumUnboundedComplementFrontierCrossingWitnessNoClosedSeparation) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    T hTcompact hTconnected hTsubset hTA hTB
  let U : Set PlanarInterface.Point := connectedComponentIn Kᶜ x
  have htrace_nonempty : (T ∩ frontier U).Nonempty := by
    rcases hTA with ⟨y, hyT, hyA⟩
    have hyFrontier : y ∈ frontier U := by
      rw [hcover]
      exact Or.inl hyA
    exact ⟨y, hyT, hyFrontier⟩
  have hfrontier_noClosed : NoClosedSeparation (frontier U) := by
    simpa [U] using
      frontier_noClosed K x T hcompact hx hunbounded hTcompact hTconnected
        hTsubset htrace_nonempty
  have hAnonempty : A.Nonempty := by
    rcases hTA with ⟨y, _hyT, hyA⟩
    exact ⟨y, hyA⟩
  have hBnonempty : B.Nonempty := by
    rcases hTB with ⟨z, _hzT, hzB⟩
    exact ⟨z, hzB⟩
  exact hfrontier_noClosed A B hAclosed hBclosed hABdisjoint
    (by simpa [U] using hcover) hAnonempty hBnonempty

set_option linter.style.longLine false in
/-- Claim `S2-q34-topology-unconditional-worker`.

The current compact/frontier no-crossing residual is lowered to the sharper
crossing-witness no-closed-separation source above.  This exposes the smallest
remaining topological issue on this route: prove no closed separation of the
selected unbounded complement frontier for compact `K` carrying the displayed
compact connected crossing witness, rather than requiring the whole compactum
`K` to be connected. -/
theorem S2_q34_noCompactConnectedKCrossing_source_of_crossingWitnessNoClosedSeparation_20260522q34
    (frontier_noClosed :
      PlanarContinuumUnboundedComplementFrontierCrossingWitnessNoClosedSeparation) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_crossingWitnessNoClosedSeparation_20260522q34
    frontier_noClosed

set_option linter.style.longLine false in
/-- The q34 source composes with the existing finite no-closed-separation
reducer, keeping downstream consumers unchanged. -/
theorem S2_q34_finiteDrawing_noClosedSeparation_source_of_crossingWitnessNoClosedSeparation_20260522q34
    (frontier_noClosed :
      PlanarContinuumUnboundedComplementFrontierCrossingWitnessNoClosedSeparation) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  S2_subagent_topology_source_20260521_current_finiteDrawing_noClosedSeparation_of_noCompactConnectedKCrossing
    (S2_q34_noCompactConnectedKCrossing_source_of_crossingWitnessNoClosedSeparation_20260522q34
      frontier_noClosed)

set_option linter.style.longLine false in
/-- Trace version of the q34 crossing-witness source.

For the no-compact-connected-`K`-crossing target, the compact connected witness
`T` is used only through its trace on the selected frontier.  This source asks
for no closed separation of that trace, rather than of the whole frontier. -/
def PlanarContinuumUnboundedComplementFrontierCrossingWitnessTraceNoClosedSeparation :
    Prop :=
  forall (K : Set PlanarInterface.Point) (x : PlanarInterface.Point)
      (T : Set PlanarInterface.Point),
    IsCompact K ->
      x ∈ Kᶜ ->
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x) ->
          IsCompact T ->
            IsConnected T ->
              T ⊆ K ->
                (T ∩ frontier (connectedComponentIn Kᶜ x)).Nonempty ->
                  NoClosedSeparation
                    (T ∩ frontier (connectedComponentIn Kᶜ x))

set_option linter.style.longLine false in
/-- The compatibility Janiszewski trace source specializes to the q35
crossing-witness trace source. -/
theorem
    planarContinuumUnboundedComplementFrontierCrossingWitnessTraceNoClosedSeparation_of_janiszewskiTraceNoClosedSeparation_20260522q35
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceNoClosedSeparation) :
    PlanarContinuumUnboundedComplementFrontierCrossingWitnessTraceNoClosedSeparation := by
  intro K x T hcompact hx hunbounded hTcompact hTconnected hTsubset
    htrace_nonempty
  exact
    trace_noClosed K (connectedComponentIn Kᶜ x) T hcompact
      ⟨x, hx, rfl⟩ hunbounded hTcompact hTconnected hTsubset
      htrace_nonempty

set_option linter.style.longLine false in
/-- The trace crossing-witness source is enough for the compact/frontier
no-compact-connected-`K`-crossing primitive.

Given a closed split `frontier U = A ∪ B`, the trace
`T ∩ frontier U` is split by its intersections with `A` and `B`.  The two
displayed crossing points make both trace sides nonempty, contradicting the
trace no-closed-separation source. -/
theorem
    planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_crossingWitnessTraceNoClosedSeparation_20260522q35
    (trace_noClosed :
      PlanarContinuumUnboundedComplementFrontierCrossingWitnessTraceNoClosedSeparation) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    T hTcompact hTconnected hTsubset hTA hTB
  let U : Set PlanarInterface.Point := connectedComponentIn Kᶜ x
  have htrace_nonempty : (T ∩ frontier U).Nonempty := by
    rcases hTA with ⟨y, hyT, hyA⟩
    have hyFrontier : y ∈ frontier U := by
      simpa [U, hcover] using (Or.inl hyA : y ∈ A ∪ B)
    exact ⟨y, hyT, hyFrontier⟩
  have htraceNoClosed : NoClosedSeparation (T ∩ frontier U) := by
    simpa [U] using
      trace_noClosed K x T hcompact hx hunbounded hTcompact hTconnected
        hTsubset htrace_nonempty
  let L : Set PlanarInterface.Point := (T ∩ frontier U) ∩ A
  let R : Set PlanarInterface.Point := (T ∩ frontier U) ∩ B
  have htraceClosed : IsClosed (T ∩ frontier U) :=
    hTcompact.isClosed.inter isClosed_frontier
  have hLclosed : IsClosed L := by
    simpa [L] using htraceClosed.inter hAclosed
  have hRclosed : IsClosed R := by
    simpa [R] using htraceClosed.inter hBclosed
  have hLRdisjoint : Disjoint L R := by
    rw [Set.disjoint_left]
    intro p hpL hpR
    exact (Set.disjoint_left.mp hABdisjoint) hpL.2 hpR.2
  have htraceCover : T ∩ frontier U = L ∪ R := by
    ext p
    constructor
    · intro hp
      have hpAB : p ∈ A ∪ B := by
        simpa [U, hcover] using hp.2
      rcases hpAB with hpA | hpB
      · exact Or.inl ⟨hp, hpA⟩
      · exact Or.inr ⟨hp, hpB⟩
    · intro hp
      rcases hp with hpL | hpR
      · exact hpL.1
      · exact hpR.1
  have hLnonempty : L.Nonempty := by
    rcases hTA with ⟨y, hyT, hyA⟩
    have hyFrontier : y ∈ frontier U := by
      simpa [U, hcover] using (Or.inl hyA : y ∈ A ∪ B)
    exact ⟨y, ⟨hyT, hyFrontier⟩, hyA⟩
  have hRnonempty : R.Nonempty := by
    rcases hTB with ⟨z, hzT, hzB⟩
    have hzFrontier : z ∈ frontier U := by
      simpa [U, hcover] using (Or.inr hzB : z ∈ A ∪ B)
    exact ⟨z, ⟨hzT, hzFrontier⟩, hzB⟩
  exact htraceNoClosed L R hLclosed hRclosed hLRdisjoint htraceCover
    hLnonempty hRnonempty

set_option linter.style.longLine false in
/-- Claim `S2-q35-topology-crossing-source-worker`, no-compact side.

The q34 crossing-witness whole-frontier source is lowered to the trace source
actually used by the compact connected crossing contradiction. -/
theorem S2_q35_noCompactConnectedKCrossing_source_of_crossingWitnessTraceNoClosedSeparation_20260522q35
    (trace_noClosed :
      PlanarContinuumUnboundedComplementFrontierCrossingWitnessTraceNoClosedSeparation) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_crossingWitnessTraceNoClosedSeparation_20260522q35
    trace_noClosed

set_option linter.style.longLine false in
/-- Claim `S2-q35-topology-crossing-source-worker`, finite no-closed side.

The finite-drawing no-closed-separation source now depends only on the q35
crossing-witness trace no-closed-separation source. -/
theorem S2_q35_finiteDrawing_noClosedSeparation_source_of_crossingWitnessTraceNoClosedSeparation_20260522q35
    (trace_noClosed :
      PlanarContinuumUnboundedComplementFrontierCrossingWitnessTraceNoClosedSeparation) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  S2_subagent_topology_source_20260521_current_finiteDrawing_noClosedSeparation_of_noCompactConnectedKCrossing
    (S2_q35_noCompactConnectedKCrossing_source_of_crossingWitnessTraceNoClosedSeparation_20260522q35
      trace_noClosed)

set_option linter.style.longLine false in
/-- Claim `S2-q35-topology-crossing-source-worker`, Janiszewski trace handoff.

The older U-indexed Janiszewski trace no-closed-separation predicate feeds the
q35 finite-drawing source by specializing `U` to the selected unbounded
complement component. -/
theorem S2_q35_finiteDrawing_noClosedSeparation_source_of_janiszewskiTraceNoClosedSeparation_20260522q35
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceNoClosedSeparation) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  S2_q35_finiteDrawing_noClosedSeparation_source_of_crossingWitnessTraceNoClosedSeparation_20260522q35
    (planarContinuumUnboundedComplementFrontierCrossingWitnessTraceNoClosedSeparation_of_janiszewskiTraceNoClosedSeparation_20260522q35
      trace_noClosed)

set_option linter.style.longLine false in
/-- q36 component-trace replacement for the overstrong q35 arbitrary-`T` trace.

For the crossing-witness contradiction it is enough to know that, at every
frontier point `y`, the selected frontier trace inside the relative component
`connectedComponentIn K y` has no closed separation.  A compact connected
crossing witness `T <= K` only serves to put its second crossed point in that
same relative component. -/
def
    PlanarContinuumUnboundedComplementFrontierCrossingWitnessKComponentTraceNoClosedSeparation :
    Prop :=
  forall (K : Set PlanarInterface.Point) (x y : PlanarInterface.Point),
    IsCompact K ->
      x ∈ Kᶜ ->
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x) ->
          y ∈ frontier (connectedComponentIn Kᶜ x) ->
            NoClosedSeparation
              (frontier (connectedComponentIn Kᶜ x) ∩ connectedComponentIn K y)

set_option linter.style.longLine false in
/-- The same-`K` Janiszewski component-trace source specializes to the q36
crossing-witness component-trace source. -/
theorem
    planarContinuumUnboundedComplementFrontierCrossingWitnessKComponentTraceNoClosedSeparation_of_janiszewskiKComponentTraceNoClosedSeparation_20260522q36
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation) :
    PlanarContinuumUnboundedComplementFrontierCrossingWitnessKComponentTraceNoClosedSeparation := by
  intro K x y hcompact hx hunbounded hyFrontier
  exact
    trace_noClosed K (connectedComponentIn Kᶜ x) y hcompact
      ⟨x, hx, rfl⟩ hunbounded hyFrontier

set_option linter.style.longLine false in
/-- q36 lowering of the q35 no-compact-connected-`K`-crossing target.

This avoids the compatibility-only arbitrary subcontinuum trace predicate.  A
closed split of `frontier U` restricts to a closed split of
`frontier U ∩ connectedComponentIn K y`, where `y` is one crossed point of the
compact connected witness `T`. -/
theorem
    planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_crossingWitnessKComponentTraceNoClosedSeparation_20260522q36
    (trace_noClosed :
      PlanarContinuumUnboundedComplementFrontierCrossingWitnessKComponentTraceNoClosedSeparation) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing := by
  intro K x A B hcompact hx hunbounded hAclosed hBclosed hABdisjoint hcover
    T _hTcompact hTconnected hTsubset hTA hTB
  let U : Set PlanarInterface.Point := connectedComponentIn Kᶜ x
  rcases hTA with ⟨y, hyT, hyA⟩
  rcases hTB with ⟨z, hzT, hzB⟩
  have hfrontier_subset_K : frontier U ⊆ K := by
    simpa [U] using
      planarContinuumUnboundedComplement_frontier_subset
        (K := K) (x := x) hcompact
  have hyFrontier : y ∈ frontier U := by
    simpa [U, hcover] using (Or.inl hyA : y ∈ A ∪ B)
  have hzFrontier : z ∈ frontier U := by
    simpa [U, hcover] using (Or.inr hzB : z ∈ A ∪ B)
  have hyK : y ∈ K := hfrontier_subset_K hyFrontier
  have hz_componentInK : z ∈ connectedComponentIn K y :=
    hTconnected.isPreconnected.subset_connectedComponentIn hyT hTsubset hzT
  have hcomponentClosed : IsClosed (connectedComponentIn K y) := by
    have hKclosed : IsClosed K := hcompact.isClosed
    rw [connectedComponentIn_eq_image hyK]
    exact
      hKclosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp
        isClosed_connectedComponent
  have htraceNoClosed :
      NoClosedSeparation (frontier U ∩ connectedComponentIn K y) := by
    simpa [U] using
      trace_noClosed K x y hcompact hx hunbounded hyFrontier
  let L : Set PlanarInterface.Point :=
    (frontier U ∩ connectedComponentIn K y) ∩ A
  let R : Set PlanarInterface.Point :=
    (frontier U ∩ connectedComponentIn K y) ∩ B
  have htraceClosed : IsClosed (frontier U ∩ connectedComponentIn K y) :=
    isClosed_frontier.inter hcomponentClosed
  have hLclosed : IsClosed L := by
    simpa [L] using htraceClosed.inter hAclosed
  have hRclosed : IsClosed R := by
    simpa [R] using htraceClosed.inter hBclosed
  have hLRdisjoint : Disjoint L R := by
    rw [Set.disjoint_left]
    intro p hpL hpR
    exact (Set.disjoint_left.mp hABdisjoint) hpL.2 hpR.2
  have htraceCover : frontier U ∩ connectedComponentIn K y = L ∪ R := by
    ext p
    constructor
    · intro hp
      have hpAB : p ∈ A ∪ B := by
        simpa [U, hcover] using hp.1
      rcases hpAB with hpA | hpB
      · exact Or.inl ⟨hp, hpA⟩
      · exact Or.inr ⟨hp, hpB⟩
    · intro hp
      rcases hp with hpL | hpR
      · exact hpL.1
      · exact hpR.1
  have hLnonempty : L.Nonempty :=
    ⟨y, ⟨hyFrontier, mem_connectedComponentIn hyK⟩, hyA⟩
  have hRnonempty : R.Nonempty :=
    ⟨z, ⟨hzFrontier, hz_componentInK⟩, hzB⟩
  exact htraceNoClosed L R hLclosed hRclosed hLRdisjoint htraceCover
    hLnonempty hRnonempty

set_option linter.style.longLine false in
/-- Claim `S2-q36-janiszewski-trace-source-worker`, no-compact side.

The q35 topology target is sourced from the correct same-`K` component trace,
not from the compatibility-only arbitrary subcontinuum trace surface. -/
theorem S2_q36_noCompactConnectedKCrossing_source_of_janiszewskiKComponentTraceNoClosedSeparation_20260522q36
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_crossingWitnessKComponentTraceNoClosedSeparation_20260522q36
    (planarContinuumUnboundedComplementFrontierCrossingWitnessKComponentTraceNoClosedSeparation_of_janiszewskiKComponentTraceNoClosedSeparation_20260522q36
      trace_noClosed)

set_option linter.style.longLine false in
/-- Claim `S2-q36-janiszewski-trace-source-worker`, finite no-closed side.

This immediately feeds the existing finite-drawing reducer chain from the
q36 component-trace source. -/
theorem S2_q36_finiteDrawing_noClosedSeparation_source_of_janiszewskiKComponentTraceNoClosedSeparation_20260522q36
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  S2_subagent_topology_source_20260521_current_finiteDrawing_noClosedSeparation_of_noCompactConnectedKCrossing
    (S2_q36_noCompactConnectedKCrossing_source_of_janiszewskiKComponentTraceNoClosedSeparation_20260522q36
      trace_noClosed)

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-component-topology-input-source-20260522`, exact finite
preconnected side.

The component-topology input source only needs finite-drawing frontier
preconnectedness for the selected actual component and the genuine selected
incident-edge row at graph-frontier vertices.  This avoids the stronger finite
no-closed-separation presentation, and introduces no boundary cycle, synthetic
enclosure, or W32 facade. -/
theorem S2_dynamic_component_topology_input_source_of_finiteDrawing_frontierPreconnected_vertexIncident_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected)
    (frontier_vertex_incident :
      FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  unboundedExteriorFrontierComponentTopologyInputSourceRows_of_actualFrontierPreconnected_frontierVertexIncident
    (C := C) (inputs := inputs)
    (actualFrontierPreconnected_of_finiteDrawing_frontierPreconnected
      (C := C) inputs frontier_preconnected)
    frontier_vertex_incident

set_option linter.style.longLine false in
/-- Claim `S2-frontier-incidence-topology`, punctured side.

Selected component-frontier vertex incidence rules out the singleton actual
frontier, so together with finite-drawing no-closed-separation it supplies the
punctured accumulation source at graph-frontier vertices. -/
theorem S2_frontier_puncturedAccumulationSource_of_finiteDrawingNoClosedSeparation_vertexIncident_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (frontier_vertex_incident :
      FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) :
    UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs :=
  unboundedExteriorFrontierVertexPuncturedAccumulationSource_of_finiteDrawingNoClosedSeparation_frontierVertexIncidentSource
    (C := C) inputs frontier_noClosedSeparation frontier_vertex_incident

set_option linter.style.longLine false in
/-- Claim `S2-frontier-incidence-topology`, singleton side.

The singleton boundary-bumping obstruction is strictly reduced to selected
component-frontier vertex incidence: an incident selected frontier edge already
contains two distinct actual frontier points. -/
theorem S2_singleton_boundaryBumpingObstruction_of_frontierVertexIncident_20260522
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (frontier_vertex_incident :
      FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) :
    UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs :=
  unboundedExteriorSingletonFrontierBoundaryBumpingObstruction_of_frontierVertexIncidentSource
    (C := C) (inputs := inputs) frontier_vertex_incident

set_option linter.style.longLine false in
/-- Claim `S2-outside-accumulation-source`, incident-edge form.

The singleton outside-accumulation source is strictly lowered to selected
frontier-vertex incidence.  The incidence row rules out a singleton actual
frontier, so the displayed singleton/outside-accumulation configuration is
impossible. -/
theorem S2_outsideAccumulationSource_of_frontierVertexIncident_20260522
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (frontier_vertex_incident :
      FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) :
    UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
      C inputs :=
  S2_r5w_outsideAccumulation_forces_actualFrontier_of_boundaryBumpingObstruction_20260522
    (C := C) (inputs := inputs)
    (S2_singleton_boundaryBumpingObstruction_of_frontierVertexIncident_20260522
      (C := C) (inputs := inputs) frontier_vertex_incident)

set_option linter.style.longLine false in
/-- Claim `S2-outside-accumulation-source`, local-sector obstruction form.

The singleton boundary-bumping obstruction reduces to the same local-sector
selected-edge source already used by the component-topology input rows. -/
theorem S2_singleton_boundaryBumpingObstruction_of_localSectorRows_20260522
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs :=
  S2_singleton_boundaryBumpingObstruction_of_frontierVertexIncident_20260522
    (C := C) (inputs := inputs)
    (frontierVertexIncidentSource_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows)

set_option linter.style.longLine false in
/-- Claim `S2-outside-accumulation-source`, local-sector form.

The outside-accumulation source now has a local-source residual:
pointwise local-sector rows at actual unbounded-frontier carrier vertices. -/
theorem S2_outsideAccumulationSource_of_localSectorRows_20260522
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
      C inputs :=
  S2_outsideAccumulationSource_of_frontierVertexIncident_20260522
    (C := C) (inputs := inputs)
    (frontierVertexIncidentSource_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows)

set_option linter.style.longLine false in
/-- Family form of
`S2_outsideAccumulationSource_of_localSectorRows_20260522`. -/
theorem S2_outsideAccumulationSource_family_of_localSectorRows_20260522
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
          C inputs :=
  fun C inputs =>
    S2_outsideAccumulationSource_of_localSectorRows_20260522
      (C := C) (inputs := inputs) (localSectorRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-q11-topology-trace-accumulation`, singleton side.

The singleton outside-accumulation source is strictly lowered to the selected
frontier-vertex incident-edge source, uniformly over finite drawing inputs.
This is the point-set singleton branch only; it introduces no carrier cycle,
actual-sector package, or W-facing consumer. -/
theorem S2_agent_q11_outsideAccumulationSource_family_of_frontierVertexIncident_20260522
    (frontier_vertex_incident :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
          C inputs :=
  fun C inputs =>
    S2_outsideAccumulationSource_of_frontierVertexIncident_20260522
      (C := C) (inputs := inputs) (frontier_vertex_incident C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-q11-topology-trace-accumulation`, paired topology handoff.

The finite separation side is now sourced by finite same-component
point-between rows, while the singleton boundary-bumping side is sourced by
selected frontier-vertex incident edges. -/
theorem S2_agent_q11_topology_sources_of_kComponentPointsBetween_frontierVertexIncident_20260522
    (points_between :
      FiniteDrawingUnboundedComplementFrontierKComponentPointsBetween)
    (frontier_vertex_incident :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation ∧
        (forall {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C),
            UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
              C inputs) := by
  exact
    S2_agent_q10_topology_sources_of_kTracePreconnected_outsideAccumulation_20260522
      (finiteDrawingUnboundedComplementFrontierKTracePreconnected_of_kComponentPointsBetween
        points_between)
      (S2_agent_q11_outsideAccumulationSource_family_of_frontierVertexIncident_20260522
        frontier_vertex_incident)

set_option linter.style.longLine false in
/-- Global same-`K` point-between specialization of the q11 paired topology
handoff. -/
theorem S2_agent_q11_topology_sources_of_globalKComponentPointsBetween_frontierVertexIncident_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (frontier_vertex_incident :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation ∧
        (forall {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C),
            UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
              C inputs) :=
  S2_agent_q11_topology_sources_of_kComponentPointsBetween_frontierVertexIncident_20260522
    (finiteDrawingUnboundedComplementFrontierKComponentPointsBetween_of_globalKComponentPointsBetween
      points_between)
    frontier_vertex_incident

set_option linter.style.longLine false in
/-- Claim `S2-agent-q12-frontier-accumulation`, singleton side.

The singleton outside-accumulation source is strictly lowered to the pointwise
punctured accumulation row on the actual unbounded exterior frontier.  The
checked route is finite/component-local: punctured accumulation gives an
incident open-segment closure row, the fixed-side propagation promotes it to a
selected `unboundedFrontierEdgeSet` incident edge, and selected incidence rules
out the singleton frontier configuration. -/
theorem S2_agent_q12_outsideAccumulationSource_of_puncturedAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (punctured :
      UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs) :
    UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
      C inputs :=
  S2_outsideAccumulationSource_of_frontierVertexIncident_20260522
    (C := C) (inputs := inputs)
    (S2_frontier_vertex_incident_source_of_puncturedAccumulation_20260522
      (C := C) inputs punctured)

set_option linter.style.longLine false in
/-- Family form of
`S2_agent_q12_outsideAccumulationSource_of_puncturedAccumulation_20260522`. -/
theorem S2_agent_q12_outsideAccumulationSource_family_of_puncturedAccumulation_20260522
    (punctured :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierVertexPuncturedAccumulationSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
          C inputs :=
  fun C inputs =>
    S2_agent_q12_outsideAccumulationSource_of_puncturedAccumulation_20260522
      (C := C) inputs (punctured C inputs)

set_option linter.style.longLine false in
/-- Boundary-bumping obstruction form of the q12 singleton handoff. -/
theorem S2_agent_q12_singletonBoundaryBumpingObstruction_of_puncturedAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (punctured :
      UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs) :
    UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs :=
  S2_singleton_boundaryBumpingObstruction_of_frontierVertexIncident_20260522
    (C := C) (inputs := inputs)
    (S2_frontier_vertex_incident_source_of_puncturedAccumulation_20260522
      (C := C) inputs punctured)

set_option linter.style.longLine false in
/-- Family form of the q12 boundary-bumping obstruction handoff. -/
theorem S2_agent_q12_singletonBoundaryBumpingObstruction_family_of_puncturedAccumulation_20260522
    (punctured :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierVertexPuncturedAccumulationSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
          C inputs :=
  fun C inputs =>
    S2_agent_q12_singletonBoundaryBumpingObstruction_of_puncturedAccumulation_20260522
      (C := C) inputs (punctured C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-agent-q12-frontier-accumulation`, paired topology handoff.

Compared with q11, the singleton row is lowered one step further: the residual
is punctured accumulation at graph vertices on the actual unbounded exterior
frontier, not selected frontier-vertex incidence and not the pointwise
outside-accumulation source. -/
theorem S2_agent_q12_topology_sources_of_kComponentPointsBetween_puncturedAccumulation_20260522
    (points_between :
      FiniteDrawingUnboundedComplementFrontierKComponentPointsBetween)
    (punctured :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierVertexPuncturedAccumulationSource
            C inputs) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation /\
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation /\
        (forall {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C),
            UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
              C inputs) :=
  S2_agent_q10_topology_sources_of_kTracePreconnected_outsideAccumulation_20260522
    (finiteDrawingUnboundedComplementFrontierKTracePreconnected_of_kComponentPointsBetween
      points_between)
    (S2_agent_q12_outsideAccumulationSource_family_of_puncturedAccumulation_20260522
      punctured)

set_option linter.style.longLine false in
/-- Global same-`K` point-between specialization of the q12 paired topology
handoff. -/
theorem S2_agent_q12_topology_sources_of_globalKComponentPointsBetween_puncturedAccumulation_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (punctured :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierVertexPuncturedAccumulationSource
            C inputs) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation /\
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation /\
        (forall {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C),
            UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
              C inputs) :=
  S2_agent_q12_topology_sources_of_kComponentPointsBetween_puncturedAccumulation_20260522
    (finiteDrawingUnboundedComplementFrontierKComponentPointsBetween_of_globalKComponentPointsBetween
      points_between)
    punctured

set_option linter.style.longLine false in
/-- Claim `S2-frontier-incidence-topology`, component input side.

The component-topology input rows now reduce to the global crossing-boundedness
topology leaf plus the selected component-frontier vertex-incidence source.
The singleton/punctured row is no longer an independent residual on this lane. -/
theorem S2_dynamic_component_topology_input_source_of_crossingSubcontinuumForcesBounded_vertexIncident_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (crossing_forces_bounded :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded)
    (frontier_vertex_incident :
      FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_dynamic_component_topology_input_source_of_finiteDrawing_frontierPreconnected_vertexIncident_20260522
    (C := C) inputs
    (finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
      (S2_dynamic_topology_finiteDrawing_noClosedSeparation_of_crossingSubcontinuumForcesBounded_20260522
        crossing_forces_bounded))
    frontier_vertex_incident

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-component-topology-input-source-20260522`, actual
boundary-bumping side.

Actual frontier preconnectedness plus the singleton-frontier boundary-bumping
obstruction gives the incident-edge row through punctured accumulation, then
fills the input source.  The proof uses only the actual unbounded exterior
frontier and the selected `unboundedFrontierEdgeSet` propagation row. -/
theorem S2_dynamic_component_topology_input_source_of_actualFrontierPreconnected_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (frontier_preconnected :
      UnboundedExteriorActualFrontierPreconnectedSource C inputs)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  unboundedExteriorFrontierComponentTopologyInputSourceRows_of_actualFrontierPreconnected_frontierVertexIncident
    (C := C) (inputs := inputs)
    frontier_preconnected
    (frontierVertexIncidentSource_of_punctured_vertex
      (C := C) (inputs := inputs)
      (S2_r7j_puncturedAccumulationSource_of_frontierPreconnected_boundaryBumpingObstruction_20260521r7j
        (C := C) (inputs := inputs)
        (by
          simpa [UnboundedExteriorActualFrontierPreconnectedSource] using
            frontier_preconnected)
        no_singleton_bumping))

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-component-topology-input-source-20260522`, finite
boundary-bumping side.

Finite-drawing frontier preconnectedness specializes to the actual selected
unbounded exterior frontier; the singleton boundary-bumping obstruction then
supplies the selected incident-edge source. -/
theorem S2_dynamic_component_topology_input_source_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_dynamic_component_topology_input_source_of_actualFrontierPreconnected_boundaryBumping_20260522
    (C := C) (inputs := inputs)
    (actualFrontierPreconnected_of_finiteDrawing_frontierPreconnected
      (C := C) inputs frontier_preconnected)
    no_singleton_bumping

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-component-topology-input-source-20260522`, bounded
crossing side.

The current crossing-subcontinuum boundedness source feeds the finite
preconnectedness leaf through the no-compact-connected-`K` crossing reducer.
The only remaining local topology row is the singleton-frontier
boundary-bumping obstruction. -/
theorem S2_dynamic_component_topology_input_source_of_crossingSubcontinuumForcesBounded_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (crossing_forces_bounded :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_dynamic_component_topology_input_source_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    (C := C) inputs
    (finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
      (S2_dynamic_topology_finiteDrawing_noClosedSeparation_of_crossingSubcontinuumForcesBounded_20260522
        crossing_forces_bounded))
    no_singleton_bumping

set_option linter.style.longLine false in
/-- Claim `S2-dynamic-component-topology-input-source-20260522`.

The requested component-topology input source is lowered to the current
crossing-subcontinuum boundedness topology leaf plus the pointwise
outside-accumulation boundary-bumping source for the singleton actual-frontier
case. -/
theorem S2_dynamic_component_topology_input_source_of_crossingSubcontinuumForcesBounded_outsideAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (crossing_forces_bounded :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded)
    (outside_accumulation :
      UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
        C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_dynamic_component_topology_input_source_of_crossingSubcontinuumForcesBounded_boundaryBumping_20260522
    (C := C) inputs crossing_forces_bounded
    (S2_r5w_singleton_boundaryBumping_obstruction_20260521r5w
      (C := C) inputs outside_accumulation)

set_option linter.style.longLine false in
/-- Family form of
`S2_dynamic_component_topology_input_source_of_crossingSubcontinuumForcesBounded_boundaryBumping_20260522`.

This is the current source-facing component-topology handoff: the global
crossing-subcontinuum boundedness leaf supplies finite frontier
preconnectedness, and the pointwise singleton boundary-bumping obstruction
supplies selected incident frontier edges. -/
theorem S2_dynamic_component_topology_input_source_family_of_crossingSubcontinuumForcesBounded_boundaryBumping_20260522
    (crossing_forces_bounded :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  fun C inputs =>
    S2_dynamic_component_topology_input_source_of_crossingSubcontinuumForcesBounded_boundaryBumping_20260522
      (C := C) inputs crossing_forces_bounded
      (no_singleton_bumping C inputs)

set_option linter.style.longLine false in
/-- Family form of
`S2_dynamic_component_topology_input_source_of_crossingSubcontinuumForcesBounded_outsideAccumulation_20260522`.

The singleton local row is kept at the outside-accumulation source surface and
erased only through the checked boundary-bumping obstruction reducer. -/
theorem S2_dynamic_component_topology_input_source_family_of_crossingSubcontinuumForcesBounded_outsideAccumulation_20260522
    (crossing_forces_bounded :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  fun C inputs =>
    S2_dynamic_component_topology_input_source_of_crossingSubcontinuumForcesBounded_outsideAccumulation_20260522
      (C := C) inputs crossing_forces_bounded (outside_accumulation C inputs)

set_option linter.style.longLine false in
/-- The crossing-subcontinuum boundedness topology leaf is sourced from the
x-indexed nontrivial relative-clopen `K`-side primitive.

The relative-clopen side rules out any compact connected `K`-subcontinuum
crossing the two closed frontier sides while the selected complement component
is unbounded; the boundedness conclusion follows by contradiction through the
checked no-compact-connected-crossing adapter. -/
theorem
    planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_nontrivialRelativeClopenKSide_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded :=
  S2_dynamic_topology_crossingSubcontinuumForcesBounded_of_noCompactConnectedKCrossing_20260522
    (S2_p2o_no_compact_connected_K_crossing_source_20260521p4
      nontrivial_side)

set_option linter.style.longLine false in
/-- Component-topology input rows from the nontrivial relative-clopen topology
primitive plus the concrete singleton-frontier boundary-bumping obstruction.

This is the same input-facing handoff as the crossing-bounded route, but with
the global topology source lowered one step further to the relative-clopen
`K`-side primitive. -/
theorem S2_dynamic_component_topology_input_source_of_nontrivialRelativeClopen_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_dynamic_component_topology_input_source_of_crossingSubcontinuumForcesBounded_boundaryBumping_20260522
    (C := C) inputs
    (planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_nontrivialRelativeClopenKSide_20260522
      nontrivial_side)
    no_singleton_bumping

set_option linter.style.longLine false in
/-- Component-topology input rows from the nontrivial relative-clopen topology
primitive plus the pointwise outside-accumulation singleton source. -/
theorem S2_dynamic_component_topology_input_source_of_nontrivialRelativeClopen_outsideAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (outside_accumulation :
      UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
        C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_dynamic_component_topology_input_source_of_nontrivialRelativeClopen_boundaryBumping_20260522
    (C := C) inputs nontrivial_side
    (S2_r5w_singleton_boundaryBumping_obstruction_20260521r5w
      (C := C) inputs outside_accumulation)

set_option linter.style.longLine false in
/-- Family form of
`S2_dynamic_component_topology_input_source_of_nontrivialRelativeClopen_boundaryBumping_20260522`. -/
theorem S2_dynamic_component_topology_input_source_family_of_nontrivialRelativeClopen_boundaryBumping_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  fun C inputs =>
    S2_dynamic_component_topology_input_source_of_nontrivialRelativeClopen_boundaryBumping_20260522
      (C := C) inputs nontrivial_side (no_singleton_bumping C inputs)

set_option linter.style.longLine false in
/-- Family form of
`S2_dynamic_component_topology_input_source_of_nontrivialRelativeClopen_outsideAccumulation_20260522`. -/
theorem S2_dynamic_component_topology_input_source_family_of_nontrivialRelativeClopen_outsideAccumulation_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  fun C inputs =>
    S2_dynamic_component_topology_input_source_of_nontrivialRelativeClopen_outsideAccumulation_20260522
      (C := C) inputs nontrivial_side (outside_accumulation C inputs)

set_option linter.style.longLine false in
/-- Source-row form of the crossing-bounded plus singleton boundary-bumping
component-topology handoff.

This is only the checked erasure from the input-facing package to the
component-topology source rows; the residual sources remain the global
crossing-subcontinuum boundedness theorem and the concrete singleton
boundary-bumping obstruction. -/
theorem S2_dynamic_component_topology_source_of_crossingSubcontinuumForcesBounded_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (crossing_forces_bounded :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  (S2_dynamic_component_topology_input_source_of_crossingSubcontinuumForcesBounded_boundaryBumping_20260522
    (C := C) inputs crossing_forces_bounded no_singleton_bumping).toComponentTopologyRows

set_option linter.style.longLine false in
/-- Source-row form of the crossing-bounded plus singleton
outside-accumulation component-topology handoff. -/
theorem S2_dynamic_component_topology_source_of_crossingSubcontinuumForcesBounded_outsideAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (crossing_forces_bounded :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded)
    (outside_accumulation :
      UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
        C inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  (S2_dynamic_component_topology_input_source_of_crossingSubcontinuumForcesBounded_outsideAccumulation_20260522
    (C := C) inputs crossing_forces_bounded outside_accumulation).toComponentTopologyRows

set_option linter.style.longLine false in
/-- Family source-row form of
`S2_dynamic_component_topology_source_of_crossingSubcontinuumForcesBounded_boundaryBumping_20260522`. -/
theorem S2_dynamic_component_topology_source_family_of_crossingSubcontinuumForcesBounded_boundaryBumping_20260522
    (crossing_forces_bounded :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  fun C inputs =>
    S2_dynamic_component_topology_source_of_crossingSubcontinuumForcesBounded_boundaryBumping_20260522
      (C := C) inputs crossing_forces_bounded (no_singleton_bumping C inputs)

set_option linter.style.longLine false in
/-- Family source-row form of
`S2_dynamic_component_topology_source_of_crossingSubcontinuumForcesBounded_outsideAccumulation_20260522`. -/
theorem S2_dynamic_component_topology_source_family_of_crossingSubcontinuumForcesBounded_outsideAccumulation_20260522
    (crossing_forces_bounded :
      PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  fun C inputs =>
    S2_dynamic_component_topology_source_of_crossingSubcontinuumForcesBounded_outsideAccumulation_20260522
      (C := C) inputs crossing_forces_bounded (outside_accumulation C inputs)

set_option linter.style.longLine false in
/-- Source-row form of the lowered nontrivial-relative-clopen plus singleton
boundary-bumping component-topology handoff.

The global topology residual is now the nontrivial relative-clopen `K`-side
primitive, and the local singleton residual is the concrete boundary-bumping
obstruction.  No actual boundary-cycle, carrier, actual-sector, W32, or final
S2 rows are introduced. -/
theorem S2_dynamic_component_topology_source_of_nontrivialRelativeClopen_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  (S2_dynamic_component_topology_input_source_of_nontrivialRelativeClopen_boundaryBumping_20260522
    (C := C) inputs nontrivial_side no_singleton_bumping).toComponentTopologyRows

set_option linter.style.longLine false in
/-- Source-row form of the lowered nontrivial-relative-clopen plus singleton
outside-accumulation component-topology handoff. -/
theorem S2_dynamic_component_topology_source_of_nontrivialRelativeClopen_outsideAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (outside_accumulation :
      UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
        C inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  (S2_dynamic_component_topology_input_source_of_nontrivialRelativeClopen_outsideAccumulation_20260522
    (C := C) inputs nontrivial_side outside_accumulation).toComponentTopologyRows

set_option linter.style.longLine false in
/-- Family source-row form of
`S2_dynamic_component_topology_source_of_nontrivialRelativeClopen_boundaryBumping_20260522`. -/
theorem S2_dynamic_component_topology_source_family_of_nontrivialRelativeClopen_boundaryBumping_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  fun C inputs =>
    S2_dynamic_component_topology_source_of_nontrivialRelativeClopen_boundaryBumping_20260522
      (C := C) inputs nontrivial_side (no_singleton_bumping C inputs)

set_option linter.style.longLine false in
/-- Strict family source-row handoff for claim
`S2-agent-q4-topology-input-source`.

Both component-topology surfaces are now lowered to the same residuals: the
planar-continuum nontrivial relative-clopen `K`-side source and the pointwise
singleton outside-accumulation source for the selected actual frontier. -/
theorem S2_agent_q4_topology_source_family_of_nontrivialRelativeClopen_outsideAccumulation_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  fun C inputs =>
    S2_dynamic_component_topology_source_of_nontrivialRelativeClopen_outsideAccumulation_20260522
      (C := C) inputs nontrivial_side (outside_accumulation C inputs)

set_option linter.style.longLine false in
/-- Paired strict q4 handoff for both component-topology row surfaces.

The first projection is the input-facing row package; the second is the
component-topology source-row package obtained by the checked input erasure. -/
theorem S2_agent_q4_topology_input_and_source_family_of_nontrivialRelativeClopen_outsideAccumulation_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs /\
          UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  fun C inputs =>
    let input_rows :=
      S2_dynamic_component_topology_input_source_of_nontrivialRelativeClopen_outsideAccumulation_20260522
        (C := C) inputs nontrivial_side (outside_accumulation C inputs)
    ⟨input_rows, input_rows.toComponentTopologyRows⟩

set_option linter.style.longLine false in
/-- Claim `S2-component-topology-source-final`, finite topology leaf form.

The component-topology source is reduced to the two current honest leaves:
finite-drawing no-closed-separation for unbounded complement frontiers and
punctured accumulation at graph vertices on the selected actual frontier.  The
first leaf supplies actual frontier preconnectedness; the second supplies the
selected incident-edge row, whose checked input-row erasure gives the selected
frontier-edge cover. -/
theorem S2_component_topology_source_final_of_finiteDrawingNoClosedSeparation_puncturedAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noClosedSeparation :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (punctured :
      UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs ∧
      UnboundedExteriorFrontierComponentTopologySourceRows inputs := by
  let input_rows :=
    S2_component_topology_input_source_of_finiteDrawingNoClosedSeparation_puncturedAccumulation_20260522
      (C := C) inputs frontier_noClosedSeparation punctured
  exact ⟨input_rows, input_rows.toComponentTopologyRows⟩

set_option linter.style.longLine false in
/-- Claim `S2-component-topology-source-final`, Janiszewski K-component form.

The finite no-closed-separation leaf in the final component-topology handoff is
strictly lowered to the current same-`K` Janiszewski frontier-component source.
The only remaining local source is punctured accumulation on the actual
selected unbounded exterior frontier; no final boundary cycles, actual-sector
rows, carrier rows, W32 facade, induced frontier graph, or all-adjacent
endpoint rows are used. -/
theorem S2_component_topology_source_final_of_kComponentFrontierComponent_puncturedAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent)
    (punctured :
      UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs ∧
      UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  S2_component_topology_source_final_of_finiteDrawingNoClosedSeparation_puncturedAccumulation_20260522
    (C := C) inputs
    (S2_r19_finiteDrawing_noClosedSeparation_of_kComponentFrontierComponent_20260521r19
      frontier_component)
    punctured

set_option linter.style.longLine false in
/-- Family form of
`S2_component_topology_source_final_of_kComponentFrontierComponent_puncturedAccumulation_20260522`.

Exact remaining leaves:
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent`
and, for each input drawing,
`UnboundedExteriorFrontierVertexPuncturedAccumulationSource`. -/
theorem S2_component_topology_source_final_family_of_kComponentFrontierComponent_puncturedAccumulation_20260522
    (frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent)
    (punctured :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierVertexPuncturedAccumulationSource
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs ∧
          UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  fun C inputs =>
    S2_component_topology_source_final_of_kComponentFrontierComponent_puncturedAccumulation_20260522
      (C := C) inputs frontier_component (punctured C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q14-component-topology-source`, finite-preconnected form.

The component-topology input rows are lowered to the smaller concrete topology
leaf `FiniteDrawingUnboundedComplementFrontierPreconnected` plus the existing
pointwise local-sector rows for the actual unbounded-frontier carrier.  The
local-sector rows are erased only to selected incident `unboundedFrontierEdgeSet`
edges at graph-frontier vertices. -/
theorem S2_q14_component_topology_input_source_of_finiteDrawingPreconnected_localSectorRows_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_dynamic_component_topology_input_source_of_finiteDrawing_frontierPreconnected_vertexIncident_20260522
    (C := C) inputs frontier_preconnected
    (frontierVertexIncidentSource_of_localSectorRows
      (C := C) (inputs := inputs) localSectorRows)

set_option linter.style.longLine false in
/-- Source-row erasure for the q14 finite-preconnected component-topology
handoff. -/
theorem S2_q14_component_topology_source_of_finiteDrawingPreconnected_localSectorRows_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  (S2_q14_component_topology_input_source_of_finiteDrawingPreconnected_localSectorRows_20260522
    (C := C) inputs frontier_preconnected localSectorRows).toComponentTopologyRows

set_option linter.style.longLine false in
/-- Claim `S2-q14-component-topology-source`, no-open form.

The finite no-open-separation source is used only through its exact smaller
preconnectedness content before erasing local-sector rows to the selected
frontier-edge cover. -/
theorem S2_q14_component_topology_source_of_finiteDrawingNoOpenSeparation_localSectorRows_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noOpen :
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation)
    (localSectorRows :
      forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
        UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  S2_q14_component_topology_source_of_finiteDrawingPreconnected_localSectorRows_20260522
    (C := C) inputs
    (S2_r23_finiteDrawing_frontierPreconnected_of_noOpenSeparation_20260521r23
      frontier_noOpen)
    localSectorRows

set_option linter.style.longLine false in
/-- Family form of the q14 no-open/local-sector component-topology source
lowering. -/
theorem S2_q14_component_topology_source_family_of_finiteDrawingNoOpenSeparation_localSectorRows_20260522
    (frontier_noOpen :
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation)
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  fun C inputs =>
    S2_q14_component_topology_source_of_finiteDrawingNoOpenSeparation_localSectorRows_20260522
      (C := C) inputs frontier_noOpen (localSectorRows C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q13-topology-leaf`, punctured subleaf.

The graph-vertex punctured-accumulation row for the actual unbounded exterior
frontier is reduced to the same-`K` Janiszewski point-between theorem plus the
concrete singleton-frontier boundary-bumping obstruction.  Point-between
supplies finite-drawing frontier preconnectedness; the singleton obstruction
rules out the isolated-frontier case. -/
theorem S2_q13_puncturedAccumulationSource_of_kComponentPointsBetween_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs :=
  S2_puncturedAccumulationSource_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    (C := C) inputs
    (finiteDrawingUnboundedComplementFrontierPreconnected_of_janiszewskiKComponentPointsBetween
      points_between)
    no_singleton_bumping

set_option linter.style.longLine false in
/-- Claim `S2-q13-topology-leaf`, input source.

The input-facing finite drawing component-topology source is lowered to two
honest topology leaves: same-`K` point-between for unbounded complement
frontiers, and the singleton boundary-bumping obstruction for the selected
actual frontier.  The checked path feeds the existing finite no-closed and
punctured-accumulation reducers. -/
theorem S2_q13_component_topology_input_source_of_kComponentPointsBetween_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_component_topology_input_source_of_finiteDrawingNoClosedSeparation_puncturedAccumulation_20260522
    (C := C) inputs
    (finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_janiszewskiKComponentPointsBetween
      points_between)
    (S2_q13_puncturedAccumulationSource_of_kComponentPointsBetween_boundaryBumping_20260522
      (C := C) inputs points_between no_singleton_bumping)

set_option linter.style.longLine false in
/-- Claim `S2-q13-topology-leaf`, source rows.

The component-topology source-row surface follows from the q13 input rows by
the checked input erasure. -/
theorem S2_q13_component_topology_source_of_kComponentPointsBetween_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  (S2_q13_component_topology_input_source_of_kComponentPointsBetween_boundaryBumping_20260522
    (C := C) inputs points_between no_singleton_bumping).toComponentTopologyRows

set_option linter.style.longLine false in
/-- Paired q13 source handoff for both component-topology row surfaces. -/
theorem S2_q13_component_topology_input_and_source_of_kComponentPointsBetween_boundaryBumping_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (no_singleton_bumping :
      UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs /\
      UnboundedExteriorFrontierComponentTopologySourceRows inputs := by
  let input_rows :=
    S2_q13_component_topology_input_source_of_kComponentPointsBetween_boundaryBumping_20260522
      (C := C) inputs points_between no_singleton_bumping
  exact And.intro input_rows input_rows.toComponentTopologyRows

set_option linter.style.longLine false in
/-- Family form of the q13 component-topology source leaf. -/
theorem S2_q13_component_topology_input_and_source_family_of_kComponentPointsBetween_boundaryBumping_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (no_singleton_bumping :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs /\
          UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  fun C inputs =>
    S2_q13_component_topology_input_and_source_of_kComponentPointsBetween_boundaryBumping_20260522
      (C := C) inputs points_between (no_singleton_bumping C inputs)

set_option linter.style.longLine false in
/-- Outside-accumulation version of the q13 family handoff.

The singleton boundary-bumping obstruction is erased through the existing
pointwise outside-accumulation source before applying the q13 bridge. -/
theorem S2_q13_component_topology_input_and_source_family_of_kComponentPointsBetween_outsideAccumulation_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs /\
          UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  S2_q13_component_topology_input_and_source_family_of_kComponentPointsBetween_boundaryBumping_20260522
    points_between
    (fun C inputs =>
      S2_r5w_singleton_boundaryBumping_obstruction_20260521r5w
        (C := C) inputs (outside_accumulation C inputs))

set_option linter.style.longLine false in
/-- Claim `S2-q14-topology-final-leaf`.

The q14 component-topology row source is lowered to the same two concrete
topology inputs used by the q13 bridge: the global same-`K` Janiszewski
point-between theorem and the selected local-sector rows.  The local-sector
rows are used only through the checked singleton boundary-bumping obstruction,
then the existing q13 point-between bridge produces both input rows and erased
component-topology source rows. -/
theorem S2_q14_component_topology_input_and_source_family_of_kComponentPointsBetween_localSectorRows_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs /\
          UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
  S2_q13_component_topology_input_and_source_family_of_kComponentPointsBetween_boundaryBumping_20260522
    points_between
    (fun C inputs =>
      S2_singleton_boundaryBumpingObstruction_of_localSectorRows_20260522
        (C := C) (inputs := inputs) (localSectorRows C inputs))

set_option linter.style.longLine false in
/-- Claim `S2-q15-topology-source`.

The finite drawing no-closed/no-open exterior-frontier topology source, together
with the component-topology row surfaces needed by the raw face-orbit route, is
strictly lowered to the compact-connected no-`K`-crossing topology theorem plus
the existing local-sector rows.  The proof uses the no-crossing source only to
obtain finite no-closed separation and hence finite frontier preconnectedness;
local-sector rows enter only through the checked q14 preconnected
component-topology bridge. -/
theorem
    S2_q15_finiteDrawing_noClosed_noOpen_componentTopology_family_of_noCompactConnectedKCrossing_localSectorRows_20260522
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing)
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation ∧
        (forall {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C),
            UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs ∧
              UnboundedExteriorFrontierComponentTopologySourceRows inputs) := by
  let frontier_noClosed :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
    S2_subagent_topology_source_20260521_current_finiteDrawing_noClosedSeparation_of_noCompactConnectedKCrossing
      no_crossing
  let frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected :=
    finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
      frontier_noClosed
  let frontier_noOpen :
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation :=
    finiteDrawingUnboundedComplementFrontierNoOpenSeparation_of_frontierPreconnected
      frontier_preconnected
  exact
    ⟨frontier_noClosed, frontier_noOpen,
      fun C inputs =>
        let input_rows :=
          S2_q14_component_topology_input_source_of_finiteDrawingPreconnected_localSectorRows_20260522
            (C := C) inputs frontier_preconnected (localSectorRows C inputs)
        ⟨input_rows, input_rows.toComponentTopologyRows⟩⟩

set_option linter.style.longLine false in
/-- Claim `S2-q15-topology-no-open-source`.

The q15 finite no-closed/no-open plus component-topology source package is
strictly lowered from the compact-connected no-`K`-crossing premise to the
same-`K` Janiszewski point-between source and the existing local-sector rows.
The finite separation rows come from the checked r19 point-between bridge;
component-topology rows come from the q14 local-sector bridge. -/
theorem
    S2_q15_finiteDrawing_noClosed_noOpen_componentTopology_family_of_kComponentPointsBetween_localSectorRows_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation ∧
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation ∧
        (forall {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C),
            UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs ∧
              UnboundedExteriorFrontierComponentTopologySourceRows inputs) := by
  let finite_rows :=
    S2_r19_finiteDrawing_noOpen_noClosed_of_kComponentPointsBetween_20260522
      points_between
  exact
    ⟨finite_rows.2, finite_rows.1,
      S2_q14_component_topology_input_and_source_family_of_kComponentPointsBetween_localSectorRows_20260522
        points_between localSectorRows⟩

set_option linter.style.longLine false in
/-- Claim `S2-q16-noCompact-source`.

The compact-connected no-`K`-crossing topology source used by the q15/q16
route is strictly lowered to the same-`K` Janiszewski boundary-bumping
point-between primitive.  This is the single upstream topology residual already
consumed by the q15 finite no-closed/no-open package above; no W facade, final
boundary-cycle row, actual-sector row, carrier row, or equivalent no-crossing
alias is introduced. -/
theorem S2_q16_noCompactConnectedKCrossing_source_of_kComponentPointsBetween_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_janiszewskiKComponentPointsBetween_20260521r7d
    points_between

set_option linter.style.longLine false in
/-- Claim `S2-q16-noCompact-source`, aligned-split lower form.

The q16 compact-connected no-`K`-crossing source is pushed one topology layer
below same-`K` point-between to the hard-case aligned closed `K`-split
primitive.  The composition uses only the existing topology lowerers and does
not touch final boundary-cycle rows, exterior-sector rows, W32 consumers,
carrier rows, induced frontier graphs, or arbitrary cycles. -/
theorem S2_q16_noCompactConnectedKCrossing_source_of_nontrivialAlignedKSplit_20260522
    (nontrivial_aligned_K_split :
      PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  S2_q16_noCompactConnectedKCrossing_source_of_kComponentPointsBetween_20260522
    (S2_r18_kcomponent_points_between_source_20260521r18
      nontrivial_aligned_K_split)

set_option linter.style.longLine false in
/-- Claim `S2-q16-noCompact-source`, nontrivial relative-clopen lower form.

This strictly lowers the q16 compact-connected no-`K`-crossing source below
the hard-case aligned closed `K`-split primitive.  A nonempty closed frontier
split already has a one-sided relative-clopen `K` separator; intersecting that
separator and its closed complement with any compact connected `T <= K`
contradicts connectedness.  This route does not use boundary-cycle rows,
carrier rows, actual-sector rows, W32 consumers, or the aligned split source. -/
theorem S2_q16_noCompactConnectedKCrossing_source_of_nontrivialRelativeClopenKSide_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  S2_p2o_no_compact_connected_K_crossing_source_20260521p4
    nontrivial_side

set_option linter.style.longLine false in
/-- Claim `S2-q16-noCompact-source`, Janiszewski relative-clopen lower form.

This records the q16 no-compact-connected-`K`-crossing source directly below
the standard U-indexed Janiszewski/boundary-bumping relative-clopen theorem.
The only extra step is specializing `U` to `connectedComponentIn Kᶜ x`;
the proof then uses the nontrivial relative-clopen q16 adapter above. -/
theorem S2_q16_noCompactConnectedKCrossing_source_of_janiszewskiBoundaryBumping_20260522
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  S2_q16_noCompactConnectedKCrossing_source_of_nontrivialRelativeClopenKSide_20260522
    (planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_janiszewskiBoundaryBumping
      boundary_bumping)

set_option linter.style.longLine false in
/-- Claim `S2-q18-pair-frontier-component-source`.

The q17 U-indexed pair-frontier-component primitive is strictly lowered to the
x-indexed nontrivial relative-clopen `K`-side boundary-bumping theorem.  The
only work is to open the complement-component witness to the Janiszewski
relative-clopen form, use the checked component-avoidance eraser, and then use
the existing q6m frontier-component extraction.  This consumes no
boundary-cycle, carrier, actual-sector, or W32 rows. -/
theorem S2_q18_pair_frontier_component_source_of_nontrivialRelativeClopenKSide_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent :=
  S2_k6m_pair_frontier_component_source
    (planarJaniszewskiBoundaryBumpingComponentAvoidance_of_relativeClopenKSide
      (janiszewskiBoundaryBumping_of_nontrivialRelativeClopenKSide
        nontrivial_side))

set_option linter.style.longLine false in
/-- Claim `S2-q17-topology-aligned-split-source`.

The hard-case aligned closed `K₁/K₂` split source is strictly lowered to the
U-indexed pair-frontier-component boundary-bumping primitive.  The checked
composition packages the frontier component as a point-between witness, turns
that point-between source into the continuous Boolean `K`-side, and then uses
the existing compact-subspace Boolean eraser to produce the aligned closed
split.  This consumes no boundary-cycle rows, carrier rows, actual-sector
rows, W32 consumers, same-`K` point-between source, or no-compact-crossing
alias. -/
theorem S2_q17_topology_alignedKSplit_source_of_pairFrontierComponent_20260522
    (pair_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent) :
    PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit :=
  planarContinuumUnboundedComplementFrontierNontrivialAlignedKSplit_of_continuousKSide
    (planarContinuumUnboundedComplementFrontierContinuousKSide_of_pointsBetween_closedSplit
      (crossingSubcontinuumPointsBetween_of_U_pairFrontierComponent
        pair_component))

set_option linter.style.longLine false in
/-- q18 lower-source route for the q17 aligned-split theorem.

This keeps the existing q17 theorem as the pair-frontier-component eraser and
records the strictly lower primitive now feeding it:
`PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide`. -/
theorem S2_q18_topology_alignedKSplit_source_of_nontrivialRelativeClopenKSide_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit :=
  S2_q17_topology_alignedKSplit_source_of_pairFrontierComponent_20260522
    (S2_q18_pair_frontier_component_source_of_nontrivialRelativeClopenKSide_20260522
      nontrivial_side)

set_option linter.style.longLine false in
/-- Claim `S2-q19-nontrivial-relative-clopen-source`.

The q18 relative-clopen side source is strictly lowered to the existing
whole-frontier no-subcontinuum obstruction.  This stays inside the source-level
topology stack: the obstruction rules out compact connected `K`-crossings of
the two closed frontier pieces, and the existing compact-Hausdorff separator
produces the nontrivial relative-clopen `K` side. -/
theorem S2_q19_nontrivialRelativeClopenKSide_source_of_noSubcontinuumObstruction_20260522
    (no_subcontinuum :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
  planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_noSubcontinuumObstruction
    no_subcontinuum

set_option linter.style.longLine false in
/-- q19 lower-source route for the q18 pair-frontier-component handoff. -/
theorem S2_q19_pair_frontier_component_source_of_noSubcontinuumObstruction_20260522
    (no_subcontinuum :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent :=
  S2_q18_pair_frontier_component_source_of_nontrivialRelativeClopenKSide_20260522
    (S2_q19_nontrivialRelativeClopenKSide_source_of_noSubcontinuumObstruction_20260522
      no_subcontinuum)

set_option linter.style.longLine false in
/-- q19 lower-source route for the q18 aligned-split handoff. -/
theorem S2_q19_topology_alignedKSplit_source_of_noSubcontinuumObstruction_20260522
    (no_subcontinuum :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction) :
    PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit :=
  S2_q18_topology_alignedKSplit_source_of_nontrivialRelativeClopenKSide_20260522
    (S2_q19_nontrivialRelativeClopenKSide_source_of_noSubcontinuumObstruction_20260522
      no_subcontinuum)

set_option linter.style.longLine false in
/-- Claim `S2-q22-frontier-continuum-source`, same-`K` frontier-component form.

The q21 Janiszewski/frontier-component leaf is lowered to the existing
relative-clopen boundary-bumping theorem.  This is only the compact-Hausdorff
component/quasicomponent topology route already isolated in
`ExteriorComponentTopology`; it uses no boundary-cycle, carrier, raw-orbit,
actual-sector, or W32 assumptions. -/
theorem S2_q22_kComponentFrontierComponent_of_janiszewskiBoundaryBumping_20260522
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
  S2_topology_kcomponent_frontier_source boundary_bumping

set_option linter.style.longLine false in
/-- Claim `S2-q22-frontier-continuum-source`, same-`K` point-between form.

The compact-witness point-between surface used by q20/q21 is strictly lowered
through the q22 frontier-component reducer above; the only extra work is the
already checked Mathlib packaging of a frontier connected component as a
compact connected plane witness. -/
theorem S2_q22_kComponentPointsBetween_of_janiszewskiBoundaryBumping_20260522
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  S2_janiszewski_kcomponent_points_between_source
    (S2_q22_kComponentFrontierComponent_of_janiszewskiBoundaryBumping_20260522
      boundary_bumping)

set_option linter.style.longLine false in
/-- Claim `S2-q24-topology-point-between`.

The live same-`K` Janiszewski point-between theorem is lowered to the sharp
existing x-indexed topology primitive already isolated in this file:
`PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide`.
The checked handoff is the earlier non-circular
`S2_agent_kcomponent_pointbetween_worker_20260521d4`; no boundary-cycle,
carrier, actual-sector, W32, induced-frontier, or endpoint shortcut enters. -/
theorem S2_q24_kComponentPointsBetween_of_nontrivialRelativeClopenKSide_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  S2_agent_kcomponent_pointbetween_worker_20260521d4 nontrivial_side

set_option linter.style.longLine false in
/-- Claim `S2-q22-frontier-continuum-source`, q21 no-subcontinuum handoff.

This records the q21 same-`K` source stack with the q22 lower topology leaf:
the remaining assumption is the Janiszewski relative-clopen
boundary-bumping theorem, not the same-`K` point-between/frontier-component
surface. -/
theorem S2_q22_no_subcontinuum_obstruction_source_of_janiszewskiBoundaryBumping_20260522
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction :=
  S2_q21_no_subcontinuum_obstruction_source_of_kComponentFrontierComponent_20260522
    (S2_q22_kComponentFrontierComponent_of_janiszewskiBoundaryBumping_20260522
      boundary_bumping)

set_option linter.style.longLine false in
/-- Claim `S2-q22-frontier-continuum-source`, finite-preconnected side.

The finite drawing frontier-preconnectedness leaf used by q21 is lowered to
the same Janiszewski relative-clopen boundary-bumping theorem by specializing
the planar-continuum preconnectedness source to the embedded finite drawing. -/
theorem S2_q22_finiteDrawing_frontierPreconnected_of_janiszewskiBoundaryBumping_20260522
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide) :
    FiniteDrawingUnboundedComplementFrontierPreconnected :=
  S2_topology_preconnected_leaf_finiteDrawing_of_janiszewskiBoundaryBumping_20260521
    boundary_bumping

set_option linter.style.longLine false in
/-- Claim `S2-q22-frontier-continuum-source`, q21 incident-edge family.

This lowers q21's paired finite leaves to their source-facing forms:
finite frontier preconnectedness comes from Janiszewski relative-clopen
boundary bumping, while the singleton actual-frontier obstruction comes from
the pointwise outside-accumulation boundary-bumping row. -/
theorem
    S2_q22_frontierVertexIncidentSource_family_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs :=
  S2_q21_frontierVertexIncidentSource_family_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    (S2_q22_finiteDrawing_frontierPreconnected_of_janiszewskiBoundaryBumping_20260522
      boundary_bumping)
    (fun C inputs =>
      S2_r5w_singleton_boundaryBumping_obstruction_20260521r5w
        (C := C) inputs (outside_accumulation C inputs))

set_option linter.style.longLine false in
/-- Claim `S2-q22-frontier-continuum-source`, q21 selected-edge cover family.

The selected frontier-edge cover used downstream by q21 is sourced from the
same lowered pair as the incident-edge family: Janiszewski relative-clopen
boundary bumping plus pointwise outside accumulation. -/
theorem
    S2_q22_selectedFrontierEdgeCover_family_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorSelectedFrontierEdgeCover C inputs :=
  S2_q21_selectedFrontierEdgeCover_family_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    (S2_q22_finiteDrawing_frontierPreconnected_of_janiszewskiBoundaryBumping_20260522
      boundary_bumping)
    (fun C inputs =>
      S2_r5w_singleton_boundaryBumping_obstruction_20260521r5w
        (C := C) inputs (outside_accumulation C inputs))

set_option linter.style.longLine false in
/-- Claim `S2-q23-topology-component-source`, selected incident-edge side.

The live face-orbit source spine already carries finite no-open separation.
That is enough to recover finite frontier preconnectedness, and the pointwise
outside-accumulation boundary-bumping source rules out the singleton actual
frontier case.  The checked q21 punctured-accumulation route then supplies the
selected frontier-vertex incident edge row, with no boundary-cycle, carrier,
raw-orbit, actual-sector, or W32 assumption. -/
theorem
    S2_q23_frontierVertexIncidentSource_of_finiteDrawingNoOpenSeparation_outsideAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noOpen :
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation)
    (outside_accumulation :
      UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
        C inputs) :
    FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs :=
  S2_q21_frontierVertexIncidentSource_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
    (C := C) inputs
    (S2_r23_finiteDrawing_frontierPreconnected_of_noOpenSeparation_20260521r23
      frontier_noOpen)
    (S2_r5w_singleton_boundaryBumping_obstruction_20260521r5w
      (C := C) inputs outside_accumulation)

set_option linter.style.longLine false in
/-- Family form of the q23 selected frontier-vertex incident source. -/
theorem
    S2_q23_frontierVertexIncidentSource_family_of_finiteDrawingNoOpenSeparation_outsideAccumulation_20260522
    (frontier_noOpen :
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs :=
  fun C inputs =>
    S2_q23_frontierVertexIncidentSource_of_finiteDrawingNoOpenSeparation_outsideAccumulation_20260522
      (C := C) inputs frontier_noOpen (outside_accumulation C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q37-selected-frontier-incidence-worker`, actual-frontier form.

The selected frontier-vertex incidence family is lowered to the two local
facts that the punctured-accumulation route actually uses: preconnectedness of
the selected actual frontier, and the singleton outside-accumulation
boundary-bumping row.  The proof only composes the existing
punctured-accumulation/open-segment/selected-edge reducers. -/
theorem
    S2_q37_selected_frontier_incidence_worker_of_actualFrontierPreconnected_outsideAccumulation_20260522
    (frontier_preconnected :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorActualFrontierPreconnectedSource C inputs)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs := by
  intro m C inputs
  exact
    S2_frontier_vertex_incident_source_of_puncturedAccumulation_20260522
      (C := C) inputs
      (S2_puncturedAccumulationSource_of_actualFrontierPreconnected_boundaryBumping_20260522
        (C := C) (inputs := inputs)
        (frontier_preconnected C inputs)
        (S2_r5w_singleton_boundaryBumping_obstruction_20260521r5w
          (C := C) inputs (outside_accumulation C inputs)))

set_option linter.style.longLine false in
/-- Claim `S2-q37-selected-frontier-incidence-worker`, finite-drawing form.

Finite-drawing frontier preconnectedness specializes to the selected actual
frontier, so the remaining source surface is exactly that finite drawing
topology fact plus the exterior singleton outside-accumulation row. -/
theorem
    S2_q37_selected_frontier_incidence_worker_of_finiteDrawingPreconnected_outsideAccumulation_20260522
    (frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs :=
  S2_q37_selected_frontier_incidence_worker_of_actualFrontierPreconnected_outsideAccumulation_20260522
    (fun C inputs =>
      actualFrontierPreconnected_of_finiteDrawing_frontierPreconnected
        (C := C) inputs frontier_preconnected)
    outside_accumulation

set_option linter.style.longLine false in
/-- Claim `S2-q23-topology-component-source`.

The input-facing component-topology row for the actual unbounded exterior
frontier is lowered to the same live finite no-open topology row plus the
pointwise outside-accumulation boundary-bumping primitive.  The finite
no-closed route remains available upstream, but this theorem uses the sharper
no-open surface already consumed by the exterior face-orbit producer. -/
theorem
    S2_q23_component_topology_input_source_of_finiteDrawingNoOpenSeparation_outsideAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (frontier_noOpen :
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation)
    (outside_accumulation :
      UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
        C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_r13_component_topology_input_source_of_finiteDrawingNoOpenSeparation_vertexIncident_20260521r13
    (C := C) inputs frontier_noOpen
    (S2_q23_frontierVertexIncidentSource_of_finiteDrawingNoOpenSeparation_outsideAccumulation_20260522
      (C := C) inputs frontier_noOpen outside_accumulation)

set_option linter.style.longLine false in
/-- Family form of the q23 component-topology input source. -/
theorem
    S2_q23_component_topology_input_source_family_of_finiteDrawingNoOpenSeparation_outsideAccumulation_20260522
    (frontier_noOpen :
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  fun C inputs =>
    S2_q23_component_topology_input_source_of_finiteDrawingNoOpenSeparation_outsideAccumulation_20260522
      (C := C) inputs frontier_noOpen (outside_accumulation C inputs)

set_option linter.style.longLine false in
/-- Claim `S2-q23-topology-source-collapse`, component input side.

This is the sharp q23 topology source surface: the actual frontier
preconnectedness field is specialized directly from the Janiszewski
relative-clopen boundary-bumping theorem, while the selected
frontier-vertex incident field comes from the pointwise outside-accumulation
singleton boundary-bumping primitive.  It does not route through finite
no-open/no-closed separation, boundary-cycle producers, actual-sector rows,
carrier rows, raw-orbit rows, or W32 consumers. -/
theorem
    S2_q23_component_topology_input_source_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (outside_accumulation :
      UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
        C inputs) :
    UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  S2_dynamic_component_topology_input_source_of_actualFrontierPreconnected_boundaryBumping_20260522
    (C := C) (inputs := inputs)
    (S2_topology_preconnected_leaf_actualFrontier_of_janiszewskiBoundaryBumping_20260521
      (C := C) inputs boundary_bumping)
    (S2_r5w_singleton_boundaryBumping_obstruction_20260521r5w
      (C := C) inputs outside_accumulation)

set_option linter.style.longLine false in
/-- Family form of the q23 topology source collapse for component input rows. -/
theorem
    S2_q23_component_topology_input_source_family_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
  fun C inputs =>
    S2_q23_component_topology_input_source_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
      (C := C) inputs boundary_bumping (outside_accumulation C inputs)

set_option linter.style.longLine false in
/-- Paired q23 topology source collapse.

The remaining topology leaves are exactly the q22 Janiszewski relative-clopen
boundary-bumping theorem and the pointwise outside-accumulation singleton
boundary-bumping primitive.  They produce both the same-`K`
Janiszewski point-between theorem and the input-facing actual component
topology rows. -/
theorem
    S2_q23_topology_source_collapse_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween /\
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs) :=
  And.intro
    (S2_q22_kComponentPointsBetween_of_janiszewskiBoundaryBumping_20260522
      boundary_bumping)
    (S2_q23_component_topology_input_source_family_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
      boundary_bumping outside_accumulation)

set_option linter.style.longLine false in
/-- Claim `S2-q25-topology-leaf`, same-`K` point-between side.

The q23 same-`K` Janiszewski point-between leaf is lowered past the
U-indexed relative-clopen surface to the x-indexed nontrivial relative-clopen
`K`-side source.  This is only the existing Janiszewski specialization plus
the checked q22 point-between packaging; it adds no W32 consumer, actual-sector
row, carrier row, or boundary-cycle assumption. -/
theorem S2_q25_kComponentPointsBetween_of_nontrivialRelativeClopenKSide_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  S2_q22_kComponentPointsBetween_of_janiszewskiBoundaryBumping_20260522
    (janiszewskiBoundaryBumping_of_nontrivialRelativeClopenKSide
      nontrivial_side)

set_option linter.style.longLine false in
/-- Claim `S2-q25-topology-leaf`, paired nontrivial-relative-clopen collapse.

The paired q23 topology surface is sourced from the x-indexed nontrivial
relative-clopen `K`-side theorem and pointwise outside accumulation.  The first
projection supplies the same-`K` Janiszewski point-between theorem; the second
projection reuses the already checked component-topology input family at the
same nontrivial-relative-clopen leaf. -/
theorem
    S2_q25_topology_source_collapse_of_nontrivialRelativeClopen_outsideAccumulation_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween /\
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs) :=
  And.intro
    (S2_q25_kComponentPointsBetween_of_nontrivialRelativeClopenKSide_20260522
      nontrivial_side)
    (S2_dynamic_component_topology_input_source_family_of_nontrivialRelativeClopen_outsideAccumulation_20260522
      nontrivial_side outside_accumulation)

set_option linter.style.longLine false in
/-- Claim `S2-q25-topology-leaf`, no-compact-connected-crossing side.

The same-`K` Janiszewski point-between leaf is lowered one more checked source
step to the no-compact-connected-`K`-crossing primitive, using the existing
compact-Hausdorff relative-clopen separator route. -/
theorem S2_q25_kComponentPointsBetween_of_noCompactConnectedKCrossing_20260522
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  S2_q25_kComponentPointsBetween_of_nontrivialRelativeClopenKSide_20260522
    (S2_r7b_relative_clopen_k_side_topology_source_20260521r7b
      no_crossing)

set_option linter.style.longLine false in
/-- Claim `S2-q25-topology-leaf`, paired no-compact-connected-crossing collapse.

This is the source-level q25 package with the topology side exposed as
`PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing`.
The local singleton side remains the pointwise outside-accumulation
boundary-bumping primitive. -/
theorem
    S2_q25_topology_source_collapse_of_noCompactConnectedKCrossing_outsideAccumulation_20260522
    (no_crossing :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween /\
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs) :=
  S2_q25_topology_source_collapse_of_nontrivialRelativeClopen_outsideAccumulation_20260522
    (S2_r7b_relative_clopen_k_side_topology_source_20260521r7b
      no_crossing)
    outside_accumulation

set_option linter.style.longLine false in
/-- Claim `S2-q26-topology-source`, same-`K` point-between side.

The q25 point-between topology leaf is strictly lowered past the
no-compact-connected-`K`-crossing and relative-clopen aliases to the local
trace no-closed-separation theorem on
`frontier U ∩ connectedComponentIn K y`.  The only checked work is the
frontier-component packaging already isolated above. -/
theorem S2_q26_kComponentPointsBetween_of_traceNoClosedSeparation_20260522
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
  planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_frontierComponent
    (S2_q26_kComponentFrontierComponent_of_traceNoClosedSeparation_20260522
      trace_noClosed)

set_option linter.style.longLine false in
/-- Claim `S2-q26-topology-source`, no-compact-connected-crossing side.

The current planar topology leaf
`PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing`
is strictly lowered to the local trace no-closed-separation source.  This path
uses only the same-`K` frontier-component reducer and the existing
frontier-subcontinuum/no-closed-separation contradiction; it introduces no
boundary-cycle, carrier, actual-sector, W32, synthetic-enclosure, or induced
frontier-graph hypothesis. -/
theorem S2_q26_noCompactConnectedKCrossing_of_traceNoClosedSeparation_20260522
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_janiszewskiKComponentFrontierComponent_20260521n9
    (S2_q26_kComponentFrontierComponent_of_traceNoClosedSeparation_20260522
      trace_noClosed)

set_option linter.style.longLine false in
/-- Claim `S2-q26-topology-source`, paired collapse.

The q25 paired topology source package is now sourced from the local
component/frontier trace no-closed-separation theorem, together with the
unchanged pointwise outside-accumulation boundary-bumping primitive for the
singleton actual-frontier side.  The exact remaining planar topology source is
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation`. -/
theorem
    S2_q26_topology_source_collapse_of_traceNoClosedSeparation_outsideAccumulation_20260522
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween /\
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs) :=
  And.intro
    (S2_q26_kComponentPointsBetween_of_traceNoClosedSeparation_20260522
      trace_noClosed)
    (S2_dynamic_component_topology_input_source_family_of_nontrivialRelativeClopen_outsideAccumulation_20260522
      (S2_r7b_relative_clopen_k_side_topology_source_20260521r7b
        (S2_q26_noCompactConnectedKCrossing_of_traceNoClosedSeparation_20260522
          trace_noClosed))
      outside_accumulation)

set_option linter.style.longLine false in
/-- Claim `S2-q38-topology-accumulation-source-worker`.

The q30-facing finite topology package is strictly lowered to the q37
component-trace no-closed source plus the pointwise outside-accumulation row.
This exposes all topology rows consumed by the selected seed route: finite
no-closed/no-open separation, punctured accumulation, selected frontier
incidence, and the erased component-topology rows.  The proof only composes
the checked q37/q30 source reducers; it adds no W32 composer, actual-sector
premise, carrier cycle, or boundary-cycle assumption. -/
theorem
    S2_q38_finiteDrawing_topology_accumulation_sources_of_traceNoClosedSeparation_outsideAccumulation_20260522
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation /\
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation /\
        (forall {m : Nat} (C : _root_.UDConfig m)
          (inputs : FinitePlanarOuterComponentInputs C),
            UnboundedExteriorFrontierVertexPuncturedAccumulationSource
              C inputs) /\
          (forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) /\
            (forall {m : Nat} (C : _root_.UDConfig m)
              (inputs : FinitePlanarOuterComponentInputs C),
                UnboundedExteriorFrontierComponentTopologyInputSourceRows
                    inputs /\
                  UnboundedExteriorFrontierComponentTopologySourceRows
                    inputs) := by
  let points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween :=
    S2_q26_kComponentPointsBetween_of_traceNoClosedSeparation_20260522
      trace_noClosed
  let frontier_component :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent :=
    S2_q26_kComponentFrontierComponent_of_traceNoClosedSeparation_20260522
      trace_noClosed
  let finite_rows :
      FiniteDrawingUnboundedComplementFrontierNoOpenSeparation /\
        FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
    S2_r19_finiteDrawing_noOpen_noClosed_of_kComponentPointsBetween_20260522
      points_between
  let frontier_preconnected :
      FiniteDrawingUnboundedComplementFrontierPreconnected :=
    finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
      finite_rows.2
  let punctured :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierVertexPuncturedAccumulationSource
            C inputs :=
    fun C inputs =>
      S2_q30_puncturedAccumulationSource_of_finiteDrawing_frontierPreconnected_boundaryBumping_20260522
        (C := C) inputs frontier_preconnected
        (S2_r5w_singleton_boundaryBumping_obstruction_20260521r5w
          (C := C) inputs (outside_accumulation C inputs))
  let frontier_incident :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs :=
    S2_q37_selected_frontier_incidence_worker_of_finiteDrawingPreconnected_outsideAccumulation_20260522
      frontier_preconnected outside_accumulation
  let component_rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows
              inputs /\
            UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
    fun C inputs =>
      S2_component_topology_source_final_of_kComponentFrontierComponent_puncturedAccumulation_20260522
        (C := C) inputs frontier_component (punctured C inputs)
  exact
    ⟨finite_rows.2, finite_rows.1, punctured, frontier_incident,
      component_rows⟩

set_option linter.style.longLine false in
/-- The exact finite topology rows consumed by the q39 reachable
closed-separation route.

The q30 seed construction needs finite no-open separation and selected
frontier incidence, while the reachable closed-separation eraser needs finite
no-closed separation.  The selected-orbit reachable-closed-separation premise
itself is deliberately not part of this topology-only package. -/
abbrev S2_q39ReachableClosedSeparationTopologyPremises : Prop :=
  FiniteDrawingUnboundedComplementFrontierNoClosedSeparation /\
    FiniteDrawingUnboundedComplementFrontierNoOpenSeparation /\
      (forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs)

set_option linter.style.longLine false in
/-- Project the q39 reachable-closed-separation topology premises from the
checked q38 finite-drawing accumulation package. -/
theorem
    S2_q39_reachableClosedSeparationTopologyPremises_of_q38_finiteDrawing_topology_accumulation_package_20260522
    (topology_package :
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation /\
        FiniteDrawingUnboundedComplementFrontierNoOpenSeparation /\
          (forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierVertexPuncturedAccumulationSource
                C inputs) /\
            (forall {m : Nat} (C : _root_.UDConfig m)
              (inputs : FinitePlanarOuterComponentInputs C),
                FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs) /\
              (forall {m : Nat} (C : _root_.UDConfig m)
                (inputs : FinitePlanarOuterComponentInputs C),
                  UnboundedExteriorFrontierComponentTopologyInputSourceRows
                      inputs /\
                    UnboundedExteriorFrontierComponentTopologySourceRows
                      inputs)) :
    S2_q39ReachableClosedSeparationTopologyPremises :=
  ⟨topology_package.1, topology_package.2.1, topology_package.2.2.2.1⟩

set_option linter.style.longLine false in
/-- q39 topology handoff from the q38 trace/no-closed and
outside-accumulation sources to the exact finite topology premises used by the
reachable closed-separation route. -/
theorem
    S2_q39_reachableClosedSeparationTopologyPremises_of_traceNoClosedSeparation_outsideAccumulation_20260522
    (trace_noClosed :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTraceNoClosedSeparation)
    (outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs) :
    S2_q39ReachableClosedSeparationTopologyPremises :=
  S2_q39_reachableClosedSeparationTopologyPremises_of_q38_finiteDrawing_topology_accumulation_package_20260522
    (S2_q38_finiteDrawing_topology_accumulation_sources_of_traceNoClosedSeparation_outsideAccumulation_20260522
      trace_noClosed outside_accumulation)

set_option linter.style.longLine false in
/-- Claim `S2-q42-topology-crossing-source-worker`, no-compact side.

The live no-compact-connected-`K`-crossing source is lowered to the local
component/frontier trace-preconnectedness theorem.  This is the sharp topology
source currently exposed by the q37/q36 route: trace preconnectedness gives
trace no-closed-separation, and that trace source rules out the compact
connected crossing witness. -/
theorem S2_q42_noCompactConnectedKCrossing_source_of_kComponentTracePreconnected_20260522q42
    (trace_preconnected :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected) :
    PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing :=
  S2_q36_noCompactConnectedKCrossing_source_of_janiszewskiKComponentTraceNoClosedSeparation_20260522q36
    (S2_q37_kComponentTraceNoClosedSeparation_of_kComponentTracePreconnected_20260522q37
      trace_preconnected)

set_option linter.style.longLine false in
/-- Claim `S2-q42-topology-crossing-source-worker`, finite no-closed side.

The finite-drawing no-closed-separation row consumed by the live exterior
frontier route follows from the same local trace-preconnectedness source via
the compact-connected crossing exclusion above. -/
theorem S2_q42_finiteDrawing_noClosedSeparation_source_of_kComponentTracePreconnected_20260522q42
    (trace_preconnected :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected) :
    FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  S2_subagent_topology_source_20260521_current_finiteDrawing_noClosedSeparation_of_noCompactConnectedKCrossing
    (S2_q42_noCompactConnectedKCrossing_source_of_kComponentTracePreconnected_20260522q42
      trace_preconnected)

set_option linter.style.longLine false in
/-- Claim `S2-q42-topology-crossing-source-worker`, finite preconnected side.

This is the preconnected presentation of the same finite topology leaf: finite
no-closed-separation converts to frontier preconnectedness by the existing
closed-piece criterion. -/
theorem S2_q42_finiteDrawing_frontierPreconnected_source_of_kComponentTracePreconnected_20260522q42
    (trace_preconnected :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected) :
    FiniteDrawingUnboundedComplementFrontierPreconnected :=
  finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
    (S2_q42_finiteDrawing_noClosedSeparation_source_of_kComponentTracePreconnected_20260522q42
      trace_preconnected)

set_option linter.style.longLine false in
/-- Paired q42 finite topology source from the sharp local trace-preconnected
residual. -/
theorem S2_q42_finiteDrawing_preconnected_noClosed_source_of_kComponentTracePreconnected_20260522q42
    (trace_preconnected :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected) :
    FiniteDrawingUnboundedComplementFrontierPreconnected /\
      FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
  And.intro
    (S2_q42_finiteDrawing_frontierPreconnected_source_of_kComponentTracePreconnected_20260522q42
      trace_preconnected)
    (S2_q42_finiteDrawing_noClosedSeparation_source_of_kComponentTracePreconnected_20260522q42
      trace_preconnected)

end

end ExteriorComponentTopology
end Swanepoel
end ErdosProblems1066
