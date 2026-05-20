# Global Task Tracker

This file is the executable task queue and compact workboard for the Lean
formalization of Erdos problem 1066.  It is intentionally not a wave ledger,
route encyclopedia, build log, or project-structure document.

Detailed theorem dependencies live in
`E:/Personal/Erdosproblems/1066/proof_workings/theorem_dependency_map.md`.
Source-paper proof plans live in `proof_workings/*_lean_ready.md`.

## Operating Rules

- Completion of the proof project is the target.  File count is not the
  scoreboard.
- A worker should own a closing obligation: prove a needed lemma, inhabit a
  concrete source field/package, verify a claimed closure, search mathlib,
  sharpen a theorem statement, or remove a blocked route from the live path.
- Active worker claims belong in this file when multiple agents may touch the
  same section.  Each claim must name the owner, role, write scope, status, and
  next verification command or gate.  Clear or summarize the claim when it is
  completed, blocked, or superseded.
- Add a new Lean file only when it gives a real ownership, import-boundary,
  reusable-certificate, or compile-time advantage.  Prefer proving related
  results near the existing owner module.
- Do not add another numbered facade/audit layer unless it directly shortens or
  closes a real obligation.
- Mark a task done only after the relevant declaration is imported by
  `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`, builds with the
  pinned toolchain, and the forbidden-token scan is clean.
- `proof_workings/` is for proof-plan `.md` files only.  Disposable logs belong
  under ignored `proof_logs/`.

## Verification Gates

Before any public-bound claim or checked-off task:

```powershell
Set-Location 'E:/Personal/Erdosproblems/1066'
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066
```

PowerShell-safe source scan:

```powershell
Set-Location 'E:/Personal/Erdosproblems/1066'
rg -n -i -e '\baxiom\b' -e '\bconstant\b' -e '\bsorry\b' -e '\badmit\b' `
  -e 'unsafe' -e 'opaque' -e 'implemented_by' -e '#check' -e '#print' `
  -e '#eval' ./ErdosProblems1066 ./ErdosProblems1066.lean --glob '*.lean'
if ($LASTEXITCODE -eq 1) { 'clean' } elseif ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
```

Active certification tasks:

- [ ] Run the pinned full root build on the current checkout.
- [x] Run the forbidden-token scan on the current checkout.
- [x] Run the trust-source scan on the current checkout.
- [x] Run retained root import coverage and resolve missing, extra, or
  duplicate imports on that surface.
- [ ] Replay the CI-style axiom audit for the current endpoint list.
- [ ] Keep `KnownBounds.lean` closed to Swanepoel `8 / 31` and Pach--Toth
  `5 / 16` until unconditional internal verified theorems exist.

Root-state ledger: current retained source surface has root import coverage
`872/872` and clean forbidden/trust scans.  Earlier successful logs
`proof_logs/root_build_20260519_082033.out.log` and
`proof_logs/ci_axiom_audit_stdout_20260519_082158.txt` predate later Lean-file
edits, so they are no longer certification for the current checkout.  Re-run
the pinned full root build and CI-style axiom audit before crediting new
checked-off work.  The exact-base all-positive flexible source is refuted by
the root-imported W33/W34 blocker stack.  W33/W34 files are completion evidence
only for the conditional endpoints they prove; they do not close Swanepoel
`8 / 31` or Pach--Toth `5 / 16` without an unconditional internal theorem.
Lean/Lake CLI resolution has been repaired at the User PATH level: the WinGet
elan shim directory now precedes `C:/Users/Tom/bin`, so new shells resolve
`lean`/`lake` through the `leanprover/lean4:v4.28.0` toolchain.  Existing
shells should refresh PATH before verification.  Concurrent Lake jobs still
cause silent `-1` exits in this workspace; serialize final certification
builds.

## Swanepoel First

Finish Swanepoel `8 / 31` before broadening Pach--Toth work.  The live work is
source inhabitation for the compact `W34ActualRoutePremises` route, not more
facades or route ledgers.

### S1. No-Cut Minimal Failure

- [x] Treat no-cut as checked infrastructure and integration-only.
  - Checked route: `CutVertexSideCardFromMinimality` refutes
    `CutPartitionBothPlusSidesCutForcedData`; W32/W34 expose
    `NoCutPointwiseBridgeW32.noCutDependency_of_refuting_bothPlusSidesCutForced`
    and `NoCutMinimalityClosureW34.noCutVertexFamily_of_refuting_bothPlusSidesCutForced`.
  - Current action: use the checked no-cut family in final assembly.  Do not
    reopen cut-partition deletion, side-card, or actual-route-premise no-cut
    branches unless a theorem name has become stale.

### S2. Minimal-Failure Topology And Boundary Rows

- [ ] Prove the input-only actual exterior boundary-cycle source theorem.
  - Paper steps: `E8-E11`, the paper jump from a 2-connected finite planar
    straight-line graph to a simple outer boundary polygon, expressed as an
    actual unbounded-exterior frontier cycle.
  - Source input:
    `JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs C`.
  - Desired theorem:
    an input-only theorem producing
    `ExteriorComponentTopology.ActualBoundaryCycleFrontierEquivalenceRows C inputs`,
    or directly producing
    `ExteriorComponentTopology.UnboundedExteriorFrontierCycleRows C inputs`,
    with only `C` and `inputs` as source parameters.
  - Final S2 target:
    `ExteriorComponentTopology.UnboundedExteriorFrontierCycleRows C inputs`,
    then `JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarStraightLineOuterComponentTheorem`,
    then `FaceBoundaryTopologySourceW32.MinimalFailureExactActualTopologyFieldsTarget`.
  - Checked reducer path:
    `ActualBoundaryCycleFrontierEquivalenceRows C inputs` erases directly via
    `unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows`.
    The carrier route through `FaceDartOrbitExteriorCarrierRows` and
    `ExteriorFrontierCarrierRows` remains a checked support path, but it is a
    consumer path; it does not construct the exterior cycle or prove outerness.
  - Current concrete blockers, in order:
    1. Construct the actual exterior boundary cycle
       `B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C`.
    2. Prove graph vertices on the unbounded exterior frontier iff they are
       boundary-cycle vertices of `B`.
    3. Prove every boundary-cycle edge has its open segment on the unbounded
       exterior frontier.
    4. Package these rows as
       `ActualBoundaryCycleFrontierEquivalenceRows C inputs` and erase to
       `UnboundedExteriorFrontierCycleRows C inputs`.
    5. If using the carrier/geometric support path, additionally prove
       `GeometricBoundarySuccessorRows` and
       `BoundaryCycleIncidentFrontierEdgeCompleteness`.
  - Checked groundwork: local edge isolation, local vertex-star isolation,
    x-axis unbounded-component seed rows, concrete geometric rotation by
    `Complex.arg`, frontier vertex/edge carriers, endpoint closure, carrier
    adjacency projection, raw face-successor orbit adapters, repeated-boundary
    no-cut helper rows, and closure-to-open-segment frontier propagation.
  - Carrier honesty requirement: the carrier graph must use actual exterior
    boundary edges of `unboundedExteriorComponentRows C inputs`, not the
    induced graph on all frontier vertices and not an arbitrary two-regular
    chord cycle.  Each carrier edge must have its open segment on the unbounded
    exterior frontier.
  - Do not use synthetic enclosure rows such as `insideOrOn := fun _ => True`,
    convex-hull vertices, the canonical/girth cycle unless it is proved outer,
    identity cyclic-order rows as geometry, or any numbered compatibility layer
    as the live method.
  - Completion gate: the source theorem is imported by
    `ErdosProblems1066.lean`, targeted owner-file builds pass, the pinned root
    build passes, the forbidden-token scan is clean, and this item is checked
    only after those gates.

S2 dynamic assignments:
  - Owner slots, not live claim entries:
    - Owner slot: `S2-boundary-successor`.  Role: prove
      `GeometricBoundarySuccessorRows` for the chosen exterior boundary cycle.
      Status: claimed by `S2-exterior-boundary-cycle-source` / Codex-main;
      local angular/source rows are split across the active exterior-sector
      and actual-boundary-cycle source claims below.  Scope:
      `Swanepoel/ExteriorComponentTopology.lean` with read-only use of
      `Swanepoel/GeometricRotationSystem.lean` and
      `Swanepoel/FinitePlaneDrawing.lean`.  Next verification: owner-file Lean
      build.
    - Owner slot: `S2-frontier-vertex-iff-cycle`.  Role: prove graph vertex on
      the unbounded exterior frontier iff it is a boundary-cycle vertex.
      Status: claimed by `S2-exterior-boundary-cycle-source` / Codex-main.
      Scope: `Swanepoel/ExteriorComponentTopology.lean` with read-only use of
      `Swanepoel/FinitePlaneDrawing.lean`.  Next verification: owner-file Lean
      build.
    - Owner slot: `S2-boundary-edge-open-frontier`.  Role: prove every
      boundary-cycle edge has its open segment on the unbounded exterior
      frontier.  Status: claimed by `S2-exterior-boundary-cycle-source` /
      Codex-main.  Scope: `Swanepoel/ExteriorComponentTopology.lean` with
      read-only use of `Swanepoel/FinitePlaneDrawing.lean`.  Next
      verification: owner-file Lean build.
    - Owner slot: `S2-incident-frontier-edge-completeness`.  Role: prove
      `BoundaryCycleIncidentFrontierEdgeCompleteness`.  Status: claimed by
      `S2-exterior-boundary-cycle-source` / Codex-main.  The bad-incident
      repeated-separation source row is closed; any remaining incident-edge
      work is covered by the active `S2-agent-actual-boundary-cycle-source`
      and `S2-agent-edgeRows-boundary-succ-source` claims.  Scope:
      `Swanepoel/ExteriorComponentTopology.lean`.
      Next verification: owner-file Lean build.
    - Owner slot: `S2-input-only-carrier-assembly`.  Role: assemble the source
      rows into `ExteriorComponentTopology.exteriorFrontierCarrierRows_of_inputs`,
      `UnboundedExteriorFrontierCycleRows C inputs`, and the W32 exact topology
      target.  Status: claimed by `S2-exterior-boundary-cycle-source` /
      Codex-main, blocked only on the source rows.  Scope:
      `Swanepoel/ExteriorComponentTopology.lean`,
      `Swanepoel/FaceBoundaryTopologySourceW32.lean`, and root imports only
      after the source theorem closes.  Next verification: owner-file Lean
      builds before any root build.
  - Active claimed tasks (refreshed 2026-05-19, S2 only):
    Only the `Claim:` entries in this refreshed block are active live claims.
    Older entries below are retained as history and must not be treated as
    live claims.
    Treat this block as the workboard: claim before editing, name one owner
    and one role per claim, keep writable scopes disjoint when possible, and
    clear a claim only by moving it to superseded history with its result and
    verification gate.
    New spawned S2 agents go in this active block only as one compact claim
    with claim id, owner, role, scope, status, and next gate.  Update an
    overlapping claim instead of adding a sibling, and move closed, blocked,
    or stale entries to the superseded history as a short result summary.
    Claim schema: `Claim`, `Owner`, `Role`, `Scope`, `Status`, `Handoff`,
    `Next gate`.  `Role` must be one specific job, not a batch label:
    theorem prover, reducer integrator, route mapper, source-row verifier,
    taskboard editor, or build verifier.  `Scope` states writable files;
    `Handoff` names the exact theorem/row consumed by the next worker; and
    `Next gate` names the targeted build or source check before the claim can
    be cleared.  Clear a live claim only after its owner is done: move it to
    superseded history with result, verification, and any remaining theorem
    names.  If a claim is abandoned or replaced, mark that explicitly instead
    of leaving a stale owner slot.
    - Claim: `S2-exterior-boundary-cycle-source`.  Owner: Codex-main.
      Role: theorem prover.  Scope:
      `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`, with read-only
      use of `Swanepoel/FinitePlaneDrawing.lean`,
      `Swanepoel/GeometricRotationSystem.lean`, and
      `Swanepoel/JordanTopologyFactsConcrete.lean`.  Status: active.  Current
      deliverable: construct the input-only unbounded exterior frontier cycle
      source from the actual exterior face route, keeping existing owner files
      green and avoiding duplicate packages/facades.  Handoff:
      `UnboundedExteriorFrontierCycleRows C inputs` for every
      `FinitePlanarOuterComponentInputs C`, then
      `FinitePlanarStraightLineOuterComponentTheorem` and the W32 exact
      topology target.  Current focus: prove the actual raw face-orbit source
      rows: raw dart-edge frontier, raw-tail coverage of the unbounded frontier
      carrier, pointwise actual local-sector rows, and repeated-tail separation
      rows for no-cut injectivity.
      New checked support rows integrated by Codex-main:
      `FinitePlaneDrawing.segmentPoint_eq_affineLineMap`,
      `FinitePlaneDrawing.closedSegment_subset_affineSpan_pair`,
      `FinitePlaneDrawing.edgeNormalCoord_segmentPoint_eq_zero`,
      `FinitePlaneDrawing.edgeNormalCoord_swap`,
      `FinitePlaneDrawing.edgeNormalCoord_normalOffsetPoint`,
      `FinitePlaneDrawing.edge_direction_sq_sum_pos`,
      `FinitePlaneDrawing.edgeNormalCoord_normalOffsetPoint_pos_of_zero_of_pos_of_ne`,
      `FinitePlaneDrawing.mem_affineSpan_pair_of_edgeNormalCoord_eq_zero_of_ne`,
      `FinitePlaneDrawing.exists_ball_inter_edgeNormalCoord_zero_subset_closedSegment_of_inOpenSegment_of_ne`,
      `FinitePlaneDrawing.convex_edgePositiveSideBall`,
      `FinitePlaneDrawing.isPreconnected_edgePositiveSideBall`,
      `FinitePlaneDrawing.mem_closure_edgePositiveSideBall_of_edgeNormalCoord_eq_zero`,
      `FinitePlaneDrawing.mem_closure_edgePositiveSideBall_of_edgeNormalCoord_eq_zero_of_mem_ball`,
      `FinitePlaneDrawing.sSameSide_ball_subset_drawingComplement_of_local_closedSegment`,
      `FinitePlaneDrawing.edgePositiveSideBall_subset_drawingComplement_of_local_closedSegment`,
      `FinitePlaneDrawing.edgePositiveSideBall_swap_subset_drawingComplement_of_local_closedSegment`,
      `ExteriorComponentTopology.preconnected_subset_unboundedExterior_of_subset_drawingComplement_of_mem`,
      `ExteriorComponentTopology.exists_preconnected_drawingComplement_patch_of_positiveSideBall_exterior_point`,
      `ExteriorComponentTopology.exists_exterior_point_in_positive_or_swapped_sideBall_of_frontier_edge_point`,
      `ExteriorComponentTopology.fixed_side_exterior_points_of_positive_or_swapped_sideBall`,
      `ExteriorComponentTopology.fixed_side_exterior_points_of_frontier_edge_point`,
      `ExteriorComponentTopology.relative_ball_closure_of_frontier_edge_point`,
      `ExteriorComponentTopology.interiorRelativeBallClosureRow_of_frontier_edge_point`,
      `ExteriorComponentTopology.interiorEdgeNearbyExteriorPointSource_of_frontier_edge_point`,
      `ExteriorComponentTopology.interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point`,
      `ExteriorComponentTopology.interiorClosureLocusRelativeOpenSource_of_frontier_edge_point`,
      `ExteriorComponentTopology.S2_agent_frontier_preconnected_source_route_rawFaceSuccOrbit_of_frontier_edge_point`,
      `ExteriorComponentTopology.S2_agent_frontier_cover_to_connected_carrier_integration_of_frontier_edge_point`,
      `ExteriorComponentTopology.rawFaceSuccOrbitActualExteriorArcSeparationRows_of_dart_edge_frontier_pairRows`,
      `ExteriorComponentTopology.S2_agent_selected_raw_orbit_frontier_and_tail_coverage_source`,
      `ExteriorComponentTopology.S2_agent_selected_raw_orbit_frontier_and_tail_coverage_source_no_edgeRows`,
      `ExteriorComponentTopology.S2_agent_selected_seed_dart_edge_frontier_of_actualBoundaryRows`,
      `ExteriorComponentTopology.S2_agent_selected_seed_raw_edge_openSegment_frontier_of_actualBoundaryRows`,
      `ExteriorComponentTopology.S2_agent_selected_seed_tail_coverage_of_actualBoundaryRows_sectorRows`,
      `ExteriorComponentTopology.S2_agent_rawExteriorFaceWalk_tail_injective_of_actualArcRows`,
      `ExteriorComponentTopology.S2_agent_rawExteriorFaceWalk_unitDistanceCycleBoundary_of_noCut`,
      `ExteriorComponentTopology.S2_agent_actualBoundaryCycleRows_of_rawExteriorFaceWalk`,
      `ExteriorComponentTopology.actualBoundaryCycleFrontierEquivalenceRows_of_rawFaceSuccOrbitSourceRows`,
      `ExteriorComponentTopology.actualBoundaryCycleFrontierEquivalenceRows_of_exists_rawFaceSuccOrbit_sourceRows`,
      `ExteriorComponentTopology.actualBoundaryCycleFrontierEquivalenceRows_of_rawFaceSuccOrbit_inputRows`,
      `ExteriorComponentTopology.RawFaceSuccOrbitRepeatedTailExteriorCutRows`,
      `ExteriorComponentTopology.rawFaceSuccOrbit_tail_injective_of_repeatedTailExteriorCutRows`,
      `ExteriorComponentTopology.localSectorRows_of_boundary_frontier_incident_edge_exterior_angular_sector`,
      `ExteriorComponentTopology.interiorRelativeBallClosureRow_of_fixed_side_halfballs`,
      `ExteriorComponentTopology.interior_frontier_edge_carrier_membership_source_of_fixed_side_halfballs`,
      `ExteriorComponentTopology.boundary_frontier_openSegment_relativeClosurePropagation_of_fixed_side_halfballs`,
      `ExteriorComponentTopology.boundary_frontier_openSegment_local_exterior_sector_of_incident_edge_angular`,
      `ExteriorComponentTopology.S2_agent_local_exterior_point_sector_source_of_incident_edge_angular`,
      `ExteriorComponentTopology.boundary_frontier_openSegment_local_exterior_sector_of_boundaryCycleIncidentFrontierEdgeCompleteness`,
      `ExteriorComponentTopology.boundary_frontier_openSegment_local_exterior_sector_of_boundaryVertexExteriorSectorRows`,
      `ExteriorComponentTopology.S2_agent_local_exterior_point_sector_source_of_boundaryCycleIncidentFrontierEdgeCompleteness`,
      `ExteriorComponentTopology.exists_local_frontier_germ_two_of_vertex_star_isolation_openSegment_local_exterior_sector`,
      `ExteriorComponentTopology.boundaryVertexExteriorSectorRowsAt_of_boundaryVertexAngularNoBetweenRows_openSegment_local_exterior_sector`,
      `ExteriorComponentTopology.boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_openSegment_local_exterior_sector`,
      `ExteriorComponentTopology.boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_incident_edge_angular`,
      `ExteriorComponentTopology.boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_boundaryCycleIncidentFrontierEdgeCompleteness`,
      `ExteriorComponentTopology.S2_agent_actual_exterior_sector_input_source_2_from_openSegment_local_exterior_sector`,
      `ExteriorComponentTopology.S2_agent_actual_exterior_sector_input_source_2_from_incident_edge_angular`,
      `ExteriorComponentTopology.S2_agent_actual_exterior_sector_input_source_2_from_boundaryCycleIncidentFrontierEdgeCompleteness`,
      `ExteriorComponentTopology.S2_agent_actual_exterior_sector_input_source_2_from_faceSuccRows_orientation_boundary_cycle_edge_mem_boundaryCycleIncidentFrontierEdgeCompleteness`,
      `ExteriorComponentTopology.interiorEdgeOpenSegmentLocalExteriorSideComponentSource_of_preconnected_drawingComplement_patch`,
      and
      `ExteriorComponentTopology.exists_preconnected_drawingComplement_patch_of_positiveSideBall_exterior_points_of_edge`,
      plus the source reducer
      `ExteriorComponentTopology.interiorEdgeOpenSegmentLocalExteriorSideComponentSource_of_positiveSideBall_exterior_points`.
      Current local-side result: the relative closure row and exact interior
      frontier-edge carrier membership source are now checked from the
      fixed-side half-ball argument.  Remaining S2 obligations are no longer
      the local edge half-ball source; the local open-segment sector route is
      now reduced to `BoundaryFrontierIncidentEdgeExteriorAngularSector`.
      The W3 point-sector path no longer needs callers to carry
      `BoundaryFrontierOpenSegmentRelativeClosurePropagation`; fixed-side
      half-balls discharge that internally, leaving the selected incident-edge
      angular row plus the explicit endpoint incident-only row.
      For the primitive boundary-sector route, the endpoint row is no longer
      needed: the new open-segment vertex-star theorem shrinks locally around
      the boundary vertex and converts `BoundaryFrontierOpenSegmentLocalExteriorSector`
      directly into the local two-germ row used by
      `BoundaryVertexExteriorSectorRowsAt`, and the bundled
      `ActualExteriorSectorInputSourceRows` now has a direct open-segment /
      incident-edge-angular source route.
      Codex-main added and checked
      `ExteriorComponentTopology.S2_agent_input_s2_assembly_gap_reducer_rawOrbitActualArcRows_of_frontier_edge_point`,
      which sources frontier preconnectedness from selected raw-orbit carrier
      edge coverage and sources raw nonbacktracking from local sectors.  This
      was sharpened with
      `ExteriorComponentTopology.rawFaceSuccOrbit_edge_coverage_of_tail_coverage_localSectorRows`
      and
      `ExteriorComponentTopology.S2_agent_input_s2_assembly_gap_reducer_rawOrbitActualArcRows_of_tailCoverage`,
      so carrier edge coverage is now derived from raw-tail coverage plus
      local sectors.  A further checked reducer,
      `ExteriorComponentTopology.S2_agent_input_s2_assembly_gap_reducer_rawOrbitActualArcRows_of_carrierConnected`,
      derives raw-tail coverage from connectedness of the actual
      unbounded-frontier carrier.  Codex-main then checked
      `ExteriorComponentTopology.rawFaceSuccOrbit_dart_edge_openSegment_frontier_of_actualExteriorArcSeparationRows`
      and
      `ExteriorComponentTopology.S2_agent_input_s2_assembly_gap_reducer_actualArcRows_of_carrierConnected`,
      so the actual exterior-arc package now supplies the selected dart-edge
      frontier row itself.  This actual-arc route is reduced to local sectors,
      honest carrier connectedness, and the orbit-level actual exterior arc
      package; the minimal repeated-tail exterior cut row remains the preferred
      replacement target if the stronger actual-arc cover row is later
      weakened.
      Continue with raw face-successor selected-edge coverage of
      `unboundedFrontierEdgeSet C inputs`, actual-boundary/local-sector rows,
      and repeated-tail separation rows for no-cut injectivity.  Latest
      targeted builds passed for
      `Swanepoel/FinitePlaneDrawing.lean` and
      `Swanepoel/ExteriorComponentTopology.lean`; latest targeted
      `Swanepoel/FaceBoundaryTopologySourceW32.lean` build also passed; latest module build
      `lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology`
      also passed.  The modified Lean forbidden scan for axioms/constants/
      sorries/admits/unsafe/opaque/debug commands is clean for the current
      S2 owner files.  Latest S2
      subagent dispatches for selected dart-edge frontier, incident angular
      rows, and repeated-tail arcs completed and were pruned; their routes are
      recorded below and incorporated where checked.  A fresh dynamic
      explorer dispatch for raw face-successor coverage was attempted by
      Codex-main and rejected by the global agent-thread cap, so no new
      subagent claim is live from that attempt.  New subagents may be
      dispatched only for one residual source row above, with a separate
      workboard claim before dispatch once capacity reopens.
      Next gate: targeted
      `ExteriorComponentTopology.lean` and
      `FaceBoundaryTopologySourceW32.lean` builds before root import/root
      build work.
    - Claim: `S2-agent-dart-edge-frontier-source`.  Owner:
      `019e42e0-4268-74f1-8da4-314aea78a146` / Averroes the 3rd.  Role:
      route mapper.  Scope: read-only
      `Swanepoel/ExteriorComponentTopology.lean`,
      `Swanepoel/FinitePlaneDrawing.lean`, and
      `Swanepoel/GeometricRotationSystem.lean`.  Status: active.  Handoff:
      a non-circular proof route for the selected raw face-successor orbit
      per-dart theorem that every dart open segment is on the unbounded
      exterior frontier.  Next gate: integrate exact theorem skeleton or move
      to superseded history.
    - Claim: `S2-agent-carrier-connected-source`.  Owner:
      `019e42e0-42b3-7db0-a1eb-720db41cbd29` / Avicenna the 3rd.  Role:
      source-row verifier.  Scope: read-only
      `Swanepoel/ExteriorComponentTopology.lean` and
      `Swanepoel/FinitePlaneDrawing.lean`.  Status: active.  Handoff: verify
      the shortest route from existing frontier preconnectedness/local-sector
      rows to connectedness of `unboundedFrontierCarrierGraph C inputs`, and
      identify any remaining theorem that must be proved rather than assumed.
      Next gate: route incorporated or claim moved to superseded history.
    - Claim: `S2-agent-repeated-tail-cut-source`.  Owner:
      `019e42e0-4301-7072-b1c3-6b912c86ccfa` / Kierkegaard the 3rd.  Role:
      theorem prover.  Scope: read-only
      `Swanepoel/ExteriorComponentTopology.lean` and graph reachability APIs.
      Status: active.  Handoff: exact proof obligation for
      `RawFaceSuccOrbitRepeatedTailExteriorCutRows` from a repeated selected
      exterior raw face orbit tail, avoiding the obsolete actual-arc cover row.
      Next gate: exact theorem skeleton integrated or claim moved to
      superseded history.
  - Superseded active-claim history (closed/pruned or stale; not live):
    Retained for audit trail until the next full workboard cleanup.
    Closed completed/pruned claim:
    `S2-agent-raw-face-orbit-source`
    (`019e42d9-4e45-7da1-828d-8aecb0e814c0`).  Result: non-circular raw route
    starts from `unboundedExteriorFrontierSeed_nonempty` and
    `exists_geometricRawFaceSuccOrbitSeed_of_unboundedExteriorFrontierSeed_localSectorRows`;
    the smallest missing theorem is the per-dart source
    `S2_agent_raw_face_orbit_dart_edge_frontier_source`, which says every
    open segment of every dart in the selected geometric raw face-successor
    orbit is on the unbounded exterior frontier.  The checked converter
    `rawFaceSuccOrbit_edge_openSegment_frontier_of_dart_edge_openSegment_frontier`
    then gives consecutive-tail open-segment frontier rows.  Verification:
    route checked read-only; no file edit needed.
    Closed completed/pruned claim:
    `S2-agent-input-only-source-reducer`
    (`019e42d9-4df1-77a2-98d3-9f090b22079d`).  Result: smallest non-circular
    input-only source remains
    `ActualBoundaryCycleFrontierEquivalenceRows.BoundaryCycleEdgeMemSource C inputs`,
    equivalently a concrete `UnitDistanceCycleBoundary` whose vertices are
    exactly graph vertices on the unbounded exterior frontier and whose
    consecutive sides are in `unboundedFrontierEdgeSet`; cyclic rows derived
    from downstream `ActualBoundaryCycleFrontierEquivalenceRows` or
    `UnboundedExteriorFrontierCycleRows` are circular as source.  Codex-main
    added raw-source erasers to display the same actual boundary-cycle row
    from non-circular raw face-orbit source rows.  Verification: targeted
    `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-agent-repeated-tail-source-check`
    (`019e42d9-4e92-7733-86e8-627222cb5b4f`).  Result:
    `RawFaceSuccOrbitActualExteriorArcSeparationRows` is too strong as a live
    source because its pair row covers all non-cut graph vertices by raw arc
    images; interior vertices break that.  Codex-main added the replacement
    `RawFaceSuccOrbitRepeatedTailExteriorCutRows` and
    `rawFaceSuccOrbit_tail_injective_of_repeatedTailExteriorCutRows`, which
    only ask for two arc-side witnesses and unreachable-after-delete, then
    erase through `repeatedExteriorBoundarySeparationRows_of_unreachable_after_delete`.
    Verification: targeted `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-agent-actual-boundary-cycle-existence-live`
    (`019e42d1-2fab-7c81-abd1-9e6a6f50ea7f`).  Result: the input-only final
    theorem shape is
    `actualBoundaryCycleFrontierEquivalenceRows_of_finitePlanarOuterComponentInputs`;
    it should construct `ActualBoundaryCycleFrontierEquivalenceRows C inputs`
    and feed
    `unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows`
    and
    `finitePlanarStraightLineOuterComponentTheorem_of_actualBoundaryCycleFrontierEquivalenceRows`.
    Verification: route checked against existing reducers; no file edit needed.
    Closed completed/pruned claim:
    `S2-agent-face-walk-simple-cycle-live`
    (`019e42d1-3000-7871-9b53-1688e911746c`).  Result: raw exterior face walk
    proof split recorded: selected raw orbit from a frontier seed, dart-edge
    frontier, repeated-tail actual arc rows, no-cut tail injectivity, and
    `ActualBoundaryCycleFrontierEquivalenceRows.ofRawFaceSuccOrbitBoundaryRows`.
    Codex-main added the checked selected-seed tail-coverage adapter
    `S2_agent_selected_seed_tail_coverage_of_actualBoundaryRows_sectorRows`.
    Verification: targeted `ExteriorComponentTopology.lean` build passed after
    integration.
    Closed completed/pruned claim:
    `S2-agent-selected-dart-edge-frontier-live`
    (`019e42cb-6f4a-77a0-8b31-a77e98c19d6b`).  Result: route incorporated;
    selected boundary-oriented raw starts from
    `ActualBoundaryCycleFrontierEquivalenceRows` now feed checked dart-edge
    and consecutive raw-edge frontier rows via
    `S2_agent_selected_seed_dart_edge_frontier_of_actualBoundaryRows` and
    `S2_agent_selected_seed_raw_edge_openSegment_frontier_of_actualBoundaryRows`.
    Verification: targeted `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-agent-boundary-incident-angular-live`
    (`019e42cb-6f9b-7231-a37a-0e1033e0cb56`).  Result: no new source package
    needed; the minimal live source remains
    `BoundaryCycleIncidentFrontierEdgeCompleteness inputs B` or equivalently,
    under angular no-between rows,
    `BoundaryFrontierIncidentEdgeExteriorAngularSector inputs B`.
    Verification: route checked against existing reducers; no file edit needed.
    Closed completed/pruned claim:
    `S2-agent-repeated-tail-arc-live`
    (`019e42cb-6fea-7e51-b675-a3eb8ed88376`).  Result: pair-level repeated
    tail source isolated as
    `RawFaceSuccOrbitRepeatedTailActualExteriorArcRows (inputs := inputs) O i j`;
    existing reducers then feed `RawFaceSuccOrbitActualExteriorArcSeparationRows`
    and no-cut tail injectivity.  Verification: route checked against existing
    reducers; no file edit needed beyond the already checked eraser.
    Closed completed/pruned claim:
    `S2-agent-raw-orbit-frontier-source-now`
    (`019e42c3-92c2-73d3-bb83-bedf650df81a`).  Result: route incorporated;
    raw-tail coverage is checked once the selected raw dart-edge frontier row
    exists, via
    `S2_agent_selected_raw_orbit_frontier_and_tail_coverage_source`.
    Verification: targeted `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-agent-local-sector-source-now`
    (`019e42c3-9315-7351-92ac-c38252414fac`).  Result: route incorporated;
    local-sector rows now reduce through
    `localSectorRows_of_boundary_frontier_incident_edge_exterior_angular_sector`;
    the genuine remaining local-sector source is
    `BoundaryFrontierIncidentEdgeExteriorAngularSector inputs B`.  Verification:
    targeted `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-agent-repeat-tail-source-now`
    (`019e42c3-9365-7a23-88f0-663b7d44e533`).  Result: route incorporated;
    no-cut injection uses
    `RawFaceSuccOrbitActualExteriorArcSeparationRows` through
    `S2_agent_no_cut_repeated_tail_source_from_actualExteriorArcRows`, and the
    new eraser
    `rawFaceSuccOrbitActualExteriorArcSeparationRows_of_dart_edge_frontier_pairRows`
    leaves only pair-level repeated-tail arc separation as source work.
    Verification: targeted `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-local-side-halfball-route`
    (`019e42b5-2afc-75f2-a26b-df96c529d25b`).  Result: route incorporated;
    Codex-main added the pointwise frontier-edge side/closure row and named
    erasers to `InteriorEdgeNearbyExteriorPointSource`,
    `InteriorFrontierEdgeCarrierMembershipSource`, and
    `InteriorClosureLocusRelativeOpenSource`.  Verification: targeted
    `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-exterior-face-carrier-route`
    (`019e42b5-2b4a-7233-a7c4-923c1779b857`).  Result: confirmed the largest
    remaining same-`B` source row is
    `BoundaryFrontierClosedSegmentLocalExteriorAngularSector inputs B`; the
    active route records this as actual local-sector/raw-face-orbit source
    work rather than a new facade.  Verification: reflected in the active
    workboard and owner-file build passed.
    Closed completed/pruned claim:
    `S2-nocut-simple-orbit-route`
    (`019e42b5-2b9a-7912-b4e2-7f9de41feaae`).  Result: confirmed the no-cut
    route should pass through repeated-tail separation rows to
    `inputs.noCutVertex`; remaining proof work is source production for those
    repeated-tail rows, not another no-cut wrapper.  Verification: reflected in
    the active workboard and owner-file build passed.
    Closed completed/pruned claim:
    `S2-agent-side-choice-at-frontier-now`
    (`019e42ae-59ba-73d0-841c-353a8a088c51`).  Result: provided the source
    theorem shape
    `exists_edgePositiveSideBall_exterior_points_or_swap_of_inOpenSegment_frontier`;
    the proof should use frontier closure, split nearby exterior witnesses by
    signed normal coordinate, perturb any zero-normal witness inside the open
    exterior, and use `closure_union` to select one side uniformly.  No edits by
    agent.
    Closed completed/pruned claim:
    `S2-agent-side-propagation-along-edge-now`
    (`019e42ae-5a09-7a73-a6f8-9ed7409e3428`).  Result: supplied a
    Lean-ready clopen-locus theorem
    `openSegment_positiveSideBall_exterior_points_of_locus_isOpen`: if the
    positive-side exterior-point locus is relatively open in the open edge and
    nonempty at one frontier point, connectedness of the open segment propagates
    the same side to every open-edge point.  No edits by agent.
    Closed completed/pruned claim:
    `S2-agent-half-ball-api-now`
    (`019e42a1-182f-7460-8fe0-3f3c11f2ef30`).  Result: provided the
    Lean-ready local side-patch API around `edgeSideFunctional`,
    `positiveSideHalfBall`, continuity, linearity, open/convex/preconnected
    rows, and local drawing isolation references.  Codex-main used the route to
    implement the symmetric `edgeNormalCoord`/`edgeSideBall` helper layer in
    `FinitePlaneDrawing.lean`.  No edits by agent.
    Closed completed/pruned claim:
    `S2-agent-post-local-sector-route-now`
    (`019e42a1-1ebb-7671-8a35-1c4a3eb0b974`).  Result: after the local
    exterior-side row, the exact next source order is
    `InteriorEdgeLocalExteriorSideComponentSource`, then
    `InteriorEdgeNearbyExteriorPointSource`, then local-sector rows plus raw
    face-successor selected-edge coverage to prove frontier preconnectedness,
    then
    `S2_agent_input_s2_assembly_gap_reducer_frontier_nearbyTailHitActualArcRows`
    with `RawFaceSuccOrbitActualExteriorArcSeparationRows` to obtain
    `UnboundedExteriorFrontierCycleRows C inputs`.  No edits by agent.
    Closed completed/pruned claim:
    `S2-agent-component-eraser-chain-now`
    (`019e42a1-1e65-7cb2-8427-a968e52b551c`).  Result: the half-ball patch
    should feed exactly
    `interior_frontier_edge_carrier_membership_source_of_preconnected_patch`;
    from there the existing chain is
    `boundary_frontier_openSegment_relativeClosurePropagation_of_interior_edge_mem`,
    then the local-sector wrappers
    `boundary_frontier_openSegment_local_exterior_sector_of_incident_edge_angular_and_relative_closure`
    or `S2_agent_local_exterior_point_sector_source`, and finally
    `localSectorRows_of_vertex_star_isolation_local_exterior_sector` once the
    independent angular/completeness rows are available.  No edits by agent.
    Closed completed/pruned claim:
    `S2-agent-local-patch-construction-now`
    (`019e429c-904c-75b1-8081-c765b50e8fa7`).  Result: the shortest
    Lean-proofable local patch route is a same-side half-ball construction
    along an isolated open edge.  Add/prove `edgeNormalCoord`,
    `edgeSideBall`, its open/convex/preconnected/closure rows, a local
    drawing-complement side-ball containment row from the existing finite
    edge-isolation theorem, and a clopen propagation row along the connected
    open segment.  This feeds the already checked
    `interiorEdgeOpenSegmentLocalExteriorSideComponentSource_of_preconnected_patch`
    and then
    `interior_frontier_edge_carrier_membership_source_of_preconnected_patch`.
    No edits by agent; claim closed after read-only route handoff.
    Closed completed/pruned claim:
    `S2-agent-raw-package-residual-order-now`
    (`019e429c-909c-7582-956c-209da5f89a7e`).  Result: the direct residual
    order for `S2_agent_input_only_unbounded_cycle_from_raw_package` is:
    `localSectorRows`, `connectedRows`, `raw_edge_openSegment_frontier`,
    `frontier_iff_tail`, then `repeated_tail_rows`.  After the local patch row,
    the next reusable target is `S2_agent_actual_exterior_sector_source`'s input
    package, because its local-sector rows feed connectedness, raw-orbit seed
    selection, nonbacktracking, and tail coverage.  No edits.
    Closed completed/pruned claim:
    `S2-raw-orbit-B-bookkeeping-erasure`.  Owner: Codex-main.  Result: added
    then pruned a too-weak direct final-row adapter from raw period,
    tail-injectivity, and frontier-iff-tail, because it did not require the
    actual exterior edge-frontier honesty row.  Existing actual-boundary erasers
    `ActualBoundaryCycleFrontierEquivalenceRows.ofRawFaceSuccOrbit` and
    `S2_agent_actual_boundary_cycle_frontier_equivalence_of_rawFaceSuccOrbit`
    already cover the valid edge-frontier route, and must remain the live
    eraser for this branch.  Verification: targeted
    `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-agent-taskboard-claim-consistency-now`
    (`019e4297-4137-7231-8b61-10bb556abecf`).  Result: live S2 ownership is
    clear; the top active block has Codex-main integration plus two read-only
    proof-source agents.  Suggested future hygiene is to relabel old
    historical `- Claim:` entries as superseded/stale so text search does not
    confuse them with live work.  No code theorem marked done.  No edits by
    agent.
    Closed completed/pruned claim:
    `S2-agent-raw-orbit-source-now`
    (`019e4297-40d7-76f3-a8e2-f9eaafb3aad2`).  Result: the minimal checked
    input-level raw-orbit source shape is
    `S2_agent_input_only_unbounded_cycle_from_raw_package`, which chooses the
    seed through `exists_rawFaceSuccOrbit_sourceRows_of_inputs` and erases via
    `unboundedExteriorFrontierCycleRows_of_exists_rawFaceSuccOrbit_sourceRows`.
    Residual source rows remain local sectors, selected carrier cyclic
    coverage/connectedness, raw whole-edge frontier, frontier-iff-tail or tail
    coverage, and no-cut repeated-tail separation.  No edits.
    Closed completed/pruned claim:
    `S2-agent-local-exterior-side-api-now`
    (`019e4297-4087-7960-a48b-8b41ff42aeef`).  Result: shortest route is to
    prove the stronger
    `InteriorEdgeOpenSegmentLocalExteriorSideComponentSource C inputs`, then
    erase via `interiorEdgeLocalExteriorSideComponentSource_of_openSegment_component_source`.
    Existing component formalities close from a local preconnected side patch
    `S` using `IsPreconnected.subset_connectedComponentIn`; the real missing
    theorem is construction of such an exterior-side patch inside
    `(unboundedExteriorComponentRows C inputs).exterior ∩ Metric.ball z r`
    with `z` in its closure.  No edits.
    Closed completed claim:
    `S2-local-side-component-formalizer`.  Owner: Codex-main.  Result: added
    checked component-bookkeeping erasers
    `interiorEdgeOpenSegmentLocalExteriorSideComponentSource_of_preconnected_patch`
    and
    `interior_frontier_edge_carrier_membership_source_of_preconnected_patch`;
    the remaining proof-owned local geometry is exactly construction of the
    preconnected exterior-side patch `S` near each open-edge point.  Verification:
    targeted `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-agent-selected-edge-chain-source-proof`
    (`019e428e-f20c-7880-a60b-5136bf2e2ac7`).  Result:
    `UnboundedFrontierEdgeCarrierSegmentChainConnected inputs` already has
    checked reducers, especially
    `S2_agent_edge_carrier_segment_chain_source_rawFaceSuccOrbit`.  The
    minimal live source is a geometric raw face-successor orbit whose
    consecutive tail edges are exactly the selected
    `unboundedFrontierEdgeSet C inputs` up to orientation and whose orbit
    covers every selected frontier edge.  No edits.
    Closed completed/pruned claim:
    `S2-agent-local-sector-source-proof`
    (`019e428e-f25a-7eb3-a059-c48b89e84452`).  Result: shortest checked
    local-sector route is `S2_agent_actual_exterior_sector_source`, consuming
    actual boundary rows, `BoundaryVertexAngularNoBetweenRows` from geometric
    rotation, and the local exterior-sector row.  The sharper primitive route
    is
    `S2_agent_actual_exterior_sector_input_source_2_from_faceSuccRows_orientation_boundary_cycle_edge_mem_closedSegment_local_exterior_angular_sector_source`;
    its residual is actual boundary identification plus
    `BoundaryFrontierClosedSegmentLocalExteriorAngularSector inputs B`.  No
    input-only local-sector source was found before actual boundary rows.  No
    edits.
    Closed completed/pruned claim:
    `S2-agent-relative-closure-source-proof`
    (`019e428e-f1be-71f2-bf72-24147c83c9ac`).  Result: the exact local source
    row is `InteriorEdgeLocalExteriorSideComponentSource C inputs`; existing
    adapters already give `InteriorEdgeNearbyExteriorPointSource C inputs`,
    `InteriorRelativeBallClosureRow C inputs`,
    `InteriorClosureLocusRelativeOpenSource C inputs`, and
    `InteriorFrontierEdgeCarrierMembershipSource C inputs`.  The missing proof
    is local side propagation along an isolated open edge, using finite drawing
    edge isolation and half-plane/connected-component APIs.  No edits.
    Closed completed/pruned claim:
    `S2-agent-interior-nearby-exterior-source-now`
    (`019e428a-18b8-7603-acb9-d98b2a2de34d`).  Result: shortest checked route
    for nearby exterior points is
    `interiorEdgeNearbyExteriorPointSource_of_interior_frontier_edge_carrier_membership`;
    the central source row is
    `InteriorFrontierEdgeCarrierMembershipSource C inputs`, equivalently
    `InteriorRelativeBallClosureRow C inputs` through the existing iff
    theorems.  Related residual rows are
    `InteriorClosureLocusRelativeOpenSource C inputs`,
    `InteriorEdgeLocalExteriorSideSource C inputs`,
    `InteriorEdgeLocalExteriorSideComponentSource C inputs`, and
    `InteriorEdgeOpenSegmentLocalExteriorSideComponentSource C inputs`.  No
    input-only producer from `FinitePlanarOuterComponentInputs C` was found.
    No edits.
    Closed completed/pruned claim:
    `S2-agent-frontier-edge-cover-source-now`
    (`019e428a-186b-7670-a6a5-974b9fee61c2`).  Result: shortest checked
    edge-cover route is
    `S2_agent_frontier_edge_cover_source_of_nearby_edge_point_exterior_points`
    feeding
    `unboundedFrontierCarrierAdjClosedTopologyRows_of_frontier_preconnected_and_frontier_edge_cover`.
    Its source residuals are
    `forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a` and
    `InteriorEdgeNearbyExteriorPointSource C inputs`; frontier
    preconnectedness is a separate argument.  No edits.
    Closed completed/pruned claim:
    `S2-agent-frontier-preconnected-source-now`
    (`019e428a-1822-7370-b840-333c760adb61`).  Result: shortest checked route
    is `unboundedExterior_frontier_preconnected_of_sourceRows` from
    `UnboundedExteriorFrontierPreconnectedSourceRows inputs`; the non-boundary
    source route is
    `S2_agent_frontier_preconnected_source_route_of_nearby_edge_point_exterior_points`,
    with residuals
    `UnboundedFrontierEdgeCarrierSegmentChainConnected inputs`,
    `forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a`, and
    `InteriorEdgeNearbyExteriorPointSource C inputs`.  No input-only producer
    for those residuals was found.  No edits.
    Closed completed/pruned claim:
    `S2-worker-raw-orbit-explicit-boundary-constructor`
    (`019e4283-ed65-7d10-bc0b-4bb188d19e3a`).  Result: added
    `exists_unitDistanceCycleBoundary_of_rawFaceSuccOrbit_tail_injective` and
    private raw-orbit boundary construction helpers in
    `Swanepoel/ExteriorComponentTopology.lean`.  This closes the direct
    raw-orbit-to-cycle packaging handoff; remaining live work is input-only
    production of the exterior frontier/source rows consumed by that route.
    Verification reported by worker: targeted
    `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-agent-exterior-frontier-source-primitives`
    (`019e4285-3d60-7260-bc38-7b1af7a843a1`).  Result: shortest checked S2
    eraser remains `ActualBoundaryCycleFrontierEquivalenceRows C inputs` to
    `unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows`
    to the finite planar theorem.  Frontier preconnectedness, edge cover, and
    carrier connectedness have checked reducers, but do not construct the
    actual boundary cycle.  No edits.
    Closed completed/pruned claim:
    `S2-agent-no-cut-repeat-to-simple-cycle`
    (`019e4285-3db0-7cd0-a08d-8c585e0b7d5f`).  Result: no-cut erasers are
    already present; `rawFaceSuccOrbit_tail_injective_of_noCutVertex` consumes
    repeated-tail separation rows and `inputs.noCutVertex`.  The missing source
    is geometric/topological production of those separation rows for a
    repeated selected raw tail, not another no-cut theorem.  No edits.
    Closed completed/pruned claim:
    `S2-agent-mathlib-exterior-component-api`
    (`019e4285-3e0f-77e0-942e-f1f3ab2c64ff`).  Result: useful Mathlib APIs are
    standard `frontier`, `connectedComponentIn`, preconnected/clopen, and
    path-component tools; Mathlib does not provide the finite straight-line
    outer-face/Jordan theorem.  The smallest useful local source remains an
    actual boundary cycle with frontier equivalence and sector or edge rows.
    No edits.
    Closed completed/pruned claim:
    `S2-agent-faceDartOrbitCarrier-source-minimal`
    (`019e4281-05c0-7372-9173-a7429bf84695`).  Result: shortest carrier
    constructor is
    `faceDartOrbitExteriorCarrierRows_of_boundaryVertexExteriorSectorRows`,
    requiring an actual boundary `B`, frontier-vertex equivalence, and
    `forall k, BoundaryVertexExteriorSectorRowsAt inputs B k`.  No theorem
    sources this from only `FinitePlanarOuterComponentInputs C`; the true
    residual is the actual `B` plus sector-row source.  No edits.
    Closed completed/pruned claim:
    `S2-agent-raw-start-on-boundary-source`
    (`019e4281-0615-7cf3-926b-dcf1c55529f2`).  Result: raw orbit selection from
    `UnboundedExteriorFrontierSeed` gives `edgeRows`, `htail`, `hhead`, and a
    raw orbit but not start identification.  Existing reducers need either
    forward `edgeRows_boundary_succ` or first-edge `hseed`; sector rows help
    after start-on-boundary is known but do not source it.  No edits.
    Closed completed/pruned claim:
    `S2-agent-carrier-connectedness-source-now`
    (`019e4281-0674-7f82-8856-f0864da99436`).  Result: shortest non-circular
    connectedness route for raw-tail hit is
    `S2_agent_raw_tail_hit_from_exterior_frontier_topologyRows`, using
    `UnboundedFrontierCarrierAdjClosedTopologySourceRows inputs`.  Current
    checked producer still needs exterior-frontier preconnectedness and a
    frontier-edge cover/local-constancy source, not just
    `FinitePlanarOuterComponentInputs C`.  No edits.
    Closed completed/pruned claim:
    `S2-agent-sectorRows-source-for-faceOrbit`
    (`019e4281-06d0-73b0-ac17-360dcbc6865c`).  Result: sector rows are sourced
    non-circularly by
    `boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_local_exterior_sector`
    or packaged as
    `(S2_agent_actual_exterior_sector_input_source_2 ...).sectorRows`.
    Residuals are actual boundary open-segment frontier, strict pred/succ
    angle, no-between, and local point-sector rows.  No edits.
    Closed completed claim:
    `S2-workboard-role-discipline`.  Result: tightened the active-claim schema
    so every live workboard item has one specific role, one writable scope, one
    exact theorem/row handoff, and an explicit clearance rule before it can be
    moved out of the live block.  Verification: TASK-only edit; no Lean build
    needed.
    Closed completed/pruned claim:
    `S2-agent-B-package-source-map`
    (`019e427d-2801-7c60-a6c3-1e654105ab85`).  Result: the A-route package is
    exactly `ActualBoundaryCycleFrontierEquivalenceRows.BoundaryCycleEdgeMemSource`.
    The shortest producer is
    `ActualBoundaryCycleFrontierEquivalenceRows.boundaryCycleEdgeMemSource`
    from `ActualBoundaryCycleFrontierEquivalenceRows C inputs`; no theorem
    closes it from only `FinitePlanarOuterComponentInputs C`.  No edits.
    Closed completed/pruned claim:
    `S2-agent-frontier-iff-tail-source-chain`
    (`019e427d-2852-7233-81e2-2403be7939bd`).  Result:
    `rawFaceSuccOrbit_frontier_iff_tail_of_frontier_vertex_tail_coverage`
    is the shortest route.  Residuals are consecutive raw edge
    open-segment-frontier plus positive raw-tail coverage; tail-hit reduces
    that to dart-edge frontier, carrier connectedness/root/topology rows,
    local-sector rows, and raw predecessor/successor nonbacktracking.  No
    edits.
    Closed completed/pruned claim:
    `S2-agent-raw-orbit-to-boundary-cycle-data`
    (`019e427d-289e-7b82-ae49-7531c137dd14`).  Result: raw-only constructors can
    manufacture a final boundary cycle, including edge membership via
    `S2_agent_raw_cyclegraph_boundary_source_route`, but they do not export
    same-`B` `B.length = O.period` and tail-equality rows.  The equality
    preserving path is through `FaceDartOrbitExteriorCarrierRows` plus raw
    start identification.  No edits.
    Closed completed/pruned claim:
    `S2-agent-boundary-edge-membership-source`
    (`019e427e-3abf-7b52-8d35-42a1dc810e1e`).  Result: same-`B` edge membership
    is exactly the `.2` projection of `S2_agent_explicit_B_raw_boundary_route`.
    Raw dart-edge frontier converts via
    `rawFaceSuccOrbit_edge_openSegment_frontier_of_dart_edge_openSegment_frontier`;
    sector-row producers exist, with residual same-boundary dart tracing /
    `raw_start_on_boundary`.  No edits.
    Closed completed/pruned claim:
    `S2-raw-boundary-direct-W32-consumer`.  Result: added
    `finitePlanarStraightLineOuterComponentTheorem_of_rawFaceSuccOrbitBoundaryRows`
    and
    `minimalFailureExactActualTopologyFieldsTarget_of_rawFaceSuccOrbitBoundaryRows`,
    exposing the direct same-`B` raw face-successor handoff at both finite
    planar and W32 surfaces.  Verification: targeted
    `lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology` and
    targeted `FaceBoundaryTopologySourceW32.lean` check passed.
    Closed completed/pruned claim:
    `S2-agent-raw-orbit-to-concrete-boundary-check`
    (`019e427d-bd3b-79d1-8d35-af930b9025bf`).  Result: no existing theorem
    constructs a concrete `UnitDistanceCycleBoundary B` from raw orbit plus
    period/tail-injectivity while also returning `hperiod` and `tail_eq`.
    Existing raw finalizers `unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit`
    and `exists_unboundedExteriorFrontierCycleBoundary_of_rawFaceSuccOrbit`
    hide the same-cycle period/tail rows.  Same-`B` period/tail rows are
    currently derivable only from `FaceDartOrbitExteriorCarrierRows`.
    Closed completed/pruned claim:
    `S2-agent-faceSucc-orientation-same-B-source`
    (`019e4272-c039-7c83-ac1c-84f754a0a105`).  Result: same-`B`
    `UnitDistanceCycleFaceSuccRows C R B` are derivable from a raw
    face-successor orbit, period equality, and tail identification; the
    boundary-orientation / `hangle` row remains the separate honest residual.
    Integrated helper:
    `rawFaceSuccOrbit_unitDistanceCycleFaceSuccRows_of_tail_eq`.  Verification:
    targeted `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-agent-boundary-orientation-source-map`
    (`019e4279-ed9e-77e3-9f64-2de7ed351288`).  Result: shortest same-`B`
    boundary-orientation source is the `angle` field carried by
    `BoundaryVertexExteriorSectorRowsAt inputs B k`; the raw orbit/face-successor
    route supplies `UnitDistanceCycleFaceSuccRows` only and does not produce the
    strict pred/succ geometric angle.  If sector rows are absent, the exact
    source row is the strict `graphDartArg` predecessor/successor inequality
    for every boundary vertex.  No edits.
    Closed completed/pruned claim:
    `S2-agent-frontier-iff-boundary-source`
    (`019e4277-f1e4-7a33-a855-d15123461d99`).  Result: shortest explicit-`B`
    frontier vertex equivalence is
    `frontier_iff_boundaryCycle_vertex_of_rawFaceSuccOrbit_tail`; the residual
    is `frontier_iff_tail`, reducible through
    `rawFaceSuccOrbit_frontier_iff_tail_of_frontier_vertex_tail_coverage` to
    raw-tail positive coverage for exterior-frontier vertices.  No edits.
    Closed completed/pruned claim:
    `S2-agent-input-only-route-choice`
    (`019e4277-f193-7a11-9ea1-7edb3523b9e0`).  Result: recommended the
    A-route: construct an actual exterior boundary cycle package with
    same-`B` frontier-vertex iff and consecutive boundary edge membership, then
    erase through `ActualBoundaryCycleFrontierEquivalenceRows` /
    `unboundedExteriorFrontierCycleRowsOfBoundary`.  Avoid heavier per-vertex
    sector or raw callback routes unless the A-route source rows fail.  No
    edits.
    Closed completed/pruned claim:
    `S2-same-B-raw-final-reducer`.  Result: added
    `unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbitBoundaryRows`,
    the direct same-`B` final reducer from `hperiod`, `tail_eq`, and
    `frontier_iff_tail` to `UnboundedExteriorFrontierCycleRows C inputs`.
    Verification: targeted `ExteriorComponentTopology.lean` check passed.
    Closed completed/pruned claim:
    `S2-agent-endpoint-incident-only-route-check`
    (`019e427a-11cd-7291-96e9-fde29375ba3c`).  Result: no existing theorem
    derives `BoundaryFrontierEndpointIncidentOnlyPredSucc inputs B`.
    `BoundaryCycleIncidentFrontierEdgeCompleteness inputs B` only covers
    selected `unboundedFrontierEdgeSet` edges.  Missing bridge, if pursued:
    frontier endpoint plus canonical adjacency implies the ordered edge is in
    `unboundedFrontierEdgeSet` up to symmetry; otherwise the endpoint row
    remains its own honest source row.
    Closed completed/pruned claim:
    `S2-agent-actual-boundary-source-assembly-check`
    (`019e427a-248a-7950-8a48-2961d89f8ab3`).  Result: shortest same-`B`
    final path is `frontier_iff_boundaryCycle_vertex_of_rawFaceSuccOrbit_tail`
    followed by `unboundedExteriorFrontierCycleRowsOfBoundary`; it needs only
    `hperiod`, `tail_eq`, and `frontier_iff_tail` for the concrete `B`.
    `edge_openSegment_frontier` is needed only when routing through
    `ActualBoundaryCycleFrontierEquivalenceRows` or edge-membership rows.
    Closed pruned claim:
    `S2-agent-endpoint-incident-only-source-map`
    (`019e4279-ed51-7d90-858c-169b24064dda`).  Result: pruned before completion
    because the overlapping live claim
    `S2-agent-endpoint-incident-only-route-check` is already owned by another
    active worker.
    Closed completed/pruned claim:
    `S2-actual-boundary-row-direct-consumer`.  Result: added direct erasers
    `finitePlanarStraightLineOuterComponentTheorem_of_actualBoundaryCycleFrontierEquivalenceRows`
    and
    `minimalFailureExactActualTopologyFieldsTarget_of_actualBoundaryCycleFrontierEquivalenceRows`,
    so the shortest current source theorem can hand off
    `ActualBoundaryCycleFrontierEquivalenceRows C inputs` directly to the S2
    finite-planar and W32 targets.  Verification: targeted
    `lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology` and
    targeted `FaceBoundaryTopologySourceW32.lean` check passed.
    Closed completed/pruned claim:
    `S2-agent-local-exterior-point-sector-source`
    (`019e4272-0a31-7522-a6e2-8eed6d6c8169`).  Result: added
    `boundary_frontier_local_exterior_sector_of_openSegment_pointSector_endpoint_incident_only`
    and `S2_agent_local_exterior_point_sector_source`, reducing the W3-carried
    point-sector obligation to the honest open-segment point-sector row plus
    endpoint incident-only.  Verification: targeted
    `ExteriorComponentTopology.lean` build passed with only pre-existing
    linter warnings.
    Closed completed/pruned claim:
    `S2-agent-explicit-B-raw-boundary-route`
    (`019e4272-bfe3-7971-a1b3-d46e5b8047ba`).  Result: added
    `S2_agent_explicit_B_raw_boundary_route`, the same-`B` raw face-successor
    handoff through `ActualBoundaryCycleFrontierEquivalenceRows.ofRawFaceSuccOrbitBoundaryRows`,
    producing the explicit boundary cycle's frontier-vertex iff and
    boundary-edge membership rows.  Verification: targeted
    `ExteriorComponentTopology.lean` build passed with only pre-existing
    linter warnings.
    Closed completed/pruned claim:
    `S2-agent-current-source-row-gap-check`
    (`019e4274-d408-7490-9bbf-94fdf30509cc`).  Result: no existing
    input-only source theorem was found.  Shortest erasers are
    `unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows`
    from `ActualBoundaryCycleFrontierEquivalenceRows C inputs`,
    `unboundedExteriorFrontierCycleRows_of_boundaryVertexExteriorSectorRows`
    from a same `B`, frontier-iff, and
    `forall k, BoundaryVertexExteriorSectorRowsAt inputs B k`, and the raw
    callback path
    `unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit_inputRows`.
    Remaining source work must construct one of those rows from
    `FinitePlanarOuterComponentInputs C`.
    Closed completed/pruned claim:
    `S2-agent-workboard-claim-consistency-check`
    (`019e4274-e26f-7332-85a3-59eef4870fd2`).  Result: applied the
    workboard wording fixes: only `Claim:` entries are live claims, owner
    slots are not live claim entries, live delegated claims have explicit
    freshness/pruning text, and the read-only face-successor map uses a
    source-map handoff gate rather than a Lean build gate.
    Closed completed/pruned claim:
    `S2-agent-same-B-final-assembly-audit`
    (`019e426f-a7a6-78e0-accc-24ec6c36bbce`).  Result: shortest checked eraser
    to `UnboundedExteriorFrontierCycleRows C inputs` is
    `unboundedExteriorFrontierCycleRowsOfBoundary inputs B
    frontier_iff_cycle_vertex`; W32 then consumes the row family through
    `minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows`.
    Treat this as an eraser only; source work must still construct the actual
    exterior face-orbit boundary cycle, not an arbitrary chord cycle.
    Closed completed/pruned claim:
    `S2-agent-local-two-germ-proof-source`
    (`019e426f-a89d-7473-b9de-e789a726a463`).  Result:
    `exists_ball_forall_unboundedExterior_frontier_mem_vertexIncidentGermW3`
    is already proved; the smallest local two-germ source is the
    `third_germ_between` / `bad_germ_between` family paired with the same
    cycle's angular `no_between` row, then erased through
    `exists_local_frontier_germ_two_of_vertex_star_isolation_and_angular_no_between`
    and `boundaryVertexExteriorSectorRowsAt_of_vertex_star_isolation_angular_order`.
    Closed completed/pruned claim:
    `S2-agent-raw-orbit-premise-export-map`
    (`019e426f-a850-74f1-9ae0-32c381711543`).  Result: the raw cyclegraph route
    manufactures an existential boundary cycle `B`; it supplies vertex
    frontier iff and `cycle_edge_mem` for that manufactured `B`, but not
    `UnitDistanceCycleFaceSuccRows` or boundary orientation for the same `B`.
    Prefer the explicit-`B` `ofRawFaceSuccOrbitBoundaryRows` route for final
    same-cycle assembly.
    Closed completed/pruned claim:
    `S2-local-sector-consumer-shape`.  Result: added direct primitive
    local-sector consumers
    `finitePlanarStraightLineOuterComponentTheorem_of_boundaryVertexExteriorSectorRows`
    and
    `minimalFailureExactActualTopologyFieldsTarget_of_boundaryVertexExteriorSectorRows`.
    Verification: targeted `ExteriorComponentTopology.lean` module build and
    targeted `FaceBoundaryTopologySourceW32.lean` build passed.
    Closed completed/pruned claim:
    `S2-agent-actual-sector-minimal-premises`
    (`019e426f-a7f3-7c83-a357-2b1f187fd5e5`).  Result: the minimal live
    constructor is `S2_agent_actual_exterior_sector_input_source_2`.  Its
    strongest remaining local/topological residual is the noncenter W3
    point-sector row `local_exterior_sector`; the closed-segment endpoint
    machinery is optional and not on the shortest route.
    Closed completed/pruned claim:
    `S2-agent-boundary-incident-no-chord-source`
    (`019e4269-e75d-7050-b620-8c14d66ff661`).  Result: added
    `S2_agent_boundary_incident_no_chord_source`, reducing incident
    completeness to `BoundaryFrontierIncidentEdgeExteriorAngularSector inputs B`
    plus the unit-distance no-between row through the existing angular reducer.
    Verification: targeted `ExteriorComponentTopology.lean` build passed with
    only pre-existing `unnecessarySimpa` warnings.
    Closed completed/pruned claim:
    `S2-closed-segment-endpoint-sector-source`.  Result: repaired the route
    away from the overstrong endpoint branch by adding complete-boundary
    erasers
    `exists_boundaryCycle_complete_of_boundaryVertexExteriorSectorRows`,
    `exists_boundaryCycle_complete_of_actualExteriorSectors`, and
    `unboundedExteriorFrontierCycleRows_of_actualExteriorSectors`.  The live
    source now uses primitive local sector rows rather than the closed W3
    endpoint residual.  Verification: targeted
    `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-agent-open-germ-consumer-repair-map`
    (`019e426b-054f-7351-8db5-3a03bcb79508`).  Result: confirmed that the
    S2 route can bypass `ActualExteriorSectorInputSourceRows` and consume
    `BoundaryVertexExteriorSectorRowsAt` /
    `boundaryCycleIncidentFrontierEdgeCompleteness_of_actualExteriorSectors`
    directly.
    Closed completed/pruned claim:
    `S2-agent-local-two-germ-source-map`
    (`019e426b-05a5-7742-819a-19632f0b4e84`).  Result: identified
    `exists_local_frontier_germ_two_of_vertex_star_isolation_local_exterior_sector`
    and `local_frontier_germ_two_of_boundary_point_sector_no_between` as the
    existing reducers; the residual is the actual local exterior point-sector
    row plus geometric no-between, not raw-orbit work.
    Closed completed/pruned claim:
    `S2-agent-no-chord-from-local-topology-audit`
    (`019e4269-e7b5-73c3-a52d-b72896607282`).  Result: shortest route to
    `BoundaryCycleIncidentFrontierEdgeCompleteness inputs B` is local
    two-germ rows, not a new open-segment/frontier contradiction.  Use
    `BoundaryVertexExteriorSectorRowsAt.boundaryCycleIncidentFrontierEdgeCompleteness`
    when `BoundaryVertexExteriorSectorRowsAt inputs B k` is available, or the
    bundled
    `boundaryCycleIncidentFrontierEdgeCompleteness_of_actualExteriorSectorInputSourceRows`.
    Lower source path is through
    `exists_ball_forall_unboundedExterior_frontier_mem_vertexIncidentGermW3`,
    `exists_local_frontier_germ_two_of_vertex_star_isolation_and_angular_no_between`,
    and `boundaryVertexExteriorSectorRowsAt_of_vertex_star_isolation_angular_order`.
    Closed completed/pruned claim:
    `S2-agent-raw-orbit-cycle-boundary-constructor`
    (`019e4262-4b9b-7fa1-98d3-7ed8fbc16cfa`).  Result: added
    `exists_unitDistanceCycleBoundary_covering_spanning_cycle_hom_edge_lifts`,
    `boundaryCycleEdgeMemSource_of_connected_two_regular_frontier_graph_edge_mem`,
    and `S2_agent_raw_cyclegraph_boundary_source_route`, producing
    `BoundaryCycleEdgeMemSource C inputs` from a raw face-successor orbit with
    period, tail-injectivity, frontier-tail equivalence, and raw open-segment
    frontier rows.
    Closed completed/pruned claim:
    `S2-agent-complete-boundary-package-source-shape`
    (`019e4267-c17b-72b3-be6a-86f280f32732`).  Result: confirmed the minimal
    W32 source is a same-`B` existential package:
    frontier-iff-cycle vertices, consecutive sides in
    `unboundedFrontierEdgeSet`, and
    `BoundaryCycleIncidentFrontierEdgeCompleteness inputs B`; the existing W32
    consumer already erases that package.
    Closed completed/pruned claim:
    `S2-agent-incident-completeness-source-map`
    (`019e4267-438f-73a2-91fb-1f2de33f6b0d`).  Result: the shortest current
    incident-completeness route is through
    `ActualExteriorSectorInputSourceRows inputs B`; with actual boundary rows,
    it needs the closed-segment local exterior angular-sector row and then
    erases by
    `boundaryCycleIncidentFrontierEdgeCompleteness_of_actualExteriorSectorInputSourceRows`.
    Closed completed/pruned claim:
    `S2-agent-closed-segment-endpoint-source-map`
    (`019e4267-43dc-7b32-a791-dbb30657f72e`).  Result: the existing closed-germ
    consumer still needs the endpoint branch; the minimal missing row is
    `BoundaryFrontierClosedSegmentEndpointExteriorAngularSector inputs B`, or
    a direct proof of
    `BoundaryFrontierClosedSegmentLocalExteriorAngularSector inputs B`.
    Closed completed/pruned claim:
    `S2-actual-sector-completeness-consumer`.  Result: added
    `boundaryCycleIncidentFrontierEdgeCompleteness_of_actualExteriorSectorInputSourceRows`,
    `exists_boundaryCycle_complete_of_boundaryEdgeMem_actualExteriorSectorInputSourceRows`,
    and
    `unboundedExteriorFrontierCycleRows_of_boundaryEdgeMem_actualExteriorSectorInputSourceRows`.
    Verification: targeted `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-frontier-preconnected-source`.  Result: added compact source rows and
    reducers
    `UnboundedExteriorFrontierPreconnectedSourceRows`,
    `unboundedExterior_frontier_preconnected_of_sourceRows`,
    `unboundedFrontierEdgeCarrierSegmentChainConnected_of_boundaryCycle_complete`,
    `unboundedExteriorFrontierPreconnectedSourceRows_of_boundaryCycle_complete`,
    and `unboundedExterior_frontier_preconnected_of_boundaryCycle_complete`.
    Verification: targeted `ExteriorComponentTopology.lean` build passed.
    Closed completed/pruned claim:
    `S2-boundary-complete-consumer-route`.  Result: added
    `finitePlanarStraightLineOuterComponentTheorem_of_exists_boundaryCycle_complete`
    and
    `minimalFailureExactActualTopologyFieldsTarget_of_exists_boundaryCycle_complete`.
    The remaining proof-owning source theorem only has to produce `B`,
    frontier-iff-cycle vertices, selected boundary sides, and
    `BoundaryCycleIncidentFrontierEdgeCompleteness`.  Verification:
    `lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology` and
    targeted W32 Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-incident-completeness-from-boundary-edge-memory`
    (`019e4267-c125-7880-acf6-2f0539dd7d04`).  Result: confirmed edge memory
    plus frontier-vertex equivalence does not prove
    `BoundaryCycleIncidentFrontierEdgeCompleteness`; the smallest honest source
    is a no-chord/no-between row, consumed by
    `boundaryCycleIncidentFrontierEdgeCompleteness_of_badIncidentEdge_impossible_of_boundary_frontier_geometry`
    or the angular no-between reducer.
    Closed completed/pruned claim:
    `S2-agent-simplegraph-walk-cycle-api`
    (`019e4262-4bf4-7dc3-ab41-2f525eb24c13`).  Result: identified
    `ListChainWalk.ofChain` as the fastest local walk builder for a cyclic
    successor-adjacent injective sequence; the remaining final vertex-equality
    proof uses `support_cons`, `support_copy`, `ListChainWalk.ofChain_support`,
    `getVert_eq_support_getElem`, `List.getElem_ofFn`, and cyclic index
    arithmetic.
    Closed completed/pruned claim:
    `S2-agent-raw-cyclegraph-boundary-source-route`
    (`019e4263-aaf1-74f0-aecf-1986cdcad93a`).  Result: confirmed the raw
    cyclegraph route to `BoundaryCycleEdgeMemSource C inputs` is viable once
    the generic edge-memory helper exists; the raw `edge_mem` callback splits
    `SimpleGraph.cycleGraph` adjacency into successor/predecessor cases and
    uses `rawFaceSuccOrbit_edge_mem_unboundedFrontierEdgeSet_or_symm`.
    Closed completed/pruned claim:
    `S2-agent-spanning-cycle-edge-memory-audit`
    (`019e4263-aaa5-7f40-8963-c7c9289ad013`).  Result: confirmed
    `exists_unitDistanceCycleBoundary_covering_spanning_cycle_hom` can be
    strengthened locally because its witness is `w.map phi`; each boundary side
    has a preimage adjacency from either `w.getVert k.val -> w.getVert
    (k.val + 1)` or the closing step to `w.getVert 0`.  Handoff sent to
    `S2-agent-raw-orbit-cycle-boundary-constructor`.
    Closed completed/pruned claim:
    `S2-agent-boundary-rows-to-edge-chain-map`
    (`019e425b-5feb-75a2-8598-b2209ecf9c98`).  Result:
    actual boundary rows or boundary-cycle edge membership alone do not prove
    `UnboundedFrontierEdgeCarrierSegmentChainConnected inputs`; the exact
    additional row is `BoundaryCycleIncidentFrontierEdgeCompleteness inputs B`,
    ruling out selected frontier chords and attaching every selected edge to
    the boundary-cycle carrier chain.
    Closed completed/pruned claim:
    `S2-agent-frontier-edge-cover-map`
    (`019e425b-5f9f-74c1-a06a-e5115612f3ef`).  Result: the cover row already
    follows from
    `S2_agent_frontier_edge_cover_source_of_nearby_edge_point_exterior_points`;
    residual inputs are local sector rows at selected frontier vertices and
    `InteriorEdgeNearbyExteriorPointSource C inputs`.
    Closed completed/pruned claim:
    `S2-agent-raw-orbit-boundary-edge-mem-source`
    (`019e425e-1e6b-71e0-9b5f-b5c207732206`).  Result: added
    `S2_agent_raw_orbit_boundary_edge_mem_source`,
    `S2_agent_raw_orbit_boundary_edge_mem_source_of_edge_frontier`, and
    `S2_agent_raw_orbit_boundary_edge_mem_source_of_dart_edge_frontier`,
    transporting actual consecutive raw-orbit `unboundedFrontierEdgeSet`
    membership to `BoundaryCycleEdgeMemSource C inputs` without using the
    downstream cycle-row projection.
    Closed completed/pruned claim:
    `S2-agent-unit-cycle-from-raw-orbit-audit`
    (`019e425e-1eb1-7ae1-9d52-46420317f4cb`).  Result: found no existing direct
    constructor from a raw face-successor orbit to
    `UnitDistanceCycleBoundary C` preserving raw darts; the missing upstream
    source is a constructor supplying `B`, `B.length = O.period`, and raw-tail
    equality, ideally exact `UnitDistanceDart.ofBoundary` equality.
    Closed completed/pruned claim:
    `S2-agent-orientation-seed-consumer-cleanup`
    (`019e425b-8c2a-7d83-85b9-f258df59f2e8`).  Result: rerouted
    `raw_start_on_boundary_of_actualBoundaryCycleFrontierEquivalenceRows_reverseTailOpenSegmentExteriorSector`
    and
    `exists_geometricRawFaceSuccOrbitBoundarySeed_of_unboundedExteriorFrontierSeed_actualBoundaryRows_reverseTailOpenSegmentExteriorSector`
    through the new boundary-oriented actual-rows theorem; the reverse-tail row
    now only preserves the older forward-start compatibility surface.
    Closed completed/pruned claim:
    `S2-agent-orientation-selecting-raw-seed`
    (`019e4253-a9b4-7a82-a7bd-b48dd0e44b68`).  Result: added
    `exists_boundary_oriented_raw_start_of_actualBoundaryCycleFrontierEquivalenceRows`
    and updated
    `exists_geometricRawFaceSuccOrbitBoundarySeed_of_unboundedExteriorFrontierSeed_actualBoundaryRows`
    to choose the actual boundary-oriented dart instead of relying on the false
    reverse-orientation exclusion route.
    Closed completed/pruned claim:
    `S2-agent-interior-edge-local-component-side`
    (`019e4256-319b-7a50-b2d2-b01d8b88c0c6`).  Result: added
    `InteriorEdgeOpenSegmentLocalExteriorSideComponentSource` and
    `interiorEdgeLocalExteriorSideComponentSource_of_openSegment_component_source`,
    reducing `InteriorEdgeLocalExteriorSideComponentSource C inputs` to an
    all-scale open-segment local component-selection source.
    Closed completed/pruned claim:
    `S2-agent-actual-boundary-edge-mem-source`
    (`019e4256-31f0-7ad1-abce-423113854fa5`).  Result: added
    `BoundaryCycleEdgeMemSource`, reduced it from
    `ActualBoundaryCycleFrontierEquivalenceRows`, and added S2-facing wrappers
    from actual rows, face-dart carrier rows, raw-orbit boundary rows, raw-start
    rows, and seed-edge orientation rows.
    Closed completed/pruned claim:
    `S2-agent-actual-boundary-source-minimal-core`
    (`019e425b-8c88-7e12-894c-a7dbd509d065`).  Result: confirmed the exact
    remaining input-only theorem is the family producing
    `BoundaryCycleEdgeMemSource C inputs`, i.e. a genuine
    `UnitDistanceCycleBoundary` whose vertices are exactly the unbounded
    exterior-frontier graph vertices and whose consecutive sides lie in
    `unboundedFrontierEdgeSet C inputs` up to orientation.
    Closed completed/pruned claim:
    `S2-agent-frontier-preconnected-api`
    (`019e4256-d704-75c3-96fd-92420b2f8365`).  Result: confirmed no input-only
    theorem currently proves the frontier preconnectedness target; the best
    existing local route is
    `S2_agent_frontier_preconnected_source_route`, reducing the target to
    `UnboundedFrontierEdgeCarrierSegmentChainConnected inputs` plus the
    `frontier_edge_cover` row.
    Closed completed/pruned claim:
    `S2-agent-frontier-preconnected-mathlib`
    (`019e4256-d75a-7493-af64-76a436fb86ec`).  Result: no direct mathlib
    theorem was found for preconnectedness of the frontier of an unbounded
    complement component; the live route remains project-local via frontier
    edge cover plus carrier preconnectedness or raw-face/local-sector rows.
    Closed completed/pruned claim:
    `S2-agent-orientation-seed-signature-audit`
    (`019e4253-aa01-73c1-8d6c-a66208569d37`).  Result: confirmed
    `raw_start_on_boundary_of_actualBoundaryCycleFrontierEquivalenceRows`
    should be replaced by an existential boundary-oriented raw-start theorem
    using `edgeLocalRows_boundary_succ_or_reverse_of_actualBoundaryCycleFrontierEquivalenceRows`;
    canonical reverse orientation is not impossible, it only means the stored
    edge orientation is opposite the actual boundary dart.
    Closed completed/pruned claim:
    `S2-agent-source-shape-refresh`
    (`019e4251-1d6b-7722-aa8e-04eae8d273ab`).  Result: confirmed the shortest
    source theorem is the actual boundary edge-membership source
    `forall C inputs, Exists B, frontier iff B.vertex /\ consecutive sides in
    unboundedFrontierEdgeSet`, consumed by
    `ActualBoundaryCycleFrontierEquivalenceRows.ofBoundaryCycleEdgeMemSource`
    and
    `unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleEdgeMem_source`.
    Closed completed/pruned claim:
    `S2-agent-local-topology-next-lemma`
    (`019e4251-1e0b-7023-a934-38ffc38a7514`).  Result: identified the
    non-overlapping next reducer
    `unboundedExterior_frontier_point_vertex_or_ordered_edgeInterior`, a
    pointwise classification of unbounded exterior frontier points as graph
    vertices or interiors of ordered canonical edges.
    Closed completed/pruned claim:
    `S2-agent-owner-file-api-refresh`
    (`019e4251-1dba-70c2-8463-120bc3dcab40`).  Result: confirmed compact
    fallback reducers
    `unboundedExteriorFrontierCycleRows_of_carrierRows` and
    `finitePlanarStraightLineOuterComponentTheorem_of_exteriorFrontierCarrierRows`;
    the two-row handoff is cyclic coverage plus local-sector rows, while raw
    face-successor callbacks touch active delegated tasks.
    Closed completed/pruned claim:
    `S2-agent-workboard-hygiene-refresh`
    (`019e4251-1e63-7df0-b5a6-8d745c63c11a`).  Result: added the active-block
    intake rule for new S2 agents and marked the stale duplicate Codex-main
    claim as superseded by the refreshed active claim.
    Closed completed/pruned claim:
    `S2-agent-interior-edge-local-exterior-side`
    (`019e4250-f7aa-77e3-b715-b41323dc4221`).  Result: added
    `InteriorEdgeLocalExteriorSideComponentSource`,
    `interiorEdgeLocalExteriorSideSource_of_component_source`, and
    `S2_agent_interior_edge_nearby_exterior_point_source_of_component_source`,
    reducing the local edge-side row to a local connected-component side
    accumulation source.
    Closed completed/pruned claim:
    `S2-agent-open-segment-relative-closure-propagation`
    (`019e424c-75cc-7c82-a681-5e435a0250e0`).  Result: added bridges proving
    `BoundaryFrontierOpenSegmentRelativeClosurePropagation inputs B` from
    `InteriorFrontierEdgeCarrierMembershipSource`, `InteriorRelativeBallClosureRow`,
    `InteriorEdgeNearbyExteriorPointSource`, and the sharper
    `InteriorEdgeLocalExteriorSideSource`.
    Closed completed/pruned claim:
    `S2-agent-reverse-tail-openSegment-sector`
    (`019e424a-9d55-7790-94a5-6ef57bcb66f6`).  Result: added
    `BoundaryReverseTailOpenSegmentNoFrontier`,
    `boundaryReverseTailOpenSegment_exteriorSector_iff_noFrontier`,
    `edgeLocalRows_boundaryReverseExcluded_of_boundaryReverseTailOpenSegmentNoFrontier`,
    `not_boundaryReverseTailOpenSegmentNoFrontier_of_cycle_edge_openSegment_frontier`,
    and
    `not_boundaryReverseTailOpenSegmentExteriorSector_of_cycle_edge_openSegment_frontier`.
    This showed the reverse-tail sector route is incompatible with actual
    boundary-cycle open-segment frontier rows; future reverse-orientation work
    must use a different honest source.
    Closed completed/pruned claim:
    `S2-agent-incident-edge-exterior-angular-sector`
    (`019e424d-04af-7910-b4be-9e183b2b0f21`).  Result: added
    `boundary_frontier_incident_edge_exterior_angular_sector_of_boundaryCycleIncidentFrontierEdgeCompleteness`,
    `boundary_frontier_incident_edge_exterior_angular_sector_iff_boundaryCycleIncidentFrontierEdgeCompleteness_of_boundaryVertexAngularNoBetweenRows`,
    `boundary_frontier_incident_edge_exterior_angular_sector_of_boundaryVertexExteriorSectorRows`,
    and
    `boundary_frontier_openSegment_local_exterior_sector_of_boundaryCycleIncidentFrontierEdgeCompleteness_and_relative_closure`,
    reducing the incident-edge angular row to actual boundary incident
    completeness when that row is available.
    Closed completed/pruned claim:
    `S2-agent-interior-nearby-exterior-points`
    (`019e4247-f4d3-7a73-87b7-68efc53ad335`).  Result: added
    `InteriorEdgeLocalExteriorSideSource`,
    `S2_agent_interior_edge_nearby_exterior_point_source`, and the updated
    `interior_edge_nearby_exterior_point_source_iff_relative_ball_closure`,
    reducing nearby exterior points along edge interiors to a local exterior
    side-patch source.
    Closed completed/pruned claim:
    `S2-agent-actual-boundary-cycle-source-route`
    (`019e424a-b597-78d0-9d7a-b4439cb44987`).  Result: confirmed the shortest
    source theorem should construct a `UnitDistanceCycleBoundary B`, prove
    graph-vertex frontier iff `B.vertex`, and prove boundary sides are in
    `unboundedFrontierEdgeSet`; Codex-main integrated
    `ActualBoundaryCycleFrontierEquivalenceRows.ofBoundaryCycleEdgeMemSource`
    and
    `unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleEdgeMem_source`.
    Closed completed/pruned claim:
    `S2-agent-cycle-edge-openSegment-frontier`
    (`019e4247-f531-79d2-a430-9c7e38b7d677`).  Result: added
    `cycle_edge_openSegment_frontier_of_unboundedFrontierEdgeSet_or_symm`,
    `cycle_edge_openSegment_frontier_iff_unboundedFrontierEdgeSet_or_symm`,
    `ActualBoundaryCycleFrontierEquivalenceRows.ofBoundaryCycleEdgeMem`,
    `S2_agent_actual_exterior_sector_input_source_2_from_boundary_cycle_edge_mem`,
    and
    `S2_agent_actual_exterior_sector_input_source_2_from_faceSuccRows_orientation_boundary_cycle_edge_mem_closedSegment_local_exterior_angular_sector_source`,
    reducing the old cycle-edge open-segment frontier row to actual
    `unboundedFrontierEdgeSet` membership for the boundary cycle.
    Closed completed/pruned claim:
    `S2-agent-open-segment-point-sector`
    (`019e4247-f47c-7d41-8511-b5be8eadbae5`).  Result: added
    `BoundaryFrontierOpenSegmentRelativeClosurePropagation`,
    `BoundaryFrontierIncidentEdgeExteriorAngularSector`,
    `boundary_frontier_openSegment_frontierEdge_or_symm_of_relative_closure`,
    and
    `boundary_frontier_openSegment_local_exterior_sector_of_incident_edge_angular_and_relative_closure`,
    reducing the point-sector row to relative open-edge frontier propagation
    plus selected incident-edge angular-sector rows.
    Closed completed/pruned claim:
    `S2-agent-reverse-tail-exterior-sector`
    (`019e4244-8c34-7a12-8913-9569cc182e69`).  Result: added
    `BoundaryReverseTailOpenSegmentExteriorSector`,
    `edgeLocalRows_boundaryReverseTailExteriorSector_of_boundaryReverseTailOpenSegmentExteriorSector`,
    and
    `edgeRows_boundary_succ_of_actualBoundaryCycleFrontierEquivalenceRows_reverseTailOpenSegmentExteriorSector`,
    reducing the reverse-tail sector source to the point-level reverse-oriented
    boundary open-segment sector row.
    Closed completed/pruned claim:
    `S2-agent-open-segment-angular-sector`
    (`019e4242-e9ad-7722-b992-64edb71cd1da`).  Result: added
    `BoundaryFrontierOpenSegmentLocalExteriorSector`,
    `boundary_frontier_openSegment_local_exterior_angular_sector_of_openSegment_local_exterior_sector`,
    and
    `boundary_frontier_closedSegment_local_exterior_angular_sector_of_openSegment_pointSector_endpoint_sources`,
    reducing the open-segment angular-sector row to the sharper point-sector
    residual and the closed-segment route to point-sector plus far-endpoint
    residuals.
    Closed completed/pruned claim:
    `S2-agent-boundary-reverse-exclusion`
    (`019e423f-d7db-7203-b7c4-c534c104f9ae`).  Result: added
    `EdgeLocalRowsBoundaryReverseTailExteriorSector`,
    `edgeLocalRows_boundaryReverseExcluded_of_reverseTailExteriorSector`, and
    `edgeRows_boundary_succ_of_actualBoundaryCycleFrontierEquivalenceRows_reverseTailExteriorSector`,
    reducing reverse-orientation exclusion to the reverse-tail exterior-sector
    source row now owned by `S2-agent-reverse-tail-exterior-sector`.
    Closed completed claim: `S2-actual-boundary-row-to-cycle-target`.
    Owner: Codex-main.  Scope: `Swanepoel/ExteriorComponentTopology.lean`.
    Result: added
    `unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows`,
    directly erasing a genuine
    `ActualBoundaryCycleFrontierEquivalenceRows C inputs` witness to the final
    `UnboundedExteriorFrontierCycleRows C inputs` target without carrier
    detours or synthetic enclosure.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed/pruned claim:
    `S2-agent-vertex-incident-openSegment-closure`
    (`019e4245-3e25-7592-9a5b-20722a0bc845`).  Result: identified the
    non-circular reducer from punctured frontier accumulation plus
    `InteriorRelativeBallClosureRow` to the graph-vertex incident
    open-segment closure row; Codex-main integrated it as
    `incident_openSegment_closure_of_punctured_vertex_and_relative_ball_closure`
    and the direct local-edge row wrapper
    `exists_unboundedExteriorFrontierEdgeLocalRows_of_punctured_vertex_and_relative_ball_closure`.
    Verification: targeted
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed after integration.
    Closed completed/pruned claim:
    `S2-agent-input-only-route-current-decomposition`
    (`019e4244-2ecf-7b53-bb62-790017bcea4e`).  Result: confirmed the shortest
    current final handoff is the actual-boundary row route:
    `ActualBoundaryCycleFrontierEquivalenceRows C inputs` to
    `UnboundedExteriorFrontierCycleRows C inputs`, with carrier/geometric rows
    remaining only when using the carrier reducer.
    Closed completed/pruned claim:
    `S2-agent-closed-segment-angular-sector`
    (`019e4240-0211-7472-ad9c-2a873569cf22`).  Result: added
    `BoundaryFrontierOpenSegmentLocalExteriorAngularSector`,
    `BoundaryFrontierClosedSegmentEndpointExteriorAngularSector`, and
    `boundary_frontier_closedSegment_local_exterior_angular_sector_of_openSegment_endpoint_sources`,
    reducing the closed-segment angular-sector row to the open-segment case and
    the far-endpoint case.
    Closed completed/pruned claim:
    `S2-agent-endpoint-angular-sector`
    (`019e4244-1732-7453-92d0-2757e29b6d89`).  Result: identified the
    far-endpoint branch as vacuous under a frontier endpoint incident-neighbour
    row; Codex-main integrated
    `BoundaryFrontierEndpointIncidentOnlyPredSucc` and
    `boundary_frontier_closedSegment_endpoint_exterior_angular_sector_of_endpoint_incident_only_pred_succ`.
    Verification: targeted
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed after integration.
    Closed completed/pruned claim:
    `S2-agent-raw-start-face-dart-identification`
    (`019e4240-2f6e-7be3-81c3-80efe544e7f2`).  Result: added
    `FaceDartOrbitExteriorCarrierRows.raw_start_eq_orbit_dart_of_edgeLocalRows_orbit_succ`,
    `FaceDartOrbitExteriorCarrierRows.raw_start_eq_orbit_zero_of_edgeLocalRows_orbit_zero_succ`,
    and
    `ActualBoundaryCycleFrontierEquivalenceRows.S2_agent_actual_boundary_cycle_frontier_equivalence_of_faceDartOrbit_rawFaceSuccOrbitSeedEdgeRows`,
    reducing raw start equality to the selected first-boundary-edge orientation
    row.
    Closed completed/pruned claim:
    `S2-agent-vertex-seed-nonvertex-accumulation`
    (`019e423b-4b2b-7b00-b9ce-4217caa9be16`).  Result: added
    `nearby_nonvertex_unboundedExterior_frontier_of_punctured_vertex`,
    `vertex_seed_side_of_punctured_vertex_unboundedExterior_frontier`, and
    `exists_unboundedExteriorFrontierEdgeLocalRows_of_unboundedExteriorFrontierSeed_punctured_vertex`,
    reducing graph-vertex seed accumulation to a punctured same-vertex
    frontier accumulation row.
    Closed completed/pruned claim:
    `S2-agent-edgeRows-boundary-succ-source`
    (`019e4238-9767-7361-a1ab-b086eaf7ac91`).  Result: added
    `edgeLocalRows_boundary_succ_or_reverse_of_actualBoundaryCycleFrontierEquivalenceRows`,
    `EdgeLocalRowsBoundaryReverseExcluded`,
    `edgeRows_boundary_succ_of_actualBoundaryCycleFrontierEquivalenceRows`,
    `raw_start_on_boundary_of_actualBoundaryCycleFrontierEquivalenceRows`, and
    `exists_geometricRawFaceSuccOrbitBoundarySeed_of_unboundedExteriorFrontierSeed_actualBoundaryRows`,
    reducing forward boundary orientation to actual boundary rows, incident
    completeness, interior carrier membership, and reverse-exclusion.
    Closed completed/pruned claim:
    `S2-agent-closed-segment-local-exterior-sector`
    (`019e4239-9290-7bf1-8624-35670a87ef02`).  Result: added
    `BoundaryFrontierClosedSegmentLocalExteriorAngularSector` and reducers from
    that angular-sector row to the closed-segment local exterior-sector source.
    Closed completed/pruned claim:
    `S2-agent-actual-boundary-cycle-source`
    (`019e423a-e002-77c0-b5ce-e40df41521ff`).  Result: added
    `ActualBoundaryCycleFrontierEquivalenceRows.ofFaceDartOrbitRawFaceSuccOrbitStartRows`
    and
    `ActualBoundaryCycleFrontierEquivalenceRows.S2_agent_actual_boundary_cycle_frontier_equivalence_of_faceDartOrbit_rawFaceSuccOrbitStartRows`,
    reducing actual boundary-cycle equivalence to honest
    `FaceDartOrbitExteriorCarrierRows` plus selected raw-orbit start
    identification.
    Closed completed/pruned claim:
    `S2-agent-current-source-chain-audit`
    (`019e4238-2b84-7e91-9f1b-6ff72aac052c`).  Result: confirmed the shortest
    checked chain is
    `unboundedExteriorFrontierCycleRows_of_carrierRows`, so the missing source
    theorem is the input-only
    `exteriorFrontierCarrierRows_nonempty_of_finite_noncrossing_segments`
    shape from `FinitePlanarOuterComponentInputs C` to
    `Nonempty (ExteriorFrontierCarrierRows C inputs)`.
    Closed completed/pruned claim:
    `S2-agent-owner-file-compile-surface-audit`
    (`019e4238-3987-76d0-b3ca-ef6090bda082`).  Result: checked the owner-file
    compile/import surface; `GeometricRotationSystem`, `ExteriorComponentTopology`,
    and `FaceBoundaryTopologySourceW32` build as owner files, root import order
    is sane, no duplicate S2 source package was found, and the non-live
    synthetic bookkeeping W32 route remains documented as forbidden for S2.
    Closed completed/pruned claim:
    `S2-agent-rightward-exterior-dart-orientation`
    (`019e4231-71cc-7cf2-8a37-db2ed6a440d4`).  Result: added
    `exists_incident_unboundedExteriorFrontierEdgeLocalRows_of_vertex_seed_side`,
    `exists_unboundedExteriorFrontierEdgeLocalRows_of_unboundedExteriorFrontierSeed`,
    `raw_start_on_boundary_of_edgeLocalRows_boundary_succ`, and
    `exists_geometricRawFaceSuccOrbitBoundarySeed_of_unboundedExteriorFrontierSeed`;
    reduced the seed-orientation branch to `hvertex_side` and
    `edgeRows_boundary_succ`.
    Closed completed/pruned claim:
    `S2-agent-interior-closure-locus-relative-open`
    (`019e4238-2b76-7402-a1e4-984b8dcdfa1d`).  Result: added
    `interior_closure_locus_relative_open_of_relative_ball_closure`,
    `interior_closure_locus_relative_open_iff_relative_ball_closure`, and
    `S2_agent_interior_closure_locus_relative_open_source`, reducing the
    relative-openness residual to `InteriorEdgeNearbyExteriorPointSource C inputs`.
    Closed completed/pruned claim:
    `S2-agent-vertex-seed-side-source`
    (`019e4238-801b-7a61-9ec3-bb5d41d2065c`).  Result: added
    `vertex_seed_side_of_nearby_nonvertex_unboundedExterior_frontier` and
    `exists_unboundedExteriorFrontierEdgeLocalRows_of_unboundedExteriorFrontierSeed_nearby_nonvertex`,
    reducing the graph-vertex seed branch to punctured non-graph-vertex
    frontier accumulation near the seed.
    Closed completed/pruned claim:
    `S2-agent-frontier-preconnected-source-route`
    (`019e4231-e096-7a01-acca-1377cfaedec3`).  Result: added
    `S2_agent_frontier_preconnected_source_route`,
    `S2_agent_frontier_preconnected_source_route_rawFaceSuccOrbit`,
    `S2_agent_frontier_preconnected_source_route_of_nearby_edge_point_exterior_points`,
    and
    `S2_agent_frontier_preconnected_source_route_rawFaceSuccOrbit_of_nearby_edge_point_exterior_points`;
    reduced the frontier preconnectedness route to selected consecutive
    raw-orbit edges, selected-edge coverage, local sector rows, and
    `InteriorEdgeNearbyExteriorPointSource C inputs`.
    Closed completed/pruned claim:
    `S2-agent-boundary-frontier-local-exterior-sector`
    (`019e4232-e27c-7c51-a599-b0fd23a0aef5`).  Result: added
    `BoundaryFrontierClosedSegmentLocalExteriorSector`,
    `boundary_frontier_local_exterior_sector_of_closedSegment_local_exterior_sector`,
    and
    `S2_agent_actual_exterior_sector_input_source_2_from_geometric_rotation_closedSegment_local_exterior_sector_source`;
    reduced the remaining local exterior-sector source to
    `BoundaryFrontierClosedSegmentLocalExteriorSector inputs B`.
    Closed completed/pruned claim:
    `S2-agent-interior-carrier-membership-source`
    (`019e4232-ffa2-73b2-b756-789769efc6bc`).  Result: reduced
    `InteriorRelativeBallClosureRow` to the local
    `InteriorFrontierEdgeCarrierMembershipSource C inputs` theorem and
    reported no file changes beyond the checked source reducer surface.
    Closed completed/pruned claim:
    `S2-agent-boundary-orientation-arg-source`
    (`019e4233-9c5c-76c3-8434-014fb200b794`).  Result: reduced the explicit
    boundary orientation source to concrete local exterior-sector/angular rows
    already consumed by the geometric rotation adapter.
    Closed completed/pruned claim:
    `S2-agent-final-gap-route-audit`
    (`019e4231-b592-73e2-9e9c-2da9efe4df8c`).  Result: confirmed the shortest
    current chain is to prove a nonempty
    `ExteriorFrontierCarrierRows C inputs` source, feed it through
    `unboundedExteriorFrontierCycleRows_of_carrierRows`, then
    `finitePlanarStraightLineOuterComponentTheorem_of_exteriorFrontierCarrierRows`,
    then W32
    `minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows`.
    Equivalent boundary-sector source: produce a `UnitDistanceCycleBoundary B`,
    `frontier_iff_cycle_vertex`, `cycle_edge_openSegment_frontier`,
    `BoundaryVertexGeometricRotationOrderRow`, and local exterior-sector rows,
    then consume `unboundedExteriorFrontierCycleRows_of_boundaryVertexExteriorSectorRows`.
    Closed completed/pruned claim:
    `S2-agent-edge-carrier-segment-chain-source-face-dart`
    (`019e4223-9d95-7963-845c-639534ec56f4`).  Result: added
    `FaceDartOrbitExteriorCarrierRows.S2_agent_edge_carrier_segment_chain_source`
    and supporting orbit-carrier edge-chain lemmas, proving
    `UnboundedFrontierEdgeCarrierSegmentChainConnected inputs` from actual
    `FaceDartOrbitExteriorCarrierRows C inputs` without carrier connectedness,
    cyclic coverage, induced frontier graph connectedness, or final S2 rows.
    Verification reported by worker and replayed by Codex-main:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.
    Closed completed/pruned claim:
    `S2-agent-third-germ-between-source`
    (`019e422f-3ab8-7f93-9489-ea780f74f502`).  Result: added
    `boundary_frontier_third_germ_between_of_local_exterior_sector_source`
    and
    `S2_agent_actual_exterior_sector_input_source_2_from_geometric_rotation_local_exterior_sector_source`,
    replacing the arbitrary `third_germ_between` input with the concrete
    noncenter `boundary_frontier_local_exterior_sector` residual.  Verification
    reported by worker and replayed by Codex-main:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.
    Closed completed/pruned claim:
    `S2-agent-geometric-boundary-nonwrap-source`
    (`019e422f-52a1-7330-aa5c-376c6cc5ef54`).  Result: added
    `boundaryVertexGeometricRotationWrapRow_not_of_pred_arg_lt_succ_arg`
    and `S2_agent_geometric_boundary_order_source_of_pred_arg_lt_succ_arg`,
    reducing the nonwrap residual to the explicit exterior orientation
    inequality
    `graphDartArg pred < graphDartArg succ` at each chosen boundary vertex.
    Verification reported by worker and replayed by Codex-main:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/GeometricRotationSystem.lean`.
    Closed completed/pruned claim:
    `S2-agent-edge-carrier-segment-chain-source`
    (`019e4224-f8a0-7bd3-818e-49191343b808`).  Result: added
    `rawFaceSuccOrbitSelectedFrontierEdge`,
    `rawFaceSuccOrbitSelectedFrontierEdge_eq_or_symm`,
    `rawFaceSuccOrbitSelectedFrontierEdge_segmentsMeet_succ`,
    `unboundedFrontierEdgeCarrierSegmentChainConnected_of_rawFaceSuccOrbit_edges`,
    and `S2_agent_edge_carrier_segment_chain_source_rawFaceSuccOrbit`,
    reducing carrier segment-chain connectedness to raw consecutive selected
    frontier edges and edge coverage.  Verification reported by worker and
    replayed by Codex-main:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.
    Closed completed/pruned claim:
    `S2-agent-interior-relative-ball-closure-source`
    (`019e4226-838e-7043-a4fd-b48886760820`).  Result: added
    `InteriorFrontierEdgeCarrierMembershipSource`,
    `interiorEdgeNearbyExteriorPointSource_of_interior_frontier_edge_carrier_membership`,
    `S2_agent_interior_relative_ball_closure_source_of_interior_frontier_edge_carrier_membership`,
    and
    `S2_agent_frontier_cover_to_connected_carrier_integration_of_interior_frontier_edge_carrier_membership`,
    reducing the nearby-exterior/interior-relative-ball source to the exact
    local carrier-membership theorem for an edge with a relative-interior point
    on the unbounded exterior frontier.  Verification reported by worker and
    replayed by Codex-main:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.
    Closed completed/pruned claim:
    `S2-agent-actual-boundary-cycle-frontier-equivalence`
    (`019e4226-98ad-7331-9936-0f33a51d0409`).  Result: added
    `ActualBoundaryCycleFrontierEquivalenceRows.ofRawFaceSuccOrbitBoundaryRows`
    and
    `ActualBoundaryCycleFrontierEquivalenceRows.S2_agent_actual_boundary_cycle_frontier_equivalence_of_rawFaceSuccOrbitBoundaryRows`,
    transporting raw face-successor orbit tails to the actual boundary-cycle
    frontier equivalence and edge-frontier rows.  Verification reported by
    worker and replayed by Codex-main:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.
    - Claim: `S2-exterior-boundary-cycle-source`.  Owner: Codex-main.
      Role: implementation integrator for the input-only exterior boundary-cycle
      source theorem.  Scope:
      `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`, with read-only
      use of `Swanepoel/FinitePlaneDrawing.lean`,
      `Swanepoel/GeometricRotationSystem.lean`, and
      `Swanepoel/JordanTopologyFactsConcrete.lean`.  Status: superseded by
      the refreshed active Codex-main claim above.  Current deliverable:
      construct a genuine unbounded-exterior frontier cycle/source
      row from `FinitePlanarOuterComponentInputs C`, then route it through the
      existing S2 reducers.  Next verification:
      `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.
    - Claim: `S2-agent-frontier-edge-cover-endpoint-cases`.  Owner:
      `Cicero the 3rd` (`019e4210-b549-7282-ab88-0de215813f61`).  Role:
      prove the graph-vertex endpoint cases of `frontier_edge_cover` using
      frontier vertex incidence and selected frontier-edge membership.  Scope:
      `Swanepoel/ExteriorComponentTopology.lean`; no `TASK.md` edits.  Status:
      superseded by completed `S2-agent-frontier-edge-cover-source`; agent
      inaccessible to Codex-main and not separately credited.
    - Claim: `S2-agent-frontier-edge-cover-interior-cases`.  Owner:
      `Kierkegaard the 3rd` (`019e4210-ceaf-75e3-9582-abb01ae20333`).  Role:
      prove the edge-interior cases of `frontier_edge_cover`, deriving
      `unboundedFrontierEdgeSet` membership from open-segment frontier rows.
      Scope: `Swanepoel/ExteriorComponentTopology.lean`; no `TASK.md` edits.
      Status: superseded by completed `S2-agent-frontier-edge-cover-source`;
      agent inaccessible to Codex-main and not separately credited.
    - Claim: `S2-agent-local-constancy-frontier-edge-cover`.  Owner:
      `Goodall the 3rd` (`019e420e-6a8e-7e83-a919-a836e056d614`).  Role:
      implement the non-circular local-constancy source for
      `UnboundedFrontierCarrierAdjClosedTopologySourceRows` from
      `frontier_edge_cover`, or expose the exact remaining endpoint/star
      local assumptions.  Scope: `Swanepoel/ExteriorComponentTopology.lean`;
      no `TASK.md` edits.  Status: stale/inaccessible on 2026-05-19; not
      pruned as completed and not credited.  Role remains open.
    - Claim: `S2-agent-local-constancy-edge-interior`.  Owner:
      `Locke the 3rd` (`019e4210-e750-7362-ac7d-8f51dc9d5268`).  Role:
      prove local constancy of carrier-subset realization near interior points
      of selected frontier edges for adjacency-closed subsets.  Scope:
      `Swanepoel/ExteriorComponentTopology.lean`; no `TASK.md` edits.  Status:
      stale/inaccessible on 2026-05-19; not pruned as completed and not
      credited.  Role remains open.
    - Claim: `S2-agent-local-constancy-vertex-star`.  Owner:
      `Bernoulli the 3rd` (`019e4211-003f-7fd1-9f6e-ea30ccb886db`).  Role:
      prove local constancy of carrier-subset realization near frontier graph
      vertices using vertex-star isolation and adjacency-closedness.  Scope:
      `Swanepoel/ExteriorComponentTopology.lean`; no `TASK.md` edits.  Status:
      stale/inaccessible on 2026-05-19; not pruned as completed and not
      credited.  Role remains open.
    - Claim: `S2-agent-raw-tail-hit-source`.  Owner:
      `Volta the 3rd` (`019e420e-83a7-7212-828c-a8144903f748`).  Role:
      prove or reduce the raw-tail hit row for the selected geometric raw
      face-successor orbit, without assuming cyclic coverage.  Scope:
      `Swanepoel/ExteriorComponentTopology.lean`; no `TASK.md` edits.  Status:
      stale/inaccessible on 2026-05-19; not pruned as completed and not
      credited.  Role remains open.
    - Claim: `S2-agent-actual-exterior-sector-input-source-2`.  Owner:
      `Nash the 3rd` (`019e420e-9820-7980-95f5-4b4ada349b42`).  Role:
      continue the actual exterior-sector source, targeting the local
      point-sector and no-between assumptions of
      `localSectorRows_of_vertex_star_isolation_local_exterior_sector`.  Scope:
      `Swanepoel/ExteriorComponentTopology.lean` and read-only
      `Swanepoel/GeometricRotationSystem.lean`; no `TASK.md` edits.  Status:
      stale/inaccessible on 2026-05-19; not pruned as completed and not
      credited.  Role remains open.
    - Claim: `S2-agent-repeated-tail-raw-identification-source`.  Owner:
      `Boyle the 3rd` (`019e420e-b099-7df2-a173-e0e0d0d8954e`).  Role:
      bridge the selected geometric raw orbit to `FaceDartOrbitExteriorCarrierRows`
      enough to use the repeated-tail source wrappers, especially `hperiod`
      and `tail_eq`, without downstream S2 cycle projection.  Scope:
      `Swanepoel/ExteriorComponentTopology.lean`; no `TASK.md` edits.  Status:
      stale/inaccessible on 2026-05-19; not pruned as completed and not
      credited.  Role remains open.
    - Claim: `S2-rightward-exterior-dart-orientation`.  Owner:
      Codex-rightward.  Role: exterior-dart orientation prover.  Scope:
      prefer `Swanepoel/FinitePlaneDrawing.lean` or
      `Swanepoel/ExteriorComponentTopology.lean`; no edits outside `TASK.md`
      unless the owner-file theorem closes or the blocker is recorded.  Status:
      blocked after checked theorem
      `exists_geometricRawFaceSuccOrbitSeed_of_unboundedExteriorFrontierSeed`.
      Exact missing local-side row: when the seed lands on a graph vertex,
      prove an incident canonical edge has an interior point on
      `frontier (unboundedExteriorComponentRows C inputs).exterior`.  Verified:
      `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
      passed.
  - Closed/pruned summary:
    Closed completed/pruned claim:
    `S2-agent-repeated-tail-actual-exterior-arc-source`
    (`019e4223-c37f-72e3-8991-d2b085665f0f`).  Result: added
    `RawFaceSuccOrbitRepeatedTailActualExteriorArcRows`,
    `RawFaceSuccOrbitActualExteriorArcSeparationRows`,
    `S2_agent_repeated_tail_arc_separation_source`, and
    `S2_agent_no_cut_repeated_tail_source_from_actualExteriorArcRows`, then
    Codex-main integrated
    `S2_agent_input_s2_assembly_gap_reducer_frontier_nearbyTailHitActualArcRows`.
    Verification: `ExteriorComponentTopology` owner build passed.
    Closed completed/pruned claim:
    `S2-agent-face-dart-orbit-exterior-carrier-source`
    (`019e4225-e94f-79e3-b70e-2ae1ad0c1aef`).  Result: added
    `faceDartOrbitExteriorCarrierRows_of_boundaryVertexExteriorSectorRows`
    and `S2_agent_face_dart_orbit_exterior_carrier_source`, reducing the
    face-dart carrier source to actual boundary cycle rows plus pointwise
    boundary exterior-sector rows.  Verification reported by worker:
    `ExteriorComponentTopology` owner build passed.
    Closed completed/pruned claim:
    `S2-agent-geometric-boundary-order-source`
    (`019e4228-3442-7dd0-8709-f4ad8f4240c4`).  Result: added
    `S2_agent_geometric_boundary_order_source` and related branch lemmas in
    `GeometricRotationSystem.lean`, reducing arbitrary geometric order rows to
    actual face-successor rows plus the explicit nonwrap residual
    `Not (BoundaryVertexGeometricRotationWrapRow C B k)`.  Verification
    reported by worker: `GeometricRotationSystem` owner build passed.
    Closed completed/pruned claim:
    `S2-agent-boundary-carrier-degree-two-from-local-sectors`
    (`019e421c-dcf7-7881-b5dd-189458fedc8c`).  Status: superseded, not
    credited as completed; the active route already has checked reducers
    `unboundedFrontierCarrierGraph_degree_two_of_dartPairRows` and
    `unboundedFrontierCarrierGraph_degree_two_of_boundaryVertexExteriorSectorRows`
    from local-sector rows.
    Closed completed/pruned claim:
    `S2-agent-angle-order-from-geometric-rotation`
    (`019e4218-3296-7b72-9a45-9b1e51ac6e8b`).  Result: added real
    sorted-geometric-rotation source rows
    `BoundaryVertexGeometricRotationOrderRow`,
    `boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRow`,
    `boundaryVertexAngularNoBetweenRows_of_geometricRotationOrderRows`,
    and the S2 wrappers
    `S2_agent_angle_order_from_geometric_rotation`,
    `S2_agent_actual_exterior_sector_input_source_2_from_geometric_rotation`,
    and
    `S2_agent_actual_exterior_sector_input_source_2_from_geometric_rotation_point_sector_source`.
    Verification reported by worker: `GeometricRotationSystem` and
    `ExteriorComponentTopology` builds passed.
    Closed completed/pruned claim:
    `S2-agent-point-sector-no-between-source`
    (`019e4218-32e2-7c02-99d1-17163bf9a597`).  Result: added
    `PointSectorNoBetweenSourceRows`,
    `S2_agent_point_sector_no_between_source`, and
    `S2_agent_actual_exterior_sector_input_source_2_of_point_sector_no_between_source`.
    Verification reported by worker: owner-file and module builds passed.
    Closed completed/pruned claim:
    `S2-agent-selected-seed-dart-edge-frontier`
    (`019e4218-e8f0-7893-9d26-ba4f4d6b687e`).  Result: added
    `rawFaceSuccOrbit_dart_on_boundary_of_boundary_faceSuccRows`,
    `rawFaceSuccOrbit_dart_on_boundary_of_sectorRows_start`, and
    `S2_agent_selected_seed_dart_edge_frontier`.  Verification reported by
    worker: owner-file and module builds passed.
    Closed completed/pruned claim:
    `S2-agent-raw-nonbacktracking-source`
    (`019e4218-e943-7741-97fa-e0968b4327f0`).  Result: added
    `exists_unit_neighbor_ne`,
    `geometricUnitDistanceRotationSystem_faceSucc_head_ne_tail_of_exists_other_neighbor`,
    `rawFaceSuccOrbit_pred_succ_tail_ne_of_geometric_localSectorRows`, and
    `S2_agent_raw_nonbacktracking_source`.  Verification reported by worker:
    owner-file and module builds passed.
    Closed completed/pruned claim:
    `S2-frontier-tailHit-reducer-and-owner-build-repair`.  Owner:
    Codex-main.  Scope: `Swanepoel/ExteriorComponentTopology.lean` and
    `TASK.md`.  Result: added
    `S2_agent_input_s2_assembly_gap_reducer_frontier_tailHitRows`, deriving
    raw-tail coverage internally from honest carrier connectedness plus the
    raw predecessor/successor nonbacktracking row; added
    `S2_agent_input_s2_assembly_gap_reducer_frontier_nearbyTailHitRows`,
    which consumes the nearby-exterior-points row directly; and repaired the local
    geometric `formPerm` proof so the owner file builds.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean
    ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean` passed.
    Closed completed/pruned claim:
    `S2-agent-raw-tail-hit-from-exterior-frontier`
    (`019e4218-31fb-7173-9f8e-89d3bc0aa2d8`).  Result: added
    `S2_agent_raw_tail_hit_from_exterior_frontier`,
    `S2_agent_raw_tail_hit_from_exterior_frontier_topologyRows`, and
    `S2_agent_raw_tail_hit_reachable_root_from_exterior_frontier`, sourcing
    raw-tail hit from actual exterior frontier data with residual rows exactly
    at raw dart open-segment frontier, honest carrier connectedness,
    `localSectorRows`, and raw predecessor/successor tail nonbacktracking.
    Verification reported by worker: owner-file Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-tail-coverage-reclaim`
    (`019e420a-62e1-7940-ac78-bef062392ce0`).  Result: confirmed raw-tail
    coverage can be sourced from concrete carrier connectedness plus
    neighbor-tail closure, but the truly non-circular route still needs the
    raw-tail hit/tracing row for every unbounded-frontier carrier vertex.
    No file edits.
    Closed completed/pruned claim:
    `S2-agent-frontier-edge-cover-source`
    (`019e420e-52d2-7401-9e8d-8480981be880`).  Result: added
    `frontier_vertex_edge_cover_of_localSectorRowsAt`,
    `frontier_edge_cover_of_localSectorRows_and_interior_edge_mem`, and
    `S2_agent_frontier_edge_cover_source`, proving the frontier-edge cover
    from local-sector rows plus interior-edge membership.  Verification:
    owner-file Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-boundary-cycle-from-raw-tail-hit`
    (`019e4211-182a-7473-895f-62de591bbc1a`).  Result: added
    `S2_agent_boundary_cycle_from_raw_tail_hit_carrier` and
    `S2_agent_boundary_cycle_from_raw_tail_hit`, turning raw-tail hit coverage,
    dart-edge frontier, local sectors, and repeated-tail rows into the honest
    carrier and then `UnboundedExteriorFrontierCycleRows`.  Verification:
    owner-file and root import builds passed.
    Closed completed/pruned claim:
    `S2-main-local-constancy-and-root-adapters`.  Owner: Codex-main.  Result:
    added
    `unboundedFrontierCarrierAdjClosedTopologyRows_of_frontier_preconnected_local_const`
    and `S2_agent_tail_coverage_from_reachable_root`, repaired stale ASCII
    `<->` notation in active S2 declarations, and fixed two owner-file compile
    breaks in carrier-subset endpoint realization and repeated-tail raw
    identification.  Verification: targeted owner-file Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-actual-exterior-sector-source`
    (`019e4201-ce8c-7352-ae66-54f6d6d112a1`).  Result: added
    `exists_local_frontier_germ_two_of_vertex_star_isolation_local_exterior_sector`,
    `unboundedFrontierCarrierLocalSectorRowsAt_of_vertex_star_isolation_local_exterior_sector`,
    `boundaryVertexExteriorSectorRowsAt_of_boundaryVertexAngularNoBetweenRows_local_exterior_sector`,
    `boundaryVertexExteriorSectorRows_of_boundaryVertexAngularNoBetweenRows_local_exterior_sector`,
    and `S2_agent_actual_exterior_sector_source`.  Verification:
    owner-file Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-raw-reachable-root-source`
    (`019e4201-b00a-7340-aa22-8274c5659d4c`).  Result: added
    `rawFaceSuccOrbit_tail_reachable_from_zero_of_edge_openSegment_frontier`
    and `S2_agent_raw_reachable_root_source`, giving non-cyclic raw successor
    reachability once every carrier vertex is known to occur as a raw tail.
    Verification: owner-file Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-repeated-tail-selected-raw-source`
    (`019e4201-c7be-7601-8509-85103da9da3f`).  Result: added
    `FaceDartOrbitExteriorCarrierRows.S2_agent_repeated_tail_selected_raw_source`
    and the arc-row variant, transporting repeated-boundary separation to the
    selected raw orbit under period/tail identification.  Verification:
    owner-file Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-input-s2-assembly-gap-reducer`
    (`019e4201-d5a5-7300-89d8-09e41b996570`).  Result: added
    `S2_agent_input_s2_assembly_gap_reducer_cyclicCoverage`,
    `S2_agent_input_s2_assembly_gap_reducer_connected`, and
    `S2_agent_input_s2_assembly_gap_reducer_topologyRows`, exposing the exact
    residual rows for the current raw S2 handoff.  Verification:
    owner-file and root import builds passed.
    Closed completed/pruned claim:
    `S2-agent-adjClosed-rows-reclaim`
    (`019e420a-632e-7822-859b-8ba553a628bc`).  Result: confirmed the
    non-circular connectedness route needs
    `unboundedFrontierCarrierAdjClosedTopologyRows_of_local_stability` plus
    honest local constancy from a real `frontier_edge_cover`; using
    `S2_agent_frontier_preconnected_source` to prove carrier connectedness is
    circular because it already assumes carrier connectedness.  No file edits.
    Closed completed/pruned claim:
    `S2-agent-frontier-preconnected-reclaim`
    (`019e420a-638c-7242-87c6-9f603cb7cf4a`).  Result: confirmed
    `frontier_preconnected` is not available from exterior component
    connectedness alone; the usable non-circular source is a genuine
    `frontier_edge_cover` plus carrier connectedness, while using it for
    connectedness itself would be circular.  No file edits.
    Closed completed/pruned claim:
    `S2-agent-clopen-realization-reclaim`
    (`019e420a-63eb-72f3-bde4-4eb7e67bf37a`).  Result: confirmed the
    relative closed/open rows reduce to one local-constancy theorem for
    `unboundedFrontierCarrierSubsetRealization` near each frontier point,
    with the same `frontier_edge_cover` as the geometric source.  No file edits.
    Closed completed/pruned claim:
    `S2-agent-tail-coverage-reclaim`
    (`019e420a-62e1-7940-ac78-bef062392ce0`).  Result: confirmed
    `S2_agent_tail_coverage_from_connected_carrier` already gives selected
    raw-orbit tail coverage from carrier connectedness, dart-edge frontier,
    local-sector rows, and nonbacktracking; no new tail-coverage route is
    needed for the connected reducer.  No file edits.
    Closed completed/pruned claim:
    `S2-agent-point-sector-source-from-exterior-side`
    (`019e41f5-90e9-7d33-8984-e3861cd073a6`).  Result: added
    `boundary_frontier_third_germ_point_between_of_graphDart_between` and
    `local_exterior_sector_of_boundary_frontier_third_germ_between`, bridging
    edge-level third-germ angular rows to point-sector rows.  Verification:
    owner-file Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-nondegenerate-frontier-germ-choice`
    (`019e41f5-9138-7930-8e2f-bf98077d39be`).  Result: strengthened the local
    bad-germ route with an explicit `q ≠ center` branch and discharged the
    center case through the closed predecessor germ.  Verification:
    owner-file Lean build passed after shared raw-package repairs.
    Closed completed/pruned claim:
    `S2-agent-boundary-angularRows-source`
    (`019e41f5-9192-7ae1-a9b4-ed33379ea9b8`).  Result: added actual
    exterior-sector sources for boundary angular no-between rows and geometric
    boundary successor rows.  Verification: owner-file Lean build passed after
    integration.
    Closed completed/pruned claim:
    `S2-agent-dart-edge-frontier-from-sectorRows`
    (`019e41f5-91e2-7f13-954b-93a3333ff2b5`).  Result: added
    `S2_agent_dart_edge_frontier_from_sectorRows`, proving selected raw
    dart-edge open-segment frontier rows from actual sector rows.  Verification:
    owner-file Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-carrier-adjClosed-all-source`
    (`019e41f5-923c-7b60-9e70-fee7cb9ed1d9`).  Result: added
    `UnboundedFrontierCarrierAdjClosedTopologyRows` plus the direct
    `unboundedFrontierCarrierGraph_connected_of_adjClosed_topologyRows`
    connectedness route.  Verification: owner-file Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-raw-orbit-edge-membership-source`
    (`019e41f7-2b86-7793-b9fb-3527fbafb01a`).  Result: added
    `S2_agent_raw_orbit_edge_membership_source`, deriving consecutive selected
    raw orbit edge membership in `unboundedFrontierEdgeSet` from raw
    open-segment frontier.  Verification: owner-file Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-input-only-unbounded-cycle-from-raw-package`
    (`019e41f7-2c8c-7091-99f2-588eb73c46f8`).  Result: added
    `S2_agent_input_only_unbounded_cycle_from_raw_package`, exposing the exact
    residual input-level assumptions for the raw S2 handoff.  Verification:
    owner-file Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-local-sector-family-from-point-sector`
    (`019e41f7-2cd7-79a3-8290-f81ea437684d`).  Result: added
    `localSectorRows_of_vertex_star_isolation_local_exterior_sector`, replacing
    the abstract bad-germ input with the point-sector/local-exterior-sector
    source row while keeping nondegeneracy explicit.  Verification:
    owner-file Lean build passed.
    Closed completed/pruned claim:
    `S2-agent-local-sector-input-route-search`
    (`019e41ff-ed2e-7852-8bb8-2bb91cd33fe2`).  Result: confirmed the shortest
    local-sector route is
    `localSectorRows_of_vertex_star_isolation_local_exterior_sector`; its live
    source inputs are an actual exterior boundary cycle, frontier-iff-cycle,
    cycle-edge frontier, local point-sector rows, and geometric no-between
    rows.  No file edits.
    Closed completed/pruned claim:
    `S2-agent-connected-carrier-route-search`
    (`019e41ff-ec81-7a92-889e-ca0d77b8a046`).  Result: confirmed the
    non-circular connectedness route is either
    `unboundedFrontierCarrierGraph_connected_of_adjClosed_topologyRows`
    followed by `unboundedFrontierCarrierCyclicCoverageRows_of_connected_localSectorRows`,
    or a direct root-reachability row for the concrete carrier.  No file edits.
    Closed completed/pruned claim:
    `S2-agent-raw-edge-membership-route-search`
    (`019e41ff-eccf-7c42-a741-081c3f8d74bb`).  Result: confirmed the leaner
    target is the direct selected raw-orbit open-segment frontier callback;
    `unboundedFrontierEdgeSet` membership is a derived side product through
    `rawFaceSuccOrbit_edge_mem_unboundedFrontierEdgeSet_or_symm` or
    `S2_agent_raw_orbit_edge_membership_source`.  No file edits.
    Closed completed/pruned claim:
    `S2-agent-repeated-tail-nocut-route-search`
    (`019e41ff-ed8e-7451-9a1c-1a6c66fc2832`).  Result: confirmed no checked
    route derives repeated raw-tail separation rows from `inputs.noCutVertex`
    alone.  The checked route is the reverse: repeated-tail separation rows
    build a cut partition, and `inputs.noCutVertex` then proves raw-tail
    injectivity.  The remaining source row is the geometric repeated-tail
    separation callback for the selected raw orbit.  No file edits.
    Closed completed/pruned claim:
    `S2-agent-raw-source-package-final-assembly`
    (`019e41f5-928b-7550-943b-8b8ca30f1189`).  Result: added
    `unboundedExteriorFrontierCycleRows_of_exists_rawFaceSuccOrbit_sourceRows`
    and `unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit_inputRows`,
    projecting the existential raw-source package into
    `UnboundedExteriorFrontierCycleRows C inputs`.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed/pruned claim:
    `S2-agent-period-three-source-for-raw-package`
    (`019e41f7-2bd2-74a3-8cc5-44e21082be7e`).  Result: added the
    frontier-iff-tail and tail-coverage variants deriving `3 <= O.period`
    inside `RawFaceSuccOrbitRemainingSourceRows`, so the period row is no
    longer a separate source assumption once raw-tail coverage and local-sector
    rows are available.  Verification: owner-file Lean build passed after
    integration.
    Closed completed/pruned claim:
    `S2-agent-remainingRows-callback-source`
    (`019e41f7-2c21-7e83-a96e-068dba16271c`).  Result: added
    `rawFaceSuccOrbitRemainingSourceRows_of_edge_openSegment_frontier` and
    `S2_agent_remainingRows_callback_source`, shaping the callback consumed by
    `exists_rawFaceSuccOrbit_sourceRows_of_inputs` from edge-frontier,
    frontier-iff-tail, connectedness, local-sector, and repeated-tail rows.
    Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed read-only claim: `S2-agent-current-signature-audit`.
    Owner: `Averroes the 3rd` (`019e41f7-2d36-7032-8d49-0d7aadc0dcaf`).
    Result: confirmed the shortest live W32 hook can be a raw-orbit input-row
    adapter, and marked `S2-connected-closed-subset-graph-lemma`,
    `S2-agent-raw-period-source-assembler-alignment`, and the old
    `S2-agent-connectedRows-source` wording as completed or superseded by the
    checked raw-source/direct-connected assemblers.  No file edits.
    Closed completed claim: `S2-agent-exterior-seed-raw-source-package`
    (`019e41f0-66a3-7af3-a1a5-2c9878c8fa71`).  Result: added
    `RawFaceSuccOrbitRemainingSourceRows`, `RawFaceSuccOrbitSourceRows`,
    `unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbitSourceRows`, and
    `exists_rawFaceSuccOrbit_sourceRows_of_inputs`, packaging an unbounded
    exterior seed plus local-sector rows into the selected geometric raw
    face-successor orbit and the live raw source-row surface.  Verification:
    `lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    and `lake env lean ErdosProblems1066.lean` passed in the worker workspace.
    Closed completed claim: `S2-agent-geometric-boundary-successor-source`
    (`019e41ed-66ae-77c1-b35e-a53e821c4585`).  Result: added
    `BoundaryVertexAngularNoBetweenRows`,
    `BoundaryVertexAngularNoBetweenRows.toGeometricBoundarySuccessorRow`, and
    `geometricBoundarySuccessorRows_of_boundary_vertex_angularNoBetweenRows`
    in `Swanepoel/GeometricRotationSystem.lean`, sourcing
    `GeometricBoundarySuccessorRows C B` from per-boundary-vertex angular
    no-between rows.  Verification:
    `lake env lean ErdosProblems1066/Swanepoel/GeometricRotationSystem.lean`
    passed and
    `lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed with the existing simplifier warning.
    Closed completed claim: `S2-agent-bad-incident-arc-separation-source`
    (`019e41f0-665a-7780-98c7-36a69d007ac6`).  Result: added
    `boundaryCycleIncidentFrontierEdgeCompleteness_of_badIncidentEdge_repeatedBoundarySeparationRows`
    and refactored
    `boundaryCycleIncidentFrontierEdgeCompleteness_of_badIncidentEdge_arcSeparationRows`
    through that direct repeated-separation wrapper.  Verification:
    `lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed with the existing simplifier warning.
    Closed completed claim: `S2-agent-nearby-exterior-points-source`
    (`019e41f0-6702-7e22-86e0-cdba158b86ac`).  Result: added
    `unboundedFrontierEdgeSet_nearby_edge_point_exterior_points` and
    `rawFaceSuccOrbit_nearby_edge_point_exterior_points_of_unboundedFrontierEdgeSet_edges`,
    deriving the raw nearby-exterior-points row from actual
    `unboundedFrontierEdgeSet` membership in either orientation.  Verification:
    `lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed with the existing simplifier warning.
    Closed completed claim: `S2-agent-raw-edge-frontier-source`
    (`019e41ed-6568-7a02-81ea-5da240baecbc`).  Result: added
    `rawFaceSuccOrbit_source_inputs_of_dart_edge_openSegment_frontier` and
    `unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit_dartEdgeFrontier_sourceRows`,
    sourcing both raw edge-frontier inputs from a single dart-edge
    open-segment frontier row.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed claim: `S2-agent-frontier-vertex-iff-source`
    (`019e41ed-66fb-75c2-8f1a-62bfec2bee6f`).  Result: added
    `frontier_iff_boundaryCycle_vertex_of_cyclicCoverageRows` and
    `frontier_iff_boundaryCycle_vertex_of_rawFaceSuccOrbit_tail`, projecting
    cyclic/raw frontier equivalences to boundary-cycle vertex equivalences.
    Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed claim: `S2-agent-boundary-cycle-existence-source`
    (`019e41ed-651b-7351-bedf-55c9786ceeca`).  Result: added
    `exteriorFrontierCarrierRows_nonempty_of_rawFaceSuccOrbit_sourceRows`
    and
    `exists_unboundedExteriorFrontierCycleBoundary_of_rawFaceSuccOrbit_sourceRows`,
    projecting checked raw face-successor source rows into honest carrier rows
    and a genuine `UnitDistanceCycleBoundary` with exact unbounded exterior
    frontier vertex equivalence.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed claim: `S2-agent-source-gap-map`
    (`019e41ed-680f-7ad2-ac47-74d79bf833a1`).  Result: confirmed the current
    non-circular boundary-cycle source gap is either an input-only boundary
    source row containing `GeometricBoundarySuccessorRows`,
    frontier-iff-cycle, open-segment frontier, and incident completeness, or
    the sector-row variant with frontier-iff-cycle plus
    `BoundaryVertexExteriorSectorRowsAt`; also flagged circular raw-route
    traps.  No file edits were made by the explorer.
    Closed completed claim: `S2-agent-existing-lemma-harvest`
    (`019e41ed-68da-7cf3-b896-7633879b59e1`).  Result: confirmed the live S2
    proof should count source rows, not wrappers: `GeometricBoundarySuccessorRows`,
    `UnboundedFrontierCarrierCyclicCoverageRows`,
    `BoundaryCycleIncidentFrontierEdgeCompleteness`,
    `RepeatedExteriorBoundarySeparationRows`, and the raw
    `edge_frontier_point`/`nearby_edge_point_exterior_points` inputs are the
    proof-producing obligations; the surrounding `...sourceRows` and
    `exteriorFrontierCarrierRows_of_inputs` declarations are reducers.
    No file edits were made by the explorer.
    Closed completed claim: `S2-input-local-sector-family-source`.  Owner:
    Codex-main/local-sector-family integrator.  Scope:
    `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`; read-only use of
    `Swanepoel/GeometricRotationSystem.lean`.  Result: added
    `localSectorRows_of_vertex_star_isolation_angular_order`, an input-level
    family theorem producing
    `forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a` from a
    boundary-cycle frontier-vertex equivalence, consecutive open-segment
    frontier rows, and pointwise `bad_germ_between`/`no_between` angular rows,
    delegating the local content to
    `unboundedFrontierCarrierLocalSectorRowsAt_of_vertex_star_isolation_angular_order`.
    Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed; target-file forbidden-token scan clean; pinned root build
    `elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066` passed.
    Closed completed claim: `S2-raw-tail-coverage-from-closed-carrier`.
    Owner: Codex.  Scope: `Swanepoel/ExteriorComponentTopology.lean` and
    `TASK.md` coordination.  Result: added
    `rawFaceSuccOrbit_frontier_vertex_tail_coverage_of_connected_closed_carrier`,
    proving raw-tail coverage from consecutive raw edge frontier rows, closed
    carrier-neighbour propagation, and concrete carrier connectedness via
    `unboundedFrontierCarrierGraph_connected_of_cyclicCoverageRows`.
    Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed claim: `S2-agent-neighbor-tail-closure-route`
    (`019e41e5-5f53-7703-8730-3ce7ef453e17`).  Result:
    `neighbor_tail_closed` is not derivable from raw edge-frontier rows and
    local-sector rows alone; the minimal non-circular extra row is raw
    predecessor/successor tail separation at each raw orbit index.  The active
    implementation claim is now
    `S2-raw-neighbor-tail-closed-nonbacktracking`; no file edits were made by
    the explorer.
    Closed completed claim: `S2-agent-raw-neighbor-tail-closure-api`
    (`019e41e8-43e5-7de0-8901-a24cd4463447`).  Result: confirmed the proof
    should use `UnboundedFrontierCarrierLocalSectorRowsAt.neighbor_iff`,
    raw consecutive edge-frontier membership, and the explicit
    predecessor/successor nonbacktracking row; no file edits were made by the
    explorer.
    Closed completed claim: `S2-agent-workboard-claim-wording`
    (`019e41e8-4fc2-7342-a3cc-138be0a5bf44`).  Result: confirmed the
    nonbacktracking closure claim belongs before the other-thread connectedness
    claim and must explicitly exclude connectedness/raw-tail coverage ownership;
    no file edits were made by the explorer.
    Closed completed claim:
    `S2-raw-neighbor-tail-closed-nonbacktracking`.  Owner:
    `Codex-main/raw nonbacktracking neighbour-closure prover`.  Scope:
    `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`.  Result: added
    `rawFaceSuccOrbit_edge_mem_unboundedFrontierEdgeSet_or_symm`,
    `rawFaceSuccOrbit_tail_mem_unboundedFrontierVertexSet`, and
    `rawFaceSuccOrbit_neighbor_tail_closed_of_localSectorRows`, then rewired
    `unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit_sourceRows` to
    consume the explicit raw predecessor/successor tail-separation row directly
    instead of a separate neighbour-closure input.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed claim: `S2-raw-orbit-source-row-assembler`.  Owner:
    `Codex-main/exterior-boundary-cycle integrator`.  Scope:
    `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`.  Result: added
    `unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit_sourceRows`,
    bundling raw edge frontier propagation, connected closed-carrier tail
    coverage, period-three, no-cut tail injectivity, and raw frontier iff-tail
    into `UnboundedExteriorFrontierCycleRows C inputs`.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed claim: `S2-boundary-sector-to-cycle-reducer`.  Owner:
    `Codex-main/local-sector-family integrator`.  Scope:
    `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`.  Result: added
    `unboundedExteriorFrontierCycleRows_of_boundaryVertexExteriorSectorRows`,
    the direct reducer from an actual exterior boundary cycle plus
    per-vertex `BoundaryVertexExteriorSectorRowsAt` to
    `UnboundedExteriorFrontierCycleRows C inputs`.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed claim: `S2-agent-vertex-seed-source-refresh`
    (`019e41de-6029-7fd1-b696-5da0900792b6`).  Result: the existing theorem
    `seed_vertex_edgeInterior_frontier_point_of_localSectorRows`, or the
    packaged
    `exists_geometricRawFaceSuccOrbitSeed_of_unboundedExteriorFrontierSeed_localSectorRows`,
    is the shortest vertex-seed route; it needs the pointwise local-sector
    family and no file edits were made.
    Closed completed claim: `S2-agent-local-sector-family-refresh`
    (`019e41de-7088-7482-8685-ead9e6211939`).  Result:
    `localSectorRows_of_vertex_star_isolation_angular_order` is the direct
    constructor for the pointwise local-sector family once an actual boundary
    cycle, frontier equivalence, edge-frontier rows, and angular no-between
    rows are proved; no file edits were made.
    Closed completed claim: `S2-agent-raw-orbit-assembly-refresh`
    (`019e41de-7edc-7831-9495-c4af3b255689`).  Result: the shortest raw-orbit
    route is through
    `unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit`; the remaining
    raw source rows are tail coverage, edge frontier points plus nearby
    exterior propagation, and repeated-tail separation rows; no file edits were
    made.
    Closed completed claim: `S2-vertex-seed-interior-frontier`.  Owner:
    `Codex-main/vertex-seed prover`.  Scope:
    `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`; read-only use of
    `Swanepoel/FinitePlaneDrawing.lean`.  Result: added
    `frontier_vertex_incident_edgeInterior_frontier_point_of_localSectorRows`,
    `seed_vertex_edgeInterior_frontier_point_of_localSectorRows`, and
    `exists_geometricRawFaceSuccOrbitSeed_of_unboundedExteriorFrontierSeed_localSectorRows`,
    closing the vertex-seed interior-frontier handoff under explicit
    local-sector rows.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed superseded claim: `S2-main-frontier-carrier-proof`.  Owner:
    Codex-main.  Result: replaced by the sharper active claim
    `S2-exterior-boundary-cycle-source` and the five owner slots above.
    Closed completed claim: `S2-local-sector-source-from-star`.  Owner:
    Codex-local-sector.  Scope:
    `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`.  Result: added
    `exists_local_frontier_germ_two_of_vertex_star_isolation_and_angular_no_between`,
    `unboundedFrontierCarrierLocalSectorRowsAt_of_vertex_star_isolation_angular_order`,
    and
    `boundaryVertexExteriorSectorRowsAt_of_vertex_star_isolation_angular_order`,
    sourcing the pointwise two-germ/local-sector row from local vertex-star
    isolation plus a geometric angular-order exclusion.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed; target-file forbidden-token scan clean.
    Closed completed claim: `S2-raw-frontier-coverage-source`.  Owner: Codex.
    Scope: `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`;
    read-only use of local topology files.  Result: added
    `rawFaceSuccOrbit_frontier_iff_tail_of_frontier_vertex_tail_coverage`
    and `rawFaceSuccOrbit_frontier_iff_tail_of_cyclicCoverageRows`, proving
    the non-circular raw frontier-iff-tail row from actual raw edge-frontier
    rows plus exact coverage of every concrete unbounded-frontier carrier
    vertex by a raw face-successor tail.  Remaining source dependency:
    `forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      Exists fun k : Fin O.period => (O.dart k).tail = a.1`
    for the actual geometric exterior-seed raw orbit, or cyclic coverage rows
    pointwise identified with that raw tail sequence.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed; target-file forbidden-token scan clean.
    Closed completed claim: `S2-faceSucc-frontier-preservation`.  Owner:
    Codex.  Scope: `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`;
    read-only use of `Swanepoel/FinitePlaneDrawing.lean` and
    `Swanepoel/GeometricRotationSystem.lean`.  Result: added
    `BoundaryVertexExteriorSectorRowsAt.geometricFaceSucc_frontier_step`,
    proving that one primitive exterior-sector row carries the incoming
    predecessor edge on the actual unbounded-exterior frontier, sends its
    geometric `faceSucc` to the successor boundary dart, and carries that
    successor edge on the same actual frontier.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed claim: `S2-agent-boundary-cycle-api-refresh`
    (`019e41d9-3b3d-7093-b26c-aa940853220a`).  Result: confirmed the shortest
    API path is the complete boundary-cycle package
    `exists_unboundedFrontierCarrierBoundaryCycle_of_inputs` feeding
    `unboundedExteriorFrontierCycleRows_of_exists_boundaryCycle_complete`, with
    the raw face-successor orbit route as an equivalent source shape.
    Closed completed claim: `S2-agent-local-frontier-source`
    (`019e41d9-479d-7f31-9005-22a97dd5d34c`).  Result: identified the checked
    local edge/vertex isolation and frontier-propagation declarations; the
    remaining local source rows are exterior-sector production near raw orbit
    edges plus coverage of all frontier vertices by the selected raw orbit.
    Closed completed claim: `S2-agent-geometric-orbit-source`
    (`019e41d9-58d3-7cf2-bbb4-9db61b16f456`).  Result: confirmed the raw
    geometric face-successor orbit is already constructible from a local
    frontier-edge seed; the remaining source rows are period/nonrepeat,
    frontier-iff-tail, and open-segment frontier for that orbit.
    Closed completed claim: `S2-agent-board-consistency`
    (`019e41d9-6775-7231-85e4-f60d9bd8bb68`).  Result: refreshed the
    taskboard decomposition into five source-row owner slots and moved this
    scout out of active after its recommendations were consumed.
    Closed completed claim: `S2-raw-period-three`.  Owner: Codex.  Scope:
    `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`.  Result: added
    `rawFaceSuccOrbit_period_three_le_of_frontier_iff_tail_localSectorRows`,
    proving the exact honest source row for `3 <= O.period`: raw-orbit
    frontier coverage plus actual pointwise unbounded-frontier local-sector
    rows rule out the period-two bridge case.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed claim: `S2-raw-orbit-assembly`.  Owner: Codex.  Scope:
    `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`.  Result: added
    `unboundedExteriorFrontierCycleRows_of_checkedRawFaceSuccOrbitHandoffs`,
    bundling a raw orbit seed, `3 <= O.period`, repeated-pair separation rows
    for no-cut tail injectivity, face-orbit period/tail identification for
    frontier-iff-tail, and raw edge-open-segment frontier into
    `UnboundedExteriorFrontierCycleRows C inputs`.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed claim: `S2-raw-edge-frontier`.  Owner: Codex.
    Scope: `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`; read-only
    use of `Swanepoel/FinitePlaneDrawing.lean`.  Result: added
    `rawFaceSuccOrbit_edge_openSegment_frontier_of_inOpenSegment_frontier_and_nearby_edge_point_exterior_points`,
    the raw-orbit row that inhabits the `edge_openSegment_frontier` input of
    `unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit` from one
    interior frontier point and local nearby exterior points on each
    consecutive raw edge.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed; target-file forbidden-token scan clean.
    Closed completed claim: `S2-raw-orbit-seed`.  Owner: Codex.
    Scope: `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`.
    Result: added
    `exists_geometricRawFaceSuccOrbitSeed_of_unboundedExteriorFrontierEdgeLocalRows`,
    producing a geometric raw face-successor orbit seed whose start dart is
    exactly the selected local frontier edge.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed; target-file forbidden-token scan clean.
    Closed completed claim: `S2-raw-tail-no-repeat`.  Owner: Codex.
    Scope: `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`.
    Result: added the concrete raw face-successor orbit tail no-repeat helper
    `rawFaceSuccOrbit_tail_injective_of_noCutVertex`, routed the arc-row
    helper through it, and recorded the honest raw-period lower bound
    `rawFaceSuccOrbit_period_two_le`.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed; target-file forbidden-token scan clean.
    Closed completed claim: `S2-boundary-cycle-source`.  Owner: Codex.
    Result:
    `unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit` and
    `exists_unboundedExteriorFrontierCycleBoundary_of_rawFaceSuccOrbit`.
    Closed completed claim: `S2-actual-sector-inhabitance`.  Owner: Codex.
    Result:
    `boundaryVertexExteriorSectorRowsAt_of_actualExteriorSector`.
    Closed completed claim: `S2-raw-frontier-iff-tail`.  Owner: Codex.
    Scope: `Swanepoel/ExteriorComponentTopology.lean` and `TASK.md`.  Result:
    added `FaceDartOrbitExteriorCarrierRows.frontier_iff_rawFaceSuccOrbit_tail`,
    extracting the exact raw-orbit frontier equivalence from existing
    face-orbit carrier rows plus period/tail identification.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed claim: `S2-board-prune-completed`.  Owner: Codex.
    Scope: `TASK.md` only.  Status: closed after pruning completed S2 claims
    from active to closed/pruned.  Verification:
    `git diff --check -- TASK.md` passed.
    Closed completed claim: `S2-agent-api-scout`
    (`019e41c7-c033-7ae2-8afa-15844b7ef42f`).  Result: shortest reducer chain
    is a genuine boundary-cycle package through
    `cyclicCoverageLocalSectorRows_of_exists_boundaryCycle_complete` and
    `unboundedExteriorFrontierCycleRows_of_pointwise_cyclicCoverageLocalSectorRows`;
    no input-only carrier theorem exists yet.
    Closed completed claim: `S2-agent-local-topology-scout`
    (`019e41c7-c07d-77d1-8a8e-f49572e10e8c`).  Result: implement the local
    seed lemma turning arbitrarily close exterior points near an edge-interior
    point into a frontier point, then use the existing open-segment frontier
    propagation.
    Closed completed claim: `S2-agent-no-cut-scout`
    (`019e41c7-c0cb-78e3-9e24-4307ade815b4`).  Result: no-cut infrastructure is
    already sufficient once repeated exterior-boundary arc separation rows are
    supplied; do not duplicate it.
    Closed completed claim: `S2-agent-mathlib-scout`
    (`019e41c7-c11b-7df2-8e38-9905249eb8ff`).  Result: no Mathlib outer-face
    theorem directly applies; use local reducers after proving connectedness
    and degree two, or cyclic coverage plus local sector rows, for the actual
    carrier.
    Closed completed claim: `S2-agent-boundary-cycle-existence-scout`
    (`019e41cc-6688-7bd1-8fd1-d2e565d6e317`).  Result: target the stronger
    `exists_unboundedFrontierCarrierBoundaryCycle` package consumed by
    `cyclicCoverageLocalSectorRows_of_exists_boundaryCycle_complete`.
    Closed completed claim: `S2-agent-degree-two-carrier-scout`
    (`019e41cc-66d3-7451-a186-b9c3b042370f`).  Result: degree-two is already
    handled by local sector rows; add only a named bridge from
    `BoundaryVertexExteriorSectorRowsAt` if useful.
    Closed completed claim: `S2-agent-connected-carrier-scout`
    (`019e41cc-6721-7993-99ab-011e5c10c824`).  Result: connectedness should be
    produced as cyclic coverage from the raw exterior face-successor orbit.
    Closed completed claim: `S2-workboard-sync`.  Owner: Codex.  Scope:
    `TASK.md` only.  Status: closed after restoring TASK as the compact
    live workboard, adding the global claim rule, and preserving the S2 active
    claim/closed-claim split.  Verification:
    `git diff --check -- TASK.md` passed.
    Closed completed claim: `S2-W32-compile-fix`.  Owner: Codex.  Scope:
    `Swanepoel/FaceBoundaryTopologySourceW32.lean` and `TASK.md`.  Status:
    closed after exposing the target's implicit `n` binder locally and passing
    `rows (n := n) C hmin` at the actual-cycle-data handoff.  No W32 endpoint
    adapters or facade wrappers were added for this claim.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean`
    passed.
    Closed completed claim: `S2-edge-frontier-honesty`.  Owner: Codex.  Scope:
    `Swanepoel/ExteriorComponentTopology.lean`.  Status: summarized/closed.
    Next verification: no board-specific verification beyond the active
    `TASK.md` diff check; any future Lean claim must run its owner-file build.
    Useful result: the smallest checked theorem for actual edge-frontier
    honesty is
    `edge_openSegment_frontier_of_inOpenSegment_frontier_and_relative_ball_closure`;
    cycle/orbit handoffs should use
    `boundary_cycle_edge_openSegment_frontier_of_inOpenSegment_frontier_and_nearby_edge_point_exterior_points`,
    `cycle_edge_openSegment_frontier_of_inOpenSegment_frontier_and_nearby_edge_point_exterior_points`,
    or
    `faceDartOrbit_edge_openSegment_frontier_of_inOpenSegment_frontier_and_nearby_edge_point_exterior_points`,
    rather than a new S2 source package.
    Closed completed claim: `S2-edge-frontier-seed`.  Owner: Codex-main.
    Scope: `Swanepoel/ExteriorComponentTopology.lean`.  Status: closed after
    adding
    `canonicalEdge_inOpenSegment_frontier_of_exterior_points_arbitrarily_close`,
    the local seed bridge from arbitrarily close exterior points to an
    edge-interior frontier point.  Verification:
    `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
    passed.
    Closed completed claim: `S2-raw-orbit-no-cut-bridge`.  Owner: Codex-main.
    Scope: `Swanepoel/ExteriorComponentTopology.lean`.  Status: closed after
    adding `rawFaceSuccOrbit_tail_injective_of_noCutVertex_arcRows`, which
    specializes the existing no-cut repeat handoff to raw face-successor
    orbits.  Verification: owner-file Lean build passed.
    Closed completed claim: `S2-raw-orbit-cyclic-coverage`.  Owner:
    Codex-main.  Scope: `Swanepoel/ExteriorComponentTopology.lean`.  Status:
    closed after adding
    `unboundedFrontierCarrierCyclicCoverageRows_of_rawFaceSuccOrbit` and
    `unboundedFrontierCarrierGraph_connected_of_rawFaceSuccOrbit`, the
    connectedness half of the raw exterior orbit route.  Verification:
    owner-file Lean build passed.
    Closed completed claim: `S2-boundary-sector-degree-two`.  Owner:
    Codex-main.  Scope: `Swanepoel/ExteriorComponentTopology.lean`.  Status:
    closed after adding
    `unboundedFrontierCarrierGraph_degree_two_of_boundaryVertexExteriorSectorRows`,
    the degree-two bridge from primitive boundary-sector rows.  Verification:
    owner-file Lean build passed.
    Completed S2 scouts, prior broad pool entries, and supplemental spawned
    agents are closed as board history; their useful results are folded into
    the checked groundwork and concrete blocker list above.  Do not maintain a
    pending subagent pool here.
  - Assignment rule:
    New S2 implementation work must claim one concrete source obligation with
    owner, scope, status, and next verification before editing.  Keep write
    scopes disjoint and preserve the carrier honesty warnings above.

### S3. Angle And Subpolygon Packages

- [ ] Prove selected nondegenerate outer-face sector/order rows.
  - Paper steps: `E12-E13`.
  - Owners:
    `Swanepoel/OuterBoundaryAngleSourceW34.lean`,
    `Swanepoel/BoundaryCountingInstantiationW10.lean`,
    `Swanepoel/PlanarBoundaryFaceDataRefinement.lean`,
    `Swanepoel/SubpolygonSelectedGeometrySourceW34.lean`.
  - Live target:
    `OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem`
    for the S2 nondegenerate topology target.
  - Newest reduction: that single theorem projects to
    `SelectedTopologyLocalAngleGeometryRows`,
    `ActualSelectedBoundaryEuclideanAngleRows`, and
    `MinimalFailureActualOuterBoundaryAngleDataRows` through the checked
    W34/W10 accounting path.  The concrete accounting support theorem is
    `OuterBoundaryAngleSourceW34.selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_polygon_of_angleMassBudgets`,
    backed by
    `BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies.accountedAngleSum_le_polygon_of_angleMassBudgets`.
  - Next action: choose the selected `longArc` predicate and prove the local
    angle rows are ordered, disjoint outer-face sectors whose accounted mass is
    bounded by the simple-polygon interior-angle sum.  Subpolygon realization
    is already on the selected outer-face lane; do not add another adapter.
  - Latest exact projection:
    `selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_simpleOuterPolygonInteriorAngleSum_of_outerFaceSectorOrder`
    extracts the scalar inequality from
    `SelectedTopologyLocalAngleOuterFaceSectorOrderRows`.  The remaining fields
    are the honest sector angles, nonnegativity, local accounted-mass
    containment in the ordered sector sum, and the simple-polygon sector-sum
    bound.
  - Scalar-accounting bookkeeping:
    `OuterBoundaryAngleSourceW34.selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_generatedAccountedAngleSum`
    and
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_iff_exists_generatedAccountedAngleSum_le_simpleOuterPolygonInteriorAngleSum`
    are checked bookkeeping equivalences only.  Do not present the generated
    scalar inequality as the live S3 proof route.  The remaining S3 source is
    honest sector-containment, genuine triangulation, or genuine
    ear-decomposition angle-mass data.
  - Latest S2 adapter:
    `OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem`
    converts a proved honest
    `SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem` into the exact
    `RemainingActualCycleSkeletonRemainderRows` field required by W34 final
    assembly.
  - Newest positive sources:
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_angleMassBudgetedSectorRows`,
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_triangulationAngleMassBudgetRows`,
    and
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_earDecompositionAngleMassBudgetRows`
    are the current concrete S3 entrances.  Prove one honest sector/triangulation
    or ear-decomposition angle-mass package; do not add another scalar wrapper.
    The triangulation/ear packages now require
    `budgetSum_le_orderedOuterFaceSectorSum`, so the budget rows must fit
    directly inside the ordered outer-face sector sum before using
    `orderedOuterFaceSectorSum_eq_simpleOuterPolygonInteriorAngleSum`.
    The triangulation rows are currently inhabited from the generated scalar budget by
    `selectedNondegenerateTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRowsOfGeneratedAccountedAngleSum`
    and
    `nonempty_selectedNondegenerateTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows_of_generatedAccountedAngleSum_le_simpleOuterPolygonInteriorAngleSum`.
    Treat these as scalar bookkeeping helpers only: they concentrate the whole
    polygon angle sum into one sector and use formal constant-angle triangles,
    so they must not be credited as an honest E12/E13 proof.
    Preferred current entrance:
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_sectorContainmentRows`.
    It uses `SelectedTopologyLocalAngleOuterFaceSectorContainmentRows`, where
    generated local angle slots are assigned to selected outer-face sectors and
    per-sector loads are bounded directly.  Populate those sector-containment
    rows rather than reviving the arbitrary generated-witness scalar route.
    The honest missing row is actual outer-face sector angles at each selected
    boundary vertex, Swanepoel cyclic unit-neighbor gaps for the generated
    local slots, correct per-slot sector assignment, per-sector load
    containment, and the real polygon angle-sum theorem.
    Subpolygon bookkeeping is not the current blocker:
    `SubpolygonSelectedGeometrySourceW34.planarBoundaryFaceDataOfMinimalFailureSelectedClassification_subpolygonData_eq_realizationFamily`
    identifies the skeleton subpolygon-data projection with the selected
    outer-face W33 realization family, and
    `selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields_lowDegreeWithHighDegreeSlack`
    exposes the E13 high-degree slack row from that family.
    The clean honest sector route should pass through
    `SelectedTopologyActualBoundaryNeighborSectorContainmentRows`; its existing
    converter fills the generic budget rows by the actual local angle values.
    The sector angle source is the predecessor/current/successor boundary
    angle, available via
    `BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex`
    or the `BoundaryWalkBridge` predecessor/successor angle rows.  The missing
    S3 content is therefore the six slot-to-sector maps, per-sector load
    containment into those actual PCS angles, and the real polygon sector-sum
    bound.
    Newest checked S3 reduction:
    `selectedBoundaryDegree3SlotSectorOfIndex`,
    `selectedBoundaryDegree4SlotSectorOfIndex`,
    `selectedBoundaryDegree5SlotSectorOfIndex`,
    `selectedBoundaryDegree6SlotSectorOfIndex`,
    `selectedBoundaryNontriangleSlotSectorOfIndex`, and
    `selectedBoundaryLongArcSlotSectorOfIndex` assign all generated slots to
    the same actual boundary-index sector.  The compact entrance is now
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexSectorRows`.
    The remaining honest S3 inputs are exactly the pointwise
    `selectedBoundaryIndexSectorLoad <= actualBoundaryNeighborSector` row and
    the actual PCS boundary-sector angle-sum bound by the simple-polygon
    interior-angle sum.
    W10 now exposes that second input as an honest row package:
    `BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows`,
    with `boundaryCyclePolygonAngleSum` matching the selected-topology
    cycle-length polygon sum.  `BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndex`
    builds the package from canonical predecessor/current/successor boundary
    sectors once the genuine polygon sector-sum inequality is proved.  The
    remaining S3 geometric inequality is therefore the local pointwise
    sector-load bound, plus the still-genuine proof of the PCS sector-sum
    inequality for the simple outer polygon.
    W34 adapter now available:
    `boundaryNeighborSectorAngleSumRows_le_simpleOuterPolygonInteriorAngleSum`
    and
    `selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfBoundaryIndexSectorsAndAngleSumRows`
    consume W10's `BoundaryNeighborSectorAngleSumRows` directly on the selected
    topology route.  The remaining local S3 source is the pointwise
    `selectedBoundaryIndexSectorLoad <= actualBoundaryNeighborSector` proof.
    Newest W10 polygon-angle bridge:
    `ClassifiedBoundary.simplePolygonInteriorAngleAt` and
    `simplePolygonInteriorAngleSum` spell the actual PCS interior-angle sum.
    `BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndexOfSimplePolygonInteriorAngleSum`
    constructs W10 sector-sum rows from the genuine theorem
    `simplePolygonInteriorAngleSum P <= boundaryCyclePolygonAngleSum P`.
    This is the exact polygon-angle theorem still needed on the selected outer
    cycle; no generated scalar budget closes it.
    Newest W10 sector/polygon accounting:
    `triangulationAngleSum_eq_boundaryCyclePolygonAngleSum`,
    `simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum_of_triangulationAngleSum`,
    `BoundaryNeighborSectorAngleSumRows.boundarySector_value_eq_simplePolygonInteriorAngleAt`,
    `.sectorAngleSum_eq_simplePolygonInteriorAngleSum`, and
    `.ofOuterBoundaryCoreIndexOfTriangulationAngleSum`.  Remaining W10-facing
    S3 input is genuine triangulation angle-sum data and the matching
    boundary-sector equality for the selected topology rows.
    Newest S3 gap-decomposition source:
    `SelectedTopologyBoundaryCyclicNeighborGapRows` is the explicit row package
    for the missing pointwise load proof.  It carries, per boundary vertex, the
    neighbor interval from boundary predecessor to successor, consecutive gap
    angles, generated-slot-to-gap maps, slot value equalities,
    slot-load-to-gap-sum, and gap-sum-to-PCS-sector inequalities.  It feeds the
    current S3 route through
    `selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfCyclicNeighborGapRowsAndAngleSumRows`
    and
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_cyclicNeighborGapRowsAndAngleSumRows`.
    The remaining positive S3 work is honest construction of these cyclic
    neighbor gap rows from planar unit-neighbor order geometry.
    Newest S3 interval source:
    `SelectedTopologyBoundaryCyclicNeighborIntervalRows` reduces the gap-row
    package to an ordered unit-neighbor interval.  The consecutive
    `UnitSeparatedAngle` gap witnesses are now constructed from
    `neighbor_unit` plus `neighbor_injective` by
    `SelectedTopologyBoundaryCyclicNeighborIntervalRows.toCyclicNeighborGapRows`.
    The final S3 constructor
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_cyclicNeighborIntervalRowsAndAngleSumRows`
    consumes these interval rows plus W10 sector-sum rows.  The remaining
    honest S3 theorem is construction of the interval rows from real planar
    cyclic unit-neighbor order data, including slot-to-gap value equalities,
    load-to-gap-sum, and gap-sum-to-PCS-sector inequalities.
    Newest per-index source:
    `SelectedBoundaryIndexCyclicNeighborIntervalRows` and
    `SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows` localize that
    obligation at each selected boundary index; their `.toIntervalRows`
    projection builds the global interval rows.  The exact remaining S3 source
    is now the real ordered unit-neighbor interval from boundary predecessor
    to successor at each boundary vertex.
    Latest interval-to-sector bridge:
    `SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows.toCyclicNeighborGapRows`,
    `.sectorLoad_le_boundarySectorAngle`,
    `.toActualBoundaryNeighborSectorContainmentRowsAndAngleSumRows`,
    `.toLocalAngleOuterFaceSectorOrderRowsAndAngleSumRows`, and
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndAngleSumRows`
    connect per-boundary-index interval rows plus W10 sector-sum rows to the
    live sector-order theorem.  Remaining S3 work is actual interval rows,
    matching `BoundaryNeighborSectorAngleSumRows`, and `boundarySector_eq`.
    The generic interval constructor is now
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndBoundaryNeighborSectorAngleSumRows`,
    and `actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex_sectorAngleSum_eq_simplePolygonInteriorAngleSum`
    removes the remaining explicit `boundarySector_eq` input.  The
    triangulation variant builds W10 rows via
    `BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndexOfTriangulationAngleSum`.
    Newest canonical S3 constructor:
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndSimplePolygonInteriorAngleSumRows`
    builds the W10 sector rows canonically from the genuine simple-polygon
    interior-angle inequality and discharges `boundarySector_eq` by `rfl`.
    Remaining S3 inputs are now actual boundary-index cyclic-neighbor interval
    rows and the genuine simple-polygon interior-angle inequality.
    Latest triangle-point S3 constructor:
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndSelectedOuterBoundaryNondegenerateTrianglePointRows`
    and the source-row variant consume selected outer-boundary nondegenerate
    triangle-point rows directly.  Remaining S3 inputs are actual interval
    rows and selected triangle-point rows.
    S3 source rows are now split as
    `SelectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows` and
    `SelectedNondegenerateTopologySimplePolygonInteriorAngleSumRows`, with
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalSourceRowsAndSimplePolygonInteriorAngleSumRows`
    as the canonical constructor.  The simple-polygon row is supplied by
    triangulation rows through
    `selectedNondegenerateTopologySimplePolygonInteriorAngleSumRowsOfTriangulationRows`.
    `PlanarBoundaryFaceDataRefinement.SelectedOuterBoundaryNondegenerateTrianglePointRows.ofCorePolygonTriangleVertices`
    now constructs the selected nondegenerate triangle-point rows from distinct
    triangle corners in the actual core outer cycle, proving the side vector is
    nonzero internally.  Do not rebuild this point-distinctness argument in S3;
    focus workers on the interval rows and the polygon angle-sum/triangulation
    source.
    `AngleGeometry.gapAngleSum_eq_sectorAngle_of_realAngle_eq_no_wrap` and
    `gapAngleSum_le_sectorAngle_of_realAngle_eq_no_wrap` are checked helpers
    for the last inequality: once cyclic order/no-crossing supplies the
    oriented `Real.Angle` telescope and the no-wrap bounds, they turn the
    telescope into the real-valued sector inequality required by the interval
    rows.  The remaining geometry is the oriented telescope and no-wrap proof,
    not another scalar accounting bridge.
    `AngleGeometry.oangle_sum_range_succ_eq_oangle` and
    `gapAngleSum_eq_sectorAngle_of_oangle_chain_no_wrap` now discharge the
    algebraic telescope once each consecutive gap is identified with the
    oriented angle between successive nonzero rays and the sector is identified
    with the first-to-last oriented angle.  S3 still must prove the actual
    cyclic-order/no-wrap hypotheses from planar neighbor order.
    Newest AngleGeometry support also includes Nat and `Fin (m + 1)` chain
    no-wrap equality/inequality forms plus concrete `angleAt` neighbor-chain
    lemmas shaped for downstream `UnitSeparatedAngle.value` goals.  The
    remaining S3 geometry is now the real planar neighbor-order/no-wrap input,
    not algebraic telescope manipulation.
    `BoundaryWalkBridge.EndpointNeighborInterval` supplies the honest
    endpoint-only interval data: predecessor first, successor last, adjacency
    to the center, and injectivity for length at least three.  The missing
    interval data is the full ordered unit-neighbor enumeration between those
    endpoints and the slot-to-gap/angle-sum fields.
    `OuterBoundaryAngleSourceW34` now has boundary-data row carriers based on
    `OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval`, with
    `selectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows_of_boundaryDataRows`
    projecting them into the selected-nondegenerate interval target.  The live
    S3 interval source is construction of those boundary-data endpoint/ordered
    neighbor rows from the actual outer boundary, not another interval adapter.
    `SelectedBoundaryIndexOrderedUnitNeighborData` and
    `SelectedBoundaryIndexCyclicNeighborSlotToGapRows` are the newest explicit
    boundary-index row surfaces: the first records the ordered cyclic
    unit-neighbor list, endpoints, unit proofs, and injectivity, and the second
    records the class-slot to consecutive-gap identifications and load/gap
    inequalities.  These feed the existing interval route; the remaining work
    is proving the real ordered unit-neighbor list and slot-to-gap geometry,
    not adding another carrier type.
    `OuterBoundaryAngleSourceW34` now consumes those two boundary-index rows
    directly, projecting them through actual/local sector-containment rows into
    `SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem`.  Do not add
    more S3 sector-containment wrappers; prove the ordered-neighbor and
    slot-to-gap rows or a real planar-cyclic-order source for them.
    `OuterBoundaryCoreConstructionW28` now constructs
    `EndpointNeighborInterval` with `gapCount = 1` from any nondegenerate
    boundary cycle, `OuterBoundaryCore`, source-with-length rows,
    actual-cycle data, or chosen Jordan outer-component rows.  The remaining S3
    boundary-order fact is the full ordered unit-neighbor/slot-to-gap data:
    cyclic neighbor list, class-slot maps, angle-value equalities,
    `slotLoad_le_gapAngleSum`, and `gapAngleSum_le_boundarySectorAngle`.
    `OuterBoundaryCoreConstructionW28.BoundaryIndexOrderedUnitNeighborData`
    is now the import-acyclic W28 endpoint-backed carrier and has constructors
    from boundary cycles, outer cores, source-with-length rows, actual-cycle
    data, and chosen Jordan rows.  It is positive endpoint data only; W34 still
    needs the full ordered unit-neighbor enumeration and slot-to-gap geometry.
    `PlanarBoundaryFaceDataRefinement.SimplePolygonInteriorAngleTriangulationRows`
    reduces the genuine simple-polygon angle bound to real triangulation rows:
    `length - 2` triangles, each with `angleAt` sum `pi`, and equality between
    polygon PCS angles and triangle-corner angles.  Construct these rows from
    a real triangulation or ear decomposition of the selected outer polygon.
    `PlanarBoundaryFaceData.SimplePolygonInteriorAngleTriangulationRows.ofNondegenerateTrianglePoints`
    now discharges each triangle's `pi` angle-sum from actual triangle corner
    points plus one nonzero side vector.  The remaining triangulation source is
    therefore the actual triangle-point/ear-decomposition data and polygon
    angle compatibility.
    `PlanarBoundaryFaceDataRefinement.SelectedOuterBoundaryNondegenerateTrianglePointRows`
    is the selected outer-boundary version of that source; its projections
    `toSimplePolygonInteriorAngleTriangulationRows`,
    `simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum`, and
    `toBoundaryNeighborSectorAngleSumRows` feed the W10/S3 angle route from
    actual triangle points plus nonzero side data.
    `SelectedOuterBoundaryCorePolygonTriangulationRows` is now the strongest S3
    triangulation source: actual indexed outer-cycle triangle vertices,
    nondegenerate side data, and PCS polygon-angle compatibility.  It projects
    to selected nondegenerate triangle-point rows, honest triangulation rows,
    the pointwise `simplePolygonInteriorAngleSum <= boundaryCyclePolygonAngleSum`
    row, and W10 boundary-neighbor sector rows.  Remaining S3 work is positive
    construction of these triangulation rows and the endpoint/ordered-neighbor
    interval rows from the actual outer boundary.
    `SelectedOuterBoundaryCorePolygonEarDecompositionRows` is the newest
    ear-decomposition source in `PlanarBoundaryFaceDataRefinement`: it records
    actual ear triangles on the selected outer cycle, the `length - 2` count,
    nondegenerate side data, and PCS polygon-angle compatibility, and projects
    to the selected triangulation rows.  Remaining S3 triangulation work is
    honest construction of these ear rows from the simple outer polygon.
    `PlanarBoundaryFaceDataRefinement` now also carries actual indexed
    triangulation/ear angle fields (`triangleAngle`, `earAngle`), nonnegativity,
    and per-triangle/per-ear angle-sum-to-`pi` rows, and its W10 sector-sum
    constructors route directly through those real angle rows.  The import
    cycle still makes W34 the downstream consumer; the remaining source is an
    honest ear decomposition/triangulation of the selected outer polygon.
    `SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows`
    is the native subpolygon version of the same triangulation obligation,
    avoiding an import cycle with `PlanarBoundaryFaceDataRefinement`.  It
    exposes actual triangle points, `AngleGeometry.angleAt` corner sums,
    boundary predecessor data, equality between boundary interior-angle sum and
    triangle-angle sum, and compatibility with the E13 degree-count total.
    `SubpolygonDataConcrete.CoreOuterBoundaryInteriorAngleTriangulationRows`
    is the upstream outer-core package equivalent to the downstream W10
    polygon-angle rows.  Its
    `.ofConcreteSubpolygonInteriorAngleTriangulationRows` bridge connects the
    native subpolygon triangulation surface to the selected outer-core sector
    sum route without reversing imports.
    `SubpolygonDataConcrete` now also supplies
    `CoreSubpolygonAngleData.ofConcreteSubpolygonInteriorAngleTriangulationRows`,
    `CoreSubpolygonAngleData.lowDegreeWithHighDegreeSlack_ofConcreteSubpolygonInteriorAngleTriangulationRows`,
    and matching `CoreFaceSubpolygonAngleData` constructors.  Remaining
    subpolygon work is genuine triangulation and boundary-angle-sum input, not
    another E13 consumer.
  - Compile status:
    `OuterBoundaryAngleSourceW34` builds with the pinned toolchain after the
    recursive finite-sum simplification loops were replaced by explicit
    `change`/`rw`/`Finset.sum_le_sum` proofs.  This is compile progress only;
    the honest S3 obligation remains a genuine sector-containment,
    triangulation, or ear-decomposition angle-mass source.

### S4. Missing Long-Arc/Triangle-Run Field, Lemma 6/7, And Lemma 9 Rows

- [ ] Inhabit the exact boundary missing field for the S2/S3 skeleton.
  - Paper steps: long-arc and thirteen-edge triangle-run material in
    `E14-E21`.
  - Owners:
    `Swanepoel/JordanBoundaryConcreteInhabitationW24.lean`,
    `Swanepoel/LongArcExistenceConcrete.lean`,
    `Swanepoel/BoundaryArcFiniteWalkConstructionW16.lean`,
    `Swanepoel/TriangleRunSelectorW17.lean`.
  - Live target:
    `SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField`
    for the `MinimalBoundaryTopologySkeletonFamily` produced by S2/S3; rowwise
    this is
    `MinimalBoundaryTopologySkeleton.MissingLongArcTriangleRunField`.
  - Next action: prove the concrete
    `LongArcExistenceConcrete.BoundaryLongArcExistenceFields` and
    `BoundaryArcTriangleRun` over the skeleton's `planarBoundary`.  Do not
    resurrect older separate "missing long arc" or "triangle run" route names
    except as compatibility aliases in Lean comments/docs.
  - Latest non-circular finite-`p/q` integration:
    `BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem`
    is now the explicit theorem surface that supplies cyclic-successor rows
    for arbitrary topology/angle/subpolygon/long-arc rows.  W17, W24, and W33
    route this theorem to
    `MinimalBoundaryTopologyMissingLongArcTriangleRunField`; in particular use
    `SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfRemainingActualCycleSkeletonRowsFinitePQSpineCyclicSuccessorRowsTheorem`
    once the W34 skeleton long-arc family is available.  Do not use
    `FrameCyclicOrderAssemblyW32.selectedFinitePQSpineCyclicSuccessorRowsSourceFamilyOfActualTopologyClosureGeneratedOrderRows`
    to build this missing field, because that theorem is keyed to the
    `componentClosure` produced only after the missing field is supplied.
    The next real source field is the skeleton-level
    `MinimalBoundaryTopologyLongArcFieldFamily`.
  - Latest skeleton closure bridge:
    `SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem`
    constructs the actual topology closure package from S2/S3 skeleton rows,
    `MinimalBoundaryTopologyLongArcFieldFamily`, and the W16 finite-`p/q`
    cyclic successor theorem.  The remaining honest S4 missing-field work is
    therefore the long-arc family plus the W16 finite-`p/q` theorem.
    The W16 theorem is now produced from a uniform finite boundary-walk source
    by
    `BoundaryArcFiniteWalkConstructionW16.finitePQSpineCyclicSuccessorRowsTheorem_of_finiteWalkTheorem`.
    Newest W16 pointwise extraction:
    `BoundaryArcFiniteWalkConstructionW16.finitePQSpineCyclicSuccessorRowsTarget_of_frameCoreTarget`
    turns a `BoundaryArcFiniteWalkFrameCoreTarget` directly into the W16
    finite-`p/q` successor-row target, using its concrete finite walk and
    frame-core fields only.  The remaining finite-walk payload is now a real
    `Nonempty BoundaryArcFiniteWalkFrameCoreData` for the selected skeleton.
    Latest W16 certificate adapters:
    `finitePQSpineCyclicSuccessorRowsOfBoundaryArcCertificate`,
    `finitePQSpineCyclicSuccessorRowsOfBoundaryArcFrameCoreFields`,
    `finitePQSpineCyclicSuccessorRows_nonempty_of_frameCoreData`,
    `finitePQSpineCyclicSuccessorRowsTarget_of_boundaryArcCertificate`, and
    `finitePQSpineCyclicSuccessorRowsTarget_of_boundaryArcFrameCoreFields`
    route boundary-arc certificate/frame-core fields into the finite-`p/q`
    target.  Remaining work is to construct those actual boundary-arc
    certificate/frame-core fields from the selected boundary spine.
    Latest finite-spine raw-fact constructors:
    `BoundarySpineFiniteCertificate.M8BoundaryCorePQSpineRows.ofCyclicOrder_pIndex`,
    `.ofCyclicOrder_q`, `.ofCyclicOrder_edgeIndex`,
    `.finitePQSpineCertificateOfCyclicOrder_pIndex`, and the analogous
    `M8BoundaryWalkPQSpineRows.ofCyclicOrder*` plus
    `frameCoreFieldsOfRawFacts` / `rawFactsOfFrameCoreFields` conversions
    expose the selected finite spine as raw cyclic-order/frame-core data.
    Use these in generated-order and W16 source construction; do not rebuild
    finite-spine raw facts elsewhere.
    Boundary-spine also now exposes explicit finite-spine source packages:
    `M8FinitePQSpineCertificate.ExplicitCyclicOrderRows`,
    `M8FinitePQSpineRawFrameCoreFacts`, and
    `M8FinitePQSpineExplicitFrameCoreSource`, with conversions to/from
    `M8FinitePQSpineFrameCoreFields` and projection to
    `M8FinitePQSpineBoundaryArcFrameCoreFields`.  Use this source when feeding
    W16 or generated-order rows.
    Boundary-spine now also exposes upstream boundary-arc fields:
    `M8FinitePQSpineBoundaryArcCertificateFields`,
    `M8FinitePQSpineCertificate.toBoundaryArcCertificateFields`,
    `M8FinitePQSpineBoundaryArcFrameCoreFields`,
    `M8FinitePQSpineCertificate.toBoundaryArcFrameCoreFields`, and the core /
    walk `boundaryArcCertificateFieldsOfCyclicOrder` /
    `boundaryArcFrameCoreFieldsOfRawFacts` constructors.  Downstream W16 work
    should consume these fields rather than rebuilding them.
    W16 now has an import-safe raw finite-spine bridge:
    `finitePQSpineCyclicSuccessorRowsOfRawFinitePQFacts`,
    `finitePQSpineCyclicSuccessorRowsOfRawFinitePQFacts_val`, and
    `finitePQSpineCyclicSuccessorRowsTarget_of_rawFinitePQFacts`.
    W16 also consumes the upstream boundary-spine fields directly via
    `boundaryArcCertificateOfFinitePQSpineBoundaryArcCertificateFields`,
    `boundaryArcCertificateOfFinitePQSpineBoundaryArcFrameCoreFields`,
    `finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcCertificateFields`,
    `finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcFrameCoreFields`,
    and the matching `finitePQSpineCyclicSuccessorRowsTarget_of_*` theorems.
    W16 theorem-level source surfaces are now available:
    `FinitePQSpineBoundaryArcCertificateFieldsTheorem` and
    `FinitePQSpineRawFinitePQFactsTheorem`; both reduce to
    `FinitePQSpineCyclicSuccessorRowsTheorem`.  The raw route preserves the
    frame-core raw facts needed later for generated-order rows.  Remaining W16
    work is positive inhabitation of one of these source theorems, not another
    W16 bridge.
    W16 now has direct positive constructors from finite-walk or triangle-run
    data:
    `finitePQSpineBoundaryArcCertificateFieldsOfFiniteWalkData`,
    `finitePQSpineBoundaryArcCertificateFieldsOfTriangleRun`,
    `finitePQSpineBoundaryArcCertificateFieldsTheorem_of_finiteWalkDataTheorem`,
    and `finitePQSpineBoundaryArcCertificateFieldsTheorem_of_triangleRunTheorem`.
    Remaining W16 input is therefore an actual finite-walk theorem or triangle
    run theorem for the selected skeleton.
  - Latest long-arc source:
    `MinimalBoundaryTopologyLongArcRawTurnRows` feeds
    `MinimalBoundaryTopologyLongArcFieldFamily`.  The remaining honest long-arc
    blocker is the raw row package: `d3 <= negativeCount + card longArcIndices`
    for the skeleton boundary, plus raw-turn nonnegativity and threshold
    interpretation.
    Lemma6/Lemma7 coverage already supplies the count inequality through
    `longArcRawTurnRowsOfGapNegativeCoverageDataAndRawTurns` or
    `longArcRawTurnRowsOfBoundaryWalkGapNegativeCoverageOutputsAndRawTurns`.
    Checked W24 bridge:
    `longArcFieldFamilyOfBoundaryLongArcGapNegativePackages` composes W13
    `BoundaryLongArcGapNegativePackage` families and a carrier equivalence into
    the live long-arc family; with the W16 theorem,
    `missingFieldOfBoundaryLongArcGapNegativePackagesFinitePQSpineCyclicSuccessorRowsTheorem`
    produces the skeleton missing field.  Remaining inputs are the actual
    package family on the selected skeleton, the equivalence to concrete
    `longArcIndices`, and the W16 finite-`p/q` theorem.
    The remaining positive long-arc content is an honest
    `rawTurn : longArcIndices -> Nat -> Real` and its nonnegativity on the
    selected arc; Lemma9 is downstream and does not construct raw turns.
    `JordanBoundaryConcreteInhabitationW24.longArcRawTurnRowsOfBoundaryLongArcGapNegativePackages`
    now builds the skeleton raw-turn rows from W13
    `BoundaryLongArcGapNegativePackage` families using the package's real
    `rawTurn` and Lemma6/Lemma7 coverage.  This is a non-circular bridge only:
    the live missing source is still construction of genuine raw turns from
    boundary geometry.
    Checked W13 source closure:
    `boundaryLongArcGapNegativePackageOfBoundaryWalkGapNegativeCoverageOutputAndRawTurns`
    and
    `boundaryLongArcGapNegativePackageOfGapNegativeCoverageDataAndRawTurns`
    build the package family from Lemma6/Lemma7 coverage plus the actual
    classified `longArcIndices` raw-turn rows.  The remaining positive input is
    still the honest raw-turn family and its nonnegativity; the boundary-walk
    output route also needs the count equality identifying the output's
    `longArcCount` with `card longArcIndices`.
    The existing honest raw-turn source type is
    `BoundaryAngleTurnW11.UDConfigRoute.BoundaryAngleTurnTopologyPackage.MinimalBoundaryTopologyBoundaryTurnAngleRows`;
    its `rawTurn` is the value of real `UnitSeparatedAngle` witnesses on the
    thirteen turn slots, and `toLongArcRawTurnRows` /
    `toLongArcFieldFamily` already route those rows into the W24 long-arc
    family.  The missing geometry is to inhabit that W11 row package: actual
    `turnVertex`, `turnAngle`, and predecessor/center/successor equalities for
    each selected long arc and turn slot.
    Newest W11 constructor:
    `MinimalBoundaryTopologyBoundaryTurnAngleRows.ofOuterBoundaryTurnVertex`
    constructs the actual `UnitSeparatedAngle` turn rows once a per-long-arc,
    per-slot outer-cycle vertex map is supplied.  The remaining positive map is
    a family
    `classification.longArcIndices -> Nat -> Fin outerCycle.length` naming the
    boundary vertex where each raw turn slot is measured; the existing single
    triangle-run `pIndex` does not yet supply this uniformly for all long arcs.
    Newest W11 triangle-run source:
    `MinimalBoundaryTopologyBoundaryTurnVertexRows.ofTriangleRun` and
    `MinimalBoundaryTopologyBoundaryTurnAngleRows.ofTriangleRun` provide that
    per-long-arc/per-slot map from the established M8 triangle-run indexing,
    using `BoundaryArcIndexMap.m8BoundaryIndexOfNat` for slots `1..13`.  The
    live W11/W13 integration task is now to feed the available triangle-run
    theorem plus Lemma6/Lemma7 count coverage into the W24 long-arc family for
    the selected skeleton.
    `TriangleRunSelectorW17.ExplicitM8TriangleRunIndices` is the explicit
    triangle-run source surface: construct the actual boundary indices
    `p_0, ..., p_13`, prove the 13 cyclic-successor rows, and prove the 13
    `IsTriangleEdge` rows.  `triangleRunTheorem_of_explicitM8TriangleRunIndicesTheorem`
    then feeds the existing triangle-run theorem.
    `ExplicitM8TriangleRunIndices` now exposes concrete projections `p0`
    through `p13`, `cyclicOrder0` through `cyclicOrder12`, and `triangleEdge0`
    through `triangleEdge12`.  Use those named row projections when proving
    W11 turn-angle rows or W16/raw finite-spine facts; do not add another
    triangle-run unpacking layer.
    W17 now reduces `ExplicitM8TriangleRunIndicesTheorem` from the existing
    triangle-run theorem, extraction targets, finite-walk data, finite-`p/q`
    successor rows, boundary-arc certificate fields, or raw finite-`p/q` facts,
    with `explicitM8TriangleRunIndicesTheorem_iff_triangleRunTheorem` as the
    main equivalence.  W11/W16 workers should consume these reductions rather
    than re-proving the named `p0..p13` surface.
    The classified Lemma 6 obstruction specialization
    `boundaryLongArcGapNegativePackageOfLemma6ObstructionAndRawTurns`
    discharges that count equality internally via `counts_B`.
    Newest W13/W24 integration:
    `Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcRawTurnRows`
    and `BoundaryLongArcGapNegativeRows` are the cycle-safe row interface
    between W11-style turn rows and W13 gap packages.
    `boundaryLongArcGapNegativePackageOfLemma6ObstructionAndRawTurnRows`
    packages Lemma6/Lemma7 coverage with raw-turn rows into the exact W13
    package, and
    `JordanBoundaryConcreteInhabitationW24.longArcFieldFamilyOfTurnRowsAndBoundaryLongArcGapNegativePackages`
    routes W11 turn rows plus W13 packages into the W24
    `MinimalBoundaryTopologyLongArcFieldFamily`.
    Latest W13 bridge:
    `BoundaryLongArcRawTurnRows.ofRawTurns`,
    `BoundaryLongArcGapNegativeRows.ofCoverageOutputAndRawTurns`, and
    `BoundaryLongArcGapNegativeRows.ofLemma6ObstructionAndRawTurns` preserve
    the selected `longArcIndices`, route
    `longArcCount = card longArcIndices = counts.B`, keep the supplied raw
    turns, and preserve nonnegativity.  There is no remaining W13 count/card
    blocker; the external source is W11 turn-angle/raw-turn geometry.
    `LongArcExistenceConcrete.BoundaryLongArcTurnAngleRows` now provides that
    raw-turn interpretation layer: `rawTurn a k` is the actual
    `UnitSeparatedAngle.value` on `turnIndexSet` and `0` off it, with
    nonnegativity from `UnitSeparatedAngle.value_nonnegative` and projection to
    `BoundaryLongArcCarrierRawTurnRows` preserving the carrier, `card = B`, and
    Lemma6/Lemma7 count row.  Remaining long-arc source is construction of
    these turn-angle rows from the actual selected boundary turns.
    `BoundaryAngleTurnW11` now connects the W11 turn-angle package to W13 raw
    turns via `BoundaryLongArcRawTurnRows.ofRawTurns`, routes the W24 raw rows
    through that adapter, and supplies the explicit-triangle-run theorem bridge
    into the `ofTriangleRun` constructor.  No boundary-vertex/turn-angle
    equality rows remain for this W11 route.
    `BoundaryAngleWitnessConstruction` now exposes cycle-safe constructors for
    canonical boundary predecessor/current/successor witnesses, explicit triple
    witnesses requiring exactly the two cyclic-successor equalities, and
    pointwise long-arc/turn-slot witness families matching
    `BoundaryLongArcTurnAngleRows.turnAngle` and S5 actual-turn consumers.
    Use these constructors rather than reproving boundary-index equalities.
    `LongArcExistenceConcrete.BoundaryLongArcTurnAngleRows.ofOuterBoundaryCoreTurnVertex`
    now imports those witness constructors and builds actual W11 turn-angle
    rows from selected boundary turn vertices; `carrierRawTurnRowsOfOuterBoundaryCoreTurnVertex`
    projects the corresponding carrier/raw-turn rows with the actual angle
    value on turn slots.  W13 also has
    `boundaryLongArcGapNegativePackageOfGapNegativeCoverageDataAndRawTurnRows`
    and `longArcExistenceFieldsOfGapNegativeCoverageAndRawTurnRows`, so actual
    raw-turn rows plus `GapNegativeCoverageData` now build the W13
    package/fields directly.
    W24's gap-negative and no-boundary-gap missing-field sources already consume
    W13 packages plus the W16 theorem; the latest cleanup reuses
    `toBoundaryLongArcCarrierRawTurnRows` directly.  The live long-arc blocker
    remains the genuine W11/W13 raw-turn package and W16 source, not W24
    plumbing.
    `LongArcExistenceConcrete.BoundaryLongArcCarrierRawTurnRows` is the
    concrete positive source surface for the same content: a finite long-arc
    carrier, cardinality `B`, Lemma6/Lemma7 coverage, and nonnegative real
    raw turns.
    `BoundaryLongArcCarrierRawTurnRows.ofFiniteCarrierRawTurns`,
    `.nonempty_of_finiteCarrierRawTurns`, and
    `.exists_nonconcave_longArc_with_turn_bounds` sharpen that upstream
    carrier route.  The exact remaining long-arc inputs are now the finite
    carrier, `card = B`, Lemma6/Lemma7 coverage `d3 <= N + card`, the real
    `rawTurn`, and raw-turn nonnegativity on the turn slots.
    Newest W11/W24 composition:
    `BoundaryAngleTurnW11.ofTriangleRunAndBoundaryLongArcGapNegativeRows`
    consumes a triangle-run family and W13 gap-negative rows to build the W11
    real turn-angle row package, and
    `missingFieldOfTriangleRunBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem`
    routes those rows plus the W16 finite-`p/q` theorem directly to the W24
    missing long-arc/triangle-run field.
    Newest compact W24 route:
    `JordanBoundaryConcreteInhabitationW24.longArcFieldFamilyOfBoundaryLongArcGapNegativeRows`
    and
    `missingFieldOfBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem`
    consume W13 `BoundaryLongArcGapNegativeRows` (using their real raw-turn
    rows) plus the W16 finite-`p/q` theorem.  The exact remaining source
    inputs are genuine W13 gap-negative rows and either explicit triangle-run
    rows or the W16 finite-`p/q` theorem over the selected skeleton.
    No-boundary-gap W24 route:
    `BoundaryLongArcNoBoundaryGapTriangleDegree34Rows`,
    `.toBoundaryLongArcGapNegativeRows`,
    `.toLongArcFieldFamily`,
    `missingFieldOfNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem`,
    and
    `ofSkeletonNoBoundaryGapTriangleDegree34RowsAndFinitePQSpineCyclicSuccessorRowsTheorem`
    route no-boundary-gap rows plus W16 finite-`p/q` rows to the missing field.
    Remaining work is the actual no-boundary-gap/no-gap rows, not another W24
    bridge.
    W24 now has `missingField_nonempty_of_noBoundaryGapTriangleDegree34Rows_explicitM8TriangleRunIndicesTheorem`,
    consuming no-boundary-gap rows plus explicit M8 triangle-run indices through
    the W17 finite-`p/q` theorem.  `BoundaryAngleTurnW11` also exposes
    `missingFieldOfTriangleRunAndBoundaryLongArcGapNegativeRows` and a
    nonempty theorem from triangle-run rows plus W13 gap-negative rows.
    `SelectedTopologyRowsInhabitationW33` packages these into
    `exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem`.
    Remaining long-arc/W24 work is positive row inhabitation, not another
    missing-field bridge.
    `Lemma6Lemma7AssemblyW13` now consumes `BoundaryLongArcGapNegativeRows`
    into classified long-arc existence fields, concrete count-gap input, and
    `M8ConstructionInterface.M8TurnBounds`, including
    `m8TurnBoundsOfBoundaryLongArcGapNegativeRows_totalTurn_lt_pi_div_three`.
    Remaining W13 work is positive gap-negative row inhabitation, not turn-bound
    extraction.
    K23 now supplies a W24-facing no-boundary-gap reduction from skeleton
    realization-carrier rows via
    `SkeletonBoundaryGapTriangleDegree34RealizationCarrierRows`,
    `noBoundaryGapTriangleDegree34RowsOfSkeletonRealizationCarrierRows`,
    `boundaryLongArcNoBoundaryGapTriangleDegree34RowsOfSkeletonRealizationCarrierRows`,
    `longArcFieldFamilyOfSkeletonRealizationCarrierRows`, and
    `missingFieldOfSkeletonRealizationCarrierRowsFinitePQSpineCyclicSuccessorRowsTheorem`.
    Remaining work is the actual skeleton realization-carrier rows and raw-turn
    rows.
    Shortest W13 source route:
    supply `ClassifiedBoundary.BoundaryLongArcRawTurnRows` for each selected
    skeleton row, then combine with Lemma6/Lemma7 coverage using
    `ClassifiedBoundary.BoundaryLongArcGapNegativeRows` or
    `BoundaryLongArcGapNegativeRows.ofLemma6Obstruction`.  W11 is optional on
    this shortest route; the real missing data is still the raw-turn family and
    nonnegativity on `turnIndexSet`.

- [ ] Instantiate boundary-walk gap-negative coverage on the selected frame.
  - Paper steps: `E14-E21`.
  - Owners:
    `Swanepoel/Lemma6NegativeAfterGapW12.lean`,
    `Swanepoel/Lemma7GapInductionW12.lean`,
    `Swanepoel/Lemma6Lemma7AssemblyW13.lean`,
    `Swanepoel/K23RouteCoverageSourceW34.lean`,
    `Swanepoel/Lemma9NatLateTripleInhabitationW22.lean`.
  - Coverage target:
    `K23RouteCoverageSourceW34.SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem`.
  - Lemma 9 target:
    `K23RouteCoverageSourceW34.SelectedFrameLemma9NatLateTripleInputsSourceTheorem`
    or the family theorem
    `SelectedFrameLemma9NatLateTripleSourceFamilyTheorem`.
  - Newest reduction: concrete five-start no-early equality now projects to
    nat-late rows via
    `lemma9NatLateTripleInputsFamilyOfConcreteNoEarlyTripleEquality`,
    `selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_concreteNoEarlyTripleEquality`,
    and then to five-start late facts / route coverage via the checked
    `*_of_natLateTripleInputs` constructors.
  - Next action: prove the actual positive nat-late rows for the selected
    frame/cyclic package and pair them with boundary-walk gap-negative
    coverage.  Do not add another no-early equality wrapper.
  - Latest route-coverage-to-Lemma9 projections:
    `NoEarlyRouteCoverageClosureW32.lemma9SourceFieldsOfRouteData`,
    `natLateTripleInputsOfRouteData`,
    `lemma9SourceFieldsOfRouteCoverageAvailable`,
    `natLateTripleInputsOfRouteCoverageAvailable`, and
    `nonempty_lemma9SourceFields_of_routeCoverage` feed Lemma 9 source fields
    directly from route-coverage data.  Remaining work is the concrete route
    coverage source plus five-start exclusions, not another Lemma 9 projection
    bridge.
    The W32 route-coverage handoff has been re-verified and is already
    sufficient; W34 already contains the selected-frame consumers from route
    coverage plus five-start exclusions.  Do not add another W32 wrapper unless
    a real theorem-shape mismatch reappears.
    W22 now has import-safe projections
    `Lemma9NatLateTripleInhabitationW22.natLateTripleInputsOfSourceFields`,
    `concreteNoEarlyTripleEqualityOfSourceFields`,
    `fiveStartExclusionsOfSourceFields`, and
    `assembledNatLateTripleInputsFamilyOfSourceFamily`, so W34 can compose
    route coverage with Lemma 9 without importing W32 back into W22.
    Newest W22 reductions:
    `concreteNoEarlyTripleEquality_iff_fiveStartExclusions`,
    `nonempty_natLateTripleInputs_iff_fiveStartExclusions`,
    `natCoverageInputs_of_coverage_and_fiveStartExclusions`,
    `nonempty_coverageConcreteRow_iff_exists_coverage_and_fiveStartExclusions`,
    and `nonempty_sourceFields_of_coverage_and_fiveStartExclusions` reduce the
    nat-late/Lemma 9 side to actual coverage plus the five-start exclusions.
    `NoEarlyTripleFromLemma9` now gives row-level conversions
    `M8Lemma9FiveStartLateFacts.iff_fiveStartExclusions`,
    `fiveStartExclusions_of_lateTriples`,
    `fiveStartExclusions_of_natLateTripleInputs`, and
    `fiveStartExclusions_of_earlyTripleObstructionInputs`, so selected-frame
    five-start exclusions can be sourced from any of those concrete inputs.
    K23/W34 now has
    `selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_routeCoverageAvailable`
    and
    `selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_routeCoverageAvailable`,
    so route coverage directly supplies the selected-frame Lemma 9 source.
    Remaining K23 work is concrete route coverage/no-gap/incidence inputs.
    K23/W34 also has direct selected-frame five-start exclusion constructors
    `selectedFrameConcreteFiveStartExclusionSourceTheorem_of_lemma9FiveStartLateFacts`,
    `_of_lateTriples`, `_of_natLateTripleInputs`, and
    `_of_earlyTripleObstructionInputs`, plus
    `selectedFrameConcreteFiveStartExclusionSourceTheorem_iff_natLateTripleInputs`.
    Do not route through W22 nat-late unless that is the actual available
    source.
    `NoEarlyTripleFromLemma9.M8FiveStartExclusions` is now the named
    five-start payload, with selected-row conversions from restricted Lemma 9
    late facts, raw late triples, nat-late inputs, or early-obstruction inputs
    into both five-start exclusions and concrete no-early equality rows.
  - Latest exact carrier reduction:
    `K23RouteCoverageSourceW34.selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows`
    now consumes actual selected no-gap rows directly through
    `boundaryWalkGapNegativeCoverageRowsOfActualSelectedNoGapRows`, instead of
    routing through the older no-gap-to-carrier equivalence.
    Actual selected no-gap rows can be produced from pointwise component-row
    refutations by
    `selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_componentRows`.
    The remaining no-gap blocker is the pointwise no-component row, not another
    coverage adapter.
    `SubpolygonConcreteRealizationW33.FaceSubpolygonRealizationFamilyData` now
    exposes flattened source reductions from component-pattern carrier rows to
    actual pointwise no-bad component rows and then into the selected
    `BoundaryGapTriangleDegree34Row` no-gap field.  Use this flattened family
    when connecting selected subpolygon realizations to route coverage.
  - Latest common-neighbor reduction:
    `K23RouteCoverageSourceW34.SelectedFrameCommonNeighborGeometrySourceTheorem`
    and the three-common-neighbor analogue now bridge to concrete no-early
    equality and nat-late/source-family/route coverage.  The remaining honest
    geometry fields are the five start-indexed common-neighbor witnesses:
    `witness_start1` through `witness_start5`, each proving the appropriate
    common-neighbor cardinality or explicit three-neighbor incidences.
  - Newest positive sources:
    `SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem` or
    `SelectedFrameCommonNeighborWitnessRowsSourceTheorem`, together with the
    actual no-gap carrier rows consumed by
    `routeCoverageAvailable_of_selectedFrameBoundaryGapTriangleDegree34CarrierRows_and_threeCommonNeighborGeometrySource`,
    are enough for the current S4 route-coverage side.  The exact remaining
    obligations are the actual selected no-gap rows and one of those five-start
    witness-row source theorems.
  - Latest positive K23 source reductions:
    `selectedFrameThreeCommonNeighborGeometrySourceTheorem_iff_witnessRows`,
    `selectedFrameCommonNeighborGeometrySourceTheorem_iff_witnessRows`, and
    `selectedFrameK23GeometrySourceTheorem_iff_witnessRows` identify the
    geometry source theorems with positive witness-row families.  Use these to
    avoid no-start/no-early geometry manufacture; the proof obligation remains
    the five-start witness rows plus actual no-gap carrier rows.
    The common-neighbor and three-neighbor witness-row formulations are now
    interconvertible through
    `selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_iff_commonNeighborWitnessRows`.
    Do not add another K23 adapter; prove the actual five-start
    incidence/cardinality rows.
    Newest checked K23 conversion:
    `CommonNeighborRouteCoverageSourceW34.ThreeCommonNeighborIncidenceDatum`
    and `threeCommonNeighborObstructionInputsOfIncidenceRows` convert explicit
    third-neighbor incidence data into the three-common-neighbor witness rows.
    Current known blocker: triple-equality rows give only the standard two
    common neighbors for adjacent `q` pairs.  The exact missing positive
    incidences are `Adj q_1 s_2`, `Adj q_2 s_3`, `Adj q_3 s_4`,
    `Adj q_4 s_5`, and `Adj q_5 s_6`, equivalently
    `Adj s_{i+1} q_i` for starts `i = 1..5`.
    `K23ObstructionConcrete` now names the Euclidean version of this blocker:
    `M8BadAdjacencyCrossAdjacencyRows` is equivalent to
    `M8BadAdjacencyCrossDistanceRows`, and the local-label aliases are
    `M8LocalLabelBadAdjacencyCrossAdjacencyRows` /
    `M8LocalLabelBadAdjacencyCrossDistanceRows`.  The precise remaining K23
    geometric source is proving those five unit-distance rows for the actual
    selected labels.
    `M8BadAdjacencyCrossFigure9DistanceRows` packages the five selected-label
    Figure 9 distance rows with `qi = q_i` and `s = s_{i+1}`;
    `m8LocalLabelBadAdjacencyCrossDistanceRows_of_figure9DistanceRows` turns
    them into the local-label cross-distance package.  The remaining K23 source
    is exactly those five Figure 9 distance rows for the cross pairs.
    `K23RouteCoverageSourceW34.BadAdjacencyCommonNeighborDatum` is the
    route-facing source package for exactly these five incidences:
    `threeCommonNeighborObstructionInputsOfBadAdjacencyData` consumes five
    such rows and feeds the common-neighbor/K23 route.
  - Latest no-gap reduction:
    `SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem`
    reduces through
    `selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_componentRows`
    to the pointwise component-row source.  The concrete missing fields are a
    uniform `coreSubpolygonData`, the exact `RowBoundary` equality, and the
    pointwise absence of the four-field bad pattern: degree-3 at `k`, not
    long-arc, triangular successor edge, and successor degree 3 or 4.  The
    carrier route may close this by producing `CoreSubpolygonCarrierCountData`
    from every bad pattern and applying the existing E13 contradiction.
    Checked row-level shortcut:
    `K23RouteCoverageSourceW34.actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_componentCarrierRows`
    now composes those component-carrier rows directly into actual selected
    no-gap rows, preserving the same `coreSubpolygonData` and `RowBoundary`
    equality fields.  This is still conditional on producing the actual
    component-carrier rows for every bad pattern.
    Newest no-gap and K23 row bridges:
    `ActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsForFrameCyclicRows`
    feeds
    `actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_realizationCarrierRows`.
    `SubpolygonSelectedGeometrySourceW34.false_of_selectedOuterFaceCoreSubpolygonCarrierCountDataOfMinimalFailureSelectedClassificationFields`
    exposes the E13 high-degree-slack contradiction for selected outer-face
    carrier data.  The remaining no-gap source is therefore an actual
    realization-carrier row for each bad pattern, not another no-gap adapter.
    Subpolygon triangulation consumers now include
    `ConcreteSubpolygonInteriorAngleTriangulationRows.toConcreteAngleBoundsOfBoundaryInteriorAngleSum`,
    `.angleLowerBound_of_forced_le_boundaryInteriorAngleSum`,
    `.lowDegreeWithHighDegreeSlack_of_forced_le_boundaryInteriorAngleSum`, and
    `.lowDegreeInequality_of_forced_le_boundaryInteriorAngleSum`; use these to
    turn genuine triangulation rows plus the boundary interior-angle inequality
    into the E13 low-degree conclusions.
    No-gap carrier realization now reduces to pointwise no-bad rows through
    `SubpolygonConcreteRealizationW33.coreSubpolygonAngleRealizationFamily_carrier_false`,
    `noBadRows_of_coreSubpolygonAngleRealizationFamily_carrierRows`,
    `coreSubpolygonAngleRealizationFamily_carrierRows_iff_noBadRows`, and the
    matching face-subpolygon variants.  Remaining no-gap work is the actual
    pointwise no-bad row source.
    `SubpolygonSelectedGeometrySourceW34` now specializes the W33
    `FaceSubpolygonRealizationFamilyData` bridge to minimal-failure selected
    classification/realization fields.  The exact remaining no-gap blocker is
    pointwise absence of `BoundaryGapTriangleDegree34ComponentPattern`, or
    equivalently producing `CoreSubpolygonCarrierCountData` for any such bad
    pattern and applying the existing E13 high-degree-slack contradiction.
    `SubpolygonConcreteRealizationW33` now has pointwise contradiction lemmas
    for core, face-subpolygon, and flattened selected face-subpolygon
    realization families: a bad
    `BoundaryGapTriangleDegree34ComponentPattern` plus matching
    `CoreSubpolygonCarrierCountData` is contradictory over the same W33
    realization family.  The remaining no-gap source is construction of that
    actual carrier-count data for any selected bad component pattern.
    `SubpolygonSelectedGeometrySourceW34` now packages selected realization
    rows as W33 `FaceSubpolygonRealizationFamilyData` and proves the
    K23-consumable no-gap theorem
    `selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_selectedFaceRealizationRows`.
    `K23RouteCoverageSourceW34` also has exact realization carrier row data
    and
    `selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_exactRealizationCarrierRows`,
    consuming W33's exact component-carrier contradiction directly.  Remaining
    no-gap work is positive selected realization/exact-carrier data, not a
    no-gap adapter.
    Latest component-pattern reduction:
    `SubpolygonConcreteRealizationW33.BoundaryGapTriangleDegree34ComponentPattern`,
    `boundaryGapTriangleDegree34Row_iff_componentPattern`,
    `coreSubpolygonAngleRealizationFamily_componentPatternCarrierRows_iff_noBadRows`,
    and
    `no_boundaryGapTriangleDegree34Rows_of_coreSubpolygonAngleRealizationFamily_componentCarrierRows`
    reduce selected no-gap to the actual four-field bad pattern
    (degree/long-arc/triangular-successor/successor degree).
    K23 now aliases `ActualSelectedBoundaryGapTriangleDegree34ComponentRow` to
    that W33 component pattern and uses the same no-boundary-gap theorem in
    `actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_realizationCarrierRows`.
    For K23 common-neighbor geometry,
    `SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem` is the compact
    five-incidence source; it feeds the three/common-neighbor witness rows and
    route coverage through
    `selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborRows`
    and
    `routeCoverageAvailable_of_selectedFrameCoverage_and_badAdjacencyCommonNeighborRows`.
    Newest positive incidence surface:
    `SelectedFrameBadAdjacencyCommonNeighborIncidenceRows` and
    `selectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem_of_incidenceRows`
    package the five start-indexed E19 incidence rows directly into the compact
    bad-adjacency source.  The remaining exact fields are the five explicit
    third-neighbor incidences `Adj q_1 s_2`, `Adj q_2 s_3`, `Adj q_3 s_4`,
    `Adj q_4 s_5`, and `Adj q_5 s_6`, plus the standard bundled distinctness
    and common-neighbor data required by each
    `BadAdjacencyCommonNeighborDatum`.
    `CommonNeighborRouteCoverageSourceW34.M8ConcreteThreeCommonNeighborIncidenceInputs`
    is the lower-level no-cycle package for the same five local incidences,
    with projections `start1_left0_adj_third` through
    `start5_left0_adj_third` and conversions to the three/common-neighbor
    obstruction inputs.
    Newest incidence/no-gap bridge:
    `M8ConcreteThreeCommonNeighborIncidenceInputs.ofWitnessStarts`,
    `start1_left1_adj_third` through `start5_left1_adj_third`,
    `k23ObstructionInputsOfIncidenceRows`,
    `selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows`,
    `selectedFrameK23WitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows`,
    `selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_badAdjacencyCommonNeighborIncidenceRows`,
    and
    `routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_badAdjacencyCommonNeighborIncidenceRows`
    route the five bad-adjacency incidences into K23/no-early coverage.  The
    remaining content is the actual five incidences from the selected finite
    labels, not another K23 adapter.
    Root-imported downstream bridge `BoundaryLabelBadAdjacencyRoute` now turns
    finite-label `BadAdjacencyIncidenceRows` into
    `M8ConcreteBadAdjacencyCommonNeighborObstructionInputs` through
    `badAdjacencyCommonNeighborDatumOfStart` and
    `badAdjacencyCommonNeighborObstructionInputsOfRows`, avoiding a K23 import
    cycle.  Remaining incidence work is the actual five adjacency rows
    `adj_q1_s2` through `adj_q5_s6` inside the finite label certificate.
    Do not import `BoundaryLabelBadAdjacencyRoute` back into K23: it already
    imports K23, so finite-label-to-selected-frame consumption must remain in a
    downstream module importing both.
    `BoundaryLabelCertificateAssembly.BadAdjacencyFiniteLabelIncidenceRows`
    is now the finite-label-facing positive target for those five rows, with
    `badAdjacencyIncidenceRows_iff_finiteLabelIncidenceRows` and
    `badAdjacencyIncidenceRows_nonempty_of_finiteLabelIncidenceRows` converting
    it to the route-facing incidence package.  Remaining incidence work is to
    prove these finite-label rows from the actual generated label certificate.
    Important blocker: the generated finite label certificate currently gives
    `q_i ~ q_{i-1}`, `q_i ~ q_{i+1}`, `q_i ~ r_i`, and `q_i ~ s_i`, but not
    the cross adjacencies `q_i ~ s_{i+1}` needed for
    `BadAdjacencyFiniteLabelIncidenceRows`.  Those five rows need a geometric
    proof or stronger selected-label construction; they are not obtainable by
    unpacking the present certificate fields alone.
    `BoundaryLabelBadAdjacencyRoute` now also consumes finite-label incidence
    rows directly through
    `selectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem_of_finiteLabelBadAdjacencyIncidenceRows`
    and `selectedFrameK23WitnessRowsSourceTheorem_of_finiteLabelBadAdjacencyIncidenceRows`.
    The remaining K23 incidence source is therefore exactly the finite-label
    row package, not a route-facing bridge.
    `CommonNeighborRouteCoverageSourceW34.BadAdjacencyCommonNeighborStandardDatumAt`
    and `M8BadAdjacencyCommonNeighborStandardRows` now package the same five
    selected bad-adjacency incidences together with the standard two adjacent
    common neighbors, and project to concrete three-common-neighbor incidence,
    three-common-neighbor obstruction, and common-neighbor card-obstruction
    inputs.  The remaining K23 source is still the five cross adjacencies or
    Figure 9 cross-distance rows; the standard-row bridge is complete.
    `M8BadAdjacencyCommonNeighborStandardRowFamily` now lifts those standard
    rows to common-neighbor route data and route-coverage availability.  The
    selected-frame consumer belongs in `K23RouteCoverageSourceW34` because that
    file imports the common-neighbor layer.
    `K23ObstructionConcrete.M8BadAdjacencyCrossSelectedFiniteLabelFigure9Rows`
    now reduces actual selected Figure 9 cross rows to cross-distance rows and
    to finite/local label incidence rows:
    `badAdjacencyFiniteLabelIncidenceRows_of_selectedFiniteLabelFigure9Rows`
    and `badAdjacencyLocalLabelIncidenceRowAt_of_selectedFiniteLabelFigure9Rows`.
    `ExactFigureWitnessSourceW34` now supplies finite-PQ wrappers from bad
    adjacency local-label or finite-label rows to exact K23 cross-distance rows.
    `BoundaryLabelCertificateAssembly` now has an import-cycle-free local
    surface for the same source:
    `BadAdjacencySelectedFiniteLabelFigure9RowAt` and
    `BadAdjacencySelectedFiniteLabelFigure9Rows`, projecting to
    `BadAdjacencyLocalLabelIncidenceRowAt`,
    `BadAdjacencyFiniteLabelIncidenceRows`, and route-facing
    `BadAdjacencyIncidenceRows`.  Remaining K23 incidence work is positive
    construction of those selected finite-label Figure 9 rows.
    For Lemma 9, `SelectedFrameConcreteFiveStartExclusionSourceTheorem` feeds
    `selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_fiveStartExclusions`
    and the five-start route-coverage bridges.
    Latest compact S4 route-coverage constructors:
    `routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_badAdjacencyCommonNeighborRows`,
    `routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_fiveStartExclusions`,
    and
    `routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_badAdjacencyCommonNeighborRows_and_fiveStartExclusions`
    combine realization-carrier no-gap rows with the bad-adjacency K23 source
    and/or five-start Lemma9 source for final assembly.

### S5. Figure 8 / Figure 9 Containment

- [ ] Prove the selected-frame local-window containment source.
  - Paper step: Lemma 10 / `E22-E23`.
  - Owners:
    `Swanepoel/Figure8ContainmentW12.lean`,
    `Swanepoel/Figure9ContainmentW12.lean`,
    `Swanepoel/ExactFigureRowsAssemblyW32.lean`,
    `Swanepoel/ExactFigureWitnessSourceW34.lean`.
  - Live target:
    `ExactFigureWitnessSourceW34.LocalWindowContainmentFieldsForFrameCyclicSource`
    for the selected frame/cyclic rows.
  - Newest reduction: local-window containment projects to both Figure 8 and
    Figure 9 distance/angle rows and directly to final-assembly figure
    components via
    `honestEuclideanSourceComponentsForFrameCyclicSource_of_localWindowContainmentFields`.
    The interface constructors from Figure 8 separated containment and Figure 9
    adjacent-left containment are checked.
  - Next action: construct the actual selected figure witnesses, Figure 8
    central-angle containment rows, and Figure 9 middle-turn realization rows
    for the selected frame; then feed them through
    `localWindowContainmentFieldsForFrameCyclicSource_of_actualS5_sourceRows`.
  - Latest compact constructor:
    `ExactFigureWitnessSourceW34.localWindowContainmentFieldsForFrameCyclicSource_of_actualS5_sourceRows`
    reduces local-window containment to selected figure witnesses, Figure 8
    central-angle containment rows, and Figure 9 middle-turn realization rows.
  - Latest Figure 8 projection:
    `ExactFigureWitnessSourceW34.figure8CentralAngleContainmentRowsForFrameCyclicSource_of_localHonestEuclideanRows`
    and
    `figure8SeparatedContainmentInterfacesForFrameCyclicSource_of_localHonestEuclideanRows`
    project Figure 8 containment directly from the honest Euclidean row package.
  - Latest selected-figure bridge:
    `ExactFigureRowsAssemblyW32` now projects existing exact row assembly to
    `LocalSelectedFigureWitnessFieldsFamily`, and
    `ExactFigureWitnessSourceW34` projects local honest Euclidean rows to
    `SelectedFigureWitnessSourceFieldsForFrameCyclicSource`, including the
    actual finite-`p_i/q_i` generated frame packages.  The remaining S5 blocker
    is honest Figure 9 middle-turn realization for the selected frame.
  - Newest compact S5 entrances:
    `localWindowContainmentFieldsForFrameCyclicSource_of_localHonestEuclideanRows`
    reduces local-window containment to
    `LocalHonestEuclideanRowsForFrameCyclicSource`; the Figure 9 side uses the
    left-angle containment row, which is the typed Lemma 10 interface.  The
    older middle-turn realization row is a stronger producer, not a final-route
    blocker.
    Equivalently, prove the Figure 8/Figure 9 distance-and-angle rows through
    `localHonestEuclideanRowsForFrameCyclicSource_iff_distance_and_angle_rows`.
    No new Figure 8 adapter is needed.
  - Latest bundled S5 source:
    `LocalHonestS5FigureRowsForFrameCyclicSource` is the compact obligation
    bundling local honest Euclidean rows with the genuine Figure 9 middle-turn
    realization.  It feeds
    `localWindowContainmentFieldsForFrameCyclicSource_nonempty_of_localHonestS5FigureRows`.
  - Latest atomic S5 entrance:
    `localHonestEuclideanRowsForFrameCyclicSource_of_distance_and_angle_rows`
    builds local honest Euclidean rows from the four atomic distance/angle row
    families.  The final constructor
    `w34ActualRoutePremises_of_exactRemainingInputPackage_distance_and_angle_rows`
    now consumes those four row families plus Figure 9 middle-turn rows.
    The current shortest final S5 route is the atomic four-row variant:
    Figure 8 distance rows, Figure 8 central-angle containment rows, Figure 9
    distance rows, and Figure 9 left-angle containment rows.  The Figure 9
    middle-turn row is a stronger producer, not required by that shortest
    route.
    Newest Figure 9 simplification:
    `Figure9ContainmentConcrete.leftAngleContainmentRows_of_angleLeMiddleTurnRows`
    proves the left-angle containment row from turn nonnegativity plus the
    pointwise upper bound `angleAt p qi s <= turn (i + 1)`.  The remaining S5
    angle source can therefore use this weaker pointwise middle-turn upper
    bound instead of the older equality-style middle-turn realization row.
    W19 exposes the same weaker source through
    `AngleContainmentBridgeProducerW19.Figure9UniversalLeftAngleLeMiddleTurnRows`
    and
    `figure9UniversalLeftAngleContainment_of_angleLeMiddleTurnRows`, with
    certificate constructors ending in
    `ofDistanceWitnessRowsAndAngleLeMiddleTurnRows`.
    Newest checked S5 integration:
    `Figure9LeftAngleLeMiddleTurnRowsForFrameCyclicSource` and
    `Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource`
    expose that weaker pointwise bound on the frame/finite-`p_i/q_i` route.
    `localHonestEuclideanRowsForFrameCyclicSource_of_distance_rows_and_angleLeMiddleTurnRows`,
    `localWindowContainmentFieldsForFrameCyclicSource_of_distance_rows_and_angleLeMiddleTurnRows`,
    and
    `honestEuclideanSourceComponentsForFrameCyclicSource_of_distance_rows_and_angleLeMiddleTurnRows`
    now turn Figure 8 distance rows, Figure 8 central-angle containment, Figure
    9 distance rows, and the weaker Figure 9 middle-turn upper-bound rows into
    the S5 local-window/Euclidean components.  The remaining S5 geometry is
    Figure 8 central-angle containment plus the actual pointwise Figure 9
    middle-turn upper-bound rows for the generated frame.
    Newest Figure 8 bridge:
    `Figure8ContainmentW12.dataWitnesses_of_distanceWitnessRowsAndCentralAngleContainmentRows`
    and `E22_of_distanceWitnessRowsAndCentralAngleContainmentRows` turn
    Figure 8 distance rows plus central-angle containment rows into the E22
    interface.  In `ExactFigureWitnessSourceW34`,
    `Figure8CentralAngleLeSeparatedTurnRowsForFrameCyclicSource` and
    `Figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource`
    are now the compact positive row surfaces for the remaining Figure 8 angle
    source, with finite-label and Figure9 upper-bound constructors ending in
    `localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_finiteLabelRows_centralAngleLeSeparatedTurnRows_and_figure9AngleLeMiddleTurnRows`.
    `BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows`
    is the compact label-certificate angle row package for the quantitative
    S5 angle facts that the finite label data itself does not contain; it
    assembles to `AngleContainmentBridges` via
    `angleContainmentBridgesOfS5AngleRows`.
    `M8FiniteBoundaryFrameCoreLabelCertificate.S5FiniteLabelAngleRows` now
    bundles the same explicit finite-label angle inequalities with direct
    projections to the Figure 8/Figure 9 containment interfaces.  The remaining
    S5 angle inputs are exactly: for Figure 8, prove
    `angleAt qi p qj <= separatedTurn turn i j` for each failed separated
    pair; for Figure 9, prove `angleAt p qi s <= turn (i + 1)` for each
    adjacent failed pair.
    Figure 8 has now been reduced to turn-window geometry:
    `Figure8ExplicitEuclideanFactsCompletionW33.Figure8CentralAngleTurnSubwindowRows`
    or `Figure8CentralAngleTurnSubwindowEqRows` feed
    `centralAngleContainmentRows_of_turnSubwindowRows` /
    `centralAngleContainmentRows_of_turnSubwindowEqRows`.  The exact remaining
    Figure 8 source is a real central-angle telescope/subwindow inside
    `Finset.Icc (i + 1) j` for each separated failed pair, plus turn
    nonnegativity.
    Latest Figure 8 source refinements:
    `Figure8CentralAngleTurnIccSubwindowRows`,
    `Figure8CentralAngleTurnIccSubwindowEqRows`,
    `Figure8CentralAngleTurnIndexedSubwindowRows`, and
    `Figure8CentralAngleTurnIndexedSubwindowEqRows` feed containment through
    the checked `centralAngleContainmentRows_of_*` constructors, including
    M8-turn-bound variants.  The remaining proof content is now the actual
    indexed/Icc window selection for every separated failed pair.
    Figure 9 has now been reduced to concrete turn geometry:
    `Figure9EuclideanFactsConcrete.Figure9AdjacentLeftCosineTurnRows` or
    `Figure9AdjacentLeftTurnChordRows` feed
    `angleLeMiddleTurnRows_of_cosineTurnRows` /
    `angleLeMiddleTurnRows_of_turnChordRows`.  The exact remaining rows are
    `turn (i + 1) ∈ [0, pi]` and either
    `Real.cos (turn (i + 1)) <= dotAt p qi s` or
    `sqDist p s <= 2 - 2 * Real.cos (turn (i + 1))`.
    Latest Figure 9 row calculus:
    `cosineTurnRows_iff_turnChordRows`,
    `middleTurn_mem_Icc_zero_pi_of_totalTurn_lt_pi_div_three`,
    `cosineTurnRows_of_totalTurn_and_cosineComparisons`,
    `turnChordRows_of_totalTurn_and_chordComparisons`,
    `angleLeMiddleTurnRows_of_totalTurn_and_cosineComparisons`, and
    `angleLeMiddleTurnRows_of_totalTurn_and_chordComparisons` reduce the
    remaining Figure 9 source to total-turn control plus pointwise cosine or
    chord comparisons.
    `Figure9EuclideanFactsConcrete` now also has pointwise comparison lemmas
    turning `angleAt p qi s <= theta` into cosine/chord comparison rows, with
    `UnitSeparatedAngle.value` and equality variants for the common case where
    the certified turn angle is exactly the Figure 9 left comparison angle.
    Remaining S5 work is to prove those pointwise angle upper bounds from the
    actual selected turn-angle geometry.
    W19 containment now consumes those concrete Figure 9 rows through
    `figure9UniversalLeftAngleLeMiddleTurnRows_of_cosineTurnRows`,
    `figure9UniversalLeftAngleLeMiddleTurnRows_of_turnChordRows`,
    `Figure9ExactAngleContainmentCertificate.ofDistanceWitnessRowsAndCosineTurnRows`,
    and `.ofDistanceWitnessRowsAndTurnChordRows`.
    Newest W19 total-turn constructors:
    `Figure9UniversalLeftCosineComparisonRows`,
    `Figure9UniversalLeftTurnChordComparisonRows`,
    `figure9UniversalLeftAngleLeMiddleTurnRows_of_totalTurn_and_cosineComparisons`,
    `figure9UniversalLeftAngleLeMiddleTurnRows_of_totalTurn_and_chordComparisons`,
    and the corresponding `Figure9ExactAngleContainmentCertificate` /
    `PointwiseFigure9SelectedExactAngleContainmentCertificate` constructors
    let S5 use total-turn control plus pointwise cosine/chord comparisons
    directly.
    Exact finite-`p_i/q_i` S5 route:
    `ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource`
    is the row-wise S5 angle package for the generated finite label
    certificate.  The label certificate supplies distance rows via
    `figure8FiniteLabelAdjacencyDistinctnessRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificate`
    and
    `figure9FiniteLabelAdjacencyDistinctnessRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificate`,
    while `S5AngleRows` supplies the quantitative angle rows via
    `figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows`
    and
    `figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows`.
    The compact S5 bundle is
    `distance_and_angle_rowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows`,
    and the direct local-window/honest-Euclidean constructors are
    `localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows`
    and
    `localWindowContainmentFieldsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows`.
    Newest finite-PQ concrete row wrappers:
    `Figure8CentralAngleTurnSubwindowRowsForFinitePQSpineGeneratedOrderSource`,
    `Figure8CentralAngleTurnSubwindowEqRowsForFinitePQSpineGeneratedOrderSource`,
    `Figure9AdjacentLeftCosineTurnRowsForFinitePQSpineGeneratedOrderSource`,
    `Figure9AdjacentLeftTurnChordRowsForFinitePQSpineGeneratedOrderSource`,
    their Figure 8/Figure 9 projections, and the four compact
    `s5AngleRowsForFinitePQSpineGeneratedOrderSource_of_*` constructors reduce
    finite-PQ S5 angle rows to actual Figure 8 subwindow rows plus Figure 9
    cosine/chord rows.
    Additional finite-PQ wrappers now cover Figure 8 Icc/indexed
    subwindow/equality rows and total-turn Figure 9 cosine/chord comparison
    rows, including `figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource_of_totalTurn_and_cosineComparisonRows`,
    the chord analogue, and the `S5AngleRowsForFinitePQSpineGeneratedOrderSource`
    constructors from Icc/indexed Figure 8 rows plus middle-turn/comparison
    rows.  Direct `localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource`
    constructors also consume those combinations.  Remaining S5 content is the
    actual subwindow selection and comparison rows from finite-label geometry.
    Boundary-label S5 now exposes local finite-label row surfaces
    `M8FiniteBoundaryFrameCoreLabelCertificate.Figure8CentralAngleTurnSubwindowRows`,
    `Figure8CentralAngleTurnIccSubwindowRows`,
    `Figure8CentralAngleTurnIndexedSubwindowRows`,
    `Figure9AdjacentLeftCosineTurnRows`, `Figure9AdjacentLeftTurnChordRows`,
    and cosine/chord comparison row aliases, with `S5AngleRows` constructors
    such as `.ofTurnSubwindowRowsAndCosineTurnRows` and
    `.ofTurnSubwindowRowsAndCosineComparisonRows`.  Remaining S5 work is to
    inhabit these rows from the actual finite label/turn geometry.
    W34 also has local-honest finite-PQ wrappers
    `localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_distance_rows_and_cosineComparisonRows`,
    `.of_distance_rows_and_chordComparisonRows`, and the finite-label-row
    variants with central-angle rows plus Figure 9 comparison rows.  Remaining
    S5 content is still the actual comparison/subwindow row source.
    W11 now exposes actual-turn S5 carriers
    `Figure8CentralAngleActualTurnIccSubwindowRows`,
    `Figure8CentralAngleActualTurnIndexedSubwindowRows`,
    `Figure9AdjacentLeftActualTurnCosineComparisonRows`, and
    `Figure9AdjacentLeftActualTurnChordComparisonRows`, plus adapters
    `s5AngleRows_of_actualTurnIccRowsAndCosineComparisonRows` and indexed /
    chord variants.  Remaining S5 work is to inhabit those actual-turn rows
    from triangle-run/turn-angle geometry.
    Newest W11 turn-angle reductions:
    `Figure8CentralAngleTurnAngleIccSubwindowRows`,
    `Figure8CentralAngleTurnAngleIndexedSubwindowRows`,
    `Figure9AdjacentLeftTurnAngleCosineComparisonRows`, and
    `Figure9AdjacentLeftTurnAngleChordComparisonRows` feed the actual-turn
    carriers via the `*_of_turnAngleRows` constructors.  The exact S5 source
    now is the real turn-angle row package for the selected triangle run:
    subwindow membership for Figure 8 and pointwise cosine/chord comparisons
    for Figure 9.
    Latest Figure 8 turn-angle bridge:
    `Figure8CentralAngleTriangleRunIccSubwindowRows` plus
    `figure8CentralAngleTurnAngleIccSubwindowRows_of_triangleRunIccSubwindowRows`
    turns explicit triangle-run Icc subwindow rows into the W11 Figure 8
    turn-angle row package.  The remaining Figure 8 source is the actual
    triangle-run Icc subwindow selection for each separated failed pair.
    `ExactFigureWitnessSourceW34` now has finite-PQ wrappers that connect W11
    actual-turn Figure 8/Figure 9 rows to
    `S5AngleRowsForFinitePQSpineGeneratedOrderSource` using the existing
    finite-label distance machinery.  The remaining S5 source is the actual W11
    turn rows themselves, not a finite-PQ adapter.
    `ExactFigureRowsAssemblyW32` now also has local adapters from finite-label
    `S5AngleRows` to `LocalHonestEuclideanInequalitySourceFields`, plus direct
    W11 turn-angle adapters for Figure 8 Icc/indexed rows with Figure 9
    cosine/chord comparison rows.  Do not add more S5 adapter layers unless the
    source row shape changes.

### S6. Swanepoel Final Assembly

- [ ] Inhabit `SwanepoelW32FinalAssembly.W34ActualRoutePremises`.
  - Short route inputs:
    checked no-cut family; actual topology/component closure; compatible
    finite-spine generated-order rows; S4 route coverage; S5 exact figure rows
    or local-window containment.
  - Preferred final constructors:
    `w34ActualRoutePremises_of_exactRemainingInputPackage`,
    `w34ActualRoutePremises_of_refuting_bothPlusSidesCutForced_finitePQSpineRows_boundaryWalkGapCoverage_lemma9Late_localWindowContainment`,
    `w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_localWindowContainment`,
    and `w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_figure8_figure9_rows`.
    The nat-late plus containment-interface constructor
    `w34K23LocalExactAngleRoutePremises_of_refuting_bothPlusSidesCutForced_finitePQSpineRows_boundaryWalkGapCoverage_natLate_containmentInterfaces`
    is a checked compatibility alias for the same `W34ActualRoutePremises`
    route; name it that way if it appears in handoff text.
  - Use `W34ActualRoutePremises` as the live route name in task text.  Older
    route names are compatibility aliases only; do not create new tasks around
    them.
  - Latest compact package:
    `w34ActualRoutePremises_of_exactRemainingInputPackage` consumes exactly the
    S2 boundary target, S3 skeleton/angle rows, S4 missing long-arc/triangle-run
    field, finite `p_i/q_i` generated-order rows, S4 carrier plus K23 geometry,
    and S5 selected-figure/Figure 8/Figure 9 rows.  Use this as the final
    assembly surface while proving the remaining positive source fields.
    The newer
    `w34ActualRoutePremises_of_exactRemainingInputPackage_honestSourceRows`
    consumes the honest source rows directly: K23 witness rows plus local
    honest S5 rows and Figure 9 middle-turn rows.  Prefer this constructor
    when integrating the latest S4/S5 obligations.
    The distance/angle-row variant
    `w34ActualRoutePremises_of_exactRemainingInputPackage_distance_and_angle_rows`
    is the current shortest S5-facing constructor when the four atomic figure
    row families are available.
    The newer
    `w34ActualRoutePremises_of_exactRemainingInputPackage_atomicFigureRows`
    removes the stronger Figure 9 middle-turn input from that shortest route.
    The compact S4/S5 route
    `w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGap_compactS4S5`
    consumes long-arc rows, the W16 finite-`p/q` theorem, actual no-gap rows,
    K23 witness rows, and bundled S5 rows directly.
    Finite generated-order rows after closure can also be sourced from W16 /
    finite-walk data via
    `selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreData` and
    `selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finiteWalkFrameCoreData`.
    W16 finite `p/q` cyclic-successor rows alone are not enough for generated
    order.  The exact upgrade surface is
    `selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finiteWalkFrameCoreCenterDegreeSix`
    or the direct-extra-cardinality variant.  The missing payload is
    `BoundaryArcFiniteWalkFrameCoreData`, `boundaryArc_eq`,
    `centerDegreeSix` or `extraNeighborCardTwo`, and generated cyclic-order
    rows for the finite-walk frame core.
    Newest generated-order source:
    `FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows`
    and the center-degree-six variant package the missing finite-walk frame
    core, boundary-arc equality, extra-neighbor-cardinality/degree-six, and
    generated cyclic-order rows.  They feed
    `selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows`
    and
    `selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows`.
    The selected finite-walk generated-order source rows now store the current
    frame-core fields directly and expose raw-fact plus bundled
    boundary-arc-frame-core constructors.  Remaining generated-order work is
    positive inhabitation of those raw/frame-core and generated cyclic-order
    inputs, not another row-shape adapter.
    Newest generated-order bridge:
    `selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfFinitePQSpineFrameCoreLemma8Rows`
    and its nonempty form produce final-consumable generated-order source rows
    from finite-spine frame-core/Lemma 8 rows plus
    `SelectedFinitePQSpineGeneratedCyclicRows`; the extra-neighbor cardinality
    row is derived from `finiteRows.lemma8`.  The remaining generated-order
    blocker on this route is exactly the selected finite-`p/q` generated cyclic
    rows.
    `FrameCyclicOrderAssemblyW32` now constructs those selected generated
    cyclic rows from
    `BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate.ExplicitCyclicOrderRows`
    through `selectedFinitePQSpineGeneratedCyclicRowsOfExplicitCyclicOrderRows`
    and its nonempty form.  Remaining generated-order source is therefore the
    explicit finite-spine cyclic-order rows, already available from the
    boundary-spine source package.
    Newest raw-fact route:
    `PointwiseFinitePQSpineRawFrameCoreFacts`,
    `finitePQSpineFrameCoreFields_iff_rawFacts`,
    `finitePQSpineGeneratedOrderRowsOfRawFacts`,
    `selectedFinitePQSpineGeneratedOrderRowsOfRawFacts`,
    `SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.rawFacts`, and
    `selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfRawFacts` connect
    finite-spine raw cyclic-order/frame-core facts to generated-order rows.
    M8 construction now has the local-honest shortest route
    `m8ConstructionData_nonempty_of_exactTopology_longArc_finitePQTheorem_generatedFiniteWalk_realizationCarrier_badAdjacencyIncidence_localHonestRows`.
    Final assembly now has the matching constructor
    `w34ActualRoutePremises_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows`.
    The remaining final-route inputs are the actual source rows named in that
    theorem: S2 exact topology, S3 sector theorem, long-arc rows, W16 finite
    p/q theorem, finite-walk generated-order rows, realization-carrier no-gap
    rows, K23 incidence rows, and S5 label-angle rows.
    `BrokenLatticeMinimalFailure` already closes
    `no_minimalClearedFailure` from a `MinimalFailureM8ConstructionEliminator`
    via `M8ConstructionData.contradiction` and
    `no_minimalClearedFailure_of_m8ConstructionEliminator`.  Do not import
    `M8ConstructionDataInhabitationW33` back into that file; it would form a
    cycle.  The remaining bridge is upstream construction of M8 data for every
    minimal failure from the current source rows.
    Current M8 endpoint:
    `m8ConstructionData_nonempty_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows`
    and
    `contradiction_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows`
    match the final source surface exactly.  Remaining blockers are only the
    positive source inputs themselves.
    `SwanepoelW32FinalAssembly` now also exposes the exact-source contradiction
    composition theorem with that same source-row surface, so the contradiction
    route and M8 data route are aligned.  Do not add another final-assembly
    shape wrapper unless the source inputs change.
    Current closure-package M8 endpoint:
    `m8ConstructionData_nonempty_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows`
    consumes the exact closure/missing-field package, finite-walk generated
    order, realization-carrier rows, bad-adjacency rows, and S5 rows directly.
    No M8 constructor mismatch remains; remaining work is positive inhabitation
    of those source inputs.
    `SwanepoelW32FinalAssembly` now has the same closure-package-shaped
    conditional M8 source and contradiction wrapper, and older long-arc/W16
    adapters route through it.  Do not add more M8 source-shape wrappers unless
    the final source inputs themselves change.
    `MinimalGraphFacts` cannot import the M8 route without a cycle
    (`MinimalGraphFacts -> BrokenLatticeMinimalFailure -> ... -> MinimalGraphFacts`).
    Downstream closure already exists via
    `BrokenLatticeMinimalFailure.no_minimalClearedFailure_of_m8ConstructionEliminator`
    and `M8ConstructionDataInhabitationW33.no_minimalClearedFailure_of_routeCertificate`.
    The exact remaining route source is
    `Nonempty M8ConstructionDataInhabitationW33.StrongestRouteSource`,
    equivalently `NoCutMinimalityClosureW34.ExactRemainingPremiseForNoCutMinimalityClosure`.
    W16 also exposes
    `finitePQSpineCyclicSuccessorRowsTarget_of_frameCoreData` for frame-core
    finite-`p/q` successor rows.
    W16 now has the assembly-facing
    `FinitePQSpineExplicitCyclicOrderRowsAndRawFactsTheorem` and
    `finitePQSpineCyclicSuccessorRowsTheorem_of_explicitCyclicOrderRowsAndRawFactsTheorem`,
    reducing the final W16 theorem to finite label certificate,
    explicit cyclic-order rows, and raw frame-core facts.
    The old exact-input constructor that listed ten independent inputs is now
    stale.  The current compact final route has seven positive source
    obligations:
    S2 `MinimalFailureExactActualTopologyFieldsTarget`;
    S3 `SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem`; an
    `ExactActualTopologyClosureMissingFieldPackage` for the resulting skeleton
    rows, or its expanded long-arc plus W16 source; finite-walk
    `SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows`; K23
    `SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem`;
    K23 `SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem`; and compact
    S5 `S5AngleRowsForFinitePQSpineGeneratedOrderSource`.  `MinimalBoundaryTopologySkeletonFamily`,
    old actual-cycle targets, atomic distance rows, and separate K23 witness
    rows are not independent blockers on this compact surface.
    W33 now has the exact-S2 package route
    `ExactActualTopologyClosureMissingFieldPackage` and
    `exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem`,
    consuming exact actual topology fields, W33 skeleton rows, W24 long-arc
    family, and the W16 finite-`p/q` theorem to produce the matching
    missing-field/closure pair for final assembly.
    `SelectedTopologyRowsInhabitationW33` also exposes direct constructors for
    `ExactActualTopologyClosureMissingFieldPackage` from W24 missing-field
    rows, W13 gap-negative rows plus W16, no-boundary-gap rows plus W16, and
    the explicit triangle-run/long-arc row surfaces.  Use these constructors
    before adding any new W33 closure layer; the remaining work is positive
    source inhabitation.
    Newest exact-S2/source-row constructor:
    `w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelAngleRows`
    composes exact topology fields, the S3 sector theorem, W33's
    `ExactActualTopologyClosureMissingFieldPackage`, finite-walk generated
    order rows, realization-carrier no-gap rows, bad-adjacency K23 rows, and
    finite label/S5 angle rows into `W34ActualRoutePremises`.  This is now the
    preferred S6 integration surface after S2/S3/S4/S5 positive sources are
    inhabited.
    `w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows`
    is the still-shorter S5-facing form: it consumes the generated finite label
    certificate plus `S5AngleRowsForFinitePQSpineGeneratedOrderSource`; the
    label certificate supplies the two distinctness rows and the S5 angle rows
    supply Figure 8 central-angle plus Figure 9 middle-turn upper bounds.
    On the S5 distance side,
    `BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.figure8DistanceWitnessRows`
    and `.figure9DistanceWitnessRows` already construct the local Figure 8/9
    distance witness rows from a finite boundary frame-core label certificate.
    The remaining S5 proof work is the actual Figure 8 central-angle
    containment and Figure 9 left-angle or middle-turn-upper-bound rows for the
    generated frame.
    Latest final/S5 integration:
    `ExactFigureRowsAssemblyW32` now has finite-label S5 constructors for
    Figure 8 containment and Figure 9 middle-turn-to-left-angle containment,
    and `ExactFigureWitnessSourceW34.honestEuclideanSourceComponentsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows`
    hands compact S5 rows to exact figure components.  `SwanepoelW32FinalAssembly`
    checks again after removing an unused proof-irrelevance cast theorem and
    routing the exact topology/S3/long-arc/W16/generated-order/no-gap/K23/S5
    surface through the closure-package helper.  M8 also exposes
    `routeCertificate_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w24NoCut_w16FinitePQ_generatedFiniteWalk_realizationCarrier_incidenceRows_labelCertificateS5AngleRows`
    as the strongest route-certificate endpoint for that source surface.
  - Compile status:
    `SwanepoelW32FinalAssembly` now builds with the pinned toolchain after
    removing duplicate `Verified` aliases already exported by
    `SwanepoelW32RouteAudit` and fixing the generated-order row universe.
    This does not inhabit `W34ActualRoutePremises`; it only verifies the
    conditional assembly surface.

- [ ] Derive the internal lower-bound target from the inhabited route.
  - Target: `Swanepoel.targetLowerBoundEightThirtyOne`.
  - Current conditional wrappers are not enough; `W34ActualRoutePremises` must
    be inhabited unconditionally and imported.

- [ ] Add public Swanepoel wrappers only after the internal theorem builds and
  the audit is clean.
  - File: `ErdosProblems1066/KnownBounds.lean`.
  - Public theorem shape: `Verified.lower_bound_eight_thirty_one` and a
    source-specific alias.

## Pach--Toth After Swanepoel

Do not spend effort on blocked rigid or translated-equation routes.  The
Pach--Toth public wrapper remains absent until the exact/arbitrary internal
targets are unconditional and audited.

### P1. Quarantine Blocked Routes

- [x] The proof-used Figure 2 edge-role table is checked infrastructure.
  Keep names/docstrings honest: it is not a complete PostScript transcription.

- [x] Treat the exact-base all-positive direct-flexible W33 source as refuted.
  - Checked blockers:
    `FiniteReducedMetricCandidateSearchW33.not_directFlexibleSourceShape`,
    `FlexibleCandidateMetricInhabitationW33.not_nonempty_directFlexibleSourcePayload`,
    and related length-one exact-base obstruction theorems.
  - Consequence: do not task workers with inhabiting the all-positive
    `DirectFlexibleSourcePayload` / `CandidatePeriodMetricData` lane unless
    they first explain why the checked obstruction no longer applies.
  - Current status:
    `CrossBlockMetricInequalitiesW33` pins the obstruction to the forced
    `T2_2 -> T1_1` unit row versus exact squared distance `12`.  This is a
    real no-go result for the exact-base all-positive flexible surface.
    W34 non-rigid material may supply conditional eventual/threshold
    endpoints, but not an unconditional Pach--Toth theorem by itself.

- [ ] Keep concrete four-target / translated-equation lanes out of the live
  proof route.
  - Blocked or audit-only modules include:
    `RoleHingeConcreteSearch`,
    `OrbitSqDistancesW12`,
    `TransitionAlternativeW13`,
    `ConcreteLowerTableValueDataBlockerW32`,
    `PeriodCandidateConcreteTableBlockerW32`.

### P2. Choose The Live Closed-Placement Route

- [ ] Target an eventual/threshold non-rigid route unless a verified
  alternative supersedes the W33 obstruction.
  - Deliverable:
    `EventualRoleHingeClosure.EventualFiniteCertificateObligations K0` or
    `LargeClosedPlacementW12.LargeExplicitClosedPlacementCertificates K0`.
  - Fields: same/opposite transition data, thresholded orientation words,
    indexed algebraic period equations, and global separation.
  - Gate: yields explicit closed-placement certificates for all large block
    counts.
  - Latest checked bridge:
    `RoleHingeCandidateSearchSurface` now has a positive thresholded route via
    `EventualPeriodSearchData T K0` and `EventualCrossBlockMetricData P`,
    proving eventual, large-block, and arbitrary-`n` targets once those
    thresholded sources and the matching small-case package are inhabited.
    `AlternativeNonRigidClosedPlacementW34` and
    `PachTothRemainingSourceLedgerW34` now also expose the threshold-six metric
    route: large closed-placement fields for `k >= 6` plus
    `BelowThresholdMetricFieldsSix` yield the full deformed metric-field
    family and the exact/arbitrary targets.  `BelowThresholdMetricFieldsSix`
    is now obtained from
    `ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificateSource`,
    so the exact small source has the same honest geometry surface as the
    existing small-certificate route.
    Large exact blocks from six onward now route through threshold-six
    closed-placement fields via
    `largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsSix` and
    related adapters in `EventualClosedPlacementSourceW34`,
    `RemainderSplitSourceClosureW32`, and
    `AlternativeNonRigidClosedPlacementW34`.  This remains secondary until the
    Swanepoel route is closed.

- [ ] Provide the finite small-complement package for the chosen threshold.
  - Deliverable: exact certificates below the threshold induced by `K0`.
  - Owners:
    `PachToth/ClosedPlacementSmallKCertificatesW19.lean`,
    `PachToth/SmallLengthExactTargetsConcreteW24.lean`.
  - Warning: `SmallUpTo_sixteen` only suffices for arbitrary `n` when the
    block threshold is compatible with `K0 <= 1`.
  - Current blocker:
    the checked small-source lane still needs a genuine
    `DeformedLengthOneTransitionGeometry` / `DeformedLengthOneSource`; the
    helper route through exact-base flexible generated closure depends on the
    now-refuted W33 direct-flexible gate.
  - Checked W34 status:
    `PachToth/DeformedLengthOneSourceW34.lean` records the honest
    geometry-to-source constructors and the blocker theorem
    `not_nonempty_directFlexibleSourcePayload`, citing the W33
    `T2_2 -> T1_1` exact-base length-one obstruction.
    The current reduced small side is
    `DeformedLengthOneExactBlocksTwoThroughFiveSource`, equivalently a genuine
    deformed length-one source plus exact blocks two through five; it feeds the
    threshold-six arbitrary/exact adapters in
    `SmallLengthExactTargetsConcreteW24`, `RemainderSplitSourceClosureW32`, and
    `FarApartRemainderSourceW34`.

### P3. Prove Closed Placements And Separation

- [ ] Construct same/opposite non-rigid transition data.
  - Owners:
    `PachToth/RoleHingeCandidateSearchSurface.lean`,
    `PachToth/FlexibleTransitionSearchW11.lean`,
    `PachToth/EventualRoleHingeClosure.lean`.

- [ ] Construct period/closure certificates for the selected route.
  - Owners:
    `PachToth/PeriodSearchInterface.lean`,
    `PachToth/PeriodWordCertificates.lean`,
    `PachToth/EventualRoleHingeClosure.lean`.

- [ ] Prove global separation through reduced cross-block metric tables.
  - Owners:
    `PachToth/GeneratedSeparationFarApart.lean`,
    `PachToth/CrossBlockLowerBoundsInterface.lean`,
    `PachToth/RoleHingeCandidateSearchSurface.lean`.

### P4. Pach--Toth Final Assembly

- [ ] Derive the eventual target after large closed placements are inhabited.
  - Target: `PachToth.targetUpperConstructionFiveSixteenEventually`.

- [ ] Derive the exact all-block target only from an all-positive certificate
  family.
  - Target: `PachToth.targetUpperConstructionFiveSixteen`.

- [ ] Derive the arbitrary target only after the exact target or a threshold
  route plus matching finite small cases.
  - Target: `PachToth.targetUpperConstructionFiveSixteenArbitrary`.
  - Latest far-apart split bridge:
    `FarApartRemainderSourceW34` and `RemainderSplitSourceClosureW32` now build
    `CanonicalSplitRealization k r` internally from an exact chain/closed
    placement family and checked finite remainders using translated far-apart
    placement.  The remaining split blocker is no longer far-apart placement;
    it is `MinimalExactRemainderSplitSourceBlocker`, equivalently
    `ExactBlocksOneThroughFive /\ LargeExactBlockTargetsFromSix`.

- [ ] Add public `KnownBounds` wrappers only after the matching internal
  theorem builds and passes the audit.

## Project Structure Tasks

- [ ] Keep `TASK.md` as this active execution queue.  Put theorem dependency
  explanations in `proof_workings/theorem_dependency_map.md`.
- [ ] Do not create new W-numbered files for bookkeeping.  If a W-numbered file
  remains, it must be a checked proof/certificate/blocker or a documented
  compatibility surface.
- [ ] For every unrooted Lean file, either root-import it after a targeted
  pinned check, merge it into the owning module, or remove/quarantine it with
  the owner decision recorded outside TASK.md.
- [ ] Defer physical folder moves until imports are stabilized.  When moving
  later, move one semantic cluster at a time and leave old-path import shims
  until all downstream imports are migrated.
