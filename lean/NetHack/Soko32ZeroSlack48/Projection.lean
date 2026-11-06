/- Projection instance for the complete original canonical soko3-2.
All negative-weight cells, the old gate support and original boulders are retained. All successful
Model actions from the original start are covered; no search-state or
player-region hypothesis is imposed. This proves no new numerical bound. -/
import NetHack.Sokoban.ProjectedOracle
import NetHack.Sokoban.SparseGoalSupport
import NetHack.SokobanLinearPhases.Map32.Invariant
import NetHack.Soko32Gate138.Verified
import NetHack.Sokoban.HistogramRecovery
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko32ZeroSlack48.Projection
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.HazardPhaseCountedCorrection

def cells : List Cell := [270, 244, 218, 243, 192, 242, 269, 295, 294, 293, 267, 292, 241, 266, 291, 215, 265, 290, 189, 214, 239, 289, 163, 188, 213, 288, 162, 212, 136, 161, 211, 135, 137, 160, 210, 134, 138, 159, 112, 133, 158, 80, 86, 106, 113, 132, 139, 165]

theorem cells_unique : cells.Nodup := by decide +kernel
theorem phase_crates_unique : ∀ phase : Fin 13, (NetHack.SokobanLinearPhases.Map32.crates phase).Nodup := by decide +kernel
theorem cells_subset : ∀ phase : Fin 13, cells ⊆ NetHack.SokobanLinearPhases.Map32.crates phase := by decide +kernel

/-- A real original-start Trace supplies every support, phase and finite-supply
premise. The projected outcome has the exact masked update and push delta. -/
theorem trace_step_projection {directions : List Dir} {state : State} {pushes moves : Nat}
    (trace : Trace soko3_2.board soko3_2.initial directions state pushes moves)
    (direction : Dir) (t : Transition) (checked : step soko3_2.board state direction = some t) :
    ∃ phase < 12, ∃ outcome,
      state.holes = soko3_2.initial.holes.drop phase ∧ state.player ∈ NetHack.SokobanLinearPhases.Map32.heroes phase ∧
      outcome ∈ ProjectedOracle.domainChoices soko3_2.board (NetHack.SokobanLinearPhases.Map32.crates phase) cells
        (16-phase) (project state.boulders) (project (soko3_2.initial.holes.drop phase)) state.player direction ∧
      Matches state t outcome ∧
      boxes cells (project t.state.boulders) =
        ProjectedOracle.projectedAfter cells (boxes cells (project state.boulders)) outcome ∧
      Generated.soko3_2Potential.value state + slack Generated.soko3_2Potential outcome =
        Int.ofNat t.pushCost + Generated.soko3_2Potential.value t.state := by
  have good := NetHack.SokobanLinearPhases.Map32.trace_phase_invariant trace
  rcases good.2 with ⟨phase,within⟩
  have phaseEq := at_phase NetHack.SokobanLinearPhases.Map32.certificate phase state within
  have active := active_of_step NetHack.SokobanLinearPhases.Map32.certificate state
    (by rw [← phaseEq]; exact within) direction t checked
  have bound : phase < 12 := by change phaseOf soko3_2.initial.holes state < 12 at active; omega
  have holes : state.holes = soko3_2.initial.holes.drop phase := within.2.1
  have length : state.holes.length = 12-phase := by rw [holes,List.length_drop]; rfl
  have conserved := trace.conservation
  change 16 + state.holes.length = state.boulders.length + 12 at conserved
  have budget : state.boulders.length ≤ 16-phase := by omega
  rcases ProjectedOracle.model_covers_domain soko3_2.board (NetHack.SokobanLinearPhases.Map32.crates phase) cells
    (16-phase) Generated.soko3_2Potential state direction t
    (phase_crates_unique ⟨phase,by omega⟩) cells_unique (cells_subset ⟨phase,by omega⟩)
    good.1 within.2.2.2 budget checked with ⟨outcome,member,effect,updated,cost⟩
  rw [holes] at member
  exact ⟨phase,bound,outcome,holes,within.2.2.1,member,effect,updated,cost⟩

/-- Every omitted phase-allowed cell has exactly zero scalar weight. -/
theorem outside_zero : ∀ phase : Fin 13, ∀ cell ∈ NetHack.SokobanLinearPhases.Map32.crates phase,
    cell ∉ cells → Generated.soko3_2Potential.boulder cell = 0 := by decide +kernel

/-- This window loses no scalar value on any original-start Trace. -/
theorem trace_weight_exact {directions : List Dir} {state : State} {pushes moves : Nat}
    (trace : Trace soko3_2.board soko3_2.initial directions state pushes moves) :
    LowerBounds.weightSum Generated.soko3_2Potential.boulder (cells.filter state.boulders.contains) =
      LowerBounds.weightSum Generated.soko3_2Potential.boulder state.boulders := by
  have good := NetHack.SokobanLinearPhases.Map32.trace_phase_invariant trace
  rcases good.2 with ⟨phase, within⟩
  have zero : ∀ cell ∈ state.boulders, cell ∉ cells → Generated.soko3_2Potential.boulder cell = 0 := by
    intro cell member outside
    exact outside_zero ⟨phase,by have := within.1; change phase ≤ 12 at this; omega⟩ cell
      (within.2.2.2 member) outside
  have recovered := HistogramRecovery.full_weight cells (fun _ => 0) (fun _ => 0) [0]
    (by decide +kernel) Generated.soko3_2Potential.boulder state cells_unique good.1
    (by intro cell member outside; simp)
    (by intro cell member outside; exact (zero cell member outside).symm)
  simpa [LowerBounds.weightSum] using recovered

end NetHack.Soko32ZeroSlack48.Projection
