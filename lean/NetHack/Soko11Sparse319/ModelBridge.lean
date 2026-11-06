/- Every successful ORIGINAL Model action is covered by a finite classifier.
Only three occupancy bits are observed; other boulders are not deleted from
the Model or supplied without a count. The classifier uses proven necessary
conditions and the exact empty-board roll endpoint of a successful push. -/
import NetHack.Soko11Sparse319.FiniteSound
namespace NetHack.Soko11Sparse319
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf)

theorem step_result (all : ∀ phase, phase < 16 → check phase = true)
    (state : State) (direction : Dir) (t : Transition)
    (good : HazardPhases.Good phases state) (checked : step soko1_1.board state direction = some t) :
    ∃ outcome, Matches state t outcome ∧
      Result (phaseOf soko1_1.initial.holes state) state.player (project state.boulders) outcome := by
  rcases good with ⟨unique, phase, atIndex⟩
  have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase state atIndex
  have within : HazardPhases.At phases (phaseOf soko1_1.initial.holes state) state := by
    rw [←phaseEq]; exact atIndex
  let index := phaseOf soko1_1.initial.holes state
  have active : index < 16 :=
    HazardPhaseCountedCorrection.active_of_step phases state within direction t checked
  have standing := step_player_clear soko1_1.board state direction t checked
  have heroHole : state.player ∉ soko1_1.initial.holes.drop index := by
    rw [←within.2.1]; exact standing.2.2.2
  let actual : Pattern := project state.boulders
  let mask := maskOf actual
  have smallClear (cell : Cell) (absent : cell ∉ state.boulders) : known mask cell = false := by
    cases found : known mask cell with
    | false => rfl
    | true =>
      have present : actual cell = true := known_subset actual cell found
      exact False.elim (absent (List.contains_iff_mem.mp present))
  have smallCorner : corner soko1_1.board (known mask) state.player direction = false :=
    HeroPhasePotential.corner_clear_mono soko1_1.board (known mask) actual
      (fun cell selected => known_subset actual cell selected) state.player direction
      ((corner_project soko1_1.board state direction).trans
        (FiniteTopology.step_corner_clear soko1_1.board state direction t checked))
  have maskBound : mask < 16 := mask_bound actual
  rcases step_cases_full soko1_1.board state direction t checked with walked | pushed
  · rcases walked with ⟨target, adjacent, floor, boxClear, holeClear, shape⟩
    have door := FiniteTopology.step_target_not_door soko1_1.board state direction t target adjacent checked
    have noHole : target ∉ soko1_1.initial.holes.drop index := by rw [←within.2.1]; exact holeClear
    have allowed : WalkAllowed index state.player target mask direction :=
      ⟨standing.1,standing.2.1,heroHole,smallClear _ standing.2.2.1,
        floor,door,noHole,smallClear _ boxClear,smallCorner⟩
    have selected := walk_sound index state.player mask direction target (all index active)
      within.2.2.1 maskBound adjacent allowed
    exact ⟨.walk target,shape,result_lift index state.player actual (.walk target) selected⟩
  · rcases pushed with ⟨source, result, adjacent, floor, present, pushed, shape⟩
    have door := FiniteTopology.step_target_not_door soko1_1.board state direction t source adjacent checked
    have sourceKnown : source ∈ support → known mask source = true := by
      intro member
      change known (maskOf actual) source = true
      rw [known_agrees actual source member]
      exact List.contains_iff_mem.mpr present
    have exactOracle := pushOracle_exact soko1_1.board state unique source direction
    rw [pushed] at exactOracle
    have physical : pushOracle soko1_1.board (project state.boulders) (project state.holes)
        source direction = some (ending result) := by
      simpa only [Option.map_some] using exactOracle.symm
    have empty := HazardPhases.push_empty_covers soko1_1.board _ _ source direction _ physical
    rw [within.2.1] at empty
    rcases (pushBoulder_spec soko1_1.board state source direction result pushed).1 with stayed | filled
    · rcases stayed with ⟨notFilled, boxesShape⟩
      have effect : Matches state t (.push source (.stay result.landing)) := by
        refine ⟨present,?_⟩
        simpa only [notFilled,boxesShape,afterFill] using shape
      have emptyStay : pushOracle soko1_1.board HazardPhases.emptyBoxes
          (project (soko1_1.initial.holes.drop index)) source direction = some (.stay result.landing) := by
        simpa only [ending,notFilled] using empty
      have nextUnique := step_boulders_nodup soko1_1.board state direction t unique checked
      have landingClear : result.landing ∉ state.boulders.erase source := by
        have uniqueAfter : (result.landing :: state.boulders.erase source).Nodup := by
          simpa only [effect.2] using nextUnique
        exact (List.nodup_cons.mp uniqueAfter).1
      have endpoint : EndpointAllowed mask source (.stay result.landing) := by
        intro selected
        by_cases same : result.landing = source
        · exact same
        apply False.elim
        have different : result.landing ≠ source := same
        have member : result.landing ∈ state.boulders :=
          List.contains_iff_mem.mp (known_subset actual result.landing selected)
        exact landingClear (unique.mem_erase_iff.mpr ⟨different,member⟩)
      have allowed : PushAllowed index state.player source mask direction (.stay result.landing) :=
        ⟨standing.1,standing.2.1,heroHole,smallClear _ standing.2.2.1,
          within.2.2.2 present,floor,door,sourceKnown,smallCorner,endpoint⟩
      have selected := push_sound index state.player mask direction source (.stay result.landing)
        (all index active) within.2.2.1 maskBound adjacent emptyStay allowed
      exact ⟨.push source (.stay result.landing),effect,
        result_lift index state.player actual (.push source (.stay result.landing)) selected⟩
    · rcases filled with ⟨hasFilled,hazard,boxesShape⟩
      have effect : Matches state t (.push source (.fill result.landing)) := by
        refine ⟨present,hazard,?_⟩
        simpa only [hasFilled,boxesShape,afterFill] using shape
      have emptyFill : pushOracle soko1_1.board HazardPhases.emptyBoxes
          (project (soko1_1.initial.holes.drop index)) source direction = some (.fill result.landing) := by
        simpa only [ending,hasFilled] using empty
      have allowed : PushAllowed index state.player source mask direction (.fill result.landing) :=
        ⟨standing.1,standing.2.1,heroHole,smallClear _ standing.2.2.1,
          within.2.2.2 present,floor,door,sourceKnown,smallCorner,True.intro⟩
      have selected := push_sound index state.player mask direction source (.fill result.landing)
        (all index active) within.2.2.1 maskBound adjacent emptyFill allowed
      exact ⟨.push source (.fill result.landing),effect,
        result_lift index state.player actual (.push source (.fill result.landing)) selected⟩
end NetHack.Soko11Sparse319
