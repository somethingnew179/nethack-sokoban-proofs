import Owner1007.ZeroWord11
import Owner1007.HeroLedger

namespace Owner1007.BudgetWords11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.PatternCorrection
open Owner1007.ZeroWord11

def pushBudgetCheck (i : Nat) : Bool :=
  allDirs.all fun dir =>
    match advance soko1_1.board (cell i) dir.opposite with
    | none => true
    | some hero =>
      if hero ∈ region i then
        match pushOracle soko1_1.board HazardPhases.emptyBoxes (project soko1_1.initial.holes) (cell i) dir with
        | none => true
        | some e => decide (2 ≤ singleSlack hero (cell i) (.push (cell i) e) ∨ Next i (.push (cell i) e))
      else true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem all_checked : (List.range 28).all pushBudgetCheck = true := by decide +kernel

theorem push_cheap_complete (i : Nat) (active : i < 28)
    (hero : Cell) (inside : hero ∈ region i) (dir : Dir) (ending : Ending)
    (behind : advance soko1_1.board (cell i) dir.opposite = some hero)
    (oracle : pushOracle soko1_1.board HazardPhases.emptyBoxes
      (project soko1_1.initial.holes) (cell i) dir = some ending)
    (cheap : singleSlack hero (cell i) (.push (cell i) ending) < 2) :
    Next i (.push (cell i) ending) := by
  have numeric := List.all_eq_true.mp all_checked i (List.mem_range.mpr active)
  have row := List.all_eq_true.mp numeric dir (Geometry.all_directions dir)
  simp only [behind, if_pos inside, oracle] at row
  exact (of_decide_eq_true row).resolve_left (fun positive => by omega)

theorem cheap_oracle_complete (i : Nat) (active : i < 28)
    (hero : Cell) (inside : hero ∈ region i) (floor : hero ∈ soko1_1.board.floor)
    (dir : Dir) (outcome : Outcome)
    (oracle : stepOracle soko1_1.board (project [cell i]) (project soko1_1.initial.holes)
      hero dir = some outcome)
    (cheap : singleSlack hero (cell i) outcome < 2) : Next i outcome := by
  obtain ⟨target, adjacent, targetFloor, door, clear, walked | pushed⟩ :=
    oracle_data _ _ _ _ _ _ oracle
  · obtain ⟨boxClear,holeClear,rfl⟩ := walked
    have different : target ≠ cell i := by
      intro same
      subst target
      simp [project] at boxClear
    have notHole : target ∉ soko1_1.initial.holes := by simpa [project] using holeClear
    exact walk_sound i (all_nodes i active) hero inside dir target adjacent targetFloor door different notHole clear
  · obtain ⟨boxPresent,ending,push,rfl⟩ := pushed
    have member : target ∈ [cell i] := List.contains_iff_mem.mp boxPresent
    have same : target = cell i := by simpa using member
    subst target
    have behind := Geometry.reverseCheck_sound soko1_1.board reverse_checked hero floor dir (cell i) adjacent
    have empty := HazardPhases.push_empty_covers soko1_1.board (project [cell i])
      (project soko1_1.initial.holes) (cell i) dir ending push
    exact push_cheap_complete i active hero inside dir ending behind empty cheap

theorem real_cheap_from_reached (i : Nat) (active : i < 28)
    {state : State} {history : List Dir} {previousPushes previousMoves : Nat}
    {dir : Dir} {t : Transition} {outcome : Outcome}
    (reached : Trace soko1_1.board soko1_1.initial history state previousPushes previousMoves)
    (present : cell i ∈ state.boulders) (holes : state.holes = soko1_1.initial.holes)
    (checked : step soko1_1.board state dir = some t) (effect : Matches state t outcome)
    (inside : state.player ∈ region i)
    (cheap : singleSlack state.player (cell i) (GhostProjection.projectedOutcome [cell i] outcome) < 2) :
    Next i (GhostProjection.projectedOutcome [cell i] outcome) := by
  have facts := reached_data reached holes
  have subset : [cell i] ⊆ state.boulders := by simpa using present
  have oracle := GhostProjection.original_matches_shadow soko1_1.board state [cell i]
    facts.1 subset facts.2 dir t checked outcome effect
  rw [holes] at oracle
  exact cheap_oracle_complete i active state.player inside (step_player_clear _ _ _ _ checked).1 dir
    (GhostProjection.projectedOutcome [cell i] outcome) oracle cheap

def value0 (state : State) (group : List Cell) : Int :=
  LowerBounds.weightSum (weight state.player) group
def gap0 (state : State) (t : Transition) (group : List Cell) (outcome : Outcome) : Int :=
  charge NetHack.Soko11Hero315.holeWeight group outcome +
    value0 t.state (update group outcome) - value0 state group

theorem singleton_gap {state : State} {t : Transition} {outcome : Outcome}
    (effect : Matches state t outcome) (box : Cell) :
    gap0 state t [box] outcome =
      singleSlack state.player box (GhostProjection.projectedOutcome [box] outcome) := by
  cases outcome with
  | walk target =>
    change t = {state := {state with player := target}, pushed := false, filled := none} at effect
    rw [effect]
    simp [gap0,value0,LowerBounds.weightSum,charge,update,GhostProjection.projectedOutcome,singleSlack]
  | push source ending =>
    by_cases same : source = box
    · subst source
      cases ending with
      | stay landing =>
        simp [gap0,value0,LowerBounds.weightSum,charge,update,move,post,
          GhostProjection.projectedOutcome,singleSlack,effect.2]
      | fill hole =>
        simp [gap0,value0,LowerBounds.weightSum,charge,update,move,post,
          GhostProjection.projectedOutcome,singleSlack,effect.2.2]
    · have notOwner : source ∉ [box] := by simp [same]
      cases ending with
      | stay landing =>
        simp [gap0,value0,LowerBounds.weightSum,charge,update,move,post,
          GhostProjection.projectedOutcome,singleSlack,effect.2,notOwner]
      | fill hole =>
        simp [gap0,value0,LowerBounds.weightSum,charge,update,move,post,
          GhostProjection.projectedOutcome,singleSlack,effect.2.2,notOwner]

#print axioms all_checked
#print axioms real_cheap_from_reached
#print axioms singleton_gap
end Owner1007.BudgetWords11
