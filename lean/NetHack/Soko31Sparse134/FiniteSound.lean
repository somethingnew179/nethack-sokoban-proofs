import NetHack.Soko31Sparse134.Mask
namespace NetHack.Soko31Sparse134
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.PatternCorrection

theorem walk_sound (phase hero mask : Nat) (direction : Dir) (target : Cell)
    (checked : check phase = true) (member : hero ∈ phases.heroes phase) (bound : mask < 8)
    (adjacent : advance soko3_1.board hero direction = some target)
    (allowed : WalkAllowed phase hero target mask direction) :
    Result phase hero (known mask) (.walk target) := by
  have selected := List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp checked hero member) mask (List.mem_range.mpr bound))
      direction (Geometry.all_directions direction)
  have part := (Bool.and_eq_true_iff.mp selected).1
  simp only [walkCheck,adjacent,if_pos allowed] at part
  exact of_decide_eq_true part
theorem push_sound (phase hero mask : Nat) (direction : Dir) (source : Cell) (result : Ending)
    (checked : check phase = true) (member : hero ∈ phases.heroes phase) (bound : mask < 8)
    (adjacent : advance soko3_1.board hero direction = some source)
    (oracle : pushOracle soko3_1.board HazardPhases.emptyBoxes
      (project (soko3_1.initial.holes.drop phase)) source direction = some result)
    (allowed : PushAllowed phase hero source mask direction result) :
    Result phase hero (known mask) (.push source result) := by
  have selected := List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp checked hero member) mask (List.mem_range.mpr bound))
      direction (Geometry.all_directions direction)
  have part := (Bool.and_eq_true_iff.mp selected).2
  simp only [pushCheck,adjacent,oracle,if_pos allowed] at part
  exact of_decide_eq_true part
end NetHack.Soko31Sparse134
