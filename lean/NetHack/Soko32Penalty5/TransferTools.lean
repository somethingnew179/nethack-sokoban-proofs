/- Elementary list and walking facts for the original-to-ghost simulation.
Deleting untracked obstacles or hazard walking blocks only admits more walks. -/
import NetHack.Soko32Penalty5.Graph
import NetHack.Sokoban.GhostProjection
import NetHack.Sokoban.NonlinearFacts
import NetHack.Sokoban.Reduction
namespace NetHack.Soko32Penalty5
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection NetHack.Sokoban.HazardPattern

theorem erase_subset {small large : List Cell} (subset : small ⊆ large) (unique : small.Nodup) (source : Cell) :
    small.erase source ⊆ large.erase source := by
  intro c member
  have different : c ≠ source := by
    intro same; subst c; exact List.Nodup.not_mem_erase unique member
  exact (List.mem_erase_of_ne different).mpr (subset (List.mem_of_mem_erase member))

theorem walking_of_step (state : State) (group : List Cell) (subset : group ⊆ state.boulders)
    (dir : Dir) (t : Transition) (checked : step soko3_2.board state dir = some t)
    (target : Cell) (adjacent : advance soko3_2.board state.player dir = some target)
    (floor : target ∈ soko3_2.board.floor) (clear : target ∉ group) :
    walking group state.player dir = some target := by
  have standing := step_player_clear soko3_2.board state dir t checked
  have hero : project group state.player = false := by
    have absent : state.player ∉ group := fun h => standing.2.2.1 (subset h)
    simp [project,absent]
  have corner := GhostProjection.original_corner_projected soko3_2.board state group subset dir t checked
  have door := FiniteTopology.step_target_not_door soko3_2.board state dir t target adjacent checked
  have fc : soko3_2.board.floor.contains target = true := List.contains_iff_mem.mpr floor
  have dc : soko3_2.board.doors.contains target = false := by simp [door]
  have bc : project group target = false := by simp [project,clear]
  simp only [walking,stepOracle,hero,adjacent,fc,dc,bc,corner,Bool.false_or,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,bind,pure,Option.bind_some]

theorem Path.append {actions : List Action} {first middle last : List Cell}
    {hero actor finish cost extra : Nat} (firstPath : Path actions first hero middle actor cost)
    (suffix : Path actions middle actor last finish extra) :
    Path actions first hero last finish (cost + extra) := by
  induction firstPath with
  | nil => simpa only [Nat.zero_add] using suffix
  | cons head tail ih => simpa only [Nat.add_assoc] using Path.cons head (ih suffix)

end NetHack.Soko32Penalty5
