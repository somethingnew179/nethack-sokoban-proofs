import Owner1007.TokenAccounting
import NetHack.Soko32Disjoint.MapFacts

namespace Owner1007.LeftPhases32
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.PatternCorrection NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection

def region : List Cell := [133,159,160]

/-- Four symbolic phases of just TWO mobile tokens; three more are fixed.
These are an invariant proposed from the geometry, not a game-state search. -/
def phase : Fin 4 → List Cell
  | 0 => [80,132,134,158,161]
  | 1 => [80,133,134,158,161]
  | 2 => [80,132,134,159,161]
  | 3 => [80,133,134,159,161]

def Good (group : List Cell) (hero : Cell) : Prop :=
  hero ∉ region ∧ ∃ p : Fin 4, group.Perm (phase p)

instance (group : List Cell) (hero : Cell) : Decidable (Good group hero) := by
  unfold Good
  infer_instance

def Bad (group : List Cell) : Prop :=
  [158,159] ⊆ group ∨ [160,161] ⊆ group

instance (group : List Cell) : Decidable (Bad group) := by
  unfold Bad
  infer_instance

def phaseCheck (p : Fin 4) (k : Fin 13) : Bool :=
  soko3_2.board.floor.all fun hero => allDirs.all fun dir =>
    if hero ∈ region then true else
      match stepOracle soko3_2.board (project (phase p))
        (project (soko3_2.initial.holes.drop k)) hero dir with
      | none => true
      | some outcome => decide (slack potential32 outcome ≠ 0 ∨
          Bad (update (phase p) outcome) ∨ Good (update (phase p) outcome) (nextHero outcome))

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked0 : ∀ k : Fin 13, phaseCheck 0 k = true := by
  decide +kernel

theorem checked1 : ∀ k : Fin 13, phaseCheck 1 k = true := by
  decide +kernel

theorem checked2 : ∀ k : Fin 13, phaseCheck 2 k = true := by
  decide +kernel

theorem checked3 : ∀ k : Fin 13, phaseCheck 3 k = true := by
  decide +kernel

theorem phases_checked : ∀ p : Fin 4, ∀ k : Fin 13, phaseCheck p k = true := by
  intro p
  rcases p with ⟨p, bound⟩
  have choices : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
  rcases choices with rfl | rfl | rfl | rfl
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3

theorem phase_length : ∀ p : Fin 4, (phase p).length = 5 := by decide +kernel

theorem zero_oracle_step (p : Fin 4) (k : Fin 13) (hero : Cell)
    (floor : hero ∈ soko3_2.board.floor) (outside : hero ∉ region)
    (dir : Dir) (outcome : Outcome)
    (checked : stepOracle soko3_2.board (project (phase p))
      (project (soko3_2.initial.holes.drop k)) hero dir = some outcome)
    (zero : slack potential32 outcome = 0) :
    Bad (update (phase p) outcome) ∨ Good (update (phase p) outcome) (nextHero outcome) := by
  have all : dir ∈ allDirs := by cases dir <;> simp [allDirs,cardinalDirs]
  have row := List.all_eq_true.mp (phases_checked p k) hero floor
  have cell := List.all_eq_true.mp row dir all
  simp only [if_neg outside, checked, decide_eq_true_eq] at cell
  exact cell.resolve_left (fun different => different zero)

#print axioms phases_checked
#print axioms zero_oracle_step
end Owner1007.LeftPhases32
