import Owner1007.FirstSplit12
import Owner1007.TokenPersistence
import NetHack.Sokoban.Generated.Soko12Potential
namespace Owner1007.NorthWrap12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting

def eastState : State := {soko1_2.initial with player:=397}
def eastT : Transition := {state:=eastState,pushed:=false,filled:=none}
def northT : Transition := {state:=FirstSplit12.afterN,pushed:=true,filled:=none,pushSource:=some 371,landing:=some 345}
theorem east_step : step soko1_2.board soko1_2.initial .east = some eastT := by decide +kernel
theorem north_step : step soko1_2.board eastState .north = some northT := by decide +kernel
theorem east_effect : Matches soko1_2.initial eastT (.walk 397) := rfl
theorem north_effect : Matches eastState northT (.push 371 (.stay 345)) := by
  refine ⟨by decide +kernel,?_⟩
  rfl
theorem canonical_north {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes) :
    Logged soko1_2.board soko1_2.initial (.east :: .north :: dirs) final
      (1+pushes) (2+moves) (.walk 397 :: .push 371 (.stay 345) :: outcomes) := by
  have first := Logged.cons north_step north_effect logged
  have whole := Logged.cons east_step east_effect first
  have moveEq : 1+(1+moves)=2+moves := by omega
  simpa [eastT,northT,Transition.pushCost,moveEq] using whole
abbrev p := Generated.soko1_2Potential
theorem north_slack : slack p (.push 371 (.stay 345))=0 := by decide +kernel
theorem energy_north (group : List Cell) (outcomes : List Outcome) :
    energy p group (.walk 397 :: .push 371 (.stay 345) :: outcomes) =
    energy p (update group (.push 371 (.stay 345))) outcomes := by
  rw [energy_cons]
  simp only [projectedOutcome,slack,update,Int.zero_add]
  rw [energy_cons]
  by_cases own : 371 ∈ group
  · simp only [projectedOutcome,if_pos own,north_slack,Int.zero_add,update]
  · simp only [projectedOutcome,if_neg own,slack,Int.zero_add,update]
#print axioms canonical_north
#print axioms energy_north
end Owner1007.NorthWrap12
