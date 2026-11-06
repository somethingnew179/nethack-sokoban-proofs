import NetHack.Soko31Sparse134.ModelBridge
namespace NetHack.Soko31Sparse134
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf nextPhase afterBoxes)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def base (state : State) : Int := HeroPhasePotential.value cert state
def value (state : State) : Int := base state +
  Int.ofNat (bonus (phaseOf soko3_1.initial.holes state) state.player (project state.boulders))
theorem bonus_bound (phase hero : Nat) (p : Pattern) : bonus phase hero p ≤ 1 := by
  unfold bonus; split <;> omega
theorem weight_nonpositive (phase hero box : Nat) : weight phase hero box ≤ 0 := by
  change NetHack.Soko31Hero133.weight phase hero box ≤ 0
  unfold NetHack.Soko31Hero133.weight HeroPhasePotential.packedWeight
  split
  · unfold HeroPhasePotential.decodeDebt
    simp only [Int.ofNat_eq_natCast]
    omega
  · exact Int.le_refl 0
theorem base_goal_zero (state : State) (completed : Goal state) : base state = 0 := by
  have empty : state.holes = [] := completed
  have last : phaseOf soko3_1.initial.holes state = 15 := by
    simp only [phaseOf,empty,List.length_nil,Nat.sub_zero]
    rfl
  have zeroSum (boxes : List Cell) : weightSum (weight 15 state.player) boxes = 0 := by
    induction boxes with
    | nil => rfl
    | cons box tail ih =>
      have zero : weight 15 state.player box = 0 := NetHack.Soko31Hero133.terminal state.player box
      simp only [weightSum_cons,zero,ih,Int.add_zero]
  change HeroPhasePotential.valueAt cert (phaseOf soko3_1.initial.holes state) state = 0
  rw [last]
  change weightSum (weight 15 state.player) state.boulders + weightSum holeWeight state.holes = 0
  rw [zeroSum,empty]
  rfl
theorem value_goal_zero (state : State) (completed : Goal state) : value state = 0 := by
  have empty : state.holes = [] := completed
  have last : phaseOf soko3_1.initial.holes state = 15 := by
    simp only [phaseOf,empty,List.length_nil,Nat.sub_zero]; rfl
  simp only [value,base_goal_zero state completed,last,bonus,Nat.lt_irrefl,false_and,
    if_false,Int.ofNat_zero,Int.add_zero]
  rfl

theorem step_bound (all : ∀ phase, phase < 15 → check phase = true)
    (state : State) (direction : Dir) (t : Transition)
    (good : HazardPhases.Good phases state) (checked : step soko3_1.board state direction = some t) :
    value state ≤ Int.ofNat t.pushCost + value t.state := by
  have baseline := HeroPhasePotential.step_bound cert state direction t good checked
  change base state ≤ Int.ofNat t.pushCost + base t.state at baseline
  have beforeBound := bonus_bound (phaseOf soko3_1.initial.holes state) state.player (project state.boulders)
  rcases step_result all state direction t good checked with ⟨outcome,effect,classify⟩
  have unique := good.1
  rcases good.2 with ⟨phase,atIndex⟩
  have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase state atIndex
  have within : HazardPhases.At phases (phaseOf soko3_1.initial.holes state) state := by
    rw [←phaseEq]; exact atIndex
  let index := phaseOf soko3_1.initial.holes state
  have afterBonus : bonus (phaseOf soko3_1.initial.holes t.state) t.state.player (project t.state.boulders) =
      bonus (nextPhase index outcome) (nextHero outcome) (afterBoxes (project state.boulders) outcome) := by
    rw [HazardPhaseCountedCorrection.matches_phase phases state t within outcome effect,
      matches_hero state t outcome effect,
      HazardPhaseCountedCorrection.matches_boxes state t unique outcome effect]
  dsimp only [index] at afterBonus
  rcases classify with monotone | pay
  · unfold value
    rw [afterBonus]
    simp only [Int.ofNat_eq_natCast] at baseline ⊢
    omega
  · cases outcome with
    | walk target => exact False.elim pay
    | push source ending =>
      cases ending with
      | stay landing =>
        have strict := HeroPhasePotential.strict_stay cert state direction t good checked source landing effect pay
        change base state ≤ base t.state at strict
        have cost : t.pushCost = 1 := by simp only [effect.2,Transition.pushCost,↓reduceIte]
        unfold value
        rw [cost]
        simp only [Int.ofNat_eq_natCast]
        omega
      | fill hole =>
        rcases pay with ⟨_,onlyHole,own,negative⟩
        have oldHole : state.holes = [hole] := within.2.1.trans onlyHole
        have bound (witness : Cell) (present : project state.boulders witness = true)
            (different : witness ≠ source) (negative : weight index state.player witness ≤ -1) :
            base state ≤ 0 := by
          have member : witness ∈ state.boulders := List.contains_iff_mem.mp present
          have retained : witness ∈ state.boulders.erase source := unique.mem_erase_iff.mpr ⟨different,member⟩
          exact HeroPhasePotential.last_fill_before_nonpositive cert index state source hole witness
            oldHole effect.1 retained (weight_nonpositive index state.player) negative own
        have before : base state ≤ 0 := by
          rcases negative with ⟨present,different,negative⟩ | ⟨present,different,negative⟩
          · exact bound 206 present different negative
          · exact bound 207 present different negative
        have done : Goal t.state := by simp [Goal,effect.2.2,oldHole]
        have after := value_goal_zero t.state done
        have cost : t.pushCost = 1 := by simp only [effect.2.2,Transition.pushCost,↓reduceIte]
        rw [after,cost]
        unfold value
        simp only [Int.ofNat_eq_natCast]
        omega

theorem trace_bound (all : ∀ phase, phase < 15 → check phase = true)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace soko3_1.board initial directions final pushes moves)
    (initialGood : HazardPhases.Good phases initial) :
    value initial ≤ Int.ofNat pushes + value final := by
  induction trace with
  | nil => simp
  | cons head tail ih =>
    have first := step_bound all _ _ _ initialGood head
    have rest := ih (HazardPhases.step_good phases _ _ _ initialGood head)
    simp only [Int.ofNat_eq_natCast,Int.natCast_add] at first rest ⊢
    omega
theorem initial_value : value soko3_1.initial = 134 := by decide +kernel
end NetHack.Soko31Sparse134
