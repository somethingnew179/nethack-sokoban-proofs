import NetHack.Soko11Sparse319.ModelBridge
namespace NetHack.Soko11Sparse319
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf nextPhase afterBoxes)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def base (state : State) : Int := HeroPhasePotential.value cert state
def value (state : State) : Int := base state +
  Int.ofNat (bonus (phaseOf soko1_1.initial.holes state) state.player (project state.boulders))
theorem weight_nonpositive (phase hero box : Nat) : weight phase hero box ≤ 0 := by
  change NetHack.Soko11Hero315.weight phase hero box ≤ 0
  unfold NetHack.Soko11Hero315.weight HeroPhasePotential.packedWeight
  split
  · unfold HeroPhasePotential.decodeDebt
    simp only [Int.ofNat_eq_natCast]
    omega
  · exact Int.le_refl 0
theorem base_goal_zero (state : State) (completed : Goal state) : base state = 0 := by
  have empty : state.holes = [] := completed
  have last : phaseOf soko1_1.initial.holes state  = 16 := by
    simp only [phaseOf,empty,List.length_nil,Nat.sub_zero]
    rfl
  have zeroSum (boxes : List Cell) : weightSum (weight 16 state.player) boxes = 0 := by
    induction boxes with
    | nil => rfl
    | cons box tail ih =>
      have zero : weight 16 state.player box = 0 := NetHack.Soko11Hero315.terminal state.player box
      simp only [weightSum_cons,zero,ih,Int.add_zero]
  change HeroPhasePotential.valueAt cert (phaseOf soko1_1.initial.holes state) state = 0
  rw [last]
  change weightSum (weight 16 state.player) state.boulders + weightSum holeWeight state.holes = 0
  rw [zeroSum,empty]
  rfl
theorem value_goal_zero (state : State) (completed : Goal state) : value state = 0 := by
  have empty : state.holes = [] := completed
  have last : phaseOf soko1_1.initial.holes state = 16 := by
    simp only [phaseOf,empty,List.length_nil,Nat.sub_zero]; rfl
  simp only [value,base_goal_zero state completed,last,bonus,Nat.lt_irrefl,if_false,Int.ofNat_zero,Int.add_zero]
  rfl

theorem selected_unique (p : Pattern) (outcome : Outcome) : (selected p outcome).Nodup := by
  have unique : support.Nodup := by decide +kernel
  cases outcome with
  | walk _ => exact unique.filter p
  | push source _ => exact unique.filter (fun cell => p cell && decide (cell ≠ source))
theorem selected_retained (state : State) (outcome : Outcome) (unique : state.boulders.Nodup) :
    selected (project state.boulders) outcome ⊆ HeroPhasePotential.SparseCredit.retained state outcome := by
  intro cell member
  cases outcome with
  | walk _ =>
    have found := (List.mem_filter.mp member).2
    exact List.contains_iff_mem.mp found
  | push source _ =>
    have found := Bool.and_eq_true_iff.mp (List.mem_filter.mp member).2
    exact unique.mem_erase_iff.mpr ⟨of_decide_eq_true found.2,List.contains_iff_mem.mp found.1⟩
theorem step_bound (all : ∀ phase, phase < 16 → check phase = true)
    (state : State) (direction : Dir) (t : Transition)
    (good : HazardPhases.Good phases state) (checked : step soko1_1.board state direction = some t) :
    value state ≤ Int.ofNat t.pushCost + value t.state := by
  have baseline := HeroPhasePotential.step_bound cert state direction t good checked
  change base state ≤ Int.ofNat t.pushCost + base t.state at baseline
  rcases step_result all state direction t good checked with ⟨outcome,effect,classify⟩
  rcases good.2 with ⟨phase,atIndex⟩
  have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase state atIndex
  have within : HazardPhases.At phases (phaseOf soko1_1.initial.holes state) state := by
    rw [←phaseEq]; exact atIndex
  let index := phaseOf soko1_1.initial.holes state
  have afterBonus : bonus (phaseOf soko1_1.initial.holes t.state) t.state.player (project t.state.boulders) =
      bonus (nextPhase index outcome) (nextHero outcome) (afterBoxes (project state.boulders) outcome) := by
    rw [HazardPhaseCountedCorrection.matches_phase phases state t within outcome effect,
      matches_hero state t outcome effect,
      HazardPhaseCountedCorrection.matches_boxes state t good.1 outcome effect]
  dsimp only [index] at afterBonus
  rcases classify with monotone | localBound
  · unfold value
    rw [afterBonus]
    simp only [Int.ofNat_eq_natCast] at baseline ⊢
    omega
  · have bound := HeroPhasePotential.SparseCredit.step_credit_bound cert state direction t good checked
      outcome effect (selected (project state.boulders) outcome) (selected_unique _ _)
      (selected_retained state outcome good.1) _ _ localBound
    change base state + _ ≤ Int.ofNat t.pushCost + base t.state + _ at bound
    unfold value
    rw [afterBonus]
    omega

theorem trace_bound (all : ∀ phase, phase < 16 → check phase = true)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace soko1_1.board initial directions final pushes moves)
    (initialGood : HazardPhases.Good phases initial) :
    value initial ≤ Int.ofNat pushes + value final := by
  induction trace with
  | nil => simp
  | cons head tail ih =>
    have first := step_bound all _ _ _ initialGood head
    have rest := ih (HazardPhases.step_good phases _ _ _ initialGood head)
    simp only [Int.ofNat_eq_natCast,Int.natCast_add] at first rest ⊢
    omega
theorem initial_value : value soko1_1.initial = 319 := by decide +kernel
end NetHack.Soko11Sparse319
