/- Coverage and exact slack of ALL original stay frames, and the unique
consuming-source frame. No monotonicity restriction is imposed. -/
import NetHack.Soko32Penalty5.Data
namespace NetHack.Soko32Penalty5
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
abbrev potential := Generated.soko3_2Potential
def stayFits (r : NetHack.Soko32SAT.Frames.Stay) (a : Action) : Bool :=
  decide (a.hero = r.hero ∧ a.source = r.source ∧ a.landing = some r.landing ∧
    Int.ofNat a.cost = 1 + potential.boulder r.landing - potential.boulder r.source)

theorem stays_checked : NetHack.Soko32SAT.Frames.stays.all (fun r =>
    actions.any (stayFits r) && decide (r.landing ≠ r.source)) = true := by decide +kernel

theorem stay_action (r : NetHack.Soko32SAT.Frames.Stay) (member : r ∈ NetHack.Soko32SAT.Frames.stays) :
    ∃ a ∈ actions, a.hero = r.hero ∧ a.source = r.source ∧ a.landing = some r.landing ∧
      Int.ofNat a.cost = 1 + potential.boulder r.landing - potential.boulder r.source := by
  obtain ⟨a,inside,fits⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp stays_checked r member)).1
  exact ⟨a,inside,of_decide_eq_true fits⟩

theorem stays_different (r : NetHack.Soko32SAT.Frames.Stay) (member : r ∈ NetHack.Soko32SAT.Frames.stays) :
    r.landing ≠ r.source := of_decide_eq_true (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp stays_checked r member)).2

def fillAction : Action := ⟨269,270,none,false,0⟩
theorem fill_member : fillAction ∈ actions := by simp [actions,fillAction]
theorem fill_cost : ∀ phase : Fin 12,
    (0 : Int) = 1 - potential.boulder 270 -
      potential.hole ((soko3_2.initial.holes.drop phase).headD 0) := by decide +kernel
theorem action_sources : actions.all (fun a => heroes.contains a.source) = true := by decide +kernel
theorem sources_inside : ∀ a ∈ actions, a.source ∈ heroes := by
  intro a member
  exact List.contains_iff_mem.mp (List.all_eq_true.mp action_sources a member)

end NetHack.Soko32Penalty5
