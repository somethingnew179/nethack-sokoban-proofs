import Owner1007.ActorPrices11
import Owner1007.OwnedStrict11
import Owner1007.UpperHeadCases11
import Owner1007.Hero315Frame11
namespace Owner1007.Left184Price11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def check (phase : Nat) : Bool := decide (2≤ActorPrices11.price phase 185 184 183)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked : (List.range 16).all check=true := by decide +kernel
theorem price (phase : Nat) (active : phase<16) : 2≤ActorPrices11.price phase 185 184 183 :=
 of_decide_eq_true (List.all_eq_true.mp checked phase (List.mem_range.mpr active))
theorem exit_row {state : State} {t : Transition} {outcome : Outcome} {group : List Cell}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t outcome)
 (unique : group.Nodup) (inside : group⊆state.boulders) (owner : 184∈group) (metadata : t.pushSource=some 184) :
 2≤charge NetHack.Soko11Hero315.holeWeight group outcome+value t.state (update group outcome)-value state group := by
 obtain ⟨phase,atIndex⟩:=valid.2
 have phaseEq:=HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
 have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
  (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq];exact atIndex
 have active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16 :=
  HazardPhaseCountedCorrection.active_of_step _ _ within _ _ head
 have holesInside : state.holes⊆soko1_1.initial.holes := by rw [atIndex.2.1];exact (List.drop_sublist phase soko1_1.initial.holes).subset
 have outEq:=UpperHeadCases11.ordinary_effect head effect metadata
  (show pushTargets soko1_1.board 184 .west=[183] by decide +kernel) (by decide +kernel) holesInside
 subst outcome
 have target:=HeroPhasePotential.step_target soko1_1.board state .west t head
 have samePlayer : t.state.player=184 := by rw [effect.2]
 have adjacent : advance soko1_1.board state.player .west=some 184 := by simpa only [samePlayer] using target.1
 have hero:=ActorPrices11.support_of_check 184 state.player .west 185 (by decide +kernel)
  (step_player_clear _ _ _ _ head).1 adjacent
 have ownPrice : 2≤1+scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) 184 183-
  scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state.player 184 := by
  change 2≤ActorPrices11.price _ state.player 184 183
  rw [hero]
  exact price _ active
 exact OwnedStrict11.owned_stay_bound scalar state .west t valid head 184 183 effect group unique inside owner 2 ownPrice
#print axioms exit_row
end Owner1007.Left184Price11
