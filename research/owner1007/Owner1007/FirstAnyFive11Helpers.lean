import Owner1007.LeftInwardStartDead11
import Owner1007.Q190Upper11Bound
import Owner1007.ForwardInwardImpossible11
import Owner1007.First137RestAnywhere11
import Owner1007.Gate139EastImpossible11
namespace Owner1007.FirstAnyFive11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : List Cell := [137,139,185,187,189]
def U : List Cell := [137,139,187,189]
theorem quiet_zero {state group dirs final pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet (fun _ _=>True) state group dirs final pushes moves outcomes) :
 ownPushes group outcomes=0:=by
 induction quiet with
 | nil => rfl
 | @cons state group dir t rest final pushes moves outcome outcomes checked effect avoid tail ih =>
  have headZero : ownPush group outcome=0:=by
   cases outcome with
   | walk target => rfl
   | push source ending =>
    by_cases owner : source∈group
    ·have metadata : t.pushSource=some source:=by
      cases ending with
      | stay landing => rw [effect.2]
      | fill hole => rw [effect.2.2]
     exact False.elim (avoid ⟨source,owner,metadata,trivial⟩)
    ·simp only [ownPush,if_neg owner]
  simpa only [ownPushes,headZero,Nat.zero_add] using ih
def directionsCheck : Bool:=K.all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈soko1_1.board.floor→¬BlockedPush soko1_1.board K source dir→dir=.east∨dir=.west)
theorem directions_checked : directionsCheck=true:=by decide +kernel
theorem directions {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (inside : K⊆state.boulders) (member : source∈K)
 (checked : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source) :
 dir=.east∨dir=.west:=by
 have row:=List.all_eq_true.mp (List.all_eq_true.mp directions_checked source member) dir (Geometry.all_directions dir)
 have clear:=step_player_clear _ _ _ _ checked
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player clear.1 dir source (PairPost11.source_adjacent checked metadata)
 simp only [directionsCheck,behind] at row
 exact of_decide_eq_true row clear.1 (WestRankHead11.source_unblocked checked metadata inside)

theorem inward_impossible {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (i : Fin 2) (head : step soko1_1.board state (ForwardInwardImpossible11.direction i)=some t)
 (effect : Matches state t (.push (ForwardInwardImpossible11.source i) (.stay 138)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++.push (ForwardInwardImpossible11.source i) (.stay 138)::after)≤8)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++.push (ForwardInwardImpossible11.source i) (.stay 138)::after)<2)
 (stationary : ownPushes [LeftInwardStart11.other i] before=0)
 (inside : K⊆state.boulders)
 (gone : endGroup (update K (.push (ForwardInwardImpossible11.source i) (.stay 138))) after=[]) : False:=by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have actual:=step_boulders_nodup _ _ _ _ valid.1 head
 have nextUnique:=GhostSubset.update_unique _ _ _ effect actual K (by decide) inside
 have nextInside:=GhostSubset.update_subset _ _ _ effect K (by decide) inside
 let one : Logged soko1_1.board state [ForwardInwardImpossible11.direction i] t.state t.pushCost 1 [.push (ForwardInwardImpossible11.source i) (.stay 138)]:=
  .cons head effect (.nil _)
 let extended:=first.append one
 have otherDifferent:=ForwardInwardImpossible11.different i
 have stationaryNext : ownPushes [LeftInwardStart11.other i] (before++[.push (ForwardInwardImpossible11.source i) (.stay 138)])=0:=by
  rw [ownPushes_append,no_push_unchanged _ _ stationary,stationary]
  have otherNot : ForwardInwardImpossible11.source i∉[LeftInwardStart11.other i]:=by simpa using otherDifferent
  simp [ownPushes,ownPush,otherNot]
 have same : (update K (.push (ForwardInwardImpossible11.source i) (.stay 138))).Perm (LeftInwardStart11.locks i):=
  ForwardInwardImpossible11.shift i
 have hero : t.state.player∈LeftInwardStart11.region i:=by rw [effect.2];exact ForwardInwardImpossible11.next_hero i
 have sequence : (before++[.push (ForwardInwardImpossible11.source i) (.stay 138)])++after=before++.push (ForwardInwardImpossible11.source i) (.stay 138)::after:=by simp only [List.append_assoc,List.singleton_append]
 exact LeftInwardStart11.impossible_gone extended last completed
  (by rw [sequence];exact upperCap) (by rw [sequence];exact restCap) i stationaryNext
  (update K (.push (ForwardInwardImpossible11.source i) (.stay 138))) nextUnique nextInside same hero gone
#print axioms quiet_zero
#print axioms directions
#print axioms inward_impossible
end Owner1007.FirstAnyFive11
