import Owner1007.QuietGroupFixed11
import Owner1007.WestRankHead11
import Owner1007.FirstRest18711
namespace Owner1007.BlockRestNorth11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem count_zero {state final dirs pushes moves outcomes}
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (cell : Cell) (blocks : cell=187∨cell=239) (present : cell∈state.boulders)
 (stationary : ownPushes [cell] outcomes=0) (group : List Cell) :
 PaidCount11.count FirstRest18711.paid group dirs outcomes=0 := by
 induction logged generalizing group with
 |nil=>rfl
 |@cons state dir t rest final pushes moves outcome outcomes checked effect tail ih=>
  have headZero : ownPush [cell] outcome=0:=by simp only [ownPushes] at stationary;omega
  have same:=ownPush_zero_update [cell] outcome headZero
  have tailZero : ownPushes [cell] outcomes=0:=by
   simpa only [ownPushes,headZero,same,Nat.zero_add] using stationary
  have inside : [cell]⊆state.boulders:=by simpa using present
  have updated:=GhostSubset.update_subset state t outcome effect [cell] (by simp) inside
  rw [same] at updated
  have nextPresent : cell∈t.state.boulders:=updated (by simp)
  have headNotPaid : ¬PaidCount11.owned FirstRest18711.paid group dir outcome:=by
   intro pays
   obtain ⟨source,owner,metadata,at213,north⟩:=(PaidCount11.owned_iff effect).mp pays
   have source213 : t.pushSource=some 213:=by simpa only [at213] using metadata
   have checkedNorth : step soko1_1.board state .north=some t:=by simpa only [north] using checked
   rcases blocks with rfl|rfl
   ·have unblocked:=WestRankHead11.source_unblocked checkedNorth source213 inside
    exact unblocked (by decide +kernel : BlockedPush soko1_1.board [187] 213 .north)
   ·have hero:=Owner1007.ActorPrices11.support_of_check 213 state.player .north 239 (by decide +kernel)
      (step_player_clear _ _ _ _ checkedNorth).1 (PairPost11.source_adjacent checkedNorth source213)
    have clear:=(step_player_clear _ _ _ _ checked).2.2.1
    exact clear (hero.symm ▸ present)
  have last:=ih nextPresent tailZero (update group outcome)
  simpa only [PaidCount11.count,if_neg headNotPaid,Nat.zero_add] using last
#print axioms count_zero
end Owner1007.BlockRestNorth11
