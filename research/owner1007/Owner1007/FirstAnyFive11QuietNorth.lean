import Owner1007.FirstAnyFive11
import Owner1007.FirstRest18711
namespace Owner1007.FirstAnyFive11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem quiet_no_north {state selected dirs final pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet (fun _ _=>True) state selected dirs final pushes moves outcomes)
 (unique : selected.Nodup) (inside : selected⊆state.boulders) (holds187 : 187∈selected)
 (group : List Cell) :
 PaidCount11.count FirstRest18711.paid group dirs outcomes=0:=by
 induction quiet generalizing group with
 |nil=>rfl
 |@cons state selected dir t rest final pushes moves outcome outcomes checked effect avoid tail ih=>
  have noHead : ¬PaidCount11.owned FirstRest18711.paid group dir outcome:=by
   intro pays
   obtain ⟨source,owner,metadata,same,north⟩:=(PaidCount11.owned_iff effect).mp pays
   subst source
   have present : [187]⊆state.boulders:=by simpa using inside holds187
   have blocked:=WestRankHead11.source_unblocked checked metadata present
   have isBlocked : BlockedPush soko1_1.board [187] 213 dir:=by rw [north];decide +kernel
   exact blocked isBlocked
  have allZero:=quiet_zero (UpperQuiet11.Quiet.cons checked effect avoid tail)
  have headZero : ownPush selected outcome=0:=by simp only [ownPushes] at allZero;omega
  have unchanged:=ownPush_zero_update selected outcome headZero
  have nextInside:=GhostSubset.update_subset _ _ _ effect selected unique inside
  have later:=ih (by simpa only [unchanged] using unique) nextInside (by simpa only [unchanged] using holds187) (update group outcome)
  simpa only [PaidCount11.count,if_neg noHead,Nat.zero_add] using later
#print axioms quiet_no_north
end Owner1007.FirstAnyFive11
