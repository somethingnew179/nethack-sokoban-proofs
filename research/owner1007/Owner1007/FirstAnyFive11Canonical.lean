import Owner1007.FirstAnyFive11
import Owner1007.ForwardSnapshots11
namespace Owner1007.FirstAnyFive11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem canonical_first_west {state final : State} {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤6)
 (leftCap : energy soko1_1.initial final [186] (before++outcomes)≤6)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)<2)
 (zero137 : ownPushes [137] before=0) (zero139 : ownPushes [139] before=0)
 (prefixFour : 4≤energy soko1_1.initial state UpperBudget11.U6 before)
 (tag186 : endGroup [186] before=[185]) (tag188 : endGroup [188] before=[187]) (tag191 : endGroup [191] before=[189]) :
 ∃cut : FirstCut (fun _ _=>True) state K dirs final pushes moves outcomes,
  ownPushes K cut.beforeOutcomes=0 ∧ cut.actor.pushSource=some 185 ∧ cut.direction=.west ∧
   Matches cut.middle cut.actor (.push 185 (.stay 184)):=by
 let whole:=first.append logged
 have upperGone:=Budget32711.upper_gone whole completed (by omega)
 have gone186:=TightSurvivors11.singleton_nil whole completed [186] (by decide) (by decide) (by decide)
  6 leftCap 186 (by simp) (by decide +kernel)
 have allGone : endGroup ForwardSnapshots11.G (before++outcomes)=[]:=by
  apply TightSurvivors11.all_nil whole (by decide) ForwardSnapshots11.G (by decide) (by decide)
  intro cell member
  have cases : cell=186∨cell∈UpperBudget11.U6:=by
   have all : ForwardSnapshots11.G.all (fun c=>decide (c=186∨c∈UpperBudget11.U6))=true:=by decide +kernel
   exact of_decide_eq_true (List.all_eq_true.mp all cell member)
  rcases cases with rfl|inUpper
  ·exact gone186
  ·have nested:=end_subset_selected whole (by decide) [cell] UpperBudget11.U6 (by simp) (by decide) (by simpa using inUpper) (by decide)
   rw [upperGone] at nested
   exact List.eq_nil_iff_forall_not_mem.mpr (by intro c h;simpa using nested h)
 have same : (endGroup ForwardSnapshots11.G before).Perm K:=
  ForwardSnapshots11.five_perm first zero137 zero139 tag186 tag188 tag191
 have facts:=first.end_subset (by decide) ForwardSnapshots11.G (by decide) (by decide)
 have inside : K⊆state.boulders:=fun c h=>facts.2 (same.mem_iff.mpr h)
 have tailSame:=endGroup_perm same outcomes
 rw [endGroup_append] at allGone
 rw [allGone] at tailSame
 have gone : endGroup K outcomes=[]:=List.perm_nil.mp tailSame.symm
 have nested : ∀c∈([137,139,188,191]:List Cell),endGroup [c] before⊆endGroup UpperBudget11.U6 before:=by
  intro c h
  exact end_subset_selected first (by decide) [c] UpperBudget11.U6 (by simp) (by decide)
   (by intro a member;have same:=List.mem_singleton.mp member;subst a;exact (show ([137,139,188,191]:List Cell)⊆UpperBudget11.U6 by decide) h) (by decide)
 have selected : U⊆endGroup UpperBudget11.U6 before:=by
  intro c member
  have cases : c=137∨c=139∨c=187∨c=189:=by simpa [U] using member
  rcases cases with rfl|rfl|rfl|rfl
  ·exact nested 137 (by decide) (by rw [no_push_unchanged _ _ zero137];simp)
  ·exact nested 139 (by decide) (by rw [no_push_unchanged _ _ zero139];simp)
  ·exact nested 188 (by decide) (by rw [tag188];simp)
  ·exact nested 191 (by decide) (by rw [tag191];simp)
 exact first_west first logged completed upperCap restCap zero137 zero139 prefixFour inside selected gone
#print axioms canonical_first_west
end Owner1007.FirstAnyFive11
