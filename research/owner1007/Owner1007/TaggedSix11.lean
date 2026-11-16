import Owner1007.TaggedFour11
import Owner1007.HeroEndSubset11
namespace Owner1007.TaggedSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Ownership of the two untouched gates and four tracked corridor boulders. -/
theorem owned {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (upper : energy soko1_1.initial final UpperBudget11.U6 (outcomes++last)≤6)
 (left186 : energy soko1_1.initial final [186] (outcomes++last)≤4)
 (left212 : energy soko1_1.initial final [212] (outcomes++last)≤2)
 (fixed137 : ownPushes [137] outcomes=0) (fixed139 : ownPushes [139] outcomes=0)
 (a b c d : Cell) (tag186 : endGroup [186] outcomes=[a]) (tag212 : endGroup [212] outcomes=[b])
 (tag188 : endGroup [188] outcomes=[c]) (tag191 : endGroup [191] outcomes=[d]) :
 ([137,139,a,b,c,d]:List Cell).Nodup ∧([137,139,a,b,c,d]:List Cell)⊆state.boulders ∧
 endGroup [137,139,a,b,c,d] last=[] ∧[137,139,c,d]⊆endGroup UpperBudget11.U6 outcomes := by
 let full:=first.append suffix
 have upperGone:=Budget32711.upper_gone full completed (by omega)
 have gone137 : endGroup [137] (outcomes++last)=[] := by
  have sub:=end_subset_selected full (by decide) [137] UpperBudget11.U6 (by decide) (by decide) (by decide) (by decide)
  rw [upperGone] at sub
  exact List.eq_nil_iff_forall_not_mem.mpr (by intro x h; simpa using sub h)
 have gone139 : endGroup [139] (outcomes++last)=[] := by
  have sub:=end_subset_selected full (by decide) [139] UpperBudget11.U6 (by decide) (by decide) (by decide) (by decide)
  rw [upperGone] at sub
  exact List.eq_nil_iff_forall_not_mem.mpr (by intro x h; simpa using sub h)
 have gone186:=TightSurvivors11.singleton_nil full completed [186] (by decide) (by decide) (by decide)
   4 left186 186 (by decide) (by decide +kernel)
 have gone212:=TightSurvivors11.singleton_nil full completed [212] (by decide) (by decide) (by decide)
   2 left212 212 (by decide) (by decide +kernel)
 have gone188:=TightSurvivors11.singleton_nil full completed UpperBudget11.U6 (by decide) (by decide) (by decide)
   6 upper 188 (by decide) (by decide +kernel)
 have gone191:=TightSurvivors11.singleton_nil full completed UpperBudget11.U6 (by decide) (by decide) (by decide)
   6 upper 191 (by decide) (by decide +kernel)
 let original : List Cell:=[137,139,186,212,188,191]
 have goneOriginal : endGroup original (outcomes++last)=[]:=by
  apply TightSurvivors11.all_nil full (by decide) original (by decide) (by decide)
  intro cell member
  change cell∈([137,139,186,212,188,191]:List Cell) at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;>assumption
 have gatesPerm:=HeroLedger.Logged.end_append_perm first (by decide) [137] [139] (by decide) (by decide)
 rw [no_push_unchanged _ _ fixed137,no_push_unchanged _ _ fixed139] at gatesPerm
 have leftPerm:=HeroLedger.Logged.end_append_perm first (by decide) [186] [212] (by decide) (by decide)
 rw [tag186,tag212] at leftPerm
 have upperPerm:=HeroLedger.Logged.end_append_perm first (by decide) [188] [191] (by decide) (by decide)
 rw [tag188,tag191] at upperPerm
 have fourPerm:=HeroLedger.Logged.end_append_perm first (by decide) [186,212] [188,191] (by decide) (by decide)
 have currentFour : (endGroup [186,212,188,191] outcomes).Perm [a,b,c,d]:=fourPerm.trans (leftPerm.append upperPerm)
 have sixPerm:=HeroLedger.Logged.end_append_perm first (by decide) [137,139] [186,212,188,191] (by decide) (by decide)
 have currentPerm : (endGroup original outcomes).Perm [137,139,a,b,c,d]:=sixPerm.trans (gatesPerm.append currentFour)
 have selected:=first.end_subset (by decide) original (by decide) (by decide)
 have goneCurrent : endGroup [137,139,a,b,c,d] last=[] := by
  rw [endGroup_append] at goneOriginal
  have same:=endGroup_perm currentPerm last
  rw [goneOriginal] at same
  exact List.perm_nil.mp same.symm
 have currentUpper:=HeroLedger.Logged.end_append_perm first (by decide) [137,139] [188,191] (by decide) (by decide)
 have currentUpperPerm : (endGroup [137,139,188,191] outcomes).Perm [137,139,c,d]:=currentUpper.trans (gatesPerm.append upperPerm)
 have sub:=end_subset_selected first (by decide) [137,139,188,191] UpperBudget11.U6 (by decide) (by decide) (by decide) (by decide)
 exact ⟨currentPerm.nodup_iff.mp selected.1,(fun cell member=>selected.2 (currentPerm.mem_iff.mpr member)),goneCurrent,
  fun cell member=>sub (currentUpperPerm.mem_iff.mpr member)⟩
#print axioms owned
end Owner1007.TaggedSix11
