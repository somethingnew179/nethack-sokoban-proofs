import Owner1007.Budget32711
namespace Owner1007.TaggedFour11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem owned {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (upper : energy soko1_1.initial final UpperBudget11.U6 (outcomes++last)≤6)
 (left186 : energy soko1_1.initial final [186] (outcomes++last)≤4)
 (left212 : energy soko1_1.initial final [212] (outcomes++last)≤2)
 (a b c d : Cell) (tag186 : endGroup [186] outcomes=[a]) (tag212 : endGroup [212] outcomes=[b])
 (tag188 : endGroup [188] outcomes=[c]) (tag191 : endGroup [191] outcomes=[d]) :
 ([a,b,c,d]:List Cell).Nodup ∧([a,b,c,d]:List Cell)⊆state.boulders ∧endGroup [a,b,c,d] last=[] := by
 let full:=first.append suffix
 have gone186:=TightSurvivors11.singleton_nil full completed [186] (by decide) (by decide) (by decide)
   4 left186 186 (by decide) (by decide +kernel)
 have gone212:=TightSurvivors11.singleton_nil full completed [212] (by decide) (by decide) (by decide)
   2 left212 212 (by decide) (by decide +kernel)
 have gone188:=TightSurvivors11.singleton_nil full completed UpperBudget11.U6 (by decide) (by decide) (by decide)
   6 upper 188 (by decide) (by decide +kernel)
 have gone191:=TightSurvivors11.singleton_nil full completed UpperBudget11.U6 (by decide) (by decide) (by decide)
   6 upper 191 (by decide) (by decide +kernel)
 let original : List Cell:=[186,212,188,191]
 have goneOriginal : endGroup original (outcomes++last)=[]:=by
  apply TightSurvivors11.all_nil full (by decide) original (by decide) (by decide)
  intro cell member
  change cell∈([186,212,188,191]:List Cell) at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;>assumption
 have leftPerm:=HeroLedger.Logged.end_append_perm first (by decide) [186] [212] (by decide) (by decide)
 rw [tag186,tag212] at leftPerm
 have upperPerm:=HeroLedger.Logged.end_append_perm first (by decide) [188] [191] (by decide) (by decide)
 rw [tag188,tag191] at upperPerm
 have split:=HeroLedger.Logged.end_append_perm first (by decide) [186,212] [188,191] (by decide) (by decide)
 have currentPerm : (endGroup original outcomes).Perm [a,b,c,d]:=split.trans (leftPerm.append upperPerm)
 have selected:=first.end_subset (by decide) original (by decide) (by decide)
 refine ⟨currentPerm.nodup_iff.mp selected.1,(fun cell member=>selected.2 (currentPerm.mem_iff.mpr member)),?_⟩
 rw [endGroup_append] at goneOriginal
 have same:=endGroup_perm currentPerm last
 rw [goneOriginal] at same
 exact List.perm_nil.mp same.symm
#print axioms owned
end Owner1007.TaggedFour11
