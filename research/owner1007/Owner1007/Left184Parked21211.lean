import Owner1007.Left212BeforeRest11
import Owner1007.Left239BeforeRest11
import Owner1007.LeftPre21411
import Owner1007.Post214LeftTwo11
namespace Owner1007.Left184Parked21211
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem from_left
 {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (cheap : pushes+lastPushes<335)
 (upper : energy soko1_1.initial final UpperBudget11.U6 (outcomes++last)≤6)
 (left186 : energy soko1_1.initial final [186] (outcomes++last)≤4)
 (left212 : energy soko1_1.initial final [212] (outcomes++last)≤2)
 (rest : energy soko1_1.initial final UpperBudget11.Rest (outcomes++last)<2)
 (noRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest dirs outcomes=0)
 (prefixFour : 4≤energy soko1_1.initial state [186] outcomes)
 (tag186 : endGroup [186] outcomes=[184])
 (tag188 : endGroup [188] outcomes=[187])
 (tag191 : endGroup [191] outcomes=[189])
 (hero185 : state.player=185) : False := by
 let full:=first.append suffix
 obtain ⟨cell,member,tag212,rankBound⟩:=Left212BeforeRest11.word first suffix completed cheap rest noRest (by omega)
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
  intro c member
  change c∈([186,212,188,191]:List Cell) at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;>assumption
 have leftPerm:=(HeroLedger.Logged.end_append_perm first (by decide) [186] [212] (by decide) (by decide))
 rw [tag186,tag212] at leftPerm
 have upperPerm:=(HeroLedger.Logged.end_append_perm first (by decide) [188] [191] (by decide) (by decide))
 rw [tag188,tag191] at upperPerm
 have split:=(HeroLedger.Logged.end_append_perm first (by decide) [186,212] [188,191] (by decide) (by decide))
 have currentPerm : (endGroup original outcomes).Perm [184,cell,187,189]:=split.trans (leftPerm.append upperPerm)
 have selected:=first.end_subset (by decide) original (by decide) (by decide)
 have currentUnique : ([184,cell,187,189]:List Cell).Nodup:=currentPerm.nodup_iff.mp selected.1
 have currentInside : ([184,cell,187,189]:List Cell)⊆state.boulders:=fun c h=>selected.2 (currentPerm.mem_iff.mpr h)
 have currentGone : endGroup [184,cell,187,189] last=[]:=by
  rw [endGroup_append] at goneOriginal
  have same:=endGroup_perm currentPerm last
  rw [goneOriginal] at same
  exact List.perm_nil.mp same.symm
 have fullLeft:=Hero315Frame11.energy_split full [186] [212] (by decide) (by decide)
 change energy soko1_1.initial final [186,212] (outcomes++last)=
   energy soko1_1.initial final [186] (outcomes++last)+energy soko1_1.initial final [212] (outcomes++last) at fullLeft
 have prefixLeft:=Hero315Frame11.energy_split first [186] [212] (by decide) (by decide)
 change energy soko1_1.initial state [186,212] outcomes=
   energy soko1_1.initial state [186] outcomes+energy soko1_1.initial state [212] outcomes at prefixLeft
 have appendLeft:=energy_append soko1_1.initial state final [186,212] outcomes last
 have localSame:=Hero315Frame11.energy_perm leftPerm state final last
 change energy state final (endGroup [186,212] outcomes) last=energy state final [184,cell] last at localSame
 have tailBudget : energy state final [184,cell] last≤2-Left212TwoWord11.rank cell:=by omega
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl
 ·have good : OwnedCorral11.Good LeftDeadSplit11.locks LeftDeadSplit11.region state [184,211,187,189]:=by
   refine ⟨1,?_,?_⟩
   ·rw [hero185];decide +kernel
   ·change ([184,211]:List Cell)⊆[184,211,187,189]
    decide
  exact LeftDeadSplit11.impossible_gone first.trace suffix [184,211,187,189] currentUnique currentInside good currentGone
 ·have physical : LeftPre21411.locks 0⊆state.boulders:=List.Subset.trans (by decide) currentInside
  have hero : state.player∈LeftPre21411.region 0:=by rw [hero185];decide +kernel
  have gone : endGroup (LeftPre21411.selected 0) last=[]:=currentGone
  have ticket:=LeftPre21411.future_four first.trace suffix 0 physical hero gone
  have rank : Left212TwoWord11.rank 212=0:=by decide +kernel
  change 4≤energy state final [184,212] last at ticket
  rw [rank] at tailBudget
  omega
 ·have physical : LeftPre21411.locks 2⊆state.boulders:=List.Subset.trans (by decide) currentInside
  have hero : state.player∈LeftPre21411.region 2:=by rw [hero185];decide +kernel
  have gone : endGroup (LeftPre21411.selected 2) last=[]:=currentGone
  have ticket:=LeftPre21411.future_four first.trace suffix 2 physical hero gone
  have rank : Left212TwoWord11.rank 213=0:=by decide +kernel
  change 4≤energy state final [184,213] last at ticket
  rw [rank] at tailBudget
  omega
 ·have physical : Post214LeftTwo11.locks 0⊆state.boulders:=List.Subset.trans (by decide) currentInside
  have hero : state.player∈Post214LeftTwo11.region 0:=by rw [hero185];decide +kernel
  have gone : endGroup (Post214LeftTwo11.selected 0) last=[]:=currentGone
  have ticket:=Post214LeftTwo11.future_two first.trace suffix 0 physical hero gone
  have rank : Left212TwoWord11.rank 214=2:=by decide +kernel
  change 2≤energy state final [184,214] last at ticket
  rw [rank] at tailBudget
  omega
 ·have above : state.player∈Pure212Above11.region 1:=by rw [hero185];decide +kernel
  exact Left239BeforeRest11.impossible first suffix completed cheap rest (by omega) noRest tag212 above
#print axioms from_left
end Owner1007.Left184Parked21211
