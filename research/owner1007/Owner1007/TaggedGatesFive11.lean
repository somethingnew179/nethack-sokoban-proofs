import Owner1007.Budget32711
namespace Owner1007.TaggedGatesFive11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def original : List Cell:=[137,139,188,191,212]
theorem owned {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (upper : energy soko1_1.initial final UpperBudget11.U6 (outcomes++last)≤6)
 (left212 : energy soko1_1.initial final [212] (outcomes++last)≤2)
 (a b c d e : Cell) (tag137 : endGroup [137] outcomes=[a]) (tag139 : endGroup [139] outcomes=[b])
 (tag188 : endGroup [188] outcomes=[c]) (tag191 : endGroup [191] outcomes=[d]) (tag212 : endGroup [212] outcomes=[e]) :
 ([a,b,c,d,e]:List Cell).Nodup ∧([a,b,c,d,e]:List Cell)⊆state.boulders ∧endGroup [a,b,c,d,e] last=[]:=by
 let whole:=first.append suffix
 have upperGone:=Budget32711.upper_gone whole completed (by omega)
 have gone212:=TightSurvivors11.singleton_nil whole completed [212] (by decide) (by decide) (by decide)
  2 left212 212 (by decide) (by decide +kernel)
 have goneOriginal : endGroup original (outcomes++last)=[]:=by
  apply TightSurvivors11.all_nil whole (by decide) original (by decide) (by decide)
  intro cell member
  have cases : cell=212∨cell∈UpperBudget11.U6:=by
   have all : original.all (fun c=>decide (c=212∨c∈UpperBudget11.U6))=true:=by decide +kernel
   exact of_decide_eq_true (List.all_eq_true.mp all cell member)
  rcases cases with rfl|inUpper
  ·exact gone212
  ·have nested:=end_subset_selected whole (by decide) [cell] UpperBudget11.U6 (by simp) (by decide)
    (by simpa using inUpper) (by decide)
   rw [upperGone] at nested
   exact List.eq_nil_iff_forall_not_mem.mpr (by intro c h;simpa using nested h)
 have one:=HeroLedger.Logged.end_append_perm first (by decide) [137] [139,188,191,212] (by decide) (by decide)
 have two:=HeroLedger.Logged.end_append_perm first (by decide) [139] [188,191,212] (by decide) (by decide)
 have three:=HeroLedger.Logged.end_append_perm first (by decide) [188] [191,212] (by decide) (by decide)
 have four:=HeroLedger.Logged.end_append_perm first (by decide) [191] [212] (by decide) (by decide)
 rw [tag137] at one
 rw [tag139] at two
 rw [tag188] at three
 rw [tag191,tag212] at four
 have perm : (endGroup original outcomes).Perm [a,b,c,d,e]:=
  one.trans ((List.Perm.refl [a]).append (two.trans ((List.Perm.refl [b]).append
   (three.trans ((List.Perm.refl [c]).append four)))))
 have facts:=first.end_subset (by decide) original (by decide) (by decide)
 refine ⟨perm.nodup_iff.mp facts.1,(fun cell member=>facts.2 (perm.mem_iff.mpr member)),?_⟩
 rw [endGroup_append] at goneOriginal
 have same:=endGroup_perm perm last
 rw [goneOriginal] at same
 exact List.perm_nil.mp same.symm
#print axioms owned
end Owner1007.TaggedGatesFive11
