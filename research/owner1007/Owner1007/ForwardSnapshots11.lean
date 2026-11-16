import Owner1007.Budget32711
import Owner1007.HeroEndSubset11
namespace Owner1007.ForwardSnapshots11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def G : List Cell := [137,139,186,188,191]
theorem pair_perm {dirs state pushes moves outcomes cell}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (fixed139 : ownPushes [139] outcomes=0) (tag : endGroup [191] outcomes=[cell]) :
 (endGroup TightSplit11.A outcomes).Perm [139,cell] := by
 have split:=HeroLedger.Logged.end_append_perm first (by decide) [139] [191] (by decide) (by decide)
 rw [no_push_unchanged _ _ fixed139,tag] at split
 exact split
theorem three_perm {dirs state pushes moves outcomes cell}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (fixed137 : ownPushes [137] outcomes=0) (fixed139 : ownPushes [139] outcomes=0)
 (tag : endGroup [191] outcomes=[cell]) :
 (endGroup [137,139,191] outcomes).Perm [137,139,cell] := by
 have one:=HeroLedger.Logged.end_append_perm first (by decide) [137] [139,191] (by decide) (by decide)
 rw [no_push_unchanged _ _ fixed137] at one
 exact one.trans ((List.Perm.refl [137]).append (pair_perm first fixed139 tag))
theorem five_perm {dirs state pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (fixed137 : ownPushes [137] outcomes=0) (fixed139 : ownPushes [139] outcomes=0)
 (tag186 : endGroup [186] outcomes=[185]) (tag188 : endGroup [188] outcomes=[187]) (tag191 : endGroup [191] outcomes=[189]) :
 (endGroup G outcomes).Perm [137,139,185,187,189] := by
 have one:=HeroLedger.Logged.end_append_perm first (by decide) [137] [139,186,188,191] (by decide) (by decide)
 have two:=HeroLedger.Logged.end_append_perm first (by decide) [139] [186,188,191] (by decide) (by decide)
 have three:=HeroLedger.Logged.end_append_perm first (by decide) [186] [188,191] (by decide) (by decide)
 have four:=HeroLedger.Logged.end_append_perm first (by decide) [188] [191] (by decide) (by decide)
 rw [no_push_unchanged _ _ fixed137] at one
 rw [no_push_unchanged _ _ fixed139] at two
 rw [tag186] at three
 rw [tag188,tag191] at four
 exact one.trans ((List.Perm.refl [137]).append (two.trans ((List.Perm.refl [139]).append
  (three.trans ((List.Perm.refl [185]).append four)))))
theorem gone {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (upper : energy soko1_1.initial final UpperBudget11.U6 outcomes≤6)
 (left : energy soko1_1.initial final [186] outcomes≤2) :
 endGroup G outcomes=[] := by
 have upperGone:=Budget32711.upper_gone logged completed (by omega)
 apply TightSurvivors11.all_nil logged (by decide) G (by decide) (by decide)
 intro cell member
 by_cases same : cell=186
 ·subst cell
  exact TightSurvivors11.singleton_nil logged completed [186] (by decide) (by decide) (by decide)
    2 left 186 (by simp) (by decide +kernel)
 ·have cases : G.all (fun c=>decide (c=186∨c∈UpperBudget11.U6))=true := by decide +kernel
  have inUpper := (of_decide_eq_true (List.all_eq_true.mp cases cell member)).resolve_left same
  have subset:=end_subset_selected logged (by decide) [cell] UpperBudget11.U6 (by simp) (by decide) (by simpa using inUpper) (by decide)
  rw [upperGone] at subset
  exact List.eq_nil_iff_forall_not_mem.mpr (by intro c h;simpa using subset h)
#print axioms five_perm
#print axioms gone
end Owner1007.ForwardSnapshots11
