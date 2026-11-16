import Owner1007.RightEarlyWords11
import Owner1007.Upper190Identity11
import Owner1007.QuietFixed11

namespace Owner1007.RightEarlyWords11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def G : List Cell:=[137,139,191,193]

theorem quiet_packet {state dirs pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid soko1_1.initial G dirs state pushes moves outcomes) :
 ∃i : Fin 5,state.player∈region i∧locks i⊆endGroup G outcomes∧
   endGroup [191] outcomes=[q i]∧endGroup [193] outcomes=[r i]∧
   ownPushes [137] outcomes=0∧ownPushes [139] outcomes=0:=by
 have good : OwnedCorral11.Good locks region soko1_1.initial G:=⟨0,initialHero,by decide +kernel⟩
 obtain ⟨i,hero,selected,tag,_⟩:=RankedCorral11.quiet_rank closed unique size
   (markerInside false) (refined false) quiet NetHack.SokobanLinearPhases.Map11.initial_good
   (by decide) (by decide) (by decide) 0 initialHero (by decide) (by simp)
 change endGroup [191] outcomes=[q i] at tag
 have zero137:=quiet.fixed (show 137∈G by decide) (by intro d;exact Or.inl rfl)
 have zero139:=quiet.fixed (show 139∈G by decide) (by intro d;exact Or.inr (Or.inl rfl))
 have p1:=HeroLedger.Logged.end_append_perm quiet.logged (by decide) [137] [139,191,193] (by decide) (by decide)
 have p2:=HeroLedger.Logged.end_append_perm quiet.logged (by decide) [139] [191,193] (by decide) (by decide)
 have p3:=HeroLedger.Logged.end_append_perm quiet.logged (by decide) [191] [193] (by decide) (by decide)
 rw [no_push_unchanged _ _ zero137] at p1
 rw [no_push_unchanged _ _ zero139] at p2
 rw [tag] at p3
 have combined:=p1.trans ((List.Perm.refl [137]).append
   (p2.trans ((List.Perm.refl [139]).append p3)))
 have same : (endGroup G outcomes).Perm ([137,139,q i]++endGroup [193] outcomes):=combined
 have member : r i∈endGroup G outcomes:=selected (by simp [locks])
 have absent : r i∉([137,139,q i]:List Cell):=by
   have row : (List.finRange 5).all (fun i=>decide (r i∉([137,139,q i]:List Cell)))=true:=by decide +kernel
   exact of_decide_eq_true (List.all_eq_true.mp row i (by simp))
 have tailMember : r i∈endGroup [193] outcomes:=
   (List.mem_append.mp (same.mem_iff.mp member)).resolve_left absent
 have tagR:=Upper190Identity11.singleton_member (endGroup [193] outcomes) (r i)
   (Nat.le_trans (endGroup_length_le [193] outcomes) (by simp)) tailMember
 exact ⟨i,hero,selected,tag,tagR,zero137,zero139⟩

def gateCheck : Bool:=([137,139]:List Cell).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉soko1_1.board.floor∨BlockedPush soko1_1.board [] source dir∨dir=.east∨dir=.west)
theorem gate_checked : gateCheck=true:=by decide +kernel
theorem gate_direction {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (member : source∈([137,139]:List Cell))
 (checked : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source) :
 dir=.east∨dir=.west:=by
 have floor:=(step_player_clear _ _ _ _ checked).1
 have adjacent:=PairPost11.source_adjacent checked metadata
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player floor dir source adjacent
 have row:=List.all_eq_true.mp (List.all_eq_true.mp gate_checked source member) dir (Geometry.all_directions dir)
 simp only [gateCheck,behind] at row
 exact ((of_decide_eq_true row).resolve_left (fun h=>h floor)).resolve_left
   (WestRankHead11.source_unblocked checked metadata (show ([]:List Cell)⊆state.boulders by simp))
#print axioms quiet_packet
#print axioms gate_direction
end Owner1007.RightEarlyWords11

