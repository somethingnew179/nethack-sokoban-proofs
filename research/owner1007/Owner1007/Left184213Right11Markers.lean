import Owner1007.Left184213Right11
import Owner1007.Upper190Identity11
import Owner1007.QuietFixed11
namespace Owner1007.Left184213Right11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem quiet_markers {state final dirs pushes moves outcomes}
 (i : Fin 2)
 (quiet : UpperQuiet11.Quiet paid state (locks i) dirs final pushes moves outcomes)
 (actual : state.boulders.Nodup) (inside : locks i⊆state.boulders)
 (j : Fin 2) (retained : locks j⊆endGroup (locks i) outcomes) :
 endGroup [u i] outcomes=[u j] ∧endGroup [184] outcomes=[184] ∧
 endGroup [189] outcomes=[189] ∧endGroup [213] outcomes=[213]:=by
 have fixed184:=no_push_unchanged [184] outcomes (quiet.fixed (by simp [locks]) (by intro d;exact Or.inl rfl))
 have fixed189:=no_push_unchanged [189] outcomes (quiet.fixed (by simp [locks]) (by intro d;exact Or.inr (Or.inr (Or.inl rfl))))
 have fixed213:=no_push_unchanged [213] outcomes (quiet.fixed (by simp [locks]) (by intro d;exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
 have othersInside : [184,189,213]⊆state.boulders:=by
  have sub : ∀i,([184,189,213]:List Cell)⊆locks i:=by decide +kernel
  exact List.Subset.trans (sub i) inside
 have second:=HeroLedger.Logged.end_append_perm quiet.logged actual [189] [213] (by decide)
  (List.Subset.trans (show ([189,213]:List Cell)⊆[184,189,213] by decide) othersInside)
 rw [fixed189,fixed213] at second
 have first:=HeroLedger.Logged.end_append_perm quiet.logged actual [184] [189,213] (by decide) othersInside
 rw [fixed184] at first
 have otherSame : (endGroup [184,189,213] outcomes).Perm [184,189,213]:=
  first.trans ((List.Perm.refl [184]).append second)
 have initialPerm : ([u i]++[184,189,213]).Perm (locks i):=by
  have all : ∀i,([u i]++[184,189,213]).Perm (locks i):=by decide +kernel
  exact all i
 have both:=HeroLedger.Logged.end_append_perm quiet.logged actual [u i] [184,189,213]
  (initialPerm.nodup_iff.mpr (unique i)) (fun c h=>inside (initialPerm.mem_iff.mp h))
 have same:=endGroup_perm initialPerm outcomes
 have allSame : (endGroup (locks i) outcomes).Perm (endGroup [u i] outcomes++[184,189,213]):=
  same.symm.trans (both.trans ((List.Perm.refl _).append otherSame))
 have uMember : u j∈endGroup (locks i) outcomes:=retained (by simp [locks])
 have split:=List.mem_append.mp (allSame.mem_iff.mp uMember)
 have markerMember : u j∈endGroup [u i] outcomes:=by
  rcases split with marker|other
  ·exact marker
  ·have outside : ∀j,u j∉([184,189,213]:List Cell):=by decide +kernel
   exact False.elim (outside j other)
 have tagged:=Upper190Identity11.singleton_member _ (u j) (Nat.le_trans (endGroup_length_le [u i] outcomes) (by simp)) markerMember
 exact ⟨tagged,fixed184,fixed189,fixed213⟩
#print axioms quiet_markers
end Owner1007.Left184213Right11
