import Owner1007.After265EastDead12
import Owner1007.After26512
namespace Owner1007.After265LowerSurvivor12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem east_activation : ∀i:Fin 4,∀j:Fin 8,i.val=j.val→i.val<3→
 After265EastDead12.locks j⊆292::(After26512.locks i).erase 291∧
 291∈After265EastDead12.region j := by decide +kernel

/-- Crowding the lower shaft with291 forces at least one selected Lower stone
into a permanently immobile cell. No energy cap or Goal premise is needed. -/
theorem survives {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 4) (hero : state.player∈After26512.region i) (inside : After26512.locks i⊆group) :
 endGroup group outcomes≠[] := by
 intro gone
 have closed:=PricedCorral11.closed_of_checkExcept _ _ _ _ _ After26512.matrix
 have actual:=reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed After26512.unique logged reached group gUnique subset hero inside with event|terminal
 ·obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroHead,locksHead,pays⟩:=event.split
  have beforeReached:=reached.append first.trace
  have old:=first.end_subset actual group gUnique subset
  have nextActual:=step_boulders_nodup _ _ _ _ (beforeReached.boulders_nodup (by decide +kernel)) checked
  have nextUnique:=GhostSubset.update_unique _ _ _ effect nextActual _ old.1 old.2
  have nextSubset:=GhostSubset.update_subset _ _ _ effect _ old.1 old.2
  have nextReached:=beforeReached.append (Trace.cons checked (Trace.nil t.state))
  have nextGone : endGroup (update (endGroup group before) outcome) after=[] := by
   rw[shape,endGroup_append] at gone
   exact gone
  cases outcome with
  |walk target=>exact False.elim pays
  |push source ending=>
   obtain ⟨owner,paid⟩:=pays
   have killed317 (targets : pushTargets soko1_2.board source dir=[317]) : False := by
    have same:=push_effect_singleton soko1_2.initial.holes beforeReached.holes_sublist.subset targets (by decide +kernel) checked effect
    subst ending
    have selected : [317]⊆update (endGroup group before) (.push source (.stay 317)) := by simp[update,move,owner,post]
    have retained:=last.locked_end_inside nextActual _ nextUnique nextSubset [317] After265EastDead12.locked317 selected
    rw[nextGone] at retained
    have impossible : (317:Cell)∈([]:List Cell) := retained (by simp)
    simpa using impossible
   rcases paid with ⟨rfl,directions⟩|⟨rfl,rfl⟩
   ·rcases directions with rfl|rfl|rfl
    ·have same:=push_effect_singleton soko1_2.initial.holes beforeReached.holes_sublist.subset
      (show pushTargets soko1_2.board 291 .east=[292] by decide +kernel) (by decide +kernel) checked effect
     subst ending
     obtain ⟨result,_,push⟩:=effect_push_data checked effect
     obtain ⟨dest,next,_,_,clear⟩:=(push_first_clear soko1_2.board middle 291 .east result push).2
     have destEq : dest=292 := Option.some.inj (next.symm.trans (by decide +kernel))
     have clear292 : 292∉middle.boulders := by simpa only[destEq] using clear
     have small : j.val<3 := by
      by_cases yes:j.val<3
      ·exact yes
      ·have val:j.val=3:=by have h:=j.isLt;omega
       have same:j=(3:Fin 4):=Fin.ext val
       subst j
       exact False.elim (clear292 (old.2 (locksHead (by decide +kernel))))
     let k:Fin 8:=⟨j.val,by omega⟩
     obtain ⟨shift,heroNext⟩:=east_activation j k rfl small
     have kept:=CageFour12.shifted_inside (After26512.unique j) locksHead owner shift
     have heroAfter : t.state.player∈After265EastDead12.region k := by
      rw[matches_hero middle t (.push 291 (.stay 292)) effect]
      exact heroNext
     exact After265EastDead12.impossible_gone last nextReached _ nextUnique nextSubset k heroAfter kept nextGone
    ·have noWest : ∀i,∀hero∈After26512.region i,advance soko1_2.board hero .west≠some 291 := by decide +kernel
     obtain ⟨_,adjacent,_⟩:=effect_push_data checked effect
     exact noWest j middle.player heroHead adjacent
    ·exact killed317 (by decide +kernel)
   ·exact killed317 (by decide +kernel)
 ·obtain ⟨j,_,retained⟩:=terminal
  rw[gone] at retained
  have member : (291:Cell)∈After26512.locks j := by simp[After26512.locks]
  exact List.not_mem_nil (retained member)
#print axioms survives
end Owner1007.After265LowerSurvivor12
