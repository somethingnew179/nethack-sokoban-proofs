import Owner1007.After265EastPureFive12
import Owner1007.OwnedEvents12
import Owner1007.CageFour12
namespace Owner1007.After265EastDead12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- The eight old three-token footprints, with no token dropped. -/
def legacy (i : Fin 8) : Fin 16 := ⟨i.val,by have h:=i.isLt;omega⟩
def locks (i : Fin 8) := After265EastFive12.locks (legacy i)
def region (i : Fin 8) := After265EastFive12.region (legacy i)
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=318∧dir=.west)∨(source=319∧dir=.east)∨(source=293∧dir=.east)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance

theorem pushes : (List.finRange 8).all
 (FastCorral11.pushPart soko1_2.board soko1_2.initial.holes locks region paid)=true := by decide +kernel

theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem nonempty : ∀i,locks i≠[] := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes locks region paid := by
 constructor
 ·intro i hero member dir target adjacent isFloor door notLock corner
  exact After265EastFive12.closed.1 (legacy i) hero member dir target adjacent isFloor door notLock corner
 ·intro i hero member dir source owner adjacent
  have row:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp pushes i (by simp)) source owner) dir (Geometry.all_directions dir)
  have behind:=Geometry.reverseCheck_sound soko1_2.board After265EastFive12.reverse hero (After265EastFive12.floors (legacy i) member) dir source adjacent
  simp only[behind] at row
  exact (of_decide_eq_true row).resolve_left (fun h=>h member)

theorem locked317 : Locked soko1_2.board [317] := locked_of_check _ _ (by decide +kernel)
theorem locked320 : Locked soko1_2.board [320] := locked_of_check _ _ (by decide +kernel)
theorem locked294 : Locked soko1_2.board [294] := locked_of_check _ _ (by decide +kernel)

theorem impossible_gone {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 8) (hero : state.player∈region i) (inside : locks i⊆group)
 (gone : endGroup group outcomes=[]) : False := by
 have actual:=reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 ·obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroHead,locksHead,pays⟩:=event.split
  have beforeReached:=reached.append first.trace
  have old:=first.end_subset actual group gUnique subset
  have nextActual:=step_boulders_nodup _ _ _ _ (beforeReached.boulders_nodup (by decide +kernel)) checked
  have nextUnique:=GhostSubset.update_unique _ _ _ effect nextActual _ old.1 old.2
  have nextSubset:=GhostSubset.update_subset _ _ _ effect _ old.1 old.2
  have nextGone : endGroup (update (endGroup group before) outcome) after=[] := by
   rw[shape,endGroup_append] at gone
   exact gone
  cases outcome with
  |walk target=>exact False.elim pays
  |push source ending=>
   obtain ⟨owner,paid⟩:=pays
   have kill {landing : Cell} (targets : pushTargets soko1_2.board source dir=[landing])
    (noHole : landing∉soko1_2.initial.holes) (locked : Locked soko1_2.board [landing]) : False := by
    have same:=push_effect_singleton soko1_2.initial.holes beforeReached.holes_sublist.subset targets noHole checked effect
    subst ending
    have selected : [landing]⊆update (endGroup group before) (.push source (.stay landing)) := by
     simp[update,move,owner,post]
    have retained:=last.locked_end_inside nextActual _ nextUnique nextSubset [landing] locked selected
    rw[nextGone] at retained
    have impossible : landing∈([]:List Cell) := retained (by simp)
    simpa using impossible
   rcases paid with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
   ·exact kill (by decide +kernel) (by decide +kernel) locked317
   ·exact kill (by decide +kernel) (by decide +kernel) locked320
   ·exact kill (by decide +kernel) (by decide +kernel) locked294
 ·obtain ⟨j,_,retained⟩:=terminal
  rw[gone] at retained
  exact nonempty j (List.eq_nil_iff_forall_not_mem.mpr (by intro c h;exact List.not_mem_nil (retained h)))
#print axioms pushes
#print axioms closed
#print axioms impossible_gone
end Owner1007.After265EastDead12
