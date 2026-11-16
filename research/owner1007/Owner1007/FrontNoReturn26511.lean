import Owner1007.Front26511Geometry
import Owner1007.Upper216Eight11
import Owner1007.OneWayToken11
import Owner1007.WestRankHead11
namespace Owner1007.FrontNoReturn26511
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.Front26511
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def returnCheck (i : Fin 3) (source : Cell) (dir : Dir) : Bool :=
 if paid source dir then true else
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>if hero∈region i then
   if BlockedPush soko1_1.board (locks i) source dir then true else
    (pushTargets soko1_1.board source dir).all fun dest=>decide (dest≠265)
  else true

theorem return_checked : (List.finRange 3).all (fun i=>(locks i).all (fun source=>allDirs.all (returnCheck i source)))=true := by decide +kernel

theorem complete (i : Fin 3) (group : List Cell) (bounded : group.length≤1)
 (selected : locks i⊆group) (source : Cell) (owner : source∈group) : source∈locks i := by
 by_cases member : source∈locks i
 ·exact member
 ·have all : source::locks i⊆group := List.cons_subset.mpr ⟨owner,selected⟩
  have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,unique i⟩) all
  simp only [List.length_cons,size i] at card
  omega

theorem landing_avoids {state : State} {dir : Dir} {t : Transition} {source dest : Cell}
 (i : Fin 3) (hero : state.player∈region i) (physical : locks i⊆state.boulders)
 (member : source∈locks i) (checked : step soko1_1.board state dir=some t)
 (metadata : t.pushSource=some source) (unpaid : ¬paid source dir)
 (target : dest∈pushTargets soko1_1.board source dir) : dest≠265 := by
 have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp return_checked i (by simp)) source member) dir (Geometry.all_directions dir)
 have adjacent := PairPost11.source_adjacent checked metadata
 have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player
   (step_player_clear _ _ _ _ checked).1 dir source adjacent
 have unblocked := WestRankHead11.source_unblocked checked metadata physical
 simp only [returnCheck,if_neg unpaid,behind,if_pos hero,if_neg unblocked] at row
 exact of_decide_eq_true (List.all_eq_true.mp row dest target)

theorem step_avoids {state group dir t outcome}
 (good : OwnedCorral11.Good locks region state group) (bounded : group.length≤1)
 (inside : group⊆state.boulders) (checked : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (avoid : ¬OwnedCorral11.PaidStep paid group dir t) : OneWayToken11.AvoidLanding 265 group outcome := by
 cases outcome with
 |walk c=>trivial
 |push source ending=>
  cases ending with
  |fill hole=>trivial
  |stay dest=>
   intro owner
   obtain ⟨i,hero,selected⟩ := good
   have member := complete i group bounded selected source owner
   have metadata : t.pushSource=some source := by rw [effect.2]
   have unpaid : ¬paid source dir := fun pays=>avoid ⟨source,owner,metadata,pays⟩
   exact landing_avoids i hero (List.Subset.trans selected inside) member checked metadata unpaid
     (UpperQuiet11.stay_geometry checked effect).2

theorem quiet_no_return {state group dirs final pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (actual : state.boulders.Nodup) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤1)
 (good : OwnedCorral11.Good locks region state group) (holes : state.holes⊆soko1_1.initial.holes) :
 OneWayToken11.NoReturn 265 group outcomes := by
 induction quiet with
 |nil=>trivial
 |@cons state group dir t rest final pushes moves outcome outcomes checked effect avoid tail ih=>
  have nextActual := step_boulders_nodup _ _ _ _ actual checked
  have nextUnique := GhostSubset.update_unique _ _ _ effect nextActual group groupUnique inside
  have nextInside := GhostSubset.update_subset _ _ _ effect group groupUnique inside
  have nextBound := Nat.le_trans (update_length group outcome) bounded
  have nextGood := OwnedCorralAny11.step_good_except closed unique good inside holes checked effect avoid
  have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ checked).subset holes
  exact ⟨step_avoids good bounded inside checked effect avoid,
    ih nextActual nextUnique nextInside nextBound nextGood nextHoles⟩

theorem stationary_if_present {state dirs final pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid state [265] dirs final pushes moves outcomes)
 (actual : state.boulders.Nodup) (inside : [265]⊆state.boulders)
 (good : OwnedCorral11.Good locks region state [265]) (holes : state.holes⊆soko1_1.initial.holes)
 (present : 265∈endGroup [265] outcomes) : ownPushes [265] outcomes=0 := by
 have noReturn := quiet_no_return quiet actual (by decide) inside (by decide) good holes
 exact (OneWayToken11.historical quiet.logged actual 265 [265] (by decide) inside noReturn present).2
#print axioms return_checked
#print axioms stationary_if_present
end Owner1007.FrontNoReturn26511
