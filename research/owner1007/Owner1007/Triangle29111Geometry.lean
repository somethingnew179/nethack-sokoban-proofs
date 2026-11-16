import Owner1007.Triangle29111Data
import Owner1007.PairFirstCut11
import Owner1007.HeroEnergyTrace11
namespace Owner1007.Triangle29111
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel

theorem unique (i : Fin 1) : (locks i).Nodup := by change ([264,266,291] : List Cell).Nodup; decide
theorem size (i : Fin 1) : (locks i).length=3 := rfl
theorem floor (i : Fin 1) : region i⊆soko1_1.board.floor := by
 have all : (region i).all (fun c=>decide (c∈soko1_1.board.floor))=true := by change (region 0).all (fun c=>decide (c∈soko1_1.board.floor))=true; decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp all c member)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 have same : i=0 := Fin.ext (by omega)
 simpa only [same] using checked
theorem complete (group : List Cell) (bounded : group.length≤3)
 (inside : locks 0⊆group) (source : Cell) (owner : source∈group) : source∈sources := by
 by_cases member : source∈sources
 · exact member
 · have all : source::sources⊆group := by
     intro c found
     rcases List.mem_cons.mp found with rfl|later
     · exact owner
     · exact inside later
   have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,by decide⟩) all
   change 4≤group.length at card
   omega
def noReturnCheck (source : Cell) (dir : Dir) : Bool :=
 if dir.diagonal then true else if paid source dir then true else
   (pushTargets soko1_1.board source dir).all fun dest => decide (dest∉sources)
theorem returns : sources.all (fun source=>allDirs.all (noReturnCheck source))=true := by decide +kernel
theorem landing_avoids (source dest : Cell) (dir : Dir) (member : source∈sources)
 (cardinal : dir.diagonal=false) (unpaid : ¬paid source dir)
 (target : dest∈pushTargets soko1_1.board source dir) : dest∉sources := by
 have row := List.all_eq_true.mp (List.all_eq_true.mp returns source member) dir (Geometry.all_directions dir)
 simp only [noReturnCheck,cardinal,Bool.false_eq_true,↓reduceIte,if_neg unpaid] at row
 exact of_decide_eq_true (List.all_eq_true.mp row dest target)
theorem quiet_no_return
 {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (actualUnique : state.boulders.Nodup) (groupUnique : group.Nodup) (inside : group⊆state.boulders)
 (bounded : group.length≤3) (good : OwnedCorral11.Good locks region state group)
 (holesInside : state.holes⊆soko1_1.initial.holes) (cell : Cell) (member : cell∈sources) :
 OneWayToken11.NoReturn cell group outcomes := by
 induction quiet with
 | nil => trivial
 | @cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih =>
   have actual := step_boulders_nodup _ _ _ _ actualUnique head
   have nextUnique := GhostSubset.update_unique _ _ _ effect actual _ groupUnique inside
   have nextInside := GhostSubset.update_subset _ _ _ effect _ groupUnique inside
   have nextBound := Nat.le_trans (update_length group outcome) bounded
   have nextGood := OwnedCorral11.step_good_except closed unique size good inside bounded holesInside head effect avoid
   have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holesInside
   refine ⟨?_,ih actual nextUnique nextInside nextBound nextGood nextHoles⟩
   cases outcome with
   | walk _ => trivial
   | push source ending =>
     cases ending with
     | fill _ => trivial
     | stay target =>
       intro owner same
       obtain ⟨i,hero,locksInside⟩ := good
       have sourceIn := complete group bounded locksInside source owner
       have unpaid : ¬paid source dir := fun paid=>avoid ⟨source,owner,by rw [effect.2],paid⟩
       obtain ⟨cardinal,targetMember⟩ := UpperQuiet11.stay_geometry head effect
       exact landing_avoids source target dir sourceIn cardinal unpaid targetMember (same ▸ member)
theorem quiet_fixed
 {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet paid state sources dirs final pushes moves outcomes)
 (actualUnique : state.boulders.Nodup) (inside : sources⊆state.boulders)
 (good : OwnedCorral11.Good locks region state sources)
 (holesInside : state.holes⊆soko1_1.initial.holes) (cell : Cell) (member : cell∈sources) :
 endGroup [cell] outcomes=[cell] := by
 have finalGood := PairFirstCut11.quiet_good closed unique size quiet actualUnique (by decide) inside (by decide) good holesInside
 obtain ⟨i,_,selected⟩ := finalGood
 have present : cell∈endGroup sources outcomes := selected member
 have historical := OneWayToken11.historical quiet.logged actualUnique cell sources (by decide) inside
   (quiet_no_return quiet actualUnique (by decide) inside (by decide) good holesInside cell member) present
 exact no_push_unchanged _ _ historical.2
#print axioms closed
#print axioms quiet_fixed


end Owner1007.Triangle29111
