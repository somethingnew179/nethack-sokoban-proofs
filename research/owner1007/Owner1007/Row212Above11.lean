import Owner1007.Pure212Above11
import Owner1007.TransportQuiet11
namespace Owner1007.Row212Above11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- The twelve cells of row8, together with its sole southern gateway239. -/
def front (i : Fin 13) : Cell := if i.val=12 then 239 else 209+i.val
def locks (i : Fin 13) : List Cell := [front i]
def region (i : Fin 13) : List Cell :=
 if front i=213 then Pure212Above11.region 0
 else if front i=239 then Pure212Above11.region 1
 else soko1_1.board.floor.erase (front i)
abbrev paid := Gate265Transport11.paid
theorem unique : ∀i,(locks i).Nodup := by intro i;simp [locks]
theorem size : ∀i,(locks i).length=1 := by intro i;rfl
theorem floor (i : Fin 13) : region i⊆soko1_1.board.floor := by
 intro c member
 by_cases at213 : front i=213
 ·simp only [region,if_pos at213] at member
  exact Pure212Above11.floor 0 member
 ·by_cases at239 : front i=239
  ·simp only [region,if_neg at213,if_pos at239] at member
   exact Pure212Above11.floor 1 member
  ·simp only [region,if_neg at213,if_neg at239] at member
   exact List.mem_of_mem_erase member
theorem push_checked : (List.finRange 13).all
 (FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid)=true := by decide +kernel

theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 constructor
 ·intro i hero member dir target adjacent isFloor door notLock corner
  by_cases at213 : front i=213
  ·have lockEq : locks i=Pure212Above11.locks 0 := by simp [locks,at213,Pure212Above11.locks,Pure212Above11.front]
   have regEq : region i=Pure212Above11.region 0 := by simp [region,at213]
   rw [regEq] at member ⊢
   rw [lockEq] at notLock corner
   exact Pure212Above11.closed.1 0 hero member dir target adjacent isFloor door notLock corner
  ·by_cases at239 : front i=239
   ·have lockEq : locks i=Pure212Above11.locks 1 := by simp [locks,at239,Pure212Above11.locks,Pure212Above11.front]
    have regEq : region i=Pure212Above11.region 1 := by simp [region,at213,at239]
    rw [regEq] at member ⊢
    rw [lockEq] at notLock corner
    exact Pure212Above11.closed.1 1 hero member dir target adjacent isFloor door notLock corner
   ·have different : target≠front i := by simpa only [locks,List.mem_singleton] using notLock
    simp only [region,if_neg at213,if_neg at239]
    exact (List.mem_erase_of_ne different).mpr isFloor
 ·intro i hero member dir source owner adjacent
  have all:=List.all_eq_true.mp push_checked i (by simp)
  have row:=List.all_eq_true.mp (List.all_eq_true.mp all source owner) dir (Geometry.all_directions dir)
  have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (floor i member) dir source adjacent
  simp only [behind] at row
  exact (of_decide_eq_true row).resolve_left (fun outside=>outside member)

theorem complete (i : Fin 13) (group : List Cell) (bounded : group.length≤1)
 (selected : locks i⊆group) (source : Cell) (owner : source∈group) : source∈locks i := by
 by_cases member : source∈locks i
 ·exact member
 ·have all : source::locks i⊆group:=List.cons_subset.mpr ⟨owner,selected⟩
  have card:=List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,unique i⟩) all
  simp only [List.length_cons,size i] at card
  omega

theorem quiet_no_north {state final group dirs pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (actual : state.boulders.Nodup) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (bounded : group.length≤1) (good : OwnedCorral11.Good locks region state group)
 (holes : state.holes⊆soko1_1.initial.holes) :
 PaidCount11.count FirstRest18711.paid group dirs outcomes=0 := by
 induction quiet with
 |nil=>rfl
 |@cons state group dir t rest final pushes moves outcome outcomes checked effect avoid tail ih=>
  obtain ⟨i,hero,selected⟩:=good
  have headNotPaid : ¬PaidCount11.owned FirstRest18711.paid group dir outcome := by
   intro pays
   obtain ⟨source,owner,metadata,same,north⟩:=(PaidCount11.owned_iff effect).mp pays
   have member:=complete i group bounded selected source owner
   have source213 : (213:Cell)∈locks i := same ▸ member
   have checkedNorth : step soko1_1.board state .north=some t := by simpa only [north] using checked
   have heroEq:=ActorPrices11.support_of_check 213 state.player .north 239 (by decide +kernel)
      (step_player_clear _ _ _ _ checkedNorth).1 (by simpa only [same] using PairPost11.source_adjacent checkedNorth metadata)
   have forbidden : ∀i,(213:Cell)∈locks i→239∉region i := by decide +kernel
   exact forbidden i source213 (heroEq ▸ hero)
  have nextActual:=step_boulders_nodup _ _ _ _ actual checked
  have nextUnique:=GhostSubset.update_unique _ _ _ effect nextActual group uniqueGroup inside
  have nextInside:=GhostSubset.update_subset _ _ _ effect group uniqueGroup inside
  have nextBound:=Nat.le_trans (update_length group outcome) bounded
  have nextGood:=OwnedCorralAny11.step_good_except closed unique ⟨i,hero,selected⟩ inside holes checked effect avoid
  have nextHoles:=List.Subset.trans (step_holes_sublist _ _ _ _ checked).subset holes
  have last:=ih nextActual nextUnique nextInside nextBound nextGood nextHoles
  simpa only [PaidCount11.count,if_neg headNotPaid,Nat.zero_add] using last

/-- No original212 can turn north through213 before ANY stone has entered265.
This statement has no energy, Goal, marker, or total-push premise. -/
theorem no_north {dirs state pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs state pushes moves outcomes) :
 PaidCount11.count FirstRest18711.paid [212] dirs outcomes=0 := by
 have small:=TransportQuiet11.Quiet.project quiet (by decide) (by decide) (by decide) [212] (by decide) (by decide)
 have good : OwnedCorral11.Good locks region soko1_1.initial [212] := by
  refine ⟨3,?_,?_⟩ <;> decide +kernel
 exact quiet_no_north small (by decide) (by decide) (by decide) (by decide) good (by simp)
#print axioms push_checked
#print axioms closed
#print axioms no_north
end Owner1007.Row212Above11
