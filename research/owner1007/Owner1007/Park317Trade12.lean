import Owner1007.RightPrice4
import Owner1007.LockedTokens
import Owner1007.TokenBounds32
import Owner1007.FastCorral11
namespace Owner1007.Park317Trade12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def cells : List Cell := [345,319,371,289,290,291,292,293,318]
def locks (i : Fin 10) : List Cell := if i.val=9 then [] else [317,cells[i.val]?.getD 0]
def region (i : Fin 10) : List Cell := soko1_2.board.floor.filter fun c=>!(locks i).contains c
def prices : List Int := [4,4,2,4,5,6,5,4,2,0]
def credit (i : Fin 10) : Int := prices[i.val]?.getD 0
def target (i : Fin 10) (source : Cell) (dir : Dir) : Fin 10 :=
 match i.val,source,dir with
 |0,345,.north=>1 |0,345,.south=>2
 |1,319,.north=>7 |1,319,.south=>0 |1,319,.west=>8
 |2,371,.north=>0
 |3,289,.east=>4
 |4,290,.west=>3 |4,290,.east=>5
 |5,291,.west=>4 |5,291,.east=>6
 |6,292,.west=>5 |6,292,.east=>7
 |7,293,.west=>6
 |_,_,_=>9
def ShiftAt (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 ∃ dest∈pushTargets soko1_2.board source dir,
 pushTargets soko1_2.board source dir=[dest] ∧ dest∉soko1_2.initial.holes ∧
 locks (target i source dir)⊆dest::(locks i).erase source ∧source∈region (target i source dir) ∧
 credit i≤1+p.boulder dest-p.boulder source+credit (target i source dir)
instance (i : Fin 10) (source : Cell) (dir : Dir) : Decidable (ShiftAt i source dir) := by unfold ShiftAt;infer_instance
def pushCheck (i : Fin 10) : Bool :=
 (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_2.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i ∨BlockedPush soko1_2.board (locks i) source dir ∨ShiftAt i source dir)
theorem checked : ∀ i, pushCheck i=true := by decide +kernel
theorem reverse : Geometry.reverseCheck soko1_2.board=true := by decide +kernel
theorem floors : ∀ i, region i⊆soko1_2.board.floor := by intro i c h; exact (List.mem_filter.mp h).1
theorem closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes p locks region credit := by
 constructor
 · intro i hero heroInside dir cell adjacent floor door notLock clear
   simp[region,floor,notLock]
 · intro i hero heroInside dir source sourceInside adjacent
   have row := List.all_eq_true.mp (List.all_eq_true.mp (checked i) source sourceInside) dir (Geometry.all_directions dir)
   have behind := Geometry.reverseCheck_sound soko1_2.board reverse hero (floors i heroInside) dir source adjacent
   simp only[pushCheck,behind] at row
   rcases (of_decide_eq_true row).resolve_left (fun outside=>outside heroInside) with blocked|shift
   ·exact Or.inl blocked
   ·exact Or.inr ⟨target i source dir,shift⟩
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem debt_credit : ∀ i, 3≤i.val→credit i≤debtOf p (locks i) := by decide +kernel
theorem bad_current : ∀ i, i.val<3→∃ c,c∈locks i ∧c≠317 := by decide +kernel
theorem locked317 : Locked soko1_2.board [317] := locked_of_check _ _ (by decide +kernel)

theorem stationary317 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 (present : 317∈state.boulders) :
 ownSlack p [317] outcomes=0 ∧endGroup [317] outcomes=[317] := by
 induction logged with
 |nil=>exact ⟨rfl,rfl⟩
 |@cons state dir t rest final pushes moves outcome outcomes checked effect tail ih=>
   have inside : ([317]:List Cell)⊆state.boulders := by
     intro c h
     simpa only[List.mem_singleton.mp h] using present
   have kept := locked_update_inside locked317 inside (fun _ h=>h) checked effect
   have shape := GhostOracleFacts.matches_update state t outcome effect
   rw[←shape] at kept
   have nextPresent : 317∈t.state.boulders := kept (by simp)
   have next := ih nextPresent
   cases outcome with
   |walk target=>simpa only[ownSlack,endGroup,projectedOutcome,slack,update,Int.zero_add] using next
   |push source ending=>
     have outside := locked_push_outside locked317 inside checked effect
     simpa only[ownSlack,endGroup,projectedOutcome,if_neg outside,slack,update,move,if_neg outside,Int.zero_add] using next

theorem energy317zero {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 (present : 317∈state.boulders) : energy p [317] outcomes=0 := by
 obtain ⟨zero,same⟩:=stationary317 logged present
 unfold energy
 rw[zero,same]
 decide +kernel
#print axioms closed
#print axioms stationary317


theorem four_or_survives {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (cell : Cell) (start : cell=345 ∨ cell=319)
 (park : 317∈state.boulders) (present : cell∈state.boulders)
 (hero : state.player=318) :
 4≤energy p [cell] outcomes ∨
 (2≤energy p [cell] outcomes ∧ endGroup [cell] outcomes≠[]) := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 let group : List Cell := [317,cell]
 have gUnique : group.Nodup := by rcases start with rfl|rfl <;> decide +kernel
 have subset : group⊆state.boulders := by
   intro c h
   rcases List.mem_cons.mp h with rfl|h
   ·exact park
   ·simpa only[List.mem_singleton.mp h] using present
 let i : Fin 10 := if cell=345 then 0 else 1
 have startCredit : credit i=4 := by rcases start with rfl|rfl <;> decide +kernel
 have startLocks : locks i⊆group := by rcases start with rfl|rfl <;> decide +kernel
 have startHero : state.player∈region i := by
   rw[hero]
   rcases start with rfl|rfl <;> decide +kernel
 obtain ⟨j,_,kept,price⟩ := RightPrice4.owned_trace_price closed unique
   logged reached group gUnique subset startHero startLocks
 rw[startCredit] at price
 change 4≤ownSlack p group outcomes+credit j at price
 have debt := NonlinearFacts.weightSum_le_of_nodup_subset (fun c=>-p.boulder c)
   (locks j) (endGroup group outcomes)
   (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c; change p.boulder c≤0 at h;omega)
   (unique j) kept
 change debtOf p (locks j)≤debtOf p (endGroup group outcomes) at debt
 have split := logged.energy_split actualUnique p [317] [cell] gUnique subset
 have zero := energy317zero logged park
 change energy p group outcomes=energy p [317] outcomes+energy p [cell] outcomes at split
 rw[zero] at split
 have same : energy p group outcomes=energy p [cell] outcomes := by omega
 by_cases bad : j.val<3
 · obtain ⟨c,member,different⟩ := bad_current j bad
   have fixed := (stationary317 logged park).2
   have shape := logged.end_split actualUnique [317] [cell] gUnique subset
   rw[fixed] at shape
   have both := shape.mem_iff.mpr (kept member)
   have last : c∈endGroup [cell] outcomes := by
     rcases List.mem_append.mp both with left|right
     ·have eq : c=317 := List.mem_singleton.mp left
      exact False.elim (different eq)
     ·exact right
   have survives : endGroup [cell] outcomes≠[] := by
     intro empty
     simpa only[empty,List.not_mem_nil] using last
   have ledger := survivor_energy p cell outcomes survives
   have nonnegative : (0:Int)≤(ownPushes [cell] outcomes:Int) := Int.natCast_nonneg _
   have initialDebt : (2:Int)≤-p.boulder cell := by rcases start with rfl|rfl <;> decide +kernel
   simp only[Int.ofNat_eq_natCast] at ledger
   exact Or.inr ⟨by omega,survives⟩
 · have large : 3≤j.val := by omega
   have amount := debt_credit j large
   have bound : 4≤energy p group outcomes := by
     unfold energy
     omega
   exact Or.inl (same ▸ bound)

#print axioms four_or_survives

end Owner1007.Park317Trade12
