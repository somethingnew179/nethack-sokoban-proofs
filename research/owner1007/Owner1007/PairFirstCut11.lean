import Owner1007.UpperFirstCut11
import Owner1007.PairBound11
import Owner1007.HeroEnergyTrace11
import Owner1007.FullSurvivor11
namespace Owner1007.PairFirstCut11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition NetHack.Sokoban.LowerBounds
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem quiet_good {n k : Nat} {locks region : Fin n→List Cell} {paid : Cell→Dir→Prop}
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (uniqueLocks : ∀ i, (locks i).Nodup) (size : ∀ i, (locks i).length=k)
 {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (actualUnique : state.boulders.Nodup) (unique : group.Nodup) (inside : group⊆state.boulders)
 (bounded : group.length≤k) (good : OwnedCorral11.Good locks region state group)
 (holesInside : state.holes⊆soko1_1.initial.holes) :
 OwnedCorral11.Good locks region final (endGroup group outcomes) := by
 induction quiet with
 | nil => exact good
 | @cons state group dir t rest final pushes moves outcome outcomes checked effect avoid tail ih =>
   have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
   have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique inside
   have nextInside := GhostSubset.update_subset state t outcome effect group unique inside
   have nextBound := Nat.le_trans (update_length group outcome) bounded
   have nextGood := OwnedCorral11.step_good_except closed uniqueLocks size good inside bounded holesInside checked effect avoid
   have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ checked).subset holesInside
   exact ih nextActual nextUnique nextInside nextBound nextGood nextHoles

def noReturnCheck : Bool := (List.finRange 9).all fun i => (PairPath11.locks i).all fun source =>
 allDirs.all fun dir => (pushTargets soko1_1.board source dir).all fun target =>
 decide (dir.diagonal=false → ¬PairPath11.paid source dir → target≠139 ∧ target≠191)
theorem no_return_checked : noReturnCheck=true := by decide +kernel

theorem landing_avoids (i : Fin 9) (source target : Cell) (dir : Dir)
 (inside : source∈PairPath11.locks i) (cardinal : dir.diagonal=false)
 (unpaid : ¬PairPath11.paid source dir) (landing : target∈pushTargets soko1_1.board source dir) :
 target≠139 ∧ target≠191 := by
 have a := List.all_eq_true.mp no_return_checked i (by simp)
 have b := List.all_eq_true.mp a source inside
 have c := List.all_eq_true.mp b dir (Geometry.all_directions dir)
 exact of_decide_eq_true (List.all_eq_true.mp c target landing) cardinal unpaid

theorem lock_complete (i : Fin 9) (group : List Cell)
 (bounded : group.length≤2) (inside : PairPath11.locks i⊆group)
 (source : Cell) (owner : source∈group) : source∈PairPath11.locks i := by
 by_cases member : source∈PairPath11.locks i
 · exact member
 · have all : source::PairPath11.locks i⊆group := by
     intro c found
     rcases List.mem_cons.mp found with rfl|later
     · exact owner
     · exact inside later
   have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,PairPath11.unique i⟩) all
   simp only [List.length_cons,PairPath11.size i] at card
   omega

theorem step_no_return {state : State} {group : List Cell} {dir : Dir} {t : Transition} {outcome : Outcome}
 (good : OwnedCorral11.Good PairPath11.locks PairPath11.region state group)
 (bounded : group.length≤2) (checked : step soko1_1.board state dir=some t)
 (effect : Matches state t outcome) (avoid : ¬OwnedCorral11.PaidStep PairPath11.paid group dir t)
 (cell : Cell) (initial : cell∈[139,191]) :
 OneWayToken11.AvoidLanding cell group outcome := by
 cases outcome with
 | walk _ => trivial
 | push source result =>
   cases result with
   | fill _ => trivial
   | stay target =>
     intro owner
     obtain ⟨i,heroInside,inside⟩ := good
     have member := lock_complete i group bounded inside source owner
     have unpaid : ¬PairPath11.paid source dir := by
       intro pays
       exact avoid ⟨source,owner,by rw [effect.2],pays⟩
     obtain ⟨cardinal,landing⟩ := UpperQuiet11.stay_geometry checked effect
     have away := landing_avoids i source target dir member cardinal unpaid landing
     simp at initial
     rcases initial with rfl|rfl <;> first | exact away.1 | exact away.2

theorem quiet_no_return {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet PairPath11.paid state group dirs final pushes moves outcomes)
 (actualUnique : state.boulders.Nodup) (unique : group.Nodup) (inside : group⊆state.boulders)
 (bounded : group.length≤2) (good : OwnedCorral11.Good PairPath11.locks PairPath11.region state group)
 (holesInside : state.holes⊆soko1_1.initial.holes) (cell : Cell) (initial : cell∈[139,191]) :
 OneWayToken11.NoReturn cell group outcomes := by
 induction quiet with
 | nil => trivial
 | @cons state group dir t rest final pushes moves outcome outcomes checked effect avoid tail ih =>
   have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
   have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique inside
   have nextInside := GhostSubset.update_subset state t outcome effect group unique inside
   have nextBound := Nat.le_trans (update_length group outcome) bounded
   have nextGood := OwnedCorral11.step_good_except PairPath11.closed PairPath11.unique PairPath11.size
     good inside bounded holesInside checked effect avoid
   have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ checked).subset holesInside
   exact ⟨step_no_return good bounded checked effect avoid cell initial,
     ih nextActual nextUnique nextInside nextBound nextGood nextHoles⟩

def originalGroup : List Cell := [139,191]
theorem initial_good : OwnedCorral11.Good PairPath11.locks PairPath11.region soko1_1.initial originalGroup := by
 refine ⟨0,?_,?_⟩ <;> decide +kernel

theorem first_cut {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : energy soko1_1.initial final originalGroup outcomes<4) :
 Nonempty (UpperFirstCut11.FirstCut PairPath11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes) := by
 rcases UpperFirstCut11.first_cut_or_quiet logged originalGroup with found|quiet
 · exact found
 · have persists := quiet_good PairPath11.closed PairPath11.unique PairPath11.size quiet
     (by decide) (by decide) (by decide) (by decide) initial_good (by simp)
   obtain ⟨i,_,selected⟩ := persists
   have card := List.Nodup.length_le_of_subset (PairPath11.unique i) selected
   rw [PairPath11.size i] at card
   have bound := endGroup_length_le originalGroup outcomes
   have same : (endGroup originalGroup outcomes).length=originalGroup.length := by
     change (endGroup originalGroup outcomes).length≤2 at bound
     change (endGroup originalGroup outcomes).length=2
     omega
   have survivor := HeroLedger.full_survivor_energy value NetHack.Soko11Hero315.holeWeight
     soko1_1.initial final originalGroup outcomes same (goal_value_zero completed _)
   change energy soko1_1.initial final originalGroup outcomes =
     Int.ofNat (ownPushes originalGroup outcomes)-value soko1_1.initial originalGroup at survivor
   have debt : value soko1_1.initial originalGroup=-34 := by decide +kernel
   have ownNN : (0:Int)≤Int.ofNat (ownPushes originalGroup outcomes) := Int.natCast_nonneg _
   omega

theorem stationary_source {dirs final pushes moves outcomes}
 (cut : UpperFirstCut11.FirstCut PairPath11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (cell : Cell) (initial : cell∈[139,191]) (present : cell∈endGroup originalGroup cut.beforeOutcomes) :
 ownPushes [cell] cut.beforeOutcomes=0 :=
 (OneWayToken11.historical cut.before.logged (by decide) cell originalGroup (by decide) (by decide)
   (quiet_no_return cut.before (by decide) (by decide) (by decide) (by decide) initial_good (by simp) cell initial) present).2
#print axioms first_cut
#print axioms stationary_source
end Owner1007.PairFirstCut11
