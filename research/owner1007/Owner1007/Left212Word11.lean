import Owner1007.ActorPrices11
import Owner1007.OwnedStrict11
import Owner1007.UpperQuiet11
import Owner1007.Guard188Word11
import Owner1007.CutStrict11
namespace Owner1007.Left212Word11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

def cells : List Cell := [212,213,239,265]
def early (source : Cell) (dir : Dir) : Prop := (source=213∧dir=.north)∨(source=265∧dir=.south)
instance (source : Cell) (dir : Dir) : Decidable (early source dir) := by unfold early;infer_instance
def check (phase : Nat) : Bool :=
 cells.all fun source=>allDirs.all fun dir=>
 if early source dir then true else
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>(pushTargets soko1_1.board source dir).all fun dest=>
   decide (dest∉soko1_1.initial.holes ∧(dest∈cells∨2≤ActorPrices11.price phase hero source dest))
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked : (List.range 16).all check=true := by decide +kernel
theorem numeric (phase : Nat) (active : phase<16) (source hero dest : Cell) (dir : Dir)
 (member : source∈cells) (unpaid : ¬early source dir)
 (behind : advance soko1_1.board source dir.opposite=some hero)
 (target : dest∈pushTargets soko1_1.board source dir) :
 dest∉soko1_1.initial.holes ∧(dest∈cells∨2≤ActorPrices11.price phase hero source dest) := by
 have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp checked phase (List.mem_range.mpr active)) source member) dir (Geometry.all_directions dir)
 simp only [if_neg unpaid,behind] at row
 exact of_decide_eq_true (List.all_eq_true.mp row dest target)

theorem one_step {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {cell : Cell}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (member : cell∈cells) (present : cell∈state.boulders)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (avoid : ¬OwnedCorral11.PaidStep early [cell] dir t)
 (cheap : charge NetHack.Soko11Hero315.holeWeight [cell] outcome+
   value t.state (update [cell] outcome)-value state [cell]<2) :
 ∃dest,dest∈cells ∧update [cell] outcome=[dest] := by
 cases outcome with
 |walk target=>exact ⟨cell,member,rfl⟩
 |push source ending=>
  by_cases owner : source∈[cell]
  ·have same : source=cell := by simpa only [List.mem_singleton] using owner
   subst source
   have metadata : t.pushSource=some cell := by
    cases ending with
    |stay target=>rw [effect.2]
    |fill hole=>rw [effect.2.2]
   have unpaid : ¬early cell dir := fun pays=>avoid ⟨cell,by simp,metadata,pays⟩
   rcases step_cases_full _ _ _ _ head with walked|pushed
   ·obtain ⟨target,_,_,_,_,shape⟩ := walked
    simp only [shape] at metadata
    contradiction
   ·obtain ⟨other,result,adjacent,_,_,push,shape⟩ := pushed
    have same : other=cell := by simpa only [shape,Option.some.injEq] using metadata
    subst other
    have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player
      (step_player_clear _ _ _ _ head).1 dir cell adjacent
    obtain ⟨phase,atIndex⟩ := valid.2
    have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
    have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
      (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq];exact atIndex
    have active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16 :=
      HazardPhaseCountedCorrection.active_of_step _ _ within _ _ head
    have spec := pushBoulder_spec _ _ _ _ _ push
    have row := numeric _ active cell state.player result.landing dir member unpaid behind spec.2
    have holesInside : state.holes⊆soko1_1.initial.holes := by rw [atIndex.2.1];exact (List.drop_sublist phase _).subset
    have noFill : result.filled=none := by
     rcases spec.1 with stay|fill
     ·exact stay.1
     ·exact False.elim (row.1 (holesInside fill.2.1))
    have landed : t.landing=some result.landing := by simp only [shape]
    have filled : t.filled=none := by simpa only [shape] using noFill
    have endingEq := CutStrict11.outcome_stay effect metadata landed filled
    have actualEffect : Matches state t (.push cell (.stay result.landing)) := by simpa only [endingEq] using effect
    rcases row.2 with inside|price
    ·refine ⟨result.landing,inside,?_⟩
     have singletonEq : update [cell] (.push cell ending)=update [cell] (.push cell (.stay result.landing)) :=
       congrArg (update [cell]) endingEq
     simpa only [update,move,if_pos (by simp :cell∈[cell]),post,List.erase_cons_head] using singletonEq
    ·have bound := OwnedStrict11.owned_stay_bound scalar state dir t valid head cell result.landing actualEffect
      [cell] (by simp) (by simpa using present) (by simp) 2 price
     change 2≤charge NetHack.Soko11Hero315.holeWeight [cell] (.push cell (.stay result.landing))+
       value t.state (update [cell] (.push cell (.stay result.landing)))-value state [cell] at bound
     rw [←endingEq] at bound
     omega
  ·exact ⟨cell,member,by simp only [update,move,if_neg owner]⟩

theorem guard_aux {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet early state group dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (cell : Cell) (tagEq : group=[cell])
 (member : cell∈cells) (present : cell∈state.boulders)
 (cheap : energy state final group outcomes<2) :
 ∃dest,dest∈cells ∧endGroup group outcomes=[dest] := by
 induction quiet generalizing cell with
 |nil=>cases tagEq;exact ⟨cell,member,rfl⟩
 |@cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih=>
  cases tagEq
  have nextValid := (groupCertificate 1).preserved _ _ _ valid head
  have actual := step_boulders_nodup _ _ _ _ valid.1 head
  have inside : [cell]⊆state.boulders := by simpa using present
  have selectedUnique := GhostSubset.update_unique _ _ _ effect actual [cell] (by simp) inside
  have selectedInside := GhostSubset.update_subset _ _ _ effect [cell] (by simp) inside
  have selectedBound : (update [cell] outcome).length≤1 := Nat.le_trans (update_length _ _) (by simp)
  have tailNN := HeroLedger.Logged.energy_nonnegative tail.logged (groupCertificate 1) nextValid
    (update [cell] outcome) selectedUnique selectedInside selectedBound
  have row := (groupCertificate 1).row state dir t outcome [cell] valid (by simp) inside (by simp) head effect
  have split := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final [cell] outcome outcomes
  change 0≤energy t.state final (update [cell] outcome) outcomes at tailNN
  change value state [cell]≤charge NetHack.Soko11Hero315.holeWeight [cell] outcome+value t.state (update [cell] outcome) at row
  change energy state final [cell] (outcome::outcomes)=charge NetHack.Soko11Hero315.holeWeight [cell] outcome+
    value t.state (update [cell] outcome)-value state [cell]+energy t.state final (update [cell] outcome) outcomes at split
  have firstCheap : charge NetHack.Soko11Hero315.holeWeight [cell] outcome+
    value t.state (update [cell] outcome)-value state [cell]<2 := by omega
  obtain ⟨dest,destMember,updated⟩ := one_step valid member present head effect avoid firstCheap
  have nextPresent : dest∈t.state.boulders := selectedInside (by rw [updated];simp)
  have nextCheap : energy t.state final (update [cell] outcome) outcomes<2 := by omega
  obtain ⟨last,lastMember,lastTag⟩ := ih nextValid dest updated destMember nextPresent nextCheap
  exact ⟨last,lastMember,lastTag⟩

theorem guard_logged {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome} {cell : Cell}
 (quiet : UpperQuiet11.Quiet early state [cell] dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (member : cell∈cells) (present : cell∈state.boulders)
 (cheap : energy state final [cell] outcomes<2) :
 ∃dest,dest∈cells ∧endGroup [cell] outcomes=[dest] :=
 guard_aux quiet valid cell rfl member present cheap
#print axioms checked
#print axioms one_step
#print axioms guard_logged
end Owner1007.Left212Word11
