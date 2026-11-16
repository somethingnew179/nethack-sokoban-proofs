import Owner1007.Left212Word11
namespace Owner1007.Left212TwoWord11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cells : List Cell := [212,213,239,265,211,214,264,266]
def rank (cell : Cell) : Int := if cell∈([211,214,264,266]:List Cell) then 2 else 0
abbrev early := Left212Word11.early
def row (state : State) (t : Transition) (cell : Cell) (outcome : Outcome) : Int :=
 charge NetHack.Soko11Hero315.holeWeight [cell] outcome+value t.state (update [cell] outcome)-value state [cell]
def cost (source dest : Cell) : Int := if dest∈cells then rank dest-rank source else 4-rank source
def check (phase : Nat) : Bool := cells.all fun source=>allDirs.all fun dir=>
 if early source dir then true else
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>(pushTargets soko1_1.board source dir).all fun dest=>
   decide (dest∉soko1_1.initial.holes ∧cost source dest≤ActorPrices11.price phase hero source dest)
theorem checked : (List.range 16).all check=true := by decide +kernel
theorem numeric (phase : Nat) (active : phase<16) (source hero dest : Cell) (dir : Dir)
 (member : source∈cells) (unpaid : ¬early source dir)
 (behind : advance soko1_1.board source dir.opposite=some hero)
 (target : dest∈pushTargets soko1_1.board source dir) :
 dest∉soko1_1.initial.holes ∧cost source dest≤ActorPrices11.price phase hero source dest := by
 have r:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp checked phase (List.mem_range.mpr active)) source member) dir (Geometry.all_directions dir)
 simp only [check,if_neg unpaid,behind] at r
 exact of_decide_eq_true (List.all_eq_true.mp r dest target)

theorem one_step {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {cell : Cell}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (member : cell∈cells) (present : cell∈state.boulders)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (avoid : ¬OwnedCorral11.PaidStep early [cell] dir t)
 (cheap : row state t cell outcome<4-rank cell) :
 ∃dest,dest∈cells ∧update [cell] outcome=[dest] ∧rank dest≤rank cell+row state t cell outcome := by
 have inside : [cell]⊆state.boulders := by simpa using present
 have nn:=(groupCertificate 1).row state dir t outcome [cell] valid (by simp) inside (by simp) head effect
 change value state [cell]≤charge NetHack.Soko11Hero315.holeWeight [cell] outcome+value t.state (update [cell] outcome) at nn
 have rowNN : 0≤row state t cell outcome := by unfold row;omega
 cases outcome with
 |walk target=>exact ⟨cell,member,rfl,by omega⟩
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
   ·obtain ⟨target,_,_,_,_,shape⟩:=walked
    simp only [shape] at metadata
    contradiction
   ·obtain ⟨other,result,adjacent,_,_,push,shape⟩:=pushed
    have same : other=cell := by simpa only [shape,Option.some.injEq] using metadata
    subst other
    have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player
      (step_player_clear _ _ _ _ head).1 dir cell adjacent
    obtain ⟨phase,atIndex⟩:=valid.2
    have phaseEq:=HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
    have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
      (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq];exact atIndex
    have active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16 :=
      HazardPhaseCountedCorrection.active_of_step _ _ within _ _ head
    have spec:=pushBoulder_spec _ _ _ _ _ push
    have price:=numeric _ active cell state.player result.landing dir member unpaid behind spec.2
    have holesInside : state.holes⊆soko1_1.initial.holes := by rw [atIndex.2.1];exact (List.drop_sublist phase _).subset
    have noFill : result.filled=none := by
     rcases spec.1 with stay|fill
     ·exact stay.1
     ·exact False.elim (price.1 (holesInside fill.2.1))
    have landed : t.landing=some result.landing := by simp only [shape]
    have filled : t.filled=none := by simpa only [shape] using noFill
    have endingEq:=CutStrict11.outcome_stay effect metadata landed filled
    have actualEffect : Matches state t (.push cell (.stay result.landing)) := by simpa only [endingEq] using effect
    have bound:=OwnedStrict11.owned_stay_bound scalar state dir t valid head cell result.landing actualEffect
      [cell] (by simp) inside (by simp) (cost cell result.landing) price.2
    change cost cell result.landing≤row state t cell (.push cell (.stay result.landing)) at bound
    rw [←endingEq] at bound
    by_cases destInside : result.landing∈cells
    ·have rankBound : rank result.landing≤rank cell+row state t cell (.push cell ending) := by
      simp only [cost,if_pos destInside] at bound
      omega
     refine ⟨result.landing,destInside,?_,rankBound⟩
     have singletonEq:=congrArg (update [cell]) endingEq
     simpa only [update,move,if_pos (by simp :cell∈[cell]),post,List.erase_cons_head] using singletonEq
    ·simp only [cost,if_neg destInside] at bound
     omega
  ·refine ⟨cell,member,?_,by omega⟩
   simp only [update,move,if_neg owner]

theorem guard_aux {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet early state group dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (cell : Cell) (tagEq : group=[cell]) (member : cell∈cells) (present : cell∈state.boulders)
 (cheap : energy state final group outcomes<4-rank cell) :
 ∃dest,dest∈cells ∧endGroup group outcomes=[dest] := by
 induction quiet generalizing cell with
 |nil=>cases tagEq;exact ⟨cell,member,rfl⟩
 |@cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih=>
  cases tagEq
  have nextValid:=(groupCertificate 1).preserved _ _ _ valid head
  have actual:=step_boulders_nodup _ _ _ _ valid.1 head
  have inside : [cell]⊆state.boulders := by simpa using present
  have selectedUnique:=GhostSubset.update_unique _ _ _ effect actual [cell] (by simp) inside
  have selectedInside:=GhostSubset.update_subset _ _ _ effect [cell] (by simp) inside
  have selectedBound : (update [cell] outcome).length≤1 := Nat.le_trans (update_length _ _) (by simp)
  have tailNN:=HeroLedger.Logged.energy_nonnegative tail.logged (groupCertificate 1) nextValid
    (update [cell] outcome) selectedUnique selectedInside selectedBound
  change 0≤energy t.state final (update [cell] outcome) outcomes at tailNN
  have certrow:=(groupCertificate 1).row state dir t outcome [cell] valid (by simp) inside (by simp) head effect
  change value state [cell]≤charge NetHack.Soko11Hero315.holeWeight [cell] outcome+value t.state (update [cell] outcome) at certrow
  have rowNN : 0≤row state t cell outcome := by unfold row;omega
  have split:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final [cell] outcome outcomes
  change energy state final [cell] (outcome::outcomes)=row state t cell outcome+
    energy t.state final (update [cell] outcome) outcomes at split
  have firstCheap : row state t cell outcome<4-rank cell := by omega
  obtain ⟨dest,destMember,updated,rankBound⟩:=one_step valid member present head effect avoid firstCheap
  have nextPresent : dest∈t.state.boulders := selectedInside (by rw [updated];simp)
  have nextCheap : energy t.state final (update [cell] outcome) outcomes<4-rank dest := by omega
  obtain ⟨last,lastMember,lastTag⟩:=ih nextValid dest updated destMember nextPresent nextCheap
  exact ⟨last,lastMember,lastTag⟩

theorem guard_logged {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet early state [212] dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (present : 212∈state.boulders) (cheap : energy state final [212] outcomes<4) :
 ∃dest,dest∈cells ∧endGroup [212] outcomes=[dest] := by
 have startRank : rank 212=0 := by decide +kernel
 apply guard_aux quiet valid 212 rfl (by decide) present
 rw [startRank]
 omega
#print axioms checked
#print axioms guard_logged
end Owner1007.Left212TwoWord11
