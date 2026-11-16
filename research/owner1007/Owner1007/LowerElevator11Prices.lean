import Owner1007.LowerElevator11Data
import Owner1007.UpperLocalPrice11
namespace Owner1007.LowerElevator11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def sources : List Cell := [265,291,292,317]
theorem positive_source (source : Cell) (dir : Dir) (pays : positive source dir) : source∈sources := by
 rcases pays with ⟨pays,_⟩|⟨rfl,_⟩
 · rcases pays with rfl|rfl|rfl <;> decide
 · decide
def priceCheck (phase : Nat) : Bool := sources.all fun source => allDirs.all fun dir =>
 if positive source dir then match advance soko1_1.board source dir.opposite with
 | none => false
 | some hero => (pushTargets soko1_1.board source dir).all fun dest =>
   decide (dest∉soko1_1.initial.holes ∧ 1≤ActorPrices11.price phase hero source dest)
 else true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem prices : (List.range 16).all priceCheck=true := by decide +kernel
theorem price_row (phase : Nat) (active : phase<16) (hero source dest : Cell) (dir : Dir)
 (pays : positive source dir) (behind : advance soko1_1.board source dir.opposite=some hero)
 (target : dest∈pushTargets soko1_1.board source dir) :
 dest∉soko1_1.initial.holes ∧ 1≤ActorPrices11.price phase hero source dest := by
 have a := List.all_eq_true.mp prices phase (List.mem_range.mpr active)
 have b := List.all_eq_true.mp (List.all_eq_true.mp a source (positive_source source dir pays)) dir (Geometry.all_directions dir)
 simp only [if_pos pays,behind] at b
 exact of_decide_eq_true (List.all_eq_true.mp b dest target)

theorem exit_row {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (unique : group.Nodup) (inside : group⊆state.boulders)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (pays : OwnedCorral11.PaidStep positive group dir t) :
 1≤charge NetHack.Soko11Hero315.holeWeight group outcome+value t.state (update group outcome)-value state group := by
 obtain ⟨source,owner,metadata,pays⟩ := pays
 rcases step_cases_full _ _ _ _ head with walked|pushed
 · obtain ⟨target,_,_,_,_,shape⟩ := walked
   simp only [shape] at metadata
   contradiction
 · obtain ⟨other,result,adjacent,_,_,push,shape⟩ := pushed
   have same : other=source := by simpa only [shape,Option.some.injEq] using metadata
   subst other
   have reverse := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player
     (step_player_clear _ _ _ _ head).1 dir source adjacent
   obtain ⟨phase,atIndex⟩ := valid.2
   have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
   have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
       (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq]; exact atIndex
   have active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16 :=
     HazardPhaseCountedCorrection.active_of_step _ _ within _ _ head
   have spec := pushBoulder_spec _ _ _ _ _ push
   have row := price_row _ active state.player source result.landing dir pays reverse spec.2
   have holesInside : state.holes⊆soko1_1.initial.holes := by rw [atIndex.2.1]; exact (List.drop_sublist phase _).subset
   have unfilled : result.filled=none := by
     rcases spec.1 with stay|fill
     · exact stay.1
     · exact False.elim (row.1 (holesInside fill.2.1))
   have landed : t.landing=some result.landing := by simp only [shape]
   have noFill : t.filled=none := by simpa only [shape] using unfilled
   have sameOutcome := CutStrict11.outcome_stay effect metadata landed noFill
   subst outcome
   exact OwnedStrict11.owned_stay_bound scalar state dir t valid head source result.landing effect group unique inside owner 1 row.2
#print axioms prices
#print axioms exit_row
end Owner1007.LowerElevator11
