import Owner1007.LowerTrap31911Data
import Owner1007.Hero315Frame11
import Owner1007.UpperBudget11
import Owner1007.OwnedCorralAny11
import Owner1007.UpperLocalPrice11
import Owner1007.HeroEnergyTrace11
import NetHack.Sokoban.Reduction
namespace Owner1007.LowerTrap31911
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def priceCheck (phase : Nat) : Bool := sources.all fun source => allDirs.all fun dir =>
 if paid source dir then match advance soko1_1.board source dir.opposite with
 | none => false
 | some hero => (pushTargets soko1_1.board source dir).all fun dest =>
   decide (dest∉soko1_1.initial.holes ∧ 2≤ActorPrices11.price phase hero source dest)
 else true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem prices : (List.range 16).all priceCheck=true := by decide +kernel
theorem price_row (phase : Nat) (active : phase<16) (hero source dest : Cell) (dir : Dir)
 (pays : paid source dir) (behind : advance soko1_1.board source dir.opposite=some hero)
 (target : dest∈pushTargets soko1_1.board source dir) :
 dest∉soko1_1.initial.holes ∧ 2≤ActorPrices11.price phase hero source dest := by
 have a := List.all_eq_true.mp prices phase (List.mem_range.mpr active)
 have b := List.all_eq_true.mp (List.all_eq_true.mp a source (paid_source source dir pays)) dir (Geometry.all_directions dir)
 simp only [if_pos pays,behind] at b
 exact of_decide_eq_true (List.all_eq_true.mp b dest target)

theorem exit_row {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (unique : group.Nodup) (inside : group⊆state.boulders)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (pays : OwnedCorral11.PaidStep paid group dir t) :
 2≤charge NetHack.Soko11Hero315.holeWeight group outcome+value t.state (update group outcome)-value state group := by
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
   exact OwnedStrict11.owned_stay_bound scalar state dir t valid head source result.landing effect group unique inside owner 2 row.2

theorem future_two (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 {prior state dirs final pushes moves outcomes priorPushes priorMoves}
 (reached : Trace soko1_1.board soko1_1.initial prior state priorPushes priorMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good locks region state group) :
 2≤energy state final group outcomes := by
 by_cases enough : 2≤energy state final group outcomes
 · exact enough
 · have cheap : energy state final group outcomes<2 := by omega
   have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   have retained := OwnedCorralAny11.small_energy_good closed unique (groupCertificate 18) 2
     (fun state dir t outcome group valid unique inside _ head effect pays=>
       exit_row valid unique inside head effect pays)
     logged valid group groupUnique inside bounded good reached.holes_sublist.subset cheap
   obtain ⟨i,_,locksInside⟩ := retained
   have finalSelected := logged.end_subset valid.1 group groupUnique inside
   have card := List.Nodup.length_le_of_subset (unique i) (List.Subset.trans locksInside finalSelected.2)
   have conservation := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   rw [empty] at conservation
   change 18+0=final.boulders.length+16 at conservation
   rw [size i] at card
   omega
theorem rest_positive (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 {beforeDirs state beforePushes beforeMoves before afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (good : OwnedCorral11.Good locks region state (endGroup UpperBudget11.Rest before)) :
 2≤energy soko1_1.initial final UpperBudget11.Rest (before++after) := by
 have selected := first.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 have bound := endGroup_length_le UpperBudget11.Rest before
 have future := future_two closed first.trace last completed _ selected.1 selected.2 (by change (endGroup UpperBudget11.Rest before).length≤18; change (endGroup UpperBudget11.Rest before).length≤10 at bound;omega) good
 have prefixNN := energy_nonnegative first UpperBudget11.Rest (by decide) (by decide)
 have split := energy_append soko1_1.initial state final UpperBudget11.Rest before after
 omega
#print axioms future_two
#print axioms rest_positive

end Owner1007.LowerTrap31911
