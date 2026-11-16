import Owner1007.Pair13711Data
import Owner1007.OwnedCorralBound11
import Owner1007.Hero315Frame11
import Owner1007.UpperHeadCases11
import Owner1007.CutStrict11
namespace Owner1007.Pair137Energy11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition NetHack.Sokoban.LowerBounds
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Exit (source : Cell) (dir : Dir) : Prop := CutActor11.Exit source dir ∨ (source=111 ∧ dir=.west)
theorem is_exit (source : Cell) (dir : Dir) (pays : Pair13711.paid source dir) : Exit source dir := by
 rcases pays with old|west137|west111
 · apply Or.inl
   rcases old with h|h|h|h|h|h <;> simp_all [CutActor11.Exit]
 · exact Or.inl (by simp [CutActor11.Exit,west137.1,west137.2])
 · exact Or.inr west111
theorem prices : (List.range 16).all (fun p => decide (ActorPrices11.price p 112 111 110=2))=true := by decide +kernel
theorem debt : (List.range 16).all (fun p => decide (weightSum (NetHack.Soko11Hero315.weight p 138) [137,191]≤-2))=true := by decide +kernel

theorem west_support {state : State} {t : Transition} {source : Cell}
 (checked : step soko1_1.board state .west=some t) (sourceEq : t.pushSource=some source) :
 advance soko1_1.board state.player .west=some source := by
 rcases step_cases_full _ _ _ _ checked with walked|pushed
 · obtain ⟨target,_,_,_,_,shape⟩ := walked
   simp only [shape] at sourceEq
   contradiction
 · obtain ⟨other,result,adjacent,_,_,_,shape⟩ := pushed
   have same : other=source := by simpa only [shape,Option.some.injEq] using sourceEq
   simpa only [same] using adjacent

theorem exit_row {state : State} {direction : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
 (good : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (checked : step soko1_1.board state direction=some t) (effect : Matches state t outcome)
 (unique : group.Nodup) (inside : group⊆state.boulders)
 (pays : ∃ source, source∈group ∧ t.pushSource=some source ∧ Exit source direction) :
 2≤charge (groupCertificate 2).holeWeight group outcome +
   value t.state (update group outcome)-value state group := by
 obtain ⟨source,owner,metadata,pays⟩ := pays
 rcases pays with old|special
 · exact CutStrict11.exit_row scalar rfl good checked effect unique inside ⟨source,owner,metadata,old⟩
 · rcases special with ⟨rfl,rfl⟩
   obtain ⟨phase,atIndex⟩ := good.2
   have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
   have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
       (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq]; exact atIndex
   have active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16 :=
     HazardPhaseCountedCorrection.active_of_step _ _ within _ _ checked
   have holesInside : state.holes⊆soko1_1.initial.holes := by
     rw [atIndex.2.1]
     exact (List.drop_sublist phase _).subset
   have same := UpperHeadCases11.ordinary_effect checked effect metadata
     (show pushTargets soko1_1.board 111 .west=[110] by decide +kernel) (by decide +kernel) holesInside
   subst outcome
   have hero := ActorPrices11.support_of_check 111 state.player .west 112 (by decide +kernel)
     (step_player_clear _ _ _ _ checked).1 (west_support checked metadata)
   have row := of_decide_eq_true (List.all_eq_true.mp prices _ (List.mem_range.mpr active))
   have ownPrice : 2≤1+scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) 111 110 -
       scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state.player 111 := by
     rw [hero]
     exact Int.le_of_eq row.symm
   exact OwnedStrict11.owned_stay_bound scalar state .west t good checked 111 110 effect group unique inside owner 2 ownPrice

theorem future_two_of_closed
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes Pair13711.locks Pair13711.region Pair13711.paid)
 {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16)
 (hero : state.player=138) (inside : [137,191]⊆state.boulders) :
 2≤energy state final [137,191] outcomes := by
 have good : OwnedCorral11.Good Pair13711.locks Pair13711.region state [137,191] := by
   refine ⟨0,?_,by intro c h; exact h⟩
   rw [hero]
   decide +kernel
 have debt : (groupCertificate 2).groupValue state [137,191]≤-(2:Int) := by
   change weightSum (NetHack.Soko11Hero315.weight _ state.player) [137,191]≤-2
   rw [hero]
   exact of_decide_eq_true (List.all_eq_true.mp debt _ (List.mem_range.mpr active))
 have priced : ∀ state dir t outcome group,
   HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
   group.Nodup → group⊆state.boulders → group.length≤2 →
   step soko1_1.board state dir=some t → Matches state t outcome →
   OwnedCorral11.PaidStep Pair13711.paid group dir t →
   2≤charge (groupCertificate 2).holeWeight group outcome +
     (groupCertificate 2).groupValue t.state (update group outcome) -
     (groupCertificate 2).groupValue state group := by
   intro state dir t outcome group valid unique inside bounded checked effect pays
   obtain ⟨source,owner,metadata,pays⟩ := pays
   exact exit_row valid checked effect unique inside ⟨source,owner,metadata,is_exit source dir pays⟩
 exact OwnedCorral11.energy_bound closed Pair13711.unique Pair13711.size (groupCertificate 2) 2 priced logged
   (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached) [137,191] (by decide) inside rfl good
   reached.holes_sublist.subset debt (goal_value_zero completed _)
#print axioms exit_row
#print axioms future_two_of_closed
end Owner1007.Pair137Energy11
