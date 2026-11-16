import Owner1007.PairBound11
import Owner1007.HeroEnergyTrace11
namespace Owner1007.PairResetFuture11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition NetHack.Sokoban.LowerBounds
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def debtCheck (p : Nat) : Bool := [138,190].all (fun hero => decide (weightSum (NetHack.Soko11Hero315.weight p hero) [139,191]≤-2))
theorem debts : (List.range 16).all debtCheck=true := by decide +kernel
theorem future_two {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16)
 (hero : state.player∈[138,190]) (inside : [139,191]⊆state.boulders) :
 2≤energy state final [139,191] outcomes := by
 have good : OwnedCorral11.Good PairPath11.locks PairPath11.region state [139,191] := by
   refine ⟨0,?_,by intro c h; exact h⟩
   have checked : [138,190].all (fun c => decide (c∈PairPath11.region 0))=true := by decide +kernel
   exact of_decide_eq_true (List.all_eq_true.mp checked _ hero)
 have debt : (groupCertificate 2).groupValue state [139,191]≤-(2:Int) := by
   have row := List.all_eq_true.mp debts _ (List.mem_range.mpr active)
   exact of_decide_eq_true (List.all_eq_true.mp row _ hero)
 have priced : ∀ state dir t outcome group,
   HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
   group.Nodup → group⊆state.boulders → group.length≤2 →
   step soko1_1.board state dir=some t → Matches state t outcome →
   OwnedCorral11.PaidStep PairPath11.paid group dir t →
   2≤charge (groupCertificate 2).holeWeight group outcome +
     (groupCertificate 2).groupValue t.state (update group outcome) -
     (groupCertificate 2).groupValue state group := by
   intro state dir t outcome group valid unique inside bounded checked effect pays
   exact PairStrict11.exit_row scalar rfl valid checked effect unique inside pays
 exact OwnedCorral11.energy_bound PairPath11.closed PairPath11.unique PairPath11.size (groupCertificate 2) 2 priced logged
   (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached) [139,191] (by decide) inside rfl good
   reached.holes_sublist.subset debt (goal_value_zero completed _)
#print axioms future_two
end Owner1007.PairResetFuture11
