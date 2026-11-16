import Owner1007.LeftGateReserve11
namespace Owner1007.LeftGateFree11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem no185 : ∀i : Fin 2,Left188Pocket11.headCheck LeftGate21311.locks LeftGate21311.region 185 (fun _=>False) i=true := by decide +kernel
theorem forces_front {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (i : Fin 2) (same : group.Perm (LeftGate21311.locks i)) (hero : state.player∈LeftGate21311.region i)
 (gone : endGroup group outcomes=[]) :
 ∃cut : FirstCut LeftGate21311.paid state group dirs final pushes moves outcomes,
 cut.actor.pushSource=some (LeftGate21311.front i)∧cut.direction=.west∧ownPushes group cut.beforeOutcomes=0 := by
 obtain ⟨cut,heads,west,zero⟩:=LeftGate21311.first_exit reached logged group uniqueGroup inside i same hero gone
 rcases heads with leftHead|frontHead
 ·have quiet:=LeftQuietIdentity11.quiet_zero_static (LeftGate21311.locks i) (LeftGate21311.region i) LeftGate21311.paid
   (LeftGate21311.phase_closed i) (LeftGate21311.unique i) (LeftGate21311.noMove i) cut.before inside same hero reached.holes_sublist.subset
  have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
  have facts:=cut.before.logged.end_subset valid.1 group uniqueGroup inside
  have fixed:=no_push_unchanged group cut.beforeOutcomes zero
  have physical : LeftGate21311.locks i⊆cut.middle.boulders := by
   intro c member
   exact facts.2 (by rw [fixed];exact same.mem_iff.mpr member)
  exact False.elim (Left188Pocket11.head_allowed LeftGate21311.locks LeftGate21311.region 185 (fun _=>False) i
   (no185 i) cut.headChecked leftHead quiet.2 (step_player_clear _ _ _ _ cut.headChecked).1 physical)
 ·exact ⟨cut,frontHead,west,zero⟩
theorem future_two {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (i : Fin 2) (same : group.Perm (LeftGate21311.locks i)) (hero : state.player∈LeftGate21311.region i)
 (gone : endGroup group outcomes=[]) :
 2≤energy state final group outcomes := by
 obtain ⟨cut,metadata,west,zero⟩:=forces_front reached logged group uniqueGroup inside i same hero gone
 have bounded : group.length≤18 := by have len:=same.length_eq;have check:(LeftGate21311.locks i).length=3:=rfl;omega
 have lower:=LeftGateReserve11.cut_lower cut reached uniqueGroup inside bounded i metadata west
 have facts:=Upper216Eight11.next_facts cut reached uniqueGroup inside bounded
 have afterReached:=(reached.append cut.before.logged.trace).append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have afterNN:=HeroLedger.Logged.energy_nonnegative cut.after (groupCertificate 18)
  (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant afterReached) _ facts.1 facts.2.1 facts.2.2
 change 0≤energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at afterNN
 omega
theorem future_four {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (same : group.Perm (LeftGate21311.locks 0)) (hero : state.player∈LeftGate21311.region 0)
 (gone : endGroup group outcomes=[]) :
 4≤energy state final group outcomes := by
 obtain ⟨cut,metadata,west,zero⟩:=forces_front reached logged group uniqueGroup inside 0 same hero gone
 change cut.actor.pushSource=some 213 at metadata
 have bounded : group.length≤18 := by have len:=same.length_eq;have check:(LeftGate21311.locks 0).length=3:=rfl;omega
 have lower:=LeftGateReserve11.cut_lower cut reached uniqueGroup inside bounded 0 metadata west
 have beforeReached:=reached.append cut.before.logged.trace
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
 have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
  (show pushTargets soko1_1.board 213 .west=[212] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
 have effect : Matches cut.middle cut.actor (.push 213 (.stay 212)) := by simpa only [headEq] using cut.headEffect
 have fixed:=no_push_unchanged group cut.beforeOutcomes zero
 have nextPerm : (update (endGroup group cut.beforeOutcomes) cut.headOutcome).Perm (LeftGate21311.locks 1) := by
  rw [fixed,headEq]
  exact (update_perm same (.push 213 (.stay 212))).trans (by decide +kernel)
 have nextHero : cut.actor.state.player∈LeftGate21311.region 1 := by rw [effect.2];change 213∈LeftGate21311.region 1;decide +kernel
 have afterReached:=beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have facts:=Upper216Eight11.next_facts cut reached uniqueGroup inside bounded
 have tail:=future_two afterReached cut.after _ facts.1 facts.2.1 1 nextPerm nextHero (Upper216Eight11.tail_gone cut gone)
 change 2≤energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at tail
 omega
#print axioms forces_front
#print axioms future_four
end Owner1007.LeftGateFree11
