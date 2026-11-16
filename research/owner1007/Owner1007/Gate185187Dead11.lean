import Owner1007.LeftGateFree11
import Owner1007.LeftDeadSplit11
namespace Owner1007.Gate185187Dead11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem at212 {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders)
 (same : group.Perm (LeftGate21311.locks 1)) (hero : state.player∈LeftGate21311.region 1)
 (gone : endGroup group outcomes=[]) : False := by
 obtain ⟨cut,metadata,west,zero⟩:=LeftGateFree11.forces_front reached logged group unique inside 1 same hero gone
 change cut.actor.pushSource=some 212 at metadata
 have bounded : group.length≤18 := by have len:=same.length_eq;have check:(LeftGate21311.locks 1).length=3:=rfl;omega
 have beforeReached:=reached.append cut.before.logged.trace
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
 have outEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
  (show pushTargets soko1_1.board 212 .west=[211] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
 have effect : Matches cut.middle cut.actor (.push 212 (.stay 211)) := by simpa only [outEq] using cut.headEffect
 have fixed:=no_push_unchanged group cut.beforeOutcomes zero
 have nextPerm : (update (endGroup group cut.beforeOutcomes) cut.headOutcome).Perm [185,187,211] := by
  rw [fixed,outEq]
  exact (update_perm same (.push 212 (.stay 211))).trans (by decide +kernel)
 have facts:=Upper216Eight11.next_facts cut reached unique inside bounded
 have afterReached:=beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have nextHero : cut.actor.state.player∈LeftDeadSplit11.region 0 := by
  rw [effect.2]
  change 212∈LeftDeadSplit11.region 0
  decide +kernel
 have good : OwnedCorral11.Good LeftDeadSplit11.locks LeftDeadSplit11.region cut.actor.state
  (update (endGroup group cut.beforeOutcomes) cut.headOutcome) := by
  refine ⟨0,nextHero,?_⟩
  intro c member
  exact nextPerm.mem_iff.mpr ((show ([185,211]:List Cell)⊆[185,187,211] by decide) member)
 exact LeftDeadSplit11.impossible_gone afterReached cut.after _ facts.1 facts.2.1 good (Upper216Eight11.tail_gone cut gone)
theorem at213 {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders)
 (same : group.Perm (LeftGate21311.locks 0)) (hero : state.player∈LeftGate21311.region 0)
 (gone : endGroup group outcomes=[]) : False := by
 obtain ⟨cut,metadata,west,zero⟩:=LeftGateFree11.forces_front reached logged group unique inside 0 same hero gone
 change cut.actor.pushSource=some 213 at metadata
 have bounded : group.length≤18 := by have len:=same.length_eq;have check:(LeftGate21311.locks 0).length=3:=rfl;omega
 have beforeReached:=reached.append cut.before.logged.trace
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
 have outEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
  (show pushTargets soko1_1.board 213 .west=[212] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
 have effect : Matches cut.middle cut.actor (.push 213 (.stay 212)) := by simpa only [outEq] using cut.headEffect
 have fixed:=no_push_unchanged group cut.beforeOutcomes zero
 have nextPerm : (update (endGroup group cut.beforeOutcomes) cut.headOutcome).Perm (LeftGate21311.locks 1) := by
  rw [fixed,outEq]
  exact (update_perm same (.push 213 (.stay 212))).trans (by decide +kernel)
 have facts:=Upper216Eight11.next_facts cut reached unique inside bounded
 have afterReached:=beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have nextHero : cut.actor.state.player∈LeftGate21311.region 1 := by rw [effect.2];change 213∈LeftGate21311.region 1;decide +kernel
 exact at212 afterReached cut.after _ facts.1 facts.2.1 nextPerm nextHero (Upper216Eight11.tail_gone cut gone)
#print axioms at212
#print axioms at213
end Owner1007.Gate185187Dead11
