import Owner1007.LeftStaggered11
import Owner1007.LeftQuietIdentity11
namespace Owner1007.LeftSplitFour11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def noMoveCheck : Bool := ([185,211] : List Cell).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉LeftSplit11.region 0∨BlockedPush soko1_1.board [185,211] source dir∨LeftPair11.paid source dir)
theorem noMove_checked : noMoveCheck=true := by decide +kernel
theorem noMove : ∀hero∈LeftSplit11.region 0,∀source∈([185,211] : List Cell),∀dir,
 advance soko1_1.board hero dir=some source→BlockedPush soko1_1.board [185,211] source dir∨LeftPair11.paid source dir := by
 intro hero member source owner dir adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp noMove_checked source owner) dir (Geometry.all_directions dir)
 have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (LeftSplit11.floor 0 member) dir source adjacent
 simp only [noMoveCheck,behind] at row
 exact (of_decide_eq_true row).resolve_left (fun outside=>outside member)

theorem future_four {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders)
 (same : group.Perm [185,211]) (hero : state.player∈LeftSplit11.region 0)
 (gone : endGroup group outcomes=[]) : 4≤energy state final group outcomes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have bound : group.length≤2 := by have eq:=same.length_eq;simpa using Nat.le_of_eq eq
 have good : OwnedCorral11.Good LeftSplit11.locks LeftSplit11.region state group := ⟨0,hero,fun _ h=>same.mem_iff.mpr h⟩
 obtain ⟨cut⟩ := LeftWestCount11.find LeftSplit11.closed (by intro i;change ([185,211] : List Cell).Nodup;decide) (by intro i;rfl)
   reached logged group groupUnique inside bound good gone
 have quietZero := LeftQuietIdentity11.quiet_zero_static [185,211] (LeftSplit11.region 0) LeftPair11.paid
   LeftSplit11.closed (by decide) noMove cut.before inside same hero reached.holes_sublist.subset
 have tag := no_push_unchanged group cut.beforeOutcomes quietZero.1
 have currentSame : (endGroup group cut.beforeOutcomes).Perm [185,211] := by rw [tag];exact same
 have beforeFacts := cut.before.logged.end_subset valid.1 group groupUnique inside
 have beforeBound := Nat.le_trans (endGroup_length_le group cut.beforeOutcomes) bound
 have currentReached := reached.append cut.before.logged.trace
 have currentValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant currentReached
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 have sourceChoices : source=185∨source=211 := by
   have member:=currentSame.mem_iff.mp owner
   simpa only [List.mem_cons,List.not_mem_nil,or_false] using member
 have west : cut.direction=.west := pays.2
 have afterGood : OwnedCorral11.Good LeftStaggered11.locks LeftStaggered11.region cut.actor.state
     (update (endGroup group cut.beforeOutcomes) cut.headOutcome) := by
  rcases sourceChoices with rfl|rfl
  ·have target : pushTargets soko1_1.board 185 cut.direction=[184] := by rw [west];decide +kernel
   have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) currentReached.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 185 (.stay 184)) := by simpa only [headEq] using cut.headEffect
   have nextPerm := update_perm currentSame cut.headOutcome
   rw [headEq] at nextPerm ⊢
   have destination : (update ([185,211] : List Cell) (.push 185 (.stay 184))).Perm (LeftStaggered11.locks 0) := by decide +kernel
   have finalPerm := nextPerm.trans destination
   refine ⟨0,?_,fun _ h=>finalPerm.mem_iff.mpr h⟩
   have sameHero : cut.actor.state.player=185 := by rw [effect.2]
   rw [sameHero]
   decide +kernel
  ·have target : pushTargets soko1_1.board 211 cut.direction=[210] := by rw [west];decide +kernel
   have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) currentReached.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 211 (.stay 210)) := by simpa only [headEq] using cut.headEffect
   have nextPerm := update_perm currentSame cut.headOutcome
   rw [headEq] at nextPerm ⊢
   have destination : (update ([185,211] : List Cell) (.push 211 (.stay 210))).Perm (LeftStaggered11.locks 1) := by decide +kernel
   have finalPerm := nextPerm.trans destination
   refine ⟨1,?_,fun _ h=>finalPerm.mem_iff.mpr h⟩
   have sameHero : cut.actor.state.player=211 := by rw [effect.2]
   rw [sameHero]
   decide +kernel
 have actual := step_boulders_nodup _ _ _ _ currentValid.1 cut.headChecked
 have nextUnique := GhostSubset.update_unique _ _ _ cut.headEffect actual _ beforeFacts.1 beforeFacts.2
 have nextInside := GhostSubset.update_subset _ _ _ cut.headEffect _ beforeFacts.1 beforeFacts.2
 have nextBound := Nat.le_trans (update_length (endGroup group cut.beforeOutcomes) cut.headOutcome) beforeBound
 have actorReached := currentReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have afterGone : endGroup (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes=[] := by
   rw [cut.outcomesEq,endGroup_append] at gone
   exact gone
 have afterTicket := LeftStaggered11.future_two actorReached cut.after _ nextUnique nextInside (by omega) afterGood afterGone
 have firstTicket := LeftSplit11.priced cut.middle cut.direction cut.actor cut.headOutcome (endGroup group cut.beforeOutcomes)
   currentValid beforeFacts.1 beforeFacts.2 (by omega) cut.headChecked cut.headEffect ⟨source,owner,metadata,pays⟩
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup group cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup group cut.beforeOutcomes) at firstTicket
 have prefixNN := HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 18) valid group groupUnique inside (by omega)
 change 0≤energy state cut.middle group cut.beforeOutcomes at prefixNN
 have split := energy_append state cut.middle final group cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup group cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup group cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
   charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup group cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup group cut.beforeOutcomes)+
   energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
 rw [cut.outcomesEq]
 omega
#print axioms future_four
end Owner1007.LeftSplitFour11
