import Owner1007.LeftGate21311
namespace Owner1007.LeftGateReserve11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem left_two_of_head {paid state group dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut paid state group dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (left : List Cell) (leftUnique : left.Nodup) (leftInside : left⊆state.boulders) (leftBound : left.length≤18)
 (owns185 : 185∈left)
 (metadata : cut.actor.pushSource=some 185) (west : cut.direction=.west)
 (fixed : ownPushes [185] cut.beforeOutcomes=0) :
 2≤energy state final left outcomes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have beforeReached := reached.append cut.before.logged.trace
 have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeReached
 have singletonTag := no_push_unchanged [185] cut.beforeOutcomes fixed
 have singletonInside : [185]⊆state.boulders := by simpa using leftInside owns185
 have selected := cut.before.logged.end_mono valid.1 [185] left (by decide) singletonInside
   (by intro c h; have same : c=185:=List.mem_singleton.mp h; exact same ▸ owns185)
 have beforeFacts := cut.before.logged.end_subset valid.1 left leftUnique leftInside
 have owns : 185∈endGroup left cut.beforeOutcomes := selected (by rw [singletonTag]; simp)
 have pays : OwnedCorral11.PaidStep LeftPair11.paid (endGroup left cut.beforeOutcomes) cut.direction cut.actor :=
   ⟨185,owns,metadata,by simp [LeftPair11.paid,west]⟩
 have row := LeftStrict11.exit_row scalar rfl beforeValid cut.headChecked cut.headEffect beforeFacts.1 beforeFacts.2 pays
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup left cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup left cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup left cut.beforeOutcomes) at row
 have prefixNN:=HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 18) valid left leftUnique leftInside leftBound
 change 0≤energy state cut.middle left cut.beforeOutcomes at prefixNN
 have afterActual:=step_boulders_nodup _ _ _ _ beforeValid.1 cut.headChecked
 have afterUnique:=GhostSubset.update_unique _ _ _ cut.headEffect afterActual _ beforeFacts.1 beforeFacts.2
 have afterInside:=GhostSubset.update_subset _ _ _ cut.headEffect _ beforeFacts.1 beforeFacts.2
 have afterBound:=Nat.le_trans (update_length (endGroup left cut.beforeOutcomes) cut.headOutcome)
   (Nat.le_trans (endGroup_length_le left cut.beforeOutcomes) leftBound)
 have afterValid:=(groupCertificate 18).preserved _ _ _ beforeValid cut.headChecked
 have tailNN:=HeroLedger.Logged.energy_nonnegative cut.after (groupCertificate 18) afterValid
   _ afterUnique afterInside afterBound
 change 0≤energy cut.actor.state final (update (endGroup left cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at tailNN
 have split:=energy_append state cut.middle final left cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have one:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup left cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup left cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
   charge NetHack.Soko11Hero315.holeWeight (endGroup left cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup left cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup left cut.beforeOutcomes)+
   energy cut.actor.state final (update (endGroup left cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
 have same:=congrArg (energy state final left) cut.outcomesEq
 omega

theorem forces_front {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (i : Fin 2) (same : group.Perm (LeftGate21311.locks i)) (hero : state.player∈LeftGate21311.region i)
 (gone : endGroup group outcomes=[])
 (left : List Cell) (leftUnique : left.Nodup) (leftInside : left⊆state.boulders) (leftBound : left.length≤18)
 (owns185 : 185∈left) (cheapLeft : energy state final left outcomes<2) :
 ∃cut : FirstCut LeftGate21311.paid state group dirs final pushes moves outcomes,
 cut.actor.pushSource=some (LeftGate21311.front i)∧cut.direction=.west∧ownPushes group cut.beforeOutcomes=0 := by
 obtain ⟨cut,heads,west,zero⟩ := LeftGate21311.first_exit reached logged group uniqueGroup inside i same hero gone
 rcases heads with leftHead|frontHead
 ·have owns : 185∈group := same.mem_iff.mpr (by simp [LeftGate21311.locks])
  have fixed := LeftQuietIdentity11.subset_zero [185] group cut.beforeOutcomes (by simpa using owns) zero
  have two := left_two_of_head cut reached left leftUnique leftInside leftBound owns185 leftHead west fixed
  omega
 ·exact ⟨cut,frontHead,west,zero⟩
#print axioms left_two_of_head
#print axioms forces_front
end Owner1007.LeftGateReserve11

namespace Owner1007.LeftGateReserve11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf)
theorem actor_row {phases : HazardPhases.Certificate soko1_1.board soko1_1.initial.holes}
    (scalar : HeroPhasePotential.Certificate soko1_1.board soko1_1.initial.holes phases)
    (weightEq : scalar.weight = NetHack.Soko11Hero315.weight)
    {state : State} {direction : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
    (good : HazardPhases.Good phases state) (checked : step soko1_1.board state direction = some t)
    (effect : Matches state t outcome) (unique : group.Nodup) (inside : group ⊆ state.boulders)
    (pays : ∃ source, source ∈ group ∧ t.pushSource = some source ∧ ActorPrices11.Exit source direction) :
    2 ≤ charge scalar.holeWeight group outcome +
      OwnedStrict11.groupValue scalar t.state (update group outcome) -
      OwnedStrict11.groupValue scalar state group := by
  obtain ⟨source,owner,sourceEq,exit⟩ := pays
  obtain ⟨phase,atIndex⟩ := good.2
  have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase state atIndex
  have within : HazardPhases.At phases (phaseOf soko1_1.initial.holes state) state := by
    rw [←phaseEq]; exact atIndex
  have active := HazardPhaseCountedCorrection.active_of_step phases state within direction t checked
  have holesInside : state.holes ⊆ soko1_1.initial.holes := by
    rw [atIndex.2.1]
    exact (List.drop_sublist phase soko1_1.initial.holes).subset
  have active16 : phaseOf soko1_1.initial.holes state < 16 := active
  obtain ⟨landing,landed,unfilled,price⟩ := ActorPrices11.exit_price checked sourceEq exit holesInside
    (phaseOf soko1_1.initial.holes state) active16
  have same := LeftStrict11.outcome_stay effect sourceEq landed unfilled
  subst outcome
  have ownPrice : 2 ≤ 1 + scalar.weight (phaseOf soko1_1.initial.holes state) source landing -
      scalar.weight (phaseOf soko1_1.initial.holes state) state.player source := by
    rw [weightEq]
    change 2 ≤ ActorPrices11.price _ _ _ _
    omega
  exact OwnedStrict11.owned_stay_bound scalar state direction t good checked source landing effect
    group unique inside owner 2 ownPrice

theorem cut_lower {state group dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut LeftGate21311.paid state group dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (uniqueGroup : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (i : Fin 2) (metadata : cut.actor.pushSource=some (LeftGate21311.front i)) (west : cut.direction=.west) :
 2+energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes
 ≤energy state final group outcomes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have beforeReached := reached.append cut.before.logged.trace
 have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeReached
 have facts := cut.before.logged.end_subset valid.1 group uniqueGroup inside
 obtain ⟨source,owner,sourceEq,pays⟩ := cut.headPaid
 have sameSource : source=LeftGate21311.front i := Option.some.inj (sourceEq.symm.trans metadata)
 have owns := sameSource ▸ owner
 have row : 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup group cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup group cut.beforeOutcomes) := by
  obtain ⟨i,bound⟩:=i
  have cases : i=0∨i=1:=by omega
  rcases cases with rfl|rfl
  ·apply actor_row scalar rfl beforeValid cut.headChecked cut.headEffect facts.1 facts.2
   exact ⟨213,owns,metadata,Or.inr (Or.inl ⟨rfl,west⟩)⟩
  ·apply LeftStrict11.exit_row scalar rfl beforeValid cut.headChecked cut.headEffect facts.1 facts.2
   exact ⟨212,owns,metadata,by simp [LeftActor11.Exit,west]⟩
 have prefixNN := HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 18) valid
  group uniqueGroup inside bounded
 change 0≤energy state cut.middle group cut.beforeOutcomes at prefixNN
 have split := energy_append state cut.middle final group cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup group cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup group cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
   charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup group cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup group cut.beforeOutcomes)+
   energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
 have same := congrArg (energy state final group) cut.outcomesEq
 omega
theorem future_two {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (i : Fin 2) (same : group.Perm (LeftGate21311.locks i)) (hero : state.player∈LeftGate21311.region i)
 (gone : endGroup group outcomes=[]) (cheap185 : energy state final [185] outcomes<2) :
 2≤energy state final group outcomes := by
 have member185 : 185∈group := same.mem_iff.mpr (by simp [LeftGate21311.locks])
 obtain ⟨cut,metadata,west,zero⟩ := forces_front reached logged group uniqueGroup inside i same hero gone
  [185] (by decide) (by simpa using inside member185) (by decide) (by simp) cheap185
 have bounded : group.length≤18 := by have len:=same.length_eq;have check:(LeftGate21311.locks i).length=3:=rfl;omega
 have lower := cut_lower cut reached uniqueGroup inside bounded i metadata west
 have facts := Upper216Eight11.next_facts cut reached uniqueGroup inside bounded
 have afterReached := (reached.append cut.before.logged.trace).append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have afterNN := HeroLedger.Logged.energy_nonnegative cut.after (groupCertificate 18)
  (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant afterReached) _ facts.1 facts.2.1 facts.2.2
 change 0≤energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at afterNN
 omega
#print axioms actor_row
#print axioms cut_lower
#print axioms future_two
end Owner1007.LeftGateReserve11

namespace Owner1007.LeftGateReserve11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem future_four {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (same : group.Perm (LeftGate21311.locks 0)) (hero : state.player∈LeftGate21311.region 0)
 (gone : endGroup group outcomes=[]) (cheap185 : energy state final [185] outcomes<2) :
 4≤energy state final group outcomes := by
 have member185 : 185∈group := same.mem_iff.mpr (by simp [LeftGate21311.locks])
 have singleInside : [185]⊆state.boulders := by simpa using inside member185
 obtain ⟨cut,metadata,west,zero⟩ := forces_front reached logged group uniqueGroup inside 0 same hero gone
  [185] (by decide) singleInside (by decide) (by simp) cheap185
 change cut.actor.pushSource=some 213 at metadata
 have bounded : group.length≤18 := by have len:=same.length_eq;have check:(LeftGate21311.locks 0).length=3:=rfl;omega
 have lower := cut_lower cut reached uniqueGroup inside bounded 0 metadata west
 have beforeReached := reached.append cut.before.logged.trace
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
 have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
  (show pushTargets soko1_1.board 213 .west=[212] by decide +kernel) (by decide +kernel) beforeReached.holes_sublist.subset
 have effect : Matches cut.middle cut.actor (.push 213 (.stay 212)) := by simpa only [headEq] using cut.headEffect
 have fixed := no_push_unchanged group cut.beforeOutcomes zero
 have nextPerm : (update (endGroup group cut.beforeOutcomes) cut.headOutcome).Perm (LeftGate21311.locks 1) := by
  rw [fixed,headEq]
  exact (update_perm same (.push 213 (.stay 212))).trans (by decide +kernel)
 have nextHero : cut.actor.state.player∈LeftGate21311.region 1 := by
  rw [effect.2]
  change 213∈LeftGate21311.region 1
  decide +kernel
 have afterReached := beforeReached.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have facts := Upper216Eight11.next_facts cut reached uniqueGroup inside bounded
 let headLogged : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
  .cons cut.headChecked cut.headEffect (.nil _)
 let lead := cut.before.logged.append headLogged
 have zero185 := LeftQuietIdentity11.subset_zero [185] group cut.beforeOutcomes (by simpa using member185) zero
 have tag185 := no_push_unchanged [185] cut.beforeOutcomes zero185
 have after185 : endGroup [185] (cut.beforeOutcomes++[cut.headOutcome])=[185] := by
  rw [endGroup_append,tag185]
  simp [endGroup,headEq,update,move]
 have prefixNN := HeroLedger.Logged.energy_nonnegative lead (groupCertificate 18)
  (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached) [185] (by decide) singleInside (by decide)
 change 0≤energy state cut.actor.state [185] (cut.beforeOutcomes++[cut.headOutcome]) at prefixNN
 have split := energy_append state cut.actor.state final [185] (cut.beforeOutcomes++[cut.headOutcome]) cut.afterOutcomes
 rw [after185] at split
 have shape : (cut.beforeOutcomes++[cut.headOutcome])++cut.afterOutcomes=outcomes := by
  simpa only [List.append_assoc,List.singleton_append] using cut.outcomesEq.symm
 rw [shape] at split
 have afterCheap : energy cut.actor.state final [185] cut.afterOutcomes<2 := by omega
 have tail := future_two afterReached cut.after _ facts.1 facts.2.1 1 nextPerm nextHero
  (Upper216Eight11.tail_gone cut gone) afterCheap
 change 2≤energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at tail
 omega
#print axioms future_four
end Owner1007.LeftGateReserve11
