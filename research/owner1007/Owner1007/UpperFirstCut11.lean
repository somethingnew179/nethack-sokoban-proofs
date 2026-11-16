import Owner1007.UpperQuiet11
namespace Owner1007.UpperFirstCut11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.UpperQuiet11

structure FirstCut (paid : Cell → Dir → Prop) (initial : State) (group : List Cell)
    (dirs : List Dir) (final : State) (pushes moves : Nat) (outcomes : List Outcome) where
  middle : State
  actor : Transition
  direction : Dir
  headOutcome : Outcome
  beforeDirs : List Dir
  beforePushes : Nat
  beforeMoves : Nat
  beforeOutcomes : List Outcome
  afterDirs : List Dir
  afterPushes : Nat
  afterMoves : Nat
  afterOutcomes : List Outcome
  before : Quiet paid initial group beforeDirs middle beforePushes beforeMoves beforeOutcomes
  headChecked : step soko1_1.board middle direction = some actor
  headEffect : Matches middle actor headOutcome
  headPaid : OwnedCorral11.PaidStep paid (endGroup group beforeOutcomes) direction actor
  after : Logged soko1_1.board actor.state afterDirs final afterPushes afterMoves afterOutcomes
  dirsEq : dirs = beforeDirs ++ direction :: afterDirs
  outcomesEq : outcomes = beforeOutcomes ++ headOutcome :: afterOutcomes
  pushesEq : pushes = beforePushes + actor.pushCost + afterPushes
  movesEq : moves = beforeMoves + 1 + afterMoves

theorem first_cut_or_quiet {paid initial dirs final pushes moves outcomes}
    (logged : Logged soko1_1.board initial dirs final pushes moves outcomes) (group : List Cell) :
    Nonempty (FirstCut paid initial group dirs final pushes moves outcomes) ∨
      Quiet paid initial group dirs final pushes moves outcomes := by
  induction logged generalizing group with
  | nil state => exact Or.inr (.nil state group)
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    by_cases pays : OwnedCorral11.PaidStep paid group dir t
    · exact Or.inl ⟨{
        middle := state, actor := t, direction := dir, headOutcome := outcome,
        beforeDirs := [], beforePushes := 0, beforeMoves := 0, beforeOutcomes := [],
        afterDirs := rest, afterPushes := pushes, afterMoves := moves, afterOutcomes := outcomes,
        before := .nil state group, headChecked := head, headEffect := effect, headPaid := pays,
        after := tail, dirsEq := rfl, outcomesEq := rfl, pushesEq := by omega, movesEq := by omega }⟩
    · rcases ih (update group outcome) with found | quiet
      · obtain ⟨later⟩ := found
        exact Or.inl ⟨{
          middle := later.middle, actor := later.actor, direction := later.direction, headOutcome := later.headOutcome,
          beforeDirs := dir :: later.beforeDirs, beforePushes := t.pushCost + later.beforePushes,
          beforeMoves := 1 + later.beforeMoves, beforeOutcomes := outcome :: later.beforeOutcomes,
          afterDirs := later.afterDirs, afterPushes := later.afterPushes,
          afterMoves := later.afterMoves, afterOutcomes := later.afterOutcomes,
          before := .cons head effect pays later.before,
          headChecked := later.headChecked, headEffect := later.headEffect, headPaid := later.headPaid,
          after := later.after,
          dirsEq := congrArg (List.cons dir) later.dirsEq,
          outcomesEq := congrArg (List.cons outcome) later.outcomesEq,
          pushesEq := by have equality := later.pushesEq; omega,
          movesEq := by have equality := later.movesEq; omega }⟩
      · exact Or.inr (.cons head effect pays quiet)

#print axioms first_cut_or_quiet
end Owner1007.UpperFirstCut11

namespace Owner1007.UpperFirstCut11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.UpperQuiet11

theorem quiet_good
    (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes UpperZero11.locks UpperZero11.region UpperZero11.paid)
    {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
    (quiet : Quiet UpperZero11.paid state group dirs final pushes moves outcomes)
    (actualUnique : state.boulders.Nodup) (unique : group.Nodup) (inside : group ⊆ state.boulders)
    (bounded : group.length ≤ 3) (good : OwnedCorral11.Good UpperZero11.locks UpperZero11.region state group)
    (holesInside : state.holes ⊆ soko1_1.initial.holes) :
    OwnedCorral11.Good UpperZero11.locks UpperZero11.region final (endGroup group outcomes) := by
  induction quiet with
  | nil => exact good
  | @cons state group dir t rest final pushes moves outcome outcomes checked effect avoid tail ih =>
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique inside
    have nextInside := GhostSubset.update_subset state t outcome effect group unique inside
    have nextBound := Nat.le_trans (update_length group outcome) bounded
    have nextGood := OwnedCorral11.step_good_except closed UpperZero11.unique UpperZero11.size
      good inside bounded holesInside checked effect avoid
    have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ checked).subset holesInside
    exact ih nextActual nextUnique nextInside nextBound nextGood nextHoles

def originalGroup : List Cell := [137,139,191]
theorem original_good : OwnedCorral11.Good UpperZero11.locks UpperZero11.region soko1_1.initial originalGroup := by
  refine ⟨⟨0,by decide⟩,?_,?_⟩ <;> decide +kernel

theorem first_cut {dirs final pushes moves outcomes}
    (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final) :
    Nonempty (FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes) := by
  rcases first_cut_or_quiet logged originalGroup with found | quiet
  · exact found
  · have persists := quiet_good UpperZero11.closed quiet (by decide) (by decide) (by decide) (by decide)
      original_good (by simp)
    obtain ⟨i,_,selected⟩ := persists
    have finalSubset := (logged.end_subset (by decide) originalGroup (by decide) (by decide)).2
    have actual : UpperZero11.locks i ⊆ final.boulders := List.Subset.trans selected finalSubset
    have card := List.Nodup.length_le_of_subset (UpperZero11.unique i) actual
    rw [UpperZero11.size i] at card
    have conservation := logged.trace.conservation
    have empty : final.holes=[] := completed
    rw [empty] at conservation
    change 18+0=final.boulders.length+16 at conservation
    omega

theorem FirstCut.stationary_source {dirs final pushes moves outcomes}
    (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
    (cell : Cell) (initial : cell ∈ [137,139,191])
    (sourceEq : cut.actor.pushSource=some cell) : ownPushes [cell] cut.beforeOutcomes=0 := by
  obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
  have same : source=cell := Option.some.inj (metadata.symm.trans sourceEq)
  have present : cell ∈ endGroup originalGroup cut.beforeOutcomes := same ▸ owner
  exact cut.before.stationary UpperZero11.closed (by decide) (by decide) (by decide) (by decide)
    original_good (by simp) cell initial present

#print axioms first_cut
#print axioms FirstCut.stationary_source
end Owner1007.UpperFirstCut11
