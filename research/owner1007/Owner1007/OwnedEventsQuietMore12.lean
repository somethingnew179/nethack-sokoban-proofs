import Owner1007.OwnedEventsQuiet12
namespace Owner1007.OwnedEvents12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem event_or_good_quiet {n : Nat} {K R : Fin n → List Cell} {paid : Cell → Dir → Prop}
    (closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes K R paid)
    (Kunique : ∀ i, (K i).Nodup)
    (J : List Cell) (fixedInside : ∀ i, J ⊆ K i)
    (guard : ∀ i hero, hero ∈ R i → ∀ dir source, source ∈ J →
      advance soko1_2.board hero dir = some source →
      BlockedPush soko1_2.board (K i) source dir ∨ paid source dir)
    {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    {i : Fin n} (heroInside : state.player ∈ R i) (locksInside : K i ⊆ group) :
    EventLog K R paid group state dirs final pushes moves outcomes ∨
    ∃ j, final.player ∈ R j ∧ K j ⊆ endGroup group outcomes ∧ ownPushes J outcomes=0 := by
  classical
  induction logged generalizing history past pastMoves group i with
  | nil current => exact Or.inr ⟨i,heroInside,locksInside,rfl⟩
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    by_cases pays : PaidOutcome paid dir group outcome
    · exact Or.inl (.head i heroInside locksInside head effect pays tail)
    · have actualUnique := reached.boulders_nodup (by decide +kernel)
      obtain ⟨j,nextHero,nextInside⟩ := owned_step_good_except closed Kunique
        state actualUnique reached.holes_sublist.subset
        (RightEnergy12.trace_disjoint reached RightEnergy12.initial_disjoint)
        group unique subset heroInside locksInside dir t head outcome effect pays
      have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
      have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique subset
      have nextSubset := GhostSubset.update_subset state t outcome effect group unique subset
      have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
      rcases ih nextReached (update group outcome) nextUnique nextSubset nextHero nextInside with event | terminal
      · exact Or.inl (.tail i heroInside locksInside head effect pays event)
      · obtain ⟨k,lastHero,lastLocks,quiet⟩ := terminal
        have same := update_fixed_of_avoid J fixedInside guard heroInside locksInside subset head effect pays
        have zero := ownPush_fixed_of_avoid J fixedInside guard heroInside locksInside subset head effect pays
        exact Or.inr ⟨k,lastHero,lastLocks,by simpa only [ownPushes,same,zero,Nat.zero_add] using quiet⟩



#print axioms event_or_good_quiet
end Owner1007.OwnedEvents12
