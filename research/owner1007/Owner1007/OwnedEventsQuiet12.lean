import Owner1007.OwnedEventsMore12
namespace Owner1007.OwnedEvents12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem ownPush_fixed_of_avoid {n : Nat} {K R : Fin n → List Cell} {paid : Cell → Dir → Prop}
    (J : List Cell) (fixedInside : ∀ i, J ⊆ K i)
    (guard : ∀ i hero, hero ∈ R i → ∀ dir source, source ∈ J →
      advance soko1_2.board hero dir = some source →
      BlockedPush soko1_2.board (K i) source dir ∨ paid source dir)
    {state group dir t outcome i}
    (heroInside : state.player ∈ R i) (locksInside : K i ⊆ group)
    (subset : group ⊆ state.boulders)
    (checked : step soko1_2.board state dir = some t) (effect : Matches state t outcome)
    (avoid : ¬ PaidOutcome paid dir group outcome) : ownPush J outcome = 0 := by
  have actualInside : K i ⊆ state.boulders := List.Subset.trans locksInside subset
  rcases step_cases_full soko1_2.board state dir t checked with walked | pushed
  · obtain ⟨target,adjacent,floor,notBox,notHole,shape⟩ := walked
    have same := matches_unique state t (.walk target) outcome shape effect
    subst outcome
    rfl
  · obtain ⟨source,result,adjacent,floor,present,push,shape⟩ := pushed
    have first := push_first_clear soko1_2.board state source dir result push
    have spec := pushBoulder_spec soko1_2.board state source dir result push
    have actualEffect : Matches state t (.push source (ending result)) := by
      rcases spec.1 with stay | fill
      · simp only [ending,stay.1]
        refine ⟨present,?_⟩
        simpa only [stay.1,stay.2,afterFill] using shape
      · simp only [ending,fill.1]
        refine ⟨present,fill.2.1,?_⟩
        simpa only [fill.1,fill.2.2,afterFill] using shape
    have same := matches_unique state t (.push source (ending result)) outcome actualEffect effect
    subst outcome
    have absent : source ∉ J := by
      intro member
      rcases guard i state.player heroInside dir source member adjacent with blocked | paid
      · rcases blocked with diagonal | blocked
        · simp only [first.1] at diagonal
          contradiction
        · obtain ⟨dest,next,destFloor,door,empty⟩ := first.2
          simp only [next] at blocked
          rcases blocked with wall | door' | box
          · exact wall destFloor
          · exact door door'
          · exact empty (actualInside box)
      · exact avoid ⟨locksInside (fixedInside i member),paid⟩
    simp only [ownPush,if_neg absent]

theorem EventLog.split_quiet {n : Nat} {K R : Fin n → List Cell} {paid : Cell → Dir → Prop}
    (J : List Cell) (fixedInside : ∀ i, J ⊆ K i)
    (guard : ∀ i hero, hero ∈ R i → ∀ dir source, source ∈ J →
      advance soko1_2.board hero dir = some source →
      BlockedPush soko1_2.board (K i) source dir ∨ paid source dir)
    {group state dirs final pushes moves outcomes}
    (event : EventLog K R paid group state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (unique : group.Nodup) (subset : group ⊆ state.boulders) :
    ∃ beforeDirs beforePushes beforeMoves before middle dir t outcome after
      afterDirs afterPushes afterMoves, ∃ i : Fin n,
      outcomes = before ++ outcome :: after ∧
      Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before ∧
      step soko1_2.board middle dir = some t ∧ Matches middle t outcome ∧
      Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
      middle.player ∈ R i ∧ K i ⊆ endGroup group before ∧
      PaidOutcome paid dir (endGroup group before) outcome ∧
      (∀ small : List Cell, small ⊆ J → endGroup small before = small) ∧ ownPushes J before = 0 := by
  induction event generalizing history past pastMoves with
  | @head group state dir t rest final pushes moves outcome outcomes i hero locks checked effect pays tail =>
    exact ⟨[],0,0,[],state,dir,t,outcome,outcomes,rest,pushes,moves,i,
      rfl,.nil state,checked,effect,tail,hero,locks,pays,⟨(by intro small _; rfl),rfl⟩⟩
  | @tail group state dir t rest final pushes moves outcome outcomes i hero locks checked effect avoid later ih =>
    have actualUnique := reached.boulders_nodup (by decide +kernel)
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique subset
    have nextSubset := GhostSubset.update_subset state t outcome effect group unique subset
    have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
    obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,payDir,u,payOutcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,one,effectOne,last,heroOne,locksOne,pays,unchanged,stationary⟩ :=
      ih nextReached nextUnique nextSubset
    refine ⟨dir::beforeDirs,t.pushCost+beforePushes,1+beforeMoves,outcome::before,
      middle,payDir,u,payOutcome,after,afterDirs,afterPushes,afterMoves,j,?_,
      .cons checked effect first,one,effectOne,last,heroOne,locksOne,pays,?_⟩
    · simp only [List.cons_append,shape]
    · constructor
      · intro small smallInside
        have same := update_fixed_of_avoid small (fun i => List.Subset.trans smallInside (fixedInside i))
          (fun i hero member dir source found adjacent => guard i hero member dir source (smallInside found) adjacent)
          hero locks subset checked effect avoid
        simpa only [endGroup,same] using unchanged small smallInside
      · have same := update_fixed_of_avoid J fixedInside guard hero locks subset checked effect avoid
        have zero := ownPush_fixed_of_avoid J fixedInside guard hero locks subset checked effect avoid
        simpa only [ownPushes,same,zero,Nat.zero_add] using stationary

#print axioms ownPush_fixed_of_avoid
#print axioms EventLog.split_quiet
end Owner1007.OwnedEvents12

