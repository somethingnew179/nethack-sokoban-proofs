import Owner1007.RightEnergy12
import Owner1007.PricedCorral11

namespace Owner1007.OwnedEvents12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def PaidOutcome (paid : Cell → Dir → Prop) (dir : Dir) (group : List Cell) : Outcome → Prop
 | .walk _ => False
 | .push source _ => source ∈ group ∧ paid source dir

theorem matches_paid {state : State} {t : Transition} {group : List Cell}
    {outcome : Outcome} {paid : Cell → Dir → Prop} {dir : Dir}
    (effect : Matches state t (projectedOutcome group outcome)) :
    PricedCorral11.PaidStep paid dir t ↔ PaidOutcome paid dir group outcome := by
  cases outcome with
  | walk target =>
    simp only [projectedOutcome,Matches] at effect
    subst t
    simp [PricedCorral11.PaidStep,PaidOutcome]
  | push source result =>
    by_cases owner : source ∈ group
    · cases result with
      | stay landing =>
        simp only [projectedOutcome,if_pos owner,Matches] at effect
        rw [effect.2]
        simp [PricedCorral11.PaidStep,PaidOutcome,owner]
      | fill hole =>
        simp only [projectedOutcome,if_pos owner,Matches] at effect
        rw [effect.2.2]
        simp [PricedCorral11.PaidStep,PaidOutcome,owner]
    · cases result <;>
        simp only [projectedOutcome,if_neg owner,Matches] at effect <;>
        subst t <;>
        simp [PricedCorral11.PaidStep,PaidOutcome,owner]

theorem owned_step_good_except {n : Nat}
    {K R : Fin n → List Cell} {paid : Cell → Dir → Prop}
    (closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes K R paid)
    (Kunique : ∀ i, (K i).Nodup)
    (state : State) (unique : state.boulders.Nodup)
    (holesInside : state.holes ⊆ soko1_2.initial.holes)
    (disjoint : ∀ c ∈ state.boulders, c ∉ state.holes)
    (group : List Cell) (groupUnique : group.Nodup) (subset : group ⊆ state.boulders)
    {i : Fin n} (heroInside : state.player ∈ R i) (locksInside : K i ⊆ group)
    (dir : Dir) (t : Transition) (checked : step soko1_2.board state dir = some t)
    (outcome : Outcome) (effect : Matches state t outcome)
    (avoid : ¬ PaidOutcome paid dir group outcome) :
    ∃ j, t.state.player ∈ R j ∧ K j ⊆ update group outcome := by
  let shadow : State := ⟨state.player,group,state.holes⟩
  have physical := step_player_clear soko1_2.board state dir t checked
  have clear : state.player ∉ group := fun h => physical.2.2.1 (subset h)
  have standing : standingAllowed soko1_2.board shadow = true := by
    simp [standingAllowed,shadow,physical.1,physical.2.1,clear,physical.2.2.2]
  have active : goal shadow = false := by
    have core : exposedStep soko1_2.board state dir = some t :=
      (exposedStep_eq soko1_2.board state dir).trans checked
    cases ongoing : goal state with
    | false => exact ongoing
    | true => simp [exposedStep,ongoing] at core
  have oracle := original_matches_shadow soko1_2.board state group unique subset disjoint dir t checked outcome effect
  obtain ⟨u,shadowStep,shadowEffect⟩ := oracle_realized soko1_2.board shadow groupUnique standing active dir
    (projectedOutcome group outcome) oracle
  have avoids : ¬ PricedCorral11.PaidStep paid dir u := fun h => avoid ((matches_paid shadowEffect).mp h)
  have good : Corral11.Good K R shadow := ⟨i,heroInside,locksInside⟩
  obtain ⟨j,nextHero,nextLocks⟩ := PricedCorral11.step_good_except closed Kunique
    good (show shadow.holes ⊆ soko1_2.initial.holes from holesInside) shadowStep avoids
  have boxes : u.state.boulders = update group outcome := by
    have h := GhostOracleFacts.matches_update shadow u _ shadowEffect
    change u.state.boulders = update group (projectedOutcome group outcome) at h
    exact h.trans (RawGhostBonus.update_projected group outcome)
  have hero : u.state.player = t.state.player :=
    (HazardPattern.matches_hero shadow u _ shadowEffect).trans
      ((RawGhostBonus.hero_projected group outcome).trans
        (HazardPattern.matches_hero state t outcome effect).symm)
  exact ⟨j,by simpa only [hero] using nextHero,by simpa only [boxes] using nextLocks⟩

inductive EventLog {n : Nat} (K R : Fin n → List Cell) (paid : Cell → Dir → Prop) :
    List Cell → State → List Dir → State → Nat → Nat → List Outcome → Prop where
 | head {group state dir t rest final pushes moves outcome outcomes}
    (i : Fin n) (hero : state.player ∈ R i) (locks : K i ⊆ group)
    (checked : step soko1_2.board state dir = some t)
    (effect : Matches state t outcome)
    (pays : PaidOutcome paid dir group outcome)
    (tail : Logged soko1_2.board t.state rest final pushes moves outcomes) :
    EventLog K R paid group state (dir :: rest) final (t.pushCost + pushes) (1 + moves) (outcome :: outcomes)
 | tail {group state dir t rest final pushes moves outcome outcomes}
    (i : Fin n) (hero : state.player ∈ R i) (locks : K i ⊆ group)
    (checked : step soko1_2.board state dir = some t)
    (effect : Matches state t outcome)
    (avoid : ¬ PaidOutcome paid dir group outcome)
    (later : EventLog K R paid (update group outcome) t.state rest final pushes moves outcomes) :
    EventLog K R paid group state (dir :: rest) final (t.pushCost + pushes) (1 + moves) (outcome :: outcomes)

theorem event_or_good {n : Nat} {K R : Fin n → List Cell} {paid : Cell → Dir → Prop}
    (closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes K R paid)
    (Kunique : ∀ i, (K i).Nodup)
    {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    {i : Fin n} (heroInside : state.player ∈ R i) (locksInside : K i ⊆ group) :
    EventLog K R paid group state dirs final pushes moves outcomes ∨
    ∃ j, final.player ∈ R j ∧ K j ⊆ endGroup group outcomes := by
  classical
  induction logged generalizing history past pastMoves group i with
  | nil current => exact Or.inr ⟨i,heroInside,locksInside⟩
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
      · exact Or.inr terminal

theorem update_fixed_of_avoid {n : Nat} {K R : Fin n → List Cell} {paid : Cell → Dir → Prop}
    (J : List Cell) (fixedInside : ∀ i, J ⊆ K i)
    (guard : ∀ i hero, hero ∈ R i → ∀ dir source, source ∈ J →
      advance soko1_2.board hero dir = some source →
      BlockedPush soko1_2.board (K i) source dir ∨ paid source dir)
    {state group dir t outcome i}
    (heroInside : state.player ∈ R i) (locksInside : K i ⊆ group)
    (subset : group ⊆ state.boulders)
    (checked : step soko1_2.board state dir = some t) (effect : Matches state t outcome)
    (avoid : ¬ PaidOutcome paid dir group outcome) : update J outcome = J := by
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
    simp only [update,move,if_neg absent]

theorem EventLog.split_fixed {n : Nat} {K R : Fin n → List Cell} {paid : Cell → Dir → Prop}
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
      ∀ small : List Cell, small ⊆ J → endGroup small before = small := by
  induction event generalizing history past pastMoves with
  | @head group state dir t rest final pushes moves outcome outcomes i hero locks checked effect pays tail =>
    exact ⟨[],0,0,[],state,dir,t,outcome,outcomes,rest,pushes,moves,i,
      rfl,.nil state,checked,effect,tail,hero,locks,pays,(by intro small _; rfl)⟩
  | @tail group state dir t rest final pushes moves outcome outcomes i hero locks checked effect avoid later ih =>
    have actualUnique := reached.boulders_nodup (by decide +kernel)
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique subset
    have nextSubset := GhostSubset.update_subset state t outcome effect group unique subset
    have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
    obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,payDir,u,payOutcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,one,effectOne,last,heroOne,locksOne,pays,unchanged⟩ :=
      ih nextReached nextUnique nextSubset
    refine ⟨dir::beforeDirs,t.pushCost+beforePushes,1+beforeMoves,outcome::before,
      middle,payDir,u,payOutcome,after,afterDirs,afterPushes,afterMoves,j,?_,
      .cons checked effect first,one,effectOne,last,heroOne,locksOne,pays,?_⟩
    · simp only [List.cons_append,shape]
    · intro small smallInside
      have same := update_fixed_of_avoid small (fun i => List.Subset.trans smallInside (fixedInside i))
        (fun i hero member dir source found adjacent => guard i hero member dir source (smallInside found) adjacent)
        hero locks subset checked effect avoid
      simpa only [endGroup,same] using unchanged small smallInside

theorem energy_at_split (potential : Potential) (group : List Cell) (before : List Outcome)
    (outcome : Outcome) (after : List Outcome) :
    energy potential group (before ++ outcome :: after) =
      ownSlack potential group before + slack potential (projectedOutcome (endGroup group before) outcome) +
      energy potential (update (endGroup group before) outcome) after := by
  simp only [energy,ownSlack_append,endGroup_append,ownSlack,endGroup]
  omega

theorem event_energy_le {board : Board} {potential : Potential}
    (valid : Valid board potential) (group : List Cell)
    {state middle next final beforeDirs afterDirs beforePushes beforeMoves afterPushes afterMoves before after}
    (first : Logged board state beforeDirs middle beforePushes beforeMoves before)
    (last : Logged board next afterDirs final afterPushes afterMoves after) (outcome : Outcome) :
    slack potential (projectedOutcome (endGroup group before) outcome) ≤
      energy potential group (before ++ outcome :: after) := by
  have left := first.ownSlack_nonnegative valid group
  have right := last.energy_nonnegative valid (update (endGroup group before) outcome)
  rw [energy_at_split]
  omega

#print axioms matches_paid
#print axioms owned_step_good_except
#print axioms event_or_good
#print axioms EventLog.split_fixed
#print axioms event_energy_le
end Owner1007.OwnedEvents12
