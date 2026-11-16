import Owner1007.PreCageFacts12
import Owner1007.CageFour12
import Owner1007.OwnedEventsMore12
namespace Owner1007.TaggedFlow12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem step_tags {n : Nat} {K R : Fin n → List Cell} {paid : Cell → Dir → Prop}
    {allowed : Fin n → Cell → Dir → Fin n → Cell → Prop} {tagS tagT : Fin n → Cell}
    (closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes K R paid)
    (unique : ∀ i, (K i).Nodup)
    (tagInside : ∀ i, tagS i ∈ K i ∧ tagT i ∈ K i)
    (tagSound : ∀ i hero, hero∈R i → ∀ source, source∈K i → ∀ dir,
      advance soko1_2.board hero dir=some source →
      BlockedPush soko1_2.board (K i) source dir ∨ paid source dir ∨
      PreCage12.TaggedShift K R allowed i source dir)
    (tagUpdate : ∀ i source dir j dest, allowed i source dir j dest →
      update [tagS i] (.push source (.stay dest))=[tagS j] ∧
      update [tagT i] (.push source (.stay dest))=[tagT j])
    {state : State} {group : List Cell} {i : Fin n}
    (hero : state.player∈R i) (inside : K i⊆group) (subset : group⊆state.boulders)
    (holes : state.holes⊆soko1_2.initial.holes)
    {dir t outcome}
    (checked : step soko1_2.board state dir=some t) (effect : Matches state t outcome)
    (avoid : ¬ OwnedEvents12.PaidOutcome paid dir group outcome) :
    ∃ j, t.state.player∈R j ∧ K j⊆update group outcome ∧
      update [tagS i] outcome=[tagS j] ∧ update [tagT i] outcome=[tagT j] := by
  have actualInside : K i⊆state.boulders := List.Subset.trans inside subset
  have smallCorner := original_corner_projected soko1_2.board state (K i) actualInside dir t checked
  rcases step_cases_full soko1_2.board state dir t checked with walked | pushed
  · obtain ⟨target,adjacent,floor,notBox,notHole,shape⟩ := walked
    have same := matches_unique state t (.walk target) outcome shape effect
    subst outcome
    have door := FiniteTopology.step_target_not_door soko1_2.board state dir t target adjacent checked
    have notLock : target∉K i := fun h => notBox (actualInside h)
    have nextHero := closed.1 i state.player hero dir target adjacent floor door notLock smallCorner
    exact ⟨i,by simpa only [shape] using nextHero,inside,rfl,rfl⟩
  · obtain ⟨source,result,adjacent,floor,present,push,shape⟩ := pushed
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
    by_cases member : source∈K i
    · have owner : source∈group := inside member
      rcases tagSound i state.player hero source member dir adjacent with blocked | pays | shifted
      · exact False.elim (CageFour12.blocked_impossible actualInside checked actualEffect blocked)
      · exact False.elim (avoid ⟨owner,pays⟩)
      · obtain ⟨j,dest,_,targets,clear,nextK,nextHero,allowedStep⟩ := shifted
        have resultSame := OwnedEvents12.push_effect_singleton soko1_2.initial.holes holes
          targets clear checked actualEffect
        have nextInside := CageFour12.shifted_inside (unique i) inside owner nextK
        have changes := tagUpdate i source dir j dest allowedStep
        refine ⟨j,by simpa only [shape] using nextHero,?_,?_,?_⟩
        · simpa only [resultSame] using nextInside
        · simpa only [resultSame] using changes.1
        · simpa only [resultSame] using changes.2
    · have door := FiniteTopology.step_target_not_door soko1_2.board state dir t source adjacent checked
      have nextHero := closed.1 i state.player hero dir source adjacent floor door member smallCorner
      have nextInside := update_mono (K i) group (unique i) inside (.push source (ending result))
      simp only [update,move,if_neg member] at nextInside
      have notS : source∉[tagS i] := by
        intro found
        have same : source=tagS i := List.mem_singleton.mp found
        exact member (same ▸ (tagInside i).1)
      have notT : source∉[tagT i] := by
        intro found
        have same : source=tagT i := List.mem_singleton.mp found
        exact member (same ▸ (tagInside i).2)
      refine ⟨i,by simpa only [shape] using nextHero,nextInside,?_,?_⟩
      · simp only [update,move,if_neg notS]
      · simp only [update,move,if_neg notT]

inductive Event {n : Nat} (K R : Fin n → List Cell) (paid : Cell → Dir → Prop)
    (tagS tagT : Fin n → Cell) :
    List Cell → List Cell → List Cell → State → List Dir → State → Nat → Nat → List Outcome → Prop where
 | head {group sg tg state dir t rest final pushes moves outcome outcomes}
    (i : Fin n) (hero : state.player∈R i) (locks : K i⊆group)
    (sEq : sg=[tagS i]) (tEq : tg=[tagT i])
    (checked : step soko1_2.board state dir=some t) (effect : Matches state t outcome)
    (pays : OwnedEvents12.PaidOutcome paid dir group outcome)
    (tail : Logged soko1_2.board t.state rest final pushes moves outcomes) :
    Event K R paid tagS tagT group sg tg state (dir::rest) final (t.pushCost+pushes) (1+moves) (outcome::outcomes)
 | tail {group sg tg state dir t rest final pushes moves outcome outcomes}
    (i : Fin n) (hero : state.player∈R i) (locks : K i⊆group)
    (sEq : sg=[tagS i]) (tEq : tg=[tagT i])
    (checked : step soko1_2.board state dir=some t) (effect : Matches state t outcome)
    (avoid : ¬OwnedEvents12.PaidOutcome paid dir group outcome)
    (later : Event K R paid tagS tagT (update group outcome) (update sg outcome) (update tg outcome)
      t.state rest final pushes moves outcomes) :
    Event K R paid tagS tagT group sg tg state (dir::rest) final (t.pushCost+pushes) (1+moves) (outcome::outcomes)

theorem event_or_good {n : Nat} {K R : Fin n → List Cell} {paid : Cell → Dir → Prop}
    {allowed : Fin n → Cell → Dir → Fin n → Cell → Prop} {tagS tagT : Fin n → Cell}
    (closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes K R paid)
    (unique : ∀ i, (K i).Nodup)
    (tagInside : ∀ i, tagS i∈K i ∧ tagT i∈K i)
    (tagSound : ∀ i hero, hero∈R i → ∀ source, source∈K i → ∀ dir,
      advance soko1_2.board hero dir=some source →
      BlockedPush soko1_2.board (K i) source dir ∨ paid source dir ∨
      PreCage12.TaggedShift K R allowed i source dir)
    (tagUpdate : ∀ i source dir j dest, allowed i source dir j dest →
      update [tagS i] (.push source (.stay dest))=[tagS j] ∧
      update [tagT i] (.push source (.stay dest))=[tagT j])
    {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group sg tg : List Cell) (groupUnique : group.Nodup) (subset : group⊆state.boulders)
    {i : Fin n} (hero : state.player∈R i) (locks : K i⊆group)
    (sEq : sg=[tagS i]) (tEq : tg=[tagT i]) :
    Event K R paid tagS tagT group sg tg state dirs final pushes moves outcomes ∨
    ∃ j, final.player∈R j ∧ K j⊆endGroup group outcomes ∧
      endGroup sg outcomes=[tagS j] ∧ endGroup tg outcomes=[tagT j] := by
  classical
  induction logged generalizing history past pastMoves group sg tg i with
  | nil current => exact Or.inr ⟨i,hero,locks,sEq,tEq⟩
  | @cons state dir t rest final pushes moves outcome outcomes checked effect tail ih =>
    by_cases pays : OwnedEvents12.PaidOutcome paid dir group outcome
    · exact Or.inl (.head i hero locks sEq tEq checked effect pays tail)
    · obtain ⟨j,nextHero,nextLocks,sChange,tChange⟩ := step_tags closed unique tagInside tagSound tagUpdate
        hero locks subset reached.holes_sublist.subset checked effect pays
      have actualUnique := reached.boulders_nodup (by decide +kernel)
      have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
      have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group groupUnique subset
      have nextSubset := GhostSubset.update_subset state t outcome effect group groupUnique subset
      have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
      have sNext : update sg outcome=[tagS j] := by simpa only [sEq] using sChange
      have tNext : update tg outcome=[tagT j] := by simpa only [tEq] using tChange
      rcases ih nextReached (update group outcome) (update sg outcome) (update tg outcome)
        nextUnique nextSubset nextHero nextLocks sNext tNext with event | terminal
      · exact Or.inl (.tail i hero locks sEq tEq checked effect pays event)
      · exact Or.inr terminal

theorem Event.split_fixed {n : Nat} {K R : Fin n → List Cell} {paid : Cell → Dir → Prop}
    {tagS tagT : Fin n → Cell}
    (fixed : List Cell) (fixedInside : ∀ i, fixed⊆K i)
    (guard : ∀ i hero, hero∈R i → ∀ dir source, source∈fixed →
      advance soko1_2.board hero dir=some source →
      BlockedPush soko1_2.board (K i) source dir ∨ paid source dir)
    {group sg tg state dirs final pushes moves outcomes}
    (event : Event K R paid tagS tagT group sg tg state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (unique : group.Nodup) (subset : group⊆state.boulders) :
    ∃ beforeDirs beforePushes beforeMoves before middle dir t outcome after afterDirs afterPushes afterMoves,
      ∃ i : Fin n,
      outcomes=before++outcome::after ∧
      Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before ∧
      step soko1_2.board middle dir=some t ∧ Matches middle t outcome ∧
      Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
      middle.player∈R i ∧ K i⊆endGroup group before ∧
      OwnedEvents12.PaidOutcome paid dir (endGroup group before) outcome ∧
      endGroup sg before=[tagS i] ∧ endGroup tg before=[tagT i] ∧
      (∀ small : List Cell, small⊆fixed → endGroup small before=small) := by
  induction event generalizing history past pastMoves with
  | @head group sg tg state dir t rest final pushes moves outcome outcomes i hero locks sEq tEq checked effect pays tail =>
    exact ⟨[],0,0,[],state,dir,t,outcome,outcomes,rest,pushes,moves,i,
      rfl,.nil state,checked,effect,tail,hero,locks,pays,sEq,tEq,by intro small _; rfl⟩
  | @tail group sg tg state dir t rest final pushes moves outcome outcomes i hero locks sEq tEq checked effect avoid later ih =>
    have actualUnique := reached.boulders_nodup (by decide +kernel)
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique subset
    have nextSubset := GhostSubset.update_subset state t outcome effect group unique subset
    have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
    obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,payDir,u,payOutcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,one,effectOne,last,heroOne,locksOne,pays,sOne,tOne,unchanged⟩ :=
      ih nextReached nextUnique nextSubset
    refine ⟨dir::beforeDirs,t.pushCost+beforePushes,1+beforeMoves,outcome::before,
      middle,payDir,u,payOutcome,after,afterDirs,afterPushes,afterMoves,j,?_,
      .cons checked effect first,one,effectOne,last,heroOne,locksOne,pays,sOne,tOne,?_⟩
    · simp only [List.cons_append,shape]
    · intro small smallInside
      have same := OwnedEvents12.update_fixed_of_avoid small
        (fun i => List.Subset.trans smallInside (fixedInside i))
        (fun i hero member dir source found adjacent => guard i hero member dir source (smallInside found) adjacent)
        hero locks subset checked effect avoid
      simpa only [endGroup,same] using unchanged small smallInside
#print axioms step_tags
#print axioms event_or_good
#print axioms Event.split_fixed
end Owner1007.TaggedFlow12
