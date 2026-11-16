import Owner1007.OwnedEvents12

namespace Owner1007.OwnedEvents12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting

theorem EventLog.split {n : Nat} {K R : Fin n → List Cell} {paid : Cell → Dir → Prop}
    {group state dirs final pushes moves outcomes}
    (event : EventLog K R paid group state dirs final pushes moves outcomes) :
    ∃ beforeDirs beforePushes beforeMoves before middle dir t outcome after
      afterDirs afterPushes afterMoves, ∃ i : Fin n,
      outcomes = before ++ outcome :: after ∧
      Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before ∧
      step soko1_2.board middle dir = some t ∧ Matches middle t outcome ∧
      Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
      middle.player ∈ R i ∧ K i ⊆ endGroup group before ∧
      PaidOutcome paid dir (endGroup group before) outcome := by
  induction event with
  | @head group state dir t rest final pushes moves outcome outcomes i hero locks checked effect pays tail =>
    exact ⟨[],0,0,[],state,dir,t,outcome,outcomes,rest,pushes,moves,i,
      rfl,.nil state,checked,effect,tail,hero,locks,pays⟩
  | @tail group state dir t rest final pushes moves outcome outcomes i hero locks checked effect avoid later ih =>
    obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,payDir,u,payOutcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,one,effectOne,last,heroOne,locksOne,pays⟩ := ih
    refine ⟨dir::beforeDirs,t.pushCost+beforePushes,1+beforeMoves,outcome::before,
      middle,payDir,u,payOutcome,after,afterDirs,afterPushes,afterMoves,j,?_,
      .cons checked effect first,one,effectOne,last,heroOne,locksOne,pays⟩
    simp only [List.cons_append,shape]

theorem push_effect_result {board : Board} {state : State} {dir : Dir} {t : Transition}
    {source : Cell} {post : Ending}
    (checked : step board state dir = some t) (effect : Matches state t (.push source post)) :
    ∃ result : PushResult, pushBoulder board state source dir = some result ∧ post = ending result := by
  rcases step_cases_full board state dir t checked with walked | pushed
  · obtain ⟨target,_,_,_,_,shape⟩ := walked
    have same := matches_unique state t (.walk target) (.push source post) shape effect
    cases same
  · obtain ⟨other,result,_,_,present,push,shape⟩ := pushed
    have spec := pushBoulder_spec board state other dir result push
    have actualEffect : Matches state t (.push other (ending result)) := by
      rcases spec.1 with stay | fill
      · simp only [ending,stay.1]
        refine ⟨present,?_⟩
        simpa only [stay.1,stay.2,afterFill] using shape
      · simp only [ending,fill.1]
        refine ⟨present,fill.2.1,?_⟩
        simpa only [fill.1,fill.2.2,afterFill] using shape
    have same := matches_unique state t (.push other (ending result)) (.push source post) actualEffect effect
    have parts := Outcome.push.inj same
    rw [parts.1] at push
    exact ⟨result,push,parts.2.symm⟩

theorem push_effect_price {board : Board} {state : State} {dir : Dir} {t : Transition}
    {source : Cell} {post : Ending} (potential : Potential) (holes : List Cell) (price : Int)
    (holesInside : state.holes ⊆ holes)
    (priced : ∀ dest ∈ pushTargets board source dir,
      dest ∉ holes ∧ price ≤ 1 + potential.boulder dest - potential.boulder source)
    (checked : step board state dir = some t) (effect : Matches state t (.push source post)) :
    price ≤ slack potential (.push source post) := by
  obtain ⟨result,push,same⟩ := push_effect_result checked effect
  have spec := pushBoulder_spec board state source dir result push
  obtain ⟨noHole,cost⟩ := priced result.landing spec.2
  have unfilled : result.filled = none := by
    rcases spec.1 with stay | fill
    · exact stay.1
    · exact False.elim (noHole (holesInside fill.2.1))
  simpa only [same,ending,unfilled,slack] using cost

theorem closedExcept_energy {n : Nat} {K R : Fin n → List Cell} {paid : Cell → Dir → Prop}
    (closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes K R paid)
    (Kunique : ∀ i, (K i).Nodup) (large : ∀ i, 2 < (K i).length)
    (price : Int)
    (priced : ∀ source dir, paid source dir → ∀ dest ∈ pushTargets soko1_2.board source dir,
      dest ∉ soko1_2.initial.holes ∧
      price ≤ 1 + Generated.soko1_2Potential.boulder dest - Generated.soko1_2Potential.boulder source)
    {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final)
    {i : Fin n} (heroInside : state.player ∈ R i) (locksInside : K i ⊆ group) :
    price ≤ energy Generated.soko1_2Potential group outcomes := by
  have finalReached := reached.append logged.trace
  have conserved := finalReached.conservation
  have empty : final.holes = [] := completed
  change 20 + final.holes.length = final.boulders.length + 18 at conserved
  rw [empty] at conserved
  simp only [List.length_nil] at conserved
  rcases event_or_good closed Kunique logged reached group unique subset heroInside locksInside with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,hero,locks,pays⟩ := event.split
    have middleReached := reached.append first.trace
    have eventBound := event_energy_le Generated.soko1_2_potential_valid group first last outcome
    rw [shape]
    cases outcome with
    | walk target => exact False.elim pays
    | push source post =>
      obtain ⟨owner,paid⟩ := pays
      have one := push_effect_price Generated.soko1_2Potential soko1_2.initial.holes price
        middleReached.holes_sublist.subset (priced source dir paid) checked effect
      simp only [projectedOutcome,if_pos owner] at eventBound
      exact Int.le_trans one eventBound
  · obtain ⟨j,hero,locks⟩ := terminal
    have actualUnique := reached.boulders_nodup (by decide +kernel)
    have finalInside := logged.end_subset actualUnique group unique subset
    have persists : K j ⊆ final.boulders := List.Subset.trans locks finalInside.2
    have count := List.Nodup.length_le_of_subset (Kunique j) persists
    have big := large j
    omega

theorem push_effect_singleton {board : Board} {state : State} {dir : Dir} {t : Transition}
    {source dest : Cell} {post : Ending} (holes : List Cell)
    (holesInside : state.holes ⊆ holes)
    (targets : pushTargets board source dir = [dest]) (clear : dest ∉ holes)
    (checked : step board state dir = some t) (effect : Matches state t (.push source post)) :
    post = .stay dest := by
  obtain ⟨result,push,same⟩ := push_effect_result checked effect
  have spec := pushBoulder_spec board state source dir result push
  have landing : result.landing = dest := by
    simpa only [targets,List.mem_singleton] using spec.2
  have unfilled : result.filled = none := by
    rcases spec.1 with stay | fill
    · exact stay.1
    · exact False.elim (clear (holesInside (landing ▸ fill.2.1)))
  simp only [same,ending,unfilled,landing]

#print axioms EventLog.split
#print axioms push_effect_price
#print axioms closedExcept_energy
#print axioms push_effect_singleton
end Owner1007.OwnedEvents12
