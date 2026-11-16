import Owner1007.After26512
import Owner1007.NorthBound12
namespace Owner1007.North265Bound12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
open Owner1007.After26512
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Owner1007.TokenAccounting Owner1007.OwnedEvents12
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
abbrev p := Generated.soko1_2Potential

theorem priced_min {source dir} (pays : paid source dir) :
    ∀ dest ∈ pushTargets soko1_2.board source dir,
      dest ∉ soko1_2.initial.holes ∧
      (if source=318 then (3:Int) else 2) ≤ 1+p.boulder dest-p.boulder source := by
  intro dest member
  have sourceInside : source ∈ ([291,318] : List Cell) := by rcases pays with h | h <;> simp_all
  have bound := paid_cost source sourceInside dir (Geometry.all_directions dir) pays dest member
  refine ⟨bound.1,?_⟩
  rw [bound.2]
  by_cases same : source=318
  · simp only [if_pos same]
    omega
  · simp only [if_neg same]
    by_cases south : dir=.south
    · simp only [if_pos south]; omega
    · simp only [if_neg south]; omega

theorem cash_cases {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (completed : Goal final)
    (i : Fin 4) (hero : state.player ∈ region i) (inside : locks i ⊆ state.boulders) :
    2 ≤ energy p [291] outcomes ∨
      (3 ≤ energy p [318] outcomes ∧ endGroup [318] outcomes ≠ []) := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
  have actualUnique := reached.boulders_nodup (by decide +kernel)
  rcases event_or_good closed unique logged reached (locks i) (unique i) inside
    hero (fun _ h => h) with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroOne,locksOne,pays,unchanged⟩ :=
      event.split_fixed fixed fixed_inside fixed_guard reached (unique i) inside
    have middleReached := reached.append first.trace
    have middleUnique := middleReached.boulders_nodup (by decide +kernel)
    have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
    cases outcome with
    | walk target => exact False.elim pays
    | push source ending =>
      obtain ⟨owner,paid⟩ := pays
      have rawCost := push_effect_price p soko1_2.initial.holes (if source=318 then (3:Int) else 2)
        middleReached.holes_sublist.subset (priced_min paid) checked effect
      rcases paid with h | h
      · obtain ⟨rfl,directions⟩ := h
        have prior := unchanged [291] (by decide +kernel)
        have bound := event_energy_le Generated.soko1_2_potential_valid [291] first last (.push 291 ending)
        simp only [prior,projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true] at bound
        change slack p (.push 291 ending) ≤ energy p [291] (before ++ .push 291 ending :: after) at bound
        have two : (2:Int) ≤ slack p (.push 291 ending) := by simpa using rawCost
        exact Or.inl (by rw [shape]; omega)
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel)
          (by decide +kernel) checked effect
        subst ending
        have bound := event_energy_le Generated.soko1_2_potential_valid [318] first last (.push 318 (.stay 317))
        have prior := unchanged [318] (by decide +kernel)
        simp only [prior,projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true] at bound
        change slack p (.push 318 (.stay 317)) ≤ energy p [318] (before ++ .push 318 (.stay 317) :: after) at bound
        have three : (3:Int) ≤ slack p (.push 318 (.stay 317)) := by simpa using rawCost
        have shapeNext : t.state.boulders=317::middle.boulders.erase 318 := by
          simpa only [Matches] using congrArg (fun h : Transition => h.state.boulders) effect.2
        have present : 317∈t.state.boulders := by rw [shapeNext]; simp
        have survives := NorthBound12.after_park_survives last nextActual 318 317 present
          NorthBound12.locked317 before prior
        exact Or.inr ⟨by rw [shape]; omega,by rw [shape]; exact survives⟩
  · obtain ⟨j,hero,locksInside⟩ := terminal
    have endInside := logged.end_subset actualUnique (locks i) (unique i) inside
    have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans locksInside endInside.2)
    have large := size j
    have conserved := (reached.append logged.trace).conservation
    have empty : final.holes=[] := completed
    change 20+final.holes.length=final.boulders.length+18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega

theorem activation : ∀ i : Fin 5, ∀ j : Fin 4, i.val=j.val →
    After26512.locks j ⊆ 291 :: (NorthEvents12.locks i).erase 265 := by decide +kernel

theorem first265_cases {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    (completed : Goal final)
    {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
    (shape : outcomes=before ++ .push 265 (.stay 291) :: after)
    (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .south=some t)
    (effect : Matches middle t (.push 265 (.stay 291)))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (i : Fin 5) (locksInside : NorthEvents12.locks i ⊆ endGroup NorthBound12.G before)
    (unchanged : ∀ small : List Cell, small ⊆ NorthEvents12.J → endGroup small before=small) :
    6 ≤ energy p NorthBound12.G outcomes ∨
      (5 ≤ energy p NorthBound12.G outcomes ∧ endGroup [318] outcomes ≠ []) := by
  have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
  have middleReached := NorthBound12.north_reached.append first.trace
  have middleUnique := middleReached.boulders_nodup (by decide +kernel)
  have oldInside := first.end_subset initialUnique NorthBound12.G (by decide +kernel) (by decide +kernel)
  have actualInside : NorthEvents12.locks i ⊆ middle.boulders := List.Subset.trans locksInside oldInside.2
  have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
  have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
  obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
  obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear soko1_2.board middle 265 .south result push).2
  have destEq : dest=291 := Option.some.inj (next.symm.trans (by decide +kernel))
  have clear291 : 291 ∉ middle.boulders := by simpa only [destEq] using clear
  have small : i.val<4 := by
    by_cases yes : i.val<4
    · exact yes
    · have val : i.val=4 := by have h:=i.isLt; omega
      have same : i=(4:Fin 5) := Fin.ext val
      subst i
      exact False.elim (clear291 (actualInside (by decide +kernel)))
  let j : Fin 4 := ⟨i.val,small⟩
  have shapeNext : t.state.boulders=291::middle.boulders.erase 265 := by
    simpa only [Matches] using congrArg (fun h : Transition => h.state.boulders) effect.2
  have erased := GhostSubset.erase_subset actualInside (NorthEvents12.unique i) 265
  have nextInside : After26512.locks j ⊆ t.state.boulders := by
    rw [shapeNext]
    exact List.Subset.trans (activation i j rfl) (List.cons_subset_cons 291 erased)
  have heroNext : t.state.player=265 := matches_hero middle t (.push 265 (.stay 291)) effect
  have nextHero : t.state.player∈After26512.region j := by rw [heroNext]; exact After26512.start_hero j
  have later := cash_cases last nextReached completed j nextHero nextInside
  have prior265 := unchanged [265] (by decide +kernel)
  have prior318 := unchanged [318] (by decide +kernel)
  have firstPrice : slack p (.push 265 (.stay 291))=2 := by decide +kernel
  have single265 : energy p [265] outcomes =
      ownSlack p [265] before + 2 + energy p [291] after := by
    rw [shape,energy_at_split,prior265]
    simp only [projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true,firstPrice,
      update,move,post,List.erase_cons_head]
  have single318 : energy p [318] outcomes =
      ownSlack p [318] before + energy p [318] after := by
    rw [shape,energy_at_split,prior318]
    have absent : (265:Cell)∉[318] := by decide +kernel
    simp only [projectedOutcome,if_neg absent,slack,update,move,Int.add_zero]
  have nn265 := first.ownSlack_nonnegative Generated.soko1_2_potential_valid [265]
  have nn318 := first.ownSlack_nonnegative Generated.soko1_2_potential_valid [318]
  change 0≤ownSlack p [265] before at nn265
  change 0≤ownSlack p [318] before at nn318
  have tailNN := last.energy_nonnegative Generated.soko1_2_potential_valid [291]
  change 0≤energy p [291] after at tailNN
  have jSplit := logged.energy_split initialUnique p [265] [210,237,238,263]
    (by decide +kernel) (by decide +kernel)
  have jPerm : ([265]++[210,237,238,263]).Perm NorthBound12.J := by decide +kernel
  have jSame := energy_perm p jPerm outcomes
  have jOther := logged.energy_nonnegative Generated.soko1_2_potential_valid [210,237,238,263]
  change 0≤energy p [210,237,238,263] outcomes at jOther
  have jReserve : energy p [265] outcomes ≤ energy p NorthBound12.J outcomes := by omega
  have bottom := NorthBound12.bottom_north_energy_two logged
  have bottomSplit := logged.energy_split initialUnique p [318] [345] (by decide +kernel) (by decide +kernel)
  change energy p NorthBound12.BottomN outcomes = energy p [318] outcomes + energy p [345] outcomes at bottomSplit
  have bottomOther := logged.energy_nonnegative Generated.soko1_2_potential_valid [345]
  change 0≤energy p [345] outcomes at bottomOther
  have gSplit := logged.energy_split initialUnique p NorthBound12.J NorthBound12.BottomN
    (by decide +kernel) (by decide +kernel)
  change energy p NorthBound12.G outcomes =
    energy p NorthBound12.J outcomes + energy p NorthBound12.BottomN outcomes at gSplit
  change 2≤energy p NorthBound12.BottomN outcomes at bottom
  rcases later with two | ⟨three,survives⟩
  · exact Or.inl (by omega)
  · refine Or.inr ⟨by omega,?_⟩
    rw [shape,endGroup_append,prior318]
    have absent : (265:Cell)∉[318] := by decide +kernel
    simpa only [endGroup,update,move,if_neg absent] using survives
#print axioms first265_cases
end Owner1007.North265Bound12
