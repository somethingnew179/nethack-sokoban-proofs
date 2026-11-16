import Owner1007.After21023612
import Owner1007.Residual290Any12


namespace Owner1007.After21023612
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
variable (matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true)
theorem priced_min {source dir} (pays : paid source dir) :
 ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧ (if source=318 then (3:Int) else 2)≤1+p.boulder dest-p.boulder source := by
 intro dest inside
 have sourceInside : source∈([262,238,265,318,291] : List Cell) := by
  rcases pays with ⟨h,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
  · rcases h with rfl | rfl | rfl <;> decide +kernel
  · decide +kernel
  · decide +kernel
 exact paid_cost source sourceInside dir (Geometry.all_directions dir) pays dest inside

include matrix in
theorem cash_cases {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (completed : Goal final)
    (group : List Cell) (gUnique : group.Nodup) (gSubset : group ⊆ state.boulders)
    (i : Fin 5) (hero : state.player ∈ region i) (inside : locks i ⊆ group) :
    2≤energy p ordinary outcomes ∨ 4≤energy p group outcomes ∨
      (3≤energy p group outcomes ∧ endGroup [318] outcomes≠[]) := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
  have actualUnique := reached.boulders_nodup (by decide +kernel)
  rcases event_or_good closed unique logged reached group gUnique gSubset hero inside with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroOne,locksOne,pays,unchanged⟩ :=
      event.split_fixed fixed fixed_inside fixed_guard reached gUnique gSubset
    have middleReached := reached.append first.trace
    have middleUnique := middleReached.boulders_nodup (by decide +kernel)
    have oldInside := first.end_subset actualUnique group gUnique gSubset
    have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
    have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual
      (endGroup group before) oldInside.1 oldInside.2
    have nextSubset := GhostSubset.update_subset middle t outcome effect
      (endGroup group before) oldInside.1 oldInside.2
    have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
    cases outcome with
    | walk target => exact False.elim pays
    | push source ending =>
      obtain ⟨owner,paid⟩ := pays
      have rawCost := push_effect_price p soko1_2.initial.holes (if source=318 then (3:Int) else 2)
        middleReached.holes_sublist.subset (priced_min paid) checked effect
      have allBound := event_energy_le Generated.soko1_2_potential_valid group first last (.push source ending)
      simp only [projectedOutcome,if_pos owner] at allBound
      change slack p (.push source ending) ≤ energy p group (before ++ .push source ending :: after) at allBound
      rcases paid with h | h | h
      · obtain ⟨choices,direction⟩ := h
        have member : source∈ordinary := by rcases choices with rfl | rfl | rfl <;> decide +kernel
        have prior := unchanged ordinary (by intro c h; exact List.mem_append_left _ h)
        have bound := event_energy_le Generated.soko1_2_potential_valid ordinary first last (.push source ending)
        simp only [prior,projectedOutcome,if_pos member] at bound
        change slack p (.push source ending) ≤ energy p ordinary (before ++ .push source ending :: after) at bound
        have different : source≠318 := by intro same; subst source; contradiction
        have two : (2:Int)≤slack p (.push source ending) := by simpa only [if_neg different] using rawCost
        exact Or.inl (by rw [shape]; omega)
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel)
          (by decide +kernel) checked effect
        subst ending
        have prior := unchanged [318] (by intro c h; have same:=List.mem_singleton.mp h; subst c; exact List.mem_append_right _ (by simp))
        have shapeNext : t.state.boulders=317::middle.boulders.erase 318 := by
          simpa only [Matches] using congrArg (fun h : Transition => h.state.boulders) effect.2
        have present : 317∈t.state.boulders := by rw [shapeNext]; simp
        have survives := NorthBound12.after_park_survives last nextActual 318 317 present
          NorthBound12.locked317 before prior
        have three : (3:Int)≤slack p (.push 318 (.stay 317)) := by simpa using rawCost
        exact Or.inr (Or.inr ⟨by rw [shape]; omega,by rw [shape]; exact survives⟩)
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          NorthEvents12.ring_activation (by decide +kernel) checked effect
        subst ending
        have erased := GhostSubset.erase_subset locksOne (unique j) 291
        have activation : ∀ j, Residual29012.locks 1 ⊆ 290::(locks j).erase 291 := by decide +kernel
        have ringInside : Residual29012.locks 1 ⊆ update (endGroup group before) (.push 291 (.stay 290)) := by
          simp only [update,move,if_pos owner,post]
          exact List.Subset.trans (activation j) (List.cons_subset_cons 290 erased)
        have heroNext : t.state.player=291 := matches_hero middle t (.push 291 (.stay 290)) effect
        have ringHeroNext : t.state.player∈Residual29012.region 1 := by rw [heroNext]; decide +kernel
        have later := Residual290Any12.owned_energy_credit Residual29012.matrix
          last nextReached (update (endGroup group before) (.push 291 (.stay 290)))
          nextUnique nextSubset 1 ringHeroNext ringInside
        change 3≤energy p (update (endGroup group before) (.push 291 (.stay 290))) after at later
        have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
        change 0≤ownSlack p group before at prefixNN
        have two : (2:Int)≤slack p (.push 291 (.stay 290)) := by simpa using rawCost
        exact Or.inr (Or.inl (by rw [shape,energy_at_split]; simp only [projectedOutcome,if_pos owner]; omega))
  · obtain ⟨j,hero,locksInside⟩ := terminal
    have endInside := logged.end_subset actualUnique group gUnique gSubset
    have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans locksInside endInside.2)
    have large := size j
    have conserved := (reached.append logged.trace).conservation
    have empty : final.holes=[] := completed
    change 20+final.holes.length=final.boulders.length+18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega
#print axioms cash_cases
end Owner1007.After21023612

