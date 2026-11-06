/- Original-Trace transfer, with no search/monotonicity premise. Only
selected pushes pay auxiliary slack; all other real costs remain available.
The final selected debt is bounded by the debt of ALL four survivors. -/
import NetHack.Soko32Penalty5.OriginalStep
import NetHack.Soko32Penalty5.Soundness
namespace NetHack.Soko32Penalty5
open NetHack.Sokoban NetHack.Sokoban.LowerBounds

theorem project_suffix {state final : State} {dirs : List Dir} {pushes moves : Nat}
    (tail : Trace soko3_2.board state dirs final pushes moves)
    {history : List Dir} {previousPushes previousMoves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state previousPushes previousMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders) :
    ∃ after cost, Path actions group state.player after final.player cost ∧
      after.Nodup ∧ after ⊆ final.boulders ∧
      potential.value state + Int.ofNat cost ≤ Int.ofNat pushes + potential.value final := by
  induction tail generalizing history previousPushes previousMoves group with
  | nil => exact ⟨group,0,.nil _ _,unique,subset,by change _ + (0 : Int) ≤ (0 : Int) + _; omega⟩
  | @cons state dir t rest final pushes moves head tail ih =>
    obtain ⟨middle,first,edge,good,inside,bound⟩ := original_step reached group unique subset dir t head
    have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
    obtain ⟨after,cost,path,lastUnique,lastInside,lastBound⟩ := ih nextReached middle good inside
    refine ⟨after,first+cost,.cons edge path,lastUnique,lastInside,?_⟩
    simp only [Int.ofNat_eq_natCast,Int.natCast_add] at bound lastBound ⊢
    omega

theorem original_projected {dirs : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_2.board soko3_2.initial dirs final pushes moves) :
    ∃ after cost, Path actions initialGroup soko3_2.initial.player after final.player cost ∧
      after.Nodup ∧ after ⊆ final.boulders ∧
      (134 : Int) + Int.ofNat cost ≤ Int.ofNat pushes + potential.value final := by
  have result := project_suffix trace (Trace.nil soko3_2.initial) initialGroup
    (by decide +kernel) (by decide +kernel)
  simpa only [Generated.soko3_2_initial_potential] using result

theorem debt_neg (boxes : List Cell) : debt boxes = -weightSum potential.boulder boxes := by
  induction boxes with
  | nil => rfl
  | cons c rest ih => change -potential.boulder c + debt rest = -(potential.boulder c + weightSum potential.boulder rest); rw [ih]; omega

theorem original_lower_of_checked_table (table : IndexedCertificateTable.Table Row)
    (checked : ∀ i, Sound heroes actions table (IndexedCertificateTable.get zeroRow table i))
    (initial : Ticket heroes table initialGroup soko3_2.initial.player 5)
    {dirs : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_2.board soko3_2.initial dirs final pushes moves) (goal : Goal final) :
    139 ≤ pushes := by
  obtain ⟨group,cost,path,unique,subset,bound⟩ := original_projected trace
  have empty : final.holes = [] := goal
  have conserved := trace.conservation
  have terminal : final.boulders.length = 4 := by
    change 16 + final.holes.length = final.boulders.length + 12 at conserved
    rw [empty] at conserved
    change 16 + 0 = final.boulders.length + 12 at conserved
    omega
  have groupLength : group.length ≤ 4 := by
    have := List.Nodup.length_le_of_subset unique subset
    omega
  have penalty := path_bound heroes actions table checked sources_inside path initial groupLength
  have debtBound := NonlinearFacts.weightSum_le_of_nodup_subset
    (fun c => -potential.boulder c) group final.boulders
    (fun c => by
      have h := Generated.soko3_2_potential_valid.nonpositive c
      change potential.boulder c ≤ 0 at h
      omega) unique subset
  change debt group ≤ debt final.boulders at debtBound
  have finalValue : potential.value final = -debt final.boulders := by
    rw [debt_neg]
    simp only [Potential.value,empty,weightSum,Int.add_zero,Int.neg_neg]
  rw [finalValue] at bound
  simp only [Int.ofNat_eq_natCast] at bound penalty
  omega

end NetHack.Soko32Penalty5
