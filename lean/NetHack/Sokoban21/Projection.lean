/- Exact state projection for the staged soko2-1 certificate.
All invariants are consequences of the executable individual-move semantics.
No certificate leaf, proposer, or dead-square intuition is an assumption. -/
import NetHack.Sokoban21.Base
import NetHack.Sokoban.NonlinearFacts

set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
namespace NetHack.Sokoban21.Projection
open NetHack.Sokoban

/-- Only invariants actually needed by the finite certificate. -/
def Good (state : State) : Prop :=
  state.boulders.Nodup ∧ state.holes ⊆ soko2_1.initial.holes ∧
    state.boulders.length = state.holes.length + 3 ∧ state.player ∈ soko2_1.board.floor

instance (state : State) : Decidable (Good state) := by
  unfold Good
  infer_instance

theorem good_initial : Good soko2_1.initial := by decide

theorem step_good (state : State) (direction : Dir) (transition : Transition)
    (good : Good state) (checked : step soko2_1.board state direction = some transition) :
    Good transition.state := by
  rcases good with ⟨unique, subset, surplus, player⟩
  refine ⟨step_boulders_nodup _ _ _ _ unique checked,
    fun cell member => subset ((step_holes_sublist _ _ _ _ checked).subset member), ?_,
    step_player_floor _ _ _ _ checked⟩
  have conserved := step_conservation _ _ _ _ checked
  omega

theorem trace_good {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace soko2_1.board initial directions final pushes moves)
    (good : Good initial) : Good final := by
  induction trace with
  | nil => exact good
  | cons head tail ih => exact ih (step_good _ _ _ good head)

theorem reached_good {final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace soko2_1.board soko2_1.initial directions final pushes moves) :
    Good final := trace_good trace good_initial

theorem contains_erase_nodup (boxes : List Cell) (unique : boxes.Nodup)
    (source cell : Cell) :
    (boxes.erase source).contains cell = (boxes.contains cell && decide (source ≠ cell)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, Bool.and_eq_true_iff, decide_eq_true_eq]
  rw [unique.mem_erase_iff]
  exact ⟨fun h => ⟨h.2, Ne.symm h.1⟩, fun h => ⟨Ne.symm h.2, h.1⟩⟩

theorem index_eq_0 (cell : Cell) : index cell = 0 ↔ cell = 183 := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [index]
  all_goals by_cases h145 : cell = 145 <;> simp_all [index]
  all_goals by_cases h65 : cell = 65 <;> simp_all [index]
  all_goals by_cases h45 : cell = 45 <;> simp_all [index]
  all_goals by_cases h48 : cell = 48 <;> simp_all [index]
  all_goals by_cases h68 : cell = 68 <;> simp_all [index]
  all_goals by_cases h126 : cell = 126 <;> simp_all [index]
  all_goals by_cases h47 : cell = 47 <;> simp_all [index]
  all_goals by_cases h67 : cell = 67 <;> simp_all [index]
  all_goals by_cases h66 : cell = 66 <;> simp_all [index]
  all_goals by_cases h70 : cell = 70 <;> simp_all [index]
  all_goals by_cases h71 : cell = 71 <;> simp_all [index]

theorem index_eq_1 (cell : Cell) : index cell = 1 ↔ cell = 145 := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [index]
  all_goals by_cases h145 : cell = 145 <;> simp_all [index]
  all_goals by_cases h65 : cell = 65 <;> simp_all [index]
  all_goals by_cases h45 : cell = 45 <;> simp_all [index]
  all_goals by_cases h48 : cell = 48 <;> simp_all [index]
  all_goals by_cases h68 : cell = 68 <;> simp_all [index]
  all_goals by_cases h126 : cell = 126 <;> simp_all [index]
  all_goals by_cases h47 : cell = 47 <;> simp_all [index]
  all_goals by_cases h67 : cell = 67 <;> simp_all [index]
  all_goals by_cases h66 : cell = 66 <;> simp_all [index]
  all_goals by_cases h70 : cell = 70 <;> simp_all [index]
  all_goals by_cases h71 : cell = 71 <;> simp_all [index]

theorem index_eq_2 (cell : Cell) : index cell = 2 ↔ cell = 65 := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [index]
  all_goals by_cases h145 : cell = 145 <;> simp_all [index]
  all_goals by_cases h65 : cell = 65 <;> simp_all [index]
  all_goals by_cases h45 : cell = 45 <;> simp_all [index]
  all_goals by_cases h48 : cell = 48 <;> simp_all [index]
  all_goals by_cases h68 : cell = 68 <;> simp_all [index]
  all_goals by_cases h126 : cell = 126 <;> simp_all [index]
  all_goals by_cases h47 : cell = 47 <;> simp_all [index]
  all_goals by_cases h67 : cell = 67 <;> simp_all [index]
  all_goals by_cases h66 : cell = 66 <;> simp_all [index]
  all_goals by_cases h70 : cell = 70 <;> simp_all [index]
  all_goals by_cases h71 : cell = 71 <;> simp_all [index]

theorem index_eq_3 (cell : Cell) : index cell = 3 ↔ cell = 45 := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [index]
  all_goals by_cases h145 : cell = 145 <;> simp_all [index]
  all_goals by_cases h65 : cell = 65 <;> simp_all [index]
  all_goals by_cases h45 : cell = 45 <;> simp_all [index]
  all_goals by_cases h48 : cell = 48 <;> simp_all [index]
  all_goals by_cases h68 : cell = 68 <;> simp_all [index]
  all_goals by_cases h126 : cell = 126 <;> simp_all [index]
  all_goals by_cases h47 : cell = 47 <;> simp_all [index]
  all_goals by_cases h67 : cell = 67 <;> simp_all [index]
  all_goals by_cases h66 : cell = 66 <;> simp_all [index]
  all_goals by_cases h70 : cell = 70 <;> simp_all [index]
  all_goals by_cases h71 : cell = 71 <;> simp_all [index]

theorem index_eq_4 (cell : Cell) : index cell = 4 ↔ cell = 48 := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [index]
  all_goals by_cases h145 : cell = 145 <;> simp_all [index]
  all_goals by_cases h65 : cell = 65 <;> simp_all [index]
  all_goals by_cases h45 : cell = 45 <;> simp_all [index]
  all_goals by_cases h48 : cell = 48 <;> simp_all [index]
  all_goals by_cases h68 : cell = 68 <;> simp_all [index]
  all_goals by_cases h126 : cell = 126 <;> simp_all [index]
  all_goals by_cases h47 : cell = 47 <;> simp_all [index]
  all_goals by_cases h67 : cell = 67 <;> simp_all [index]
  all_goals by_cases h66 : cell = 66 <;> simp_all [index]
  all_goals by_cases h70 : cell = 70 <;> simp_all [index]
  all_goals by_cases h71 : cell = 71 <;> simp_all [index]

theorem index_eq_5 (cell : Cell) : index cell = 5 ↔ cell = 68 := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [index]
  all_goals by_cases h145 : cell = 145 <;> simp_all [index]
  all_goals by_cases h65 : cell = 65 <;> simp_all [index]
  all_goals by_cases h45 : cell = 45 <;> simp_all [index]
  all_goals by_cases h48 : cell = 48 <;> simp_all [index]
  all_goals by_cases h68 : cell = 68 <;> simp_all [index]
  all_goals by_cases h126 : cell = 126 <;> simp_all [index]
  all_goals by_cases h47 : cell = 47 <;> simp_all [index]
  all_goals by_cases h67 : cell = 67 <;> simp_all [index]
  all_goals by_cases h66 : cell = 66 <;> simp_all [index]
  all_goals by_cases h70 : cell = 70 <;> simp_all [index]
  all_goals by_cases h71 : cell = 71 <;> simp_all [index]

theorem index_eq_6 (cell : Cell) : index cell = 6 ↔ cell = 126 := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [index]
  all_goals by_cases h145 : cell = 145 <;> simp_all [index]
  all_goals by_cases h65 : cell = 65 <;> simp_all [index]
  all_goals by_cases h45 : cell = 45 <;> simp_all [index]
  all_goals by_cases h48 : cell = 48 <;> simp_all [index]
  all_goals by_cases h68 : cell = 68 <;> simp_all [index]
  all_goals by_cases h126 : cell = 126 <;> simp_all [index]
  all_goals by_cases h47 : cell = 47 <;> simp_all [index]
  all_goals by_cases h67 : cell = 67 <;> simp_all [index]
  all_goals by_cases h66 : cell = 66 <;> simp_all [index]
  all_goals by_cases h70 : cell = 70 <;> simp_all [index]
  all_goals by_cases h71 : cell = 71 <;> simp_all [index]

theorem index_eq_7 (cell : Cell) : index cell = 7 ↔ cell = 47 := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [index]
  all_goals by_cases h145 : cell = 145 <;> simp_all [index]
  all_goals by_cases h65 : cell = 65 <;> simp_all [index]
  all_goals by_cases h45 : cell = 45 <;> simp_all [index]
  all_goals by_cases h48 : cell = 48 <;> simp_all [index]
  all_goals by_cases h68 : cell = 68 <;> simp_all [index]
  all_goals by_cases h126 : cell = 126 <;> simp_all [index]
  all_goals by_cases h47 : cell = 47 <;> simp_all [index]
  all_goals by_cases h67 : cell = 67 <;> simp_all [index]
  all_goals by_cases h66 : cell = 66 <;> simp_all [index]
  all_goals by_cases h70 : cell = 70 <;> simp_all [index]
  all_goals by_cases h71 : cell = 71 <;> simp_all [index]

theorem index_eq_8 (cell : Cell) : index cell = 8 ↔ cell = 67 := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [index]
  all_goals by_cases h145 : cell = 145 <;> simp_all [index]
  all_goals by_cases h65 : cell = 65 <;> simp_all [index]
  all_goals by_cases h45 : cell = 45 <;> simp_all [index]
  all_goals by_cases h48 : cell = 48 <;> simp_all [index]
  all_goals by_cases h68 : cell = 68 <;> simp_all [index]
  all_goals by_cases h126 : cell = 126 <;> simp_all [index]
  all_goals by_cases h47 : cell = 47 <;> simp_all [index]
  all_goals by_cases h67 : cell = 67 <;> simp_all [index]
  all_goals by_cases h66 : cell = 66 <;> simp_all [index]
  all_goals by_cases h70 : cell = 70 <;> simp_all [index]
  all_goals by_cases h71 : cell = 71 <;> simp_all [index]

theorem index_eq_9 (cell : Cell) : index cell = 9 ↔ cell = 66 := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [index]
  all_goals by_cases h145 : cell = 145 <;> simp_all [index]
  all_goals by_cases h65 : cell = 65 <;> simp_all [index]
  all_goals by_cases h45 : cell = 45 <;> simp_all [index]
  all_goals by_cases h48 : cell = 48 <;> simp_all [index]
  all_goals by_cases h68 : cell = 68 <;> simp_all [index]
  all_goals by_cases h126 : cell = 126 <;> simp_all [index]
  all_goals by_cases h47 : cell = 47 <;> simp_all [index]
  all_goals by_cases h67 : cell = 67 <;> simp_all [index]
  all_goals by_cases h66 : cell = 66 <;> simp_all [index]
  all_goals by_cases h70 : cell = 70 <;> simp_all [index]
  all_goals by_cases h71 : cell = 71 <;> simp_all [index]

theorem index_eq_10 (cell : Cell) : index cell = 10 ↔ cell = 70 := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [index]
  all_goals by_cases h145 : cell = 145 <;> simp_all [index]
  all_goals by_cases h65 : cell = 65 <;> simp_all [index]
  all_goals by_cases h45 : cell = 45 <;> simp_all [index]
  all_goals by_cases h48 : cell = 48 <;> simp_all [index]
  all_goals by_cases h68 : cell = 68 <;> simp_all [index]
  all_goals by_cases h126 : cell = 126 <;> simp_all [index]
  all_goals by_cases h47 : cell = 47 <;> simp_all [index]
  all_goals by_cases h67 : cell = 67 <;> simp_all [index]
  all_goals by_cases h66 : cell = 66 <;> simp_all [index]
  all_goals by_cases h70 : cell = 70 <;> simp_all [index]
  all_goals by_cases h71 : cell = 71 <;> simp_all [index]

theorem index_eq_11 (cell : Cell) : index cell = 11 ↔ cell = 71 := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [index]
  all_goals by_cases h145 : cell = 145 <;> simp_all [index]
  all_goals by_cases h65 : cell = 65 <;> simp_all [index]
  all_goals by_cases h45 : cell = 45 <;> simp_all [index]
  all_goals by_cases h48 : cell = 48 <;> simp_all [index]
  all_goals by_cases h68 : cell = 68 <;> simp_all [index]
  all_goals by_cases h126 : cell = 126 <;> simp_all [index]
  all_goals by_cases h47 : cell = 47 <;> simp_all [index]
  all_goals by_cases h67 : cell = 67 <;> simp_all [index]
  all_goals by_cases h66 : cell = 66 <;> simp_all [index]
  all_goals by_cases h70 : cell = 70 <;> simp_all [index]
  all_goals by_cases h71 : cell = 71 <;> simp_all [index]

private theorem and_ne (value : Bool) (source cell : Cell) :
    (value && decide (source ≠ cell)) = (if source = cell then false else value) := by
  by_cases same : source = cell <;> simp [same]

theorem ofBoxes_erase (boxes : List Cell) (unique : boxes.Nodup) (source : Cell) :
    ofBoxes (boxes.erase source) = erase (ofBoxes boxes) source := by
  simp only [ofBoxes, erase, change, Twelve.mk.injEq,
    contains_erase_nodup boxes unique source, and_ne,
    index_eq_0,
    index_eq_1,
    index_eq_2,
    index_eq_3,
    index_eq_4,
    index_eq_5,
    index_eq_6,
    index_eq_7,
    index_eq_8,
    index_eq_9,
    index_eq_10,
    index_eq_11,
    Nat.reduceEqDiff, ↓reduceIte]

private theorem or_eq_if (value : Bool) (destination cell : Cell) :
    ((cell == destination) || value) = (if destination = cell then true else value) := by
  by_cases same : destination = cell
  · simp [same]
  · have reversed : cell ≠ destination := Ne.symm same
    simp [same, reversed]

theorem ofBoxes_cons (boxes : List Cell) (destination : Cell) :
    ofBoxes (destination :: boxes) = insert (ofBoxes boxes) destination := by
  simp only [ofBoxes, insert, change, Twelve.mk.injEq, List.contains_cons,
    index_eq_0,
    index_eq_1,
    index_eq_2,
    index_eq_3,
    index_eq_4,
    index_eq_5,
    index_eq_6,
    index_eq_7,
    index_eq_8,
    index_eq_9,
    index_eq_10,
    index_eq_11,
    Nat.reduceEqDiff, ↓reduceIte, or_eq_if]

theorem change_eq_insert_erase (pattern : Twelve) (source destination : Cell) :
    change pattern (index source) (index destination) = insert (erase pattern source) destination := by
  simp only [insert, erase, change, Twelve.mk.injEq, Nat.reduceEqDiff, ↓reduceIte]

theorem ofBoxes_replace (boxes : List Cell) (unique : boxes.Nodup) (source destination : Cell) :
    ofBoxes (destination :: boxes.erase source) =
      change (ofBoxes boxes) (index source) (index destination) := by
  rw [ofBoxes_cons, ofBoxes_erase boxes unique, ← change_eq_insert_erase]

/-- Exact count equations count occurrences, and do not assume Nodup. -/
theorem deadCount_cons (boxes : List Cell) (destination : Cell) :
    deadCount (destination :: boxes) = deadCount boxes + if destination ∈ deadCells then 1 else 0 := by
  by_cases dead : destination ∈ deadCells <;> simp [deadCount, List.filter_cons, dead, Nat.add_comm]

theorem deadCount_erase_add (boxes : List Cell) (source : Cell) (present : source ∈ boxes) :
    deadCount (boxes.erase source) + (if source ∈ deadCells then 1 else 0) = deadCount boxes := by
  by_cases dead : source ∈ deadCells
  · have filtered : source ∈ boxes.filter (fun cell => deadCells.contains cell) := by simp [present, dead]
    have erased := List.length_erase_of_mem filtered
    have positive := List.length_pos_of_mem filtered
    rw [List.erase_filter] at erased
    simp only [deadCount, if_pos dead]
    omega
  · have absent : source ∉ boxes.filter (fun cell => deadCells.contains cell) := by simp [dead]
    have equal := List.erase_of_not_mem absent
    rw [List.erase_filter] at equal
    simp only [deadCount, if_neg dead, Nat.add_zero]
    exact congrArg List.length equal

theorem deadCount_replace (boxes : List Cell) (source destination : Cell) (present : source ∈ boxes) :
    deadCount (destination :: boxes.erase source) + (if source ∈ deadCells then 1 else 0) =
      deadCount boxes + (if destination ∈ deadCells then 1 else 0) := by
  rw [deadCount_cons]
  have removed := deadCount_erase_add boxes source present
  omega

theorem known_ofBoxes_eq (boxes : List Cell) (cell : Cell) :
    known (ofBoxes boxes) cell = (support.contains cell && boxes.contains cell) := by
  all_goals by_cases h183 : cell = 183 <;> simp_all [known, ofBoxes, support]
  all_goals by_cases h145 : cell = 145 <;> simp_all [known, ofBoxes, support]
  all_goals by_cases h65 : cell = 65 <;> simp_all [known, ofBoxes, support]
  all_goals by_cases h45 : cell = 45 <;> simp_all [known, ofBoxes, support]
  all_goals by_cases h48 : cell = 48 <;> simp_all [known, ofBoxes, support]
  all_goals by_cases h68 : cell = 68 <;> simp_all [known, ofBoxes, support]
  all_goals by_cases h126 : cell = 126 <;> simp_all [known, ofBoxes, support]
  all_goals by_cases h47 : cell = 47 <;> simp_all [known, ofBoxes, support]
  all_goals by_cases h67 : cell = 67 <;> simp_all [known, ofBoxes, support]
  all_goals by_cases h66 : cell = 66 <;> simp_all [known, ofBoxes, support]
  all_goals by_cases h70 : cell = 70 <;> simp_all [known, ofBoxes, support]
  all_goals by_cases h71 : cell = 71 <;> simp_all [known, ofBoxes, support]

theorem known_ofBoxes_true (boxes : List Cell) (cell : Cell) :
    known (ofBoxes boxes) cell = true ↔ cell ∈ support ∧ cell ∈ boxes := by
  simp [known_ofBoxes_eq]

def occupied (pattern : Twelve) : List Cell := support.filter (known pattern)
def occupiedLive (boxes : List Cell) : List Cell :=
  support.filter fun cell => !deadCells.contains cell && boxes.contains cell

theorem support_nodup : support.Nodup := by decide

theorem occupied_ofBoxes (boxes : List Cell) :
    occupied (ofBoxes boxes) = NonlinearFacts.occupied support boxes := by
  unfold occupied NonlinearFacts.occupied
  apply List.filter_congr
  intro cell member
  simp [known_ofBoxes_eq, member]

theorem occupied_length_le (boxes : List Cell) :
    (occupied (ofBoxes boxes)).length ≤ boxes.length := by
  rw [occupied_ofBoxes]
  exact NonlinearFacts.occupied_length_le support boxes support_nodup

theorem deadCount_le (boxes : List Cell) : deadCount boxes ≤ boxes.length :=
  List.length_filter_le _ _

private theorem filter_partition_length (predicate : Cell → Bool) (cells : List Cell) :
    (cells.filter predicate).length + (cells.filter fun cell => !predicate cell).length = cells.length := by
  induction cells with
  | nil => rfl
  | cons head tail ih =>
    cases selected : predicate head <;> simp [List.filter_cons, selected] at * <;> omega

theorem dead_live_budget (boxes : List Cell) :
    deadCount boxes + (occupiedLive boxes).length ≤ boxes.length := by
  have unique : (occupiedLive boxes).Nodup := List.Nodup.sublist List.filter_sublist support_nodup
  have subset : occupiedLive boxes ⊆ boxes.filter (fun cell => !deadCells.contains cell) := by
    intro cell member
    have properties := List.mem_filter.mp member
    rcases Bool.and_eq_true_iff.mp properties.2 with ⟨live, present⟩
    exact List.mem_filter.mpr ⟨List.contains_iff_mem.mp present, live⟩
  have bound := List.Nodup.length_le_of_subset unique subset
  have partition := filter_partition_length (fun cell => deadCells.contains cell) boxes
  unfold deadCount
  omega

theorem goal_boxes_length (state : State) (good : Good state) (completed : Goal state) :
    state.boulders.length = 3 := by
  have surplus := good.2.2.1
  change state.holes = [] at completed
  simpa [completed] using surplus

theorem goal_budgets (state : State) (good : Good state) (completed : Goal state) :
    deadCount state.boulders ≤ 3 ∧ (occupied (ofBoxes state.boulders)).length ≤ 3 ∧
      deadCount state.boulders + (occupiedLive state.boulders).length ≤ 3 := by
  have length := goal_boxes_length state good completed
  exact ⟨by simpa only [length] using deadCount_le state.boulders,
    by simpa only [length] using occupied_length_le state.boulders,
    by simpa only [length] using dead_live_budget state.boulders⟩

/-- The finite dead-cell premise is checked against every relaxed push/roll
landing, not guessed from visual corners or search pruning. -/
def deadClosedCheck : Bool := deadCells.all fun source => allDirs.all fun direction =>
  (pushTargets soko2_1.board source direction).all fun landing => deadCells.contains landing

theorem dead_closed_row0 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 21 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row1 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 22 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row2 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 23 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row3 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 24 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row4 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 25 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row5 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 26 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row6 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 27 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row7 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 28 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row8 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 30 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row9 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 31 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row10 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 32 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row11 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 34 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row12 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 35 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row13 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 36 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row14 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 37 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row15 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 38 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row16 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 41 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row17 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 52 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row18 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 54 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row19 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 55 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row20 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 56 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row21 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 57 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row22 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 58 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row23 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 61 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row24 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 72 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row25 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 74 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row26 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 75 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row27 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 76 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row28 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 77 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row29 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 78 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row30 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 84 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row31 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 85 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row32 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 92 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row33 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 94 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row34 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 95 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row35 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 96 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row36 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 97 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row37 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 98 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row38 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 101 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row39 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 103 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row40 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 106 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row41 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 112 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row42 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 114 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row43 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 115 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row44 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 116 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row45 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 117 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row46 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 118 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row47 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 121 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row48 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 125 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row49 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 127 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row50 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 131 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row51 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 134 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row52 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 135 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row53 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 136 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row54 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 137 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row55 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 138 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row56 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 141 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row57 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 148 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row58 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 149 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row59 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 150 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row60 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 154 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row61 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 155 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row62 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 156 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row63 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 157 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row64 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 158 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row65 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 181 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row66 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 198 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row67 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 201 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row68 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 202 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row69 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 203 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row70 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 205 direction).all fun landing => deadCells.contains landing) = true := by decide
theorem dead_closed_row71 : allDirs.all (fun direction =>
    (pushTargets soko2_1.board 206 direction).all fun landing => deadCells.contains landing) = true := by decide

theorem dead_closed_checked : deadClosedCheck = true :=
  List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨dead_closed_row0, (List.forall_mem_cons.mpr ⟨dead_closed_row1, (List.forall_mem_cons.mpr ⟨dead_closed_row2, (List.forall_mem_cons.mpr ⟨dead_closed_row3, (List.forall_mem_cons.mpr ⟨dead_closed_row4, (List.forall_mem_cons.mpr ⟨dead_closed_row5, (List.forall_mem_cons.mpr ⟨dead_closed_row6, (List.forall_mem_cons.mpr ⟨dead_closed_row7, (List.forall_mem_cons.mpr ⟨dead_closed_row8, (List.forall_mem_cons.mpr ⟨dead_closed_row9, (List.forall_mem_cons.mpr ⟨dead_closed_row10, (List.forall_mem_cons.mpr ⟨dead_closed_row11, (List.forall_mem_cons.mpr ⟨dead_closed_row12, (List.forall_mem_cons.mpr ⟨dead_closed_row13, (List.forall_mem_cons.mpr ⟨dead_closed_row14, (List.forall_mem_cons.mpr ⟨dead_closed_row15, (List.forall_mem_cons.mpr ⟨dead_closed_row16, (List.forall_mem_cons.mpr ⟨dead_closed_row17, (List.forall_mem_cons.mpr ⟨dead_closed_row18, (List.forall_mem_cons.mpr ⟨dead_closed_row19, (List.forall_mem_cons.mpr ⟨dead_closed_row20, (List.forall_mem_cons.mpr ⟨dead_closed_row21, (List.forall_mem_cons.mpr ⟨dead_closed_row22, (List.forall_mem_cons.mpr ⟨dead_closed_row23, (List.forall_mem_cons.mpr ⟨dead_closed_row24, (List.forall_mem_cons.mpr ⟨dead_closed_row25, (List.forall_mem_cons.mpr ⟨dead_closed_row26, (List.forall_mem_cons.mpr ⟨dead_closed_row27, (List.forall_mem_cons.mpr ⟨dead_closed_row28, (List.forall_mem_cons.mpr ⟨dead_closed_row29, (List.forall_mem_cons.mpr ⟨dead_closed_row30, (List.forall_mem_cons.mpr ⟨dead_closed_row31, (List.forall_mem_cons.mpr ⟨dead_closed_row32, (List.forall_mem_cons.mpr ⟨dead_closed_row33, (List.forall_mem_cons.mpr ⟨dead_closed_row34, (List.forall_mem_cons.mpr ⟨dead_closed_row35, (List.forall_mem_cons.mpr ⟨dead_closed_row36, (List.forall_mem_cons.mpr ⟨dead_closed_row37, (List.forall_mem_cons.mpr ⟨dead_closed_row38, (List.forall_mem_cons.mpr ⟨dead_closed_row39, (List.forall_mem_cons.mpr ⟨dead_closed_row40, (List.forall_mem_cons.mpr ⟨dead_closed_row41, (List.forall_mem_cons.mpr ⟨dead_closed_row42, (List.forall_mem_cons.mpr ⟨dead_closed_row43, (List.forall_mem_cons.mpr ⟨dead_closed_row44, (List.forall_mem_cons.mpr ⟨dead_closed_row45, (List.forall_mem_cons.mpr ⟨dead_closed_row46, (List.forall_mem_cons.mpr ⟨dead_closed_row47, (List.forall_mem_cons.mpr ⟨dead_closed_row48, (List.forall_mem_cons.mpr ⟨dead_closed_row49, (List.forall_mem_cons.mpr ⟨dead_closed_row50, (List.forall_mem_cons.mpr ⟨dead_closed_row51, (List.forall_mem_cons.mpr ⟨dead_closed_row52, (List.forall_mem_cons.mpr ⟨dead_closed_row53, (List.forall_mem_cons.mpr ⟨dead_closed_row54, (List.forall_mem_cons.mpr ⟨dead_closed_row55, (List.forall_mem_cons.mpr ⟨dead_closed_row56, (List.forall_mem_cons.mpr ⟨dead_closed_row57, (List.forall_mem_cons.mpr ⟨dead_closed_row58, (List.forall_mem_cons.mpr ⟨dead_closed_row59, (List.forall_mem_cons.mpr ⟨dead_closed_row60, (List.forall_mem_cons.mpr ⟨dead_closed_row61, (List.forall_mem_cons.mpr ⟨dead_closed_row62, (List.forall_mem_cons.mpr ⟨dead_closed_row63, (List.forall_mem_cons.mpr ⟨dead_closed_row64, (List.forall_mem_cons.mpr ⟨dead_closed_row65, (List.forall_mem_cons.mpr ⟨dead_closed_row66, (List.forall_mem_cons.mpr ⟨dead_closed_row67, (List.forall_mem_cons.mpr ⟨dead_closed_row68, (List.forall_mem_cons.mpr ⟨dead_closed_row69, (List.forall_mem_cons.mpr ⟨dead_closed_row70, (List.forall_mem_cons.mpr ⟨dead_closed_row71, (by intro source member; cases member)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

private theorem allDirs_mem (direction : Dir) : direction ∈ allDirs := by
  cases direction <;> simp [allDirs, cardinalDirs]

theorem dead_closed (source : Cell) (dead : source ∈ deadCells) (direction : Dir)
    (landing : Cell) (target : landing ∈ pushTargets soko2_1.board source direction) :
    landing ∈ deadCells := by
  exact List.contains_iff_mem.mp (List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp dead_closed_checked source dead)
      direction (allDirs_mem direction)) landing target)

def deadNoHolesCheck : Bool := deadCells.all fun cell => !soko2_1.initial.holes.contains cell

theorem dead_no_holes_checked : deadNoHolesCheck = true := by decide

theorem dead_no_original_hole (cell : Cell) (dead : cell ∈ deadCells) :
    cell ∉ soko2_1.initial.holes := by
  have absent := List.all_eq_true.mp dead_no_holes_checked cell dead
  simpa using absent

theorem floor_eq : floor = soko2_1.board.floor := by decide

/-- An admitted non-consuming push removes one occurrence and inserts its
actual (possibly multi-cell rolling) landing; the dead count never falls. -/
theorem push_deadCount (state : State) (source : Cell) (direction : Dir) (result : PushResult)
    (holes : state.holes ⊆ soko2_1.initial.holes) (present : source ∈ state.boulders)
    (checked : pushBoulder soko2_1.board state source direction = some result) :
    deadCount state.boulders ≤ deadCount result.boulders := by
  rcases pushBoulder_spec _ _ _ _ _ checked with ⟨shape, target⟩
  rcases shape with stays | consumes
  · rcases stays with ⟨_, boxes⟩
    rw [boxes]
    have counts := deadCount_replace state.boulders source result.landing present
    by_cases dead : source ∈ deadCells
    · have landing := dead_closed source dead direction result.landing target
      simp only [if_pos dead, if_pos landing] at counts
      omega
    · simp only [if_neg dead] at counts
      omega
  · rcases consumes with ⟨_, hazard, boxes⟩
    rw [boxes]
    have counts := deadCount_erase_add state.boulders source present
    have sourceLive : source ∉ deadCells := by
      intro dead
      have landing := dead_closed source dead direction result.landing target
      exact dead_no_original_hole result.landing landing (holes hazard)
    simpa only [if_neg sourceLive, Nat.add_zero] using Nat.le_of_eq counts.symm

theorem step_deadCount (state : State) (direction : Dir) (transition : Transition)
    (good : Good state) (checked : step soko2_1.board state direction = some transition) :
    deadCount state.boulders ≤ deadCount transition.state.boulders := by
  rcases step_cases_full _ _ _ _ checked with walk | pushed
  · rcases walk with ⟨_, _, _, _, _, shape⟩
    simp [shape]
  · rcases pushed with ⟨source, result, _, _, present, pushChecked, shape⟩
    simpa only [shape] using push_deadCount state source direction result good.2.1 present pushChecked


theorem known_clear (boxes : List Cell) (cell : Cell) (absent : cell ∉ boxes) :
    known (ofBoxes boxes) cell = false := by
  simp [known_ofBoxes_eq, absent]

theorem source_dead_budget (boxes : List Cell) (source : Cell)
    (present : source ∈ boxes) (dead : source ∈ deadCells) : 1 ≤ deadCount boxes := by
  have member : source ∈ boxes.filter (fun cell => deadCells.contains cell) := by simp [present, dead]
  exact List.length_pos_of_mem member

theorem deadCount_erase (boxes : List Cell) (source : Cell) (present : source ∈ boxes) :
    deadCount (boxes.erase source) = deadCount boxes - (if source ∈ deadCells then 1 else 0) := by
  have counts := deadCount_erase_add boxes source present
  by_cases dead : source ∈ deadCells <;> simp only [dead, ↓reduceIte] at * <;> omega

theorem deadCount_replace_exact (boxes : List Cell) (source destination : Cell) (present : source ∈ boxes) :
    deadCount (destination :: boxes.erase source) = deadCount boxes -
      (if source ∈ deadCells then 1 else 0) + (if destination ∈ deadCells then 1 else 0) := by
  rw [deadCount_cons, deadCount_erase boxes source present]

theorem push_consumes_deadCount (state : State) (source : Cell) (direction : Dir) (result : PushResult)
    (holes : state.holes ⊆ soko2_1.initial.holes) (present : source ∈ state.boulders)
    (checked : pushBoulder soko2_1.board state source direction = some result)
    (consumed : result.filled = some result.landing) :
    source ∉ deadCells ∧ deadCount result.boulders = deadCount state.boulders := by
  rcases pushBoulder_spec _ _ _ _ _ checked with ⟨shape, target⟩
  rcases shape with stays | consumes
  · rcases stays with ⟨empty, _⟩
    rw [empty] at consumed
    contradiction
  · rcases consumes with ⟨_, hazard, boxes⟩
    have sourceLive : source ∉ deadCells := by
      intro dead
      exact dead_no_original_hole result.landing (dead_closed source dead direction result.landing target)
        (holes hazard)
    refine ⟨sourceLive, ?_⟩
    rw [boxes, deadCount_erase state.boulders source present]
    simp only [if_neg sourceLive, Nat.sub_zero]

theorem push_projection (state : State) (source : Cell) (direction : Dir) (result : PushResult)
    (good : Good state) (present : source ∈ state.boulders)
    (checked : pushBoulder soko2_1.board state source direction = some result) :
    (result.filled = none ∧
      ofBoxes result.boulders = change (ofBoxes state.boulders) (index source) (index result.landing) ∧
      deadCount result.boulders = deadCount state.boulders - (if source ∈ deadCells then 1 else 0) +
        (if result.landing ∈ deadCells then 1 else 0)) ∨
    (result.filled = some result.landing ∧ result.landing ∈ state.holes ∧
      ofBoxes result.boulders = erase (ofBoxes state.boulders) source ∧
      source ∉ deadCells ∧ deadCount result.boulders = deadCount state.boulders) := by
  rcases (pushBoulder_spec _ _ _ _ _ checked).1 with stays | consumes
  · rcases stays with ⟨filled, boxes⟩
    refine Or.inl ⟨filled, ?_, ?_⟩
    · rw [boxes]
      exact ofBoxes_replace state.boulders good.1 source result.landing
    · rw [boxes]
      exact deadCount_replace_exact state.boulders source result.landing present
  · rcases consumes with ⟨filled, hazard, boxes⟩
    rcases push_consumes_deadCount state source direction result good.2.1 present checked filled with
      ⟨sourceLive, counts⟩
    refine Or.inr ⟨filled, hazard, ?_, sourceLive, counts⟩
    rw [boxes]
    exact ofBoxes_erase state.boulders good.1 source

theorem trace_deadCount {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace soko2_1.board initial directions final pushes moves) (good : Good initial) :
    deadCount initial.boulders ≤ deadCount final.boulders := by
  induction trace with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    exact Nat.le_trans (step_deadCount _ _ _ good head) (ih (step_good _ _ _ good head))

theorem goal_known_live_clear (state : State) (good : Good state) (completed : Goal state)
    (spent : deadCount state.boulders = 3) (cell : Cell) (live : cell ∉ deadCells) :
    known (ofBoxes state.boulders) cell = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  rcases (known_ofBoxes_true state.boulders cell).mp present with ⟨supported, box⟩
  have member : cell ∈ occupiedLive state.boulders := by
    simp [occupiedLive, supported, live, box]
  have positive := List.length_pos_of_mem member
  have budget := (goal_budgets state good completed).2.2
  omega


theorem support_live_checked : support.all (fun cell => !deadCells.contains cell) = true := by decide

theorem support_live (cell : Cell) (member : cell ∈ support) : cell ∉ deadCells := by
  have live := List.all_eq_true.mp support_live_checked cell member
  simpa using live

theorem occupiedLive_ofBoxes (boxes : List Cell) : occupiedLive boxes = occupied (ofBoxes boxes) := by
  unfold occupiedLive occupied
  apply List.filter_congr
  intro cell member
  simp [known_ofBoxes_eq, member, support_live cell member]

theorem goal_occupied_budget (state : State) (good : Good state) (completed : Goal state) :
    deadCount state.boulders + (occupied (ofBoxes state.boulders)).length ≤ 3 := by
  have budget := (goal_budgets state good completed).2.2
  simpa only [occupiedLive_ofBoxes] using budget

end NetHack.Sokoban21.Projection
