import NetHack.Sokoban.Maps

namespace Owner1007
open NetHack.Sokoban

/-- The first destination is blocked independently of open holes or rolls. -/
def BlockedPush (board : Board) (locks : List Cell) (source : Cell) (dir : Dir) : Prop :=
  dir.diagonal = true ∨ match advance board source dir with
    | none => True
    | some dest => dest ∉ board.floor ∨ dest ∈ board.doors ∨ dest ∈ locks

instance (board : Board) (locks : List Cell) (source : Cell) (dir : Dir) :
    Decidable (BlockedPush board locks source dir) := by
  unfold BlockedPush
  cases advance board source dir <;> dsimp <;> infer_instance

/-- An occupancy cut: a push touching the set needs a hero inside it, or has
an immediately blocked destination. This quantifies over positions, not game states. -/
def Locked (board : Board) (locks : List Cell) : Prop :=
  ∀ hero ∈ board.floor, ∀ dir : Dir, ∀ source ∈ locks,
    advance board hero dir = some source → hero ∈ locks ∨ BlockedPush board locks source dir

def lockedCheck (board : Board) (locks : List Cell) : Bool :=
  board.floor.all fun hero => allDirs.all fun dir => locks.all fun source =>
    decide (advance board hero dir ≠ some source ∨ hero ∈ locks ∨ BlockedPush board locks source dir)

theorem locked_of_check (board : Board) (locks : List Cell)
    (checked : lockedCheck board locks = true) : Locked board locks := by
  intro hero floor dir source member adjacent
  have all : dir ∈ allDirs := by cases dir <;> simp [allDirs, cardinalDirs]
  have row := List.all_eq_true.mp checked hero floor
  have cells := List.all_eq_true.mp row dir all
  have entry := of_decide_eq_true (List.all_eq_true.mp cells source member)
  exact entry.resolve_left (fun different => different adjacent)

theorem push_first_clear (board : Board) (state : State) (source : Cell)
    (dir : Dir) (result : PushResult)
    (checked : pushBoulder board state source dir = some result) :
    dir.diagonal = false ∧ ∃ dest, advance board source dir = some dest ∧
      dest ∈ board.floor ∧ dest ∉ board.doors ∧ dest ∉ state.boulders := by
  cases diagonal : dir.diagonal with
  | true => simp [pushBoulder, diagonal] at checked
  | false =>
    refine ⟨rfl, ?_⟩
    cases support : advance board source dir.opposite with
    | none => simp [pushBoulder, diagonal, support] at checked
    | some behind =>
      by_cases floor : behind ∈ board.floor
      · by_cases door : behind ∈ board.doors
        · simp [pushBoulder, diagonal, support, floor, door] at checked
        · cases adjacent : advance board source dir with
          | none => simp [pushBoulder, diagonal, support, floor, door, adjacent] at checked
          | some dest =>
            by_cases targetFloor : dest ∈ board.floor
            · by_cases targetDoor : dest ∈ board.doors
              · simp [pushBoulder, diagonal, support, floor, door, adjacent, targetFloor, targetDoor] at checked
              · by_cases collision : dest ∈ state.boulders
                · simp [pushBoulder, diagonal, support, floor, door, adjacent, targetFloor, targetDoor, collision] at checked
                · exact ⟨dest, rfl, targetFloor, targetDoor, collision⟩
            · simp [pushBoulder, diagonal, support, floor, door, adjacent, targetFloor] at checked
      · simp [pushBoulder, diagonal, support, floor] at checked

theorem locked_step {board : Board} {locks : List Cell} (locked : Locked board locks)
    {state : State} {dir : Dir} {t : Transition} (inside : locks ⊆ state.boulders)
    (checked : step board state dir = some t) : locks ⊆ t.state.boulders := by
  rcases step_cases_full board state dir t checked with walked | pushed
  · obtain ⟨target, _, _, _, _, shape⟩ := walked
    simpa only [shape] using inside
  · obtain ⟨source, result, adjacent, _, _, push, shape⟩ := pushed
    have clear := step_player_clear board state dir t checked
    have first := push_first_clear board state source dir result push
    have outside : source ∉ locks := by
      intro member
      rcases locked state.player clear.1 dir source member adjacent with hero | blocked
      · exact clear.2.2.1 (inside hero)
      · rcases blocked with diagonal | blocked
        · simp [first.1] at diagonal
        · obtain ⟨dest, next, floor, door, empty⟩ := first.2
          simp only [next] at blocked
          rcases blocked with wall | door' | box
          · exact wall floor
          · exact door door'
          · exact empty (inside box)
    intro cell member
    have different : cell ≠ source := by
      intro same
      exact outside (same ▸ member)
    have erased : cell ∈ state.boulders.erase source :=
      (List.mem_erase_of_ne different).mpr (inside member)
    rcases (pushBoulder_spec board state source dir result push).1 with stays | fills
    · simpa only [shape, stays.2] using List.mem_cons_of_mem result.landing erased
    · simpa only [shape, fills.2.2] using erased

theorem locked_trace {board : Board} {locks : List Cell} (locked : Locked board locks)
    {state final : State} {dirs : List Dir} {pushes moves : Nat}
    (trace : Trace board state dirs final pushes moves) (inside : locks ⊆ state.boulders) :
    locks ⊆ final.boulders := by
  induction trace with
  | nil => exact inside
  | cons head tail ih => exact ih (locked_step locked inside head)

def square12 : List Cell := [186, 187, 212, 213]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem square12_locked : Locked soko1_2.board square12 := by
  exact locked_of_check _ _ (by decide +kernel)

/-- No completing suffix of any reached original state can contain this
four-boulder square. This uses the original consumption/conservation law. -/
theorem square12_excluded {state final : State} {history dirs : List Dir}
    {previousPushes previousMoves pushes moves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state previousPushes previousMoves)
    (tail : Trace soko1_2.board state dirs final pushes moves) (completed : Goal final) :
    ¬ square12 ⊆ state.boulders := by
  intro inside
  have persists := locked_trace square12_locked tail inside
  have cardinality := List.Nodup.length_le_of_subset (show square12.Nodup by decide +kernel) persists
  have prefixConserved := reached.conservation
  have suffixConserved := tail.conservation
  have empty : final.holes = [] := completed
  change 20 + state.holes.length = state.boulders.length + 18 at prefixConserved
  rw [empty] at suffixConserved
  change 4 ≤ final.boulders.length at cardinality
  simp only [List.length_nil] at suffixConserved
  omega

theorem dead317_locked : Locked soko1_2.board [317] := by
  exact locked_of_check _ _ (by decide +kernel)

theorem dead317_persists {state final : State} {dirs : List Dir} {pushes moves : Nat}
    (trace : Trace soko1_2.board state dirs final pushes moves)
    (present : 317 ∈ state.boulders) : 317 ∈ final.boulders :=
  locked_trace dead317_locked trace (by simpa using present) (by simp)

def dead12 : List Cell := [135, 317, 320, 370, 294, 288]

theorem dead12_checked : dead12.all (fun cell => lockedCheck soko1_2.board [cell]) = true := by
  decide +kernel

/-- Several separately frozen corners share the same TWO-survivor budget.
One cannot add independent corner penalties while forgetting this common budget. -/
theorem dead12_budget {state final : State} {history dirs : List Dir}
    {previousPushes previousMoves pushes moves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state previousPushes previousMoves)
    (tail : Trace soko1_2.board state dirs final pushes moves) (completed : Goal final)
    (frozen : List Cell) (unique : frozen.Nodup) (corners : frozen ⊆ dead12)
    (inside : frozen ⊆ state.boulders) : frozen.length ≤ 2 := by
  have persists : frozen ⊆ final.boulders := by
    intro cell member
    have check := List.all_eq_true.mp dead12_checked cell (corners member)
    have singleton := locked_of_check _ _ check
    have stays := locked_trace singleton tail (show [cell] ⊆ state.boulders by simpa using inside member)
    exact stays (by simp)
  have cardinality := List.Nodup.length_le_of_subset unique persists
  have prefixConserved := reached.conservation
  have suffixConserved := tail.conservation
  have empty : final.holes = [] := completed
  change 20 + state.holes.length = state.boulders.length + 18 at prefixConserved
  rw [empty] at suffixConserved
  simp only [List.length_nil] at suffixConserved
  omega

theorem pair11_left_locked : Locked soko1_1.board [266, 267] :=
  locked_of_check _ _ (by decide +kernel)

theorem pair11_right_locked : Locked soko1_1.board [267, 268] :=
  locked_of_check _ _ (by decide +kernel)

#print axioms square12_excluded
#print axioms dead317_persists
#print axioms dead12_budget
#print axioms pair11_left_locked
#print axioms pair11_right_locked
end Owner1007
