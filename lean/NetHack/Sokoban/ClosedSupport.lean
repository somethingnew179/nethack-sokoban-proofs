/- Closed floor supports are proved invariants, not smaller puzzle profiles. -/
import NetHack.Sokoban.Geometry
import NetHack.Sokoban.NonlinearFacts
set_option linter.unusedSimpArgs false
namespace NetHack.Sokoban.ClosedSupport

def Closed (board : Board) (cells : List Cell) : Prop :=
  ∀ current, current ∈ cells → ∀ direction next,
    advance board current direction = some next → next ∈ board.floor → next ∈ cells

def check (board : Board) (cells : List Cell) : Bool :=
  cells.all fun current => allDirs.all fun direction =>
    match advance board current direction with
    | none => true
    | some next => !board.floor.contains next || cells.contains next

theorem check_sound (board : Board) (cells : List Cell) (checked : check board cells = true) :
    Closed board cells := by
  intro current member direction next adjacent floor
  have row := List.all_eq_true.mp (List.all_eq_true.mp checked current member)
    direction (Geometry.all_directions direction)
  simpa only [adjacent, List.contains_iff_mem.mpr floor, Bool.not_true, Bool.false_or,
    List.contains_iff_mem] using row

theorem ray_closed (board : Board) (cells : List Cell) (closed : Closed board cells)
    (direction : Dir) (fuel current cell : Nat) (standing : current ∈ cells)
    (member : cell ∈ rayTargets board direction fuel current) : cell ∈ cells := by
  induction fuel generalizing current with
  | zero => simp [rayTargets] at member; simpa [member] using standing
  | succ fuel ih =>
    simp only [rayTargets, List.mem_cons] at member
    rcases member with same | later
    · simpa [same] using standing
    · cases adjacent : advance board current direction with
      | none => simp [adjacent] at later
      | some next =>
        by_cases door : next ∈ board.doors
        · simp [adjacent, door] at later
        · by_cases floor : next ∈ board.floor
          · simp [adjacent, door, floor] at later
            exact ih next (closed current standing direction next adjacent floor) later
          · simp [adjacent, door, floor] at later

theorem targets_closed (board : Board) (cells : List Cell) (closed : Closed board cells)
    (source : Cell) (direction : Dir) (standing : source ∈ cells) (cell : Cell)
    (member : cell ∈ pushTargets board source direction) : cell ∈ cells := by
  cases diagonal : direction.diagonal with
  | true => simp [pushTargets, diagonal] at member
  | false =>
    cases support : advance board source direction.opposite with
    | none => simp [pushTargets, diagonal, support] at member
    | some behind =>
      by_cases behindFloor : behind ∈ board.floor
      · by_cases behindDoor : behind ∈ board.doors
        · simp [pushTargets, diagonal, support, behindFloor, behindDoor] at member
        · cases adjacent : advance board source direction with
          | none => simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent] at member
          | some destination =>
            by_cases floor : destination ∈ board.floor
            · by_cases door : destination ∈ board.doors
              · simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent, floor, door] at member
              · by_cases rolling : destination ∈ board.rollingTraps
                · simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, rolling] at member
                  exact ray_closed board cells closed direction _ source cell standing member
                · simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, rolling] at member
                  subst cell
                  exact closed source standing direction destination adjacent floor
            · simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent, floor] at member
      · simp [pushTargets, diagonal, support, behindFloor] at member

def Within (cells : List Cell) (state : State) : Prop :=
  state.player ∈ cells ∧ state.boulders ⊆ cells
instance (cells : List Cell) (state : State) : Decidable (Within cells state) := by
  unfold Within; infer_instance

theorem step_within (board : Board) (cells : List Cell) (closed : Closed board cells)
    (state : State) (direction : Dir) (t : Transition) (within : Within cells state)
    (checked : step board state direction = some t) : Within cells t.state := by
  rcases step_cases_full _ _ _ _ checked with walk | pushed
  · rcases walk with ⟨target, adjacent, floor, _, _, shape⟩
    subst t
    exact ⟨closed state.player within.1 direction target adjacent floor, within.2⟩
  · rcases pushed with ⟨source, result, adjacent, floor, present, pushed, shape⟩
    have sourceWithin := closed state.player within.1 direction source adjacent floor
    have spec := pushBoulder_spec _ _ _ _ _ pushed
    have landing := targets_closed board cells closed source direction sourceWithin result.landing spec.2
    subst t
    refine ⟨sourceWithin, ?_⟩
    rcases spec.1 with stays | consumes
    · rw [stays.2]
      intro cell member
      rcases List.mem_cons.mp member with same | later
      · simpa only [same] using landing
      · exact within.2 (List.mem_of_mem_erase later)
    · rw [consumes.2.2]
      intro cell member
      exact within.2 (List.mem_of_mem_erase member)

theorem trace_within {board : Board} {cells : List Cell} (closed : Closed board cells)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) (within : Within cells initial) :
    Within cells final := by
  induction trace with
  | nil => exact within
  | cons head tail ih => exact ih (step_within _ _ closed _ _ _ within head)

/-- With a closed exact support and distinct boulders, projection has exactly
as many entries as the original boulder list, not merely an inequality. -/
theorem projection_length (cells boxes : List Cell) (cellsUnique : cells.Nodup)
    (boxesUnique : boxes.Nodup) (subset : boxes ⊆ cells) :
    (NonlinearFacts.occupied cells boxes).length = boxes.length := by
  apply Nat.le_antisymm (NonlinearFacts.occupied_length_le cells boxes cellsUnique)
  apply List.Nodup.length_le_of_subset boxesUnique
  intro cell member
  exact List.mem_filter.mpr ⟨subset member, List.contains_iff_mem.mpr member⟩
/-- Exact mass information needed to prohibit ghost-box creation in proposers.
This holds for every reached state of the original individual-move model. -/
theorem trace_projection_mass {board : Board} {cells : List Cell} {allowance : Nat}
    (closed : Closed board cells) (cellsUnique : cells.Nodup)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (initialWithin : Within cells initial) (initialUnique : initial.boulders.Nodup)
    (initialMass : initial.boulders.length = initial.holes.length + allowance)
    (trace : Trace board initial directions final pushes moves) :
    (NonlinearFacts.occupied cells final.boulders).length = final.holes.length + allowance := by
  have within := trace_within closed trace initialWithin
  have preserve {initial final : State} {directions : List Dir} {pushes moves : Nat}
      (trace : Trace board initial directions final pushes moves) :
      initial.boulders.Nodup → final.boulders.Nodup := by
    induction trace with
    | nil => exact id
    | cons head tail ih => intro unique; exact ih (step_boulders_nodup _ _ _ _ unique head)
  have unique := preserve trace initialUnique
  rw [projection_length cells final.boulders cellsUnique unique within.2]
  have conserved := trace.conservation
  omega

theorem trace_goal_projection {board : Board} {cells : List Cell} {allowance : Nat}
    (closed : Closed board cells) (cellsUnique : cells.Nodup)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (initialWithin : Within cells initial) (initialUnique : initial.boulders.Nodup)
    (initialMass : initial.boulders.length = initial.holes.length + allowance)
    (trace : Trace board initial directions final pushes moves) (completed : Goal final) :
    (NonlinearFacts.occupied cells final.boulders).length = allowance := by
  have mass := trace_projection_mass closed cellsUnique initialWithin initialUnique initialMass trace
  change final.holes = [] at completed
  simpa only [completed, List.length_nil, Nat.zero_add] using mass
end NetHack.Sokoban.ClosedSupport
