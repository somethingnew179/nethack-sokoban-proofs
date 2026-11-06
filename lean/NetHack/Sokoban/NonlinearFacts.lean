/- Generic list/mass facts for independently checked occupancy-pattern
certificates. Actual boulder lists may contain duplicates in these lemmas;
the projected support list is required to have distinct cells. No search
result or finite numeric pattern table is assumed here. -/
import NetHack.Sokoban.LowerBounds
import Init.Data.List.Perm

namespace NetHack.Sokoban.NonlinearFacts

open LowerBounds

def surplus (state : State) : Int :=
  Int.ofNat state.boulders.length - Int.ofNat state.holes.length

def massPenaltyWith (allowance : Nat) (state : State) : Int :=
  max 0 (surplus state - Int.ofNat allowance)

def massPenalty (state : State) : Int := massPenaltyWith 2 state

theorem step_surplus (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (checked : step board state direction = some transition) :
    surplus state = surplus transition.state := by
  have conserved := step_conservation board state direction transition checked
  unfold surplus
  simp only [Int.ofNat_eq_natCast]
  omega

theorem trace_surplus {board : Board} {initial : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) :
    surplus initial = surplus final := by
  have conserved := trace.conservation
  unfold surplus
  simp only [Int.ofNat_eq_natCast]
  omega

theorem step_massPenaltyWith (allowance : Nat) (board : Board) (state : State)
    (direction : Dir) (transition : Transition)
    (checked : step board state direction = some transition) :
    massPenaltyWith allowance state = massPenaltyWith allowance transition.state := by
  unfold massPenaltyWith
  rw [step_surplus board state direction transition checked]

theorem step_massPenalty (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (checked : step board state direction = some transition) :
    massPenalty state = massPenalty transition.state :=
  step_massPenaltyWith 2 board state direction transition checked

theorem trace_massPenalty {board : Board} {initial : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) :
    massPenalty initial = massPenalty final := by
  unfold massPenalty massPenaltyWith
  rw [trace_surplus trace]

/-- Projecting onto distinct support cells counts occupied positions once,
even if an arbitrary input boulder list contains repetitions. -/
def occupied (support boxes : List Cell) : List Cell :=
  support.filter (fun cell => boxes.contains cell)

theorem occupied_subset (support boxes : List Cell) : occupied support boxes ⊆ boxes := by
  intro cell member
  have facts := List.mem_filter.mp member
  simpa using facts.2

theorem occupied_nodup (support boxes : List Cell) (unique : support.Nodup) :
    (occupied support boxes).Nodup :=
  List.Nodup.sublist List.filter_sublist unique

theorem occupied_length_le (support boxes : List Cell) (unique : support.Nodup) :
    (occupied support boxes).length ≤ boxes.length :=
  List.Nodup.length_le_of_subset (occupied_nodup support boxes unique) (occupied_subset support boxes)

/-- Four distinct occupied locations require at least four boulders, without
assuming the entire boulder list is canonical or duplicate-free. -/
theorem four_occupied_length (a b c d : Cell) (boxes : List Cell)
    (distinct : [a, b, c, d].Nodup)
    (present : a ∈ boxes ∧ b ∈ boxes ∧ c ∈ boxes ∧ d ∈ boxes) :
    4 ≤ boxes.length := by
  have subset : [a, b, c, d] ⊆ boxes := by
    intro cell member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact present.1
    · exact present.2.1
    · exact present.2.2.1
    · exact present.2.2.2
  exact List.Nodup.length_le_of_subset distinct subset

theorem weightSum_nonnegative (weight : Cell → Int) (cells : List Cell)
    (nonnegative : ∀ cell, 0 ≤ weight cell) : 0 ≤ weightSum weight cells := by
  induction cells with
  | nil => exact Int.le_refl 0
  | cons head tail ih =>
    have bound := nonnegative head
    simp only [weightSum]
    omega

/-- Distinct selected entries of a nonnegative weighted list have no larger
sum. Extra duplicates in the full list only increase its available weight. -/
theorem weightSum_le_of_nodup_subset (weight : Cell → Int) (selected boxes : List Cell)
    (nonnegative : ∀ cell, 0 ≤ weight cell)
    (unique : selected.Nodup) (subset : selected ⊆ boxes) :
    weightSum weight selected ≤ weightSum weight boxes := by
  induction selected generalizing boxes with
  | nil => exact weightSum_nonnegative weight boxes nonnegative
  | cons head tail ih =>
    have present : head ∈ boxes := subset (by simp)
    have uniqueTail := List.nodup_cons.mp unique
    have tailSubset : tail ⊆ boxes.erase head := by
      intro cell member
      have different : cell ≠ head := by
        intro same
        subst cell
        exact uniqueTail.1 member
      exact (List.mem_erase_of_ne different).mpr (subset (by simp [member]))
    have smaller := ih (boxes.erase head) uniqueTail.2 tailSubset
    have erased := LowerBounds.weightSum_erase weight boxes head present
    simp only [weightSum]
    omega

theorem occupied_weightSum_le (weight : Cell → Int) (support boxes : List Cell)
    (nonnegative : ∀ cell, 0 ≤ weight cell) (unique : support.Nodup) :
    weightSum weight (occupied support boxes) ≤ weightSum weight boxes :=
  weightSum_le_of_nodup_subset weight (occupied support boxes) boxes nonnegative
    (occupied_nodup support boxes unique) (occupied_subset support boxes)

theorem roll_landing_clear (board : Board) (stationary holes : List Cell) (direction : Dir)
    (fuel current : Nat) (result : PushResult) (fresh : current ∉ stationary)
    (checked : roll board stationary holes direction fuel current = some result) :
    result.landing ∉ stationary := by
  induction fuel generalizing current result with
  | zero => simp [roll] at checked
  | succ fuel ih =>
    cases adjacent : advance board current direction with
    | none =>
      simp [roll, adjacent] at checked
      subst result
      exact fresh
    | some next =>
      by_cases door : next ∈ board.doors
      · simp [roll, adjacent, door] at checked
      · by_cases floor : next ∈ board.floor
        · by_cases collision : next ∈ stationary
          · simp [roll, adjacent, door, floor, collision] at checked
          · by_cases hazard : next ∈ holes
            · simp [roll, adjacent, door, floor, collision, hazard] at checked
              subst result
              exact collision
            · simp [roll, adjacent, door, floor, collision, hazard] at checked
              exact ih next result collision checked
        · simp [roll, adjacent, door, floor] at checked
          subst result
          exact fresh

/-- The first destination is clear in the actual input list, not merely in
an abstract projected pattern. This holds even for lists with duplicates. -/
theorem pushBoulder_first_clear (board : Board) (state : State) (source : Cell)
    (direction : Dir) (result : PushResult)
    (checked : pushBoulder board state source direction = some result) :
    ∃ destination, advance board source direction = some destination ∧
      destination ∈ board.floor ∧ destination ∉ board.doors ∧ destination ∉ state.boulders := by
  cases diagonal : direction.diagonal with
  | true => simp [pushBoulder, diagonal] at checked
  | false =>
    cases support : advance board source direction.opposite with
    | none => simp [pushBoulder, diagonal, support] at checked
    | some behind =>
      cases adjacent : advance board source direction with
      | none => simp [pushBoulder, diagonal, support, adjacent] at checked
      | some destination =>
        refine ⟨destination, rfl, ?_, ?_, ?_⟩
        · by_cases standing : destination ∈ board.floor
          · exact standing
          · simp [pushBoulder, diagonal, support, adjacent, standing] at checked
        · intro blocked
          simp [pushBoulder, diagonal, support, adjacent, blocked] at checked
        · intro blocked
          simp [pushBoulder, diagonal, support, adjacent, blocked] at checked

/-- The surviving or consuming landing cell is disjoint from every stationary
boulder after erasing exactly the pushed occurrence. No Nodup premise is used. -/
theorem pushBoulder_landing_clear (board : Board) (state : State) (source : Cell)
    (direction : Dir) (result : PushResult)
    (checked : pushBoulder board state source direction = some result) :
    result.landing ∉ state.boulders.erase source := by
  rcases pushBoulder_first_clear board state source direction result checked with
    ⟨destination, adjacent, floor, door, clear⟩
  have clearRemaining : destination ∉ state.boulders.erase source :=
    fun member => clear (List.mem_of_mem_erase member)
  cases diagonal : direction.diagonal with
  | true => simp [pushBoulder, diagonal] at checked
  | false =>
    cases support : advance board source direction.opposite with
    | none => simp [pushBoulder, diagonal, support] at checked
    | some behind =>
      by_cases hazard : destination ∈ state.holes
      · simp [pushBoulder, diagonal, support, adjacent, floor, door, clear, hazard] at checked
        have resultEq := checked.2
        subst result
        exact clearRemaining
      · by_cases rolling : destination ∈ board.rollingTraps
        · simp [pushBoulder, diagonal, support, adjacent, floor, door, clear, hazard, rolling] at checked
          have rolled := checked.2
          simp [roll, adjacent, floor, door, clearRemaining, hazard] at rolled
          exact roll_landing_clear board (state.boulders.erase source) state.holes direction
            (board.width * board.height) destination result clearRemaining rolled
        · simp [pushBoulder, diagonal, support, adjacent, floor, door, clear, hazard, rolling] at checked
          have resultEq := checked.2
          subst result
          exact clearRemaining

theorem pushBoulder_landing_old_clear_or_source (board : Board) (state : State) (source : Cell)
    (direction : Dir) (result : PushResult)
    (checked : pushBoulder board state source direction = some result) :
    result.landing = source ∨ result.landing ∉ state.boulders := by
  by_cases same : result.landing = source
  · exact Or.inl same
  · apply Or.inr
    intro member
    have remained := (List.mem_erase_of_ne same).mpr member
    exact pushBoulder_landing_clear board state source direction result checked remained

end NetHack.Sokoban.NonlinearFacts
