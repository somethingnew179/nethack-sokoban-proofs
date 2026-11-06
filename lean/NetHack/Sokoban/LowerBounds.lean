/- Kernel-checked lower-bound arguments for the explicit Sokoban profile.
Searchers propose paths and potential tables; neither is trusted by these
theorems. A concrete potential must separately prove every admitted step's
inequality before the general trace bound can establish optimality. -/
import NetHack.Sokoban.Model

namespace NetHack.Sokoban
namespace LowerBounds

/-- One admitted player action fills at most one hazard and needs a push to
do so, even when the boulder rolls through several cells automatically. -/
theorem trace_holes_bound {board : Board} {initial : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) :
    initial.holes.length ≤ pushes + final.holes.length := by
  induction trace with
  | nil => simp
  | cons head tail ih =>
    have bound := step_holes_length _ _ _ _ head
    omega

theorem goal_holes_lower_bound {board : Board} {initial : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) (completed : Goal final) :
    initial.holes.length ≤ pushes := by
  have bound := trace_holes_bound trace
  unfold Goal at completed
  simpa [completed] using bound

theorem trace_pushes_le_moves {board : Board} {initial : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) : pushes ≤ moves := by
  induction trace with
  | nil => exact Nat.le_refl 0
  | @cons state direction next rest final pushes moves head tail ih =>
    have one : next.pushCost ≤ 1 := by
      unfold Transition.pushCost
      split <;> omega
    omega

theorem goal_holes_moves_lower_bound {board : Board} {initial : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) (completed : Goal final) :
    initial.holes.length ≤ moves :=
  Nat.le_trans (goal_holes_lower_bound trace completed) (trace_pushes_le_moves trace)

/-- Integer weights permit independently checked assignment-dual certificates.
No matching algorithm or external solver is part of this definition. -/
def weightSum (weight : Cell → Int) : List Cell → Int
  | [] => 0
  | cell :: cells => weight cell + weightSum weight cells

theorem weightSum_cons (weight : Cell → Int) (cell : Cell) (cells : List Cell) :
    weightSum weight (cell :: cells) = weight cell + weightSum weight cells := rfl

theorem weightSum_erase (weight : Cell → Int) (cells : List Cell) (cell : Cell)
    (member : cell ∈ cells) :
    weightSum weight cells = weight cell + weightSum weight (cells.erase cell) := by
  induction cells with
  | nil => simp at member
  | cons head tail ih =>
    by_cases same : head = cell
    · subst head
      simp [weightSum]
    · have later : cell ∈ tail := by simpa [same, Ne.symm same] using member
      have smaller := ih later
      simp [same, weightSum]
      omega

theorem weightSum_nonpositive (weight : Cell → Int) (cells : List Cell)
    (nonpositive : ∀ cell, weight cell ≤ 0) : weightSum weight cells ≤ 0 := by
  induction cells with
  | nil => exact Int.le_refl 0
  | cons head tail ih =>
    simp only [weightSum]
    have bound := nonpositive head
    omega

structure Potential where
  boulder : Cell → Int
  hole : Cell → Int

def Potential.value (potential : Potential) (state : State) : Int :=
  weightSum potential.boulder state.boulders + weightSum potential.hole state.holes

theorem Potential.goal_nonpositive (potential : Potential) (state : State)
    (nonpositive : ∀ cell, potential.boulder cell ≤ 0) (completed : Goal state) :
    potential.value state ≤ 0 := by
  have bound := weightSum_nonpositive potential.boulder state.boulders nonpositive
  unfold Goal at completed
  simpa only [Potential.value, completed, weightSum, Int.add_zero] using bound

/-- Replacing one boulder has at most one unit of potential decrease whenever
the proposed source-to-landing edge satisfies the checked static inequality. -/
theorem Potential.replace_bound (potential : Potential) (state : State)
    (source destination : Cell) (member : source ∈ state.boulders)
    (edge : potential.boulder source ≤ 1 + potential.boulder destination) :
    potential.value state ≤ 1 + potential.value
      {state with boulders := destination :: state.boulders.erase source} := by
  have erase := weightSum_erase potential.boulder state.boulders source member
  simp only [Potential.value, weightSum]
  omega

/-- A consumed boulder removes exactly one original hazard. A long automatic
roll still initiates just one push and needs the same endpoint inequality. -/
theorem Potential.consume_bound (potential : Potential) (state : State)
    (source destination : Cell) (boulderMember : source ∈ state.boulders)
    (holeMember : destination ∈ state.holes)
    (edge : potential.boulder source ≤ 1 + potential.boulder destination)
    (absorption : potential.boulder destination + potential.hole destination ≤ 0) :
    potential.value state ≤ 1 + potential.value
      {state with boulders := state.boulders.erase source, holes := state.holes.erase destination} := by
  have boxes := weightSum_erase potential.boulder state.boulders source boulderMember
  have holes := weightSum_erase potential.hole state.holes destination holeMember
  simp only [Potential.value]
  omega

/-- The required premise is a theorem about ALL admitted steps, not merely
the returned solution path or the states an external search happened to visit. -/
def StepBound (board : Board) (potential : State → Int) : Prop :=
  ∀ state direction transition,
    step board state direction = some transition →
    potential state ≤ Int.ofNat transition.pushCost + potential transition.state

/-- Universal obligations discharged by a finite concrete certificate checker.
Static relaxed endpoints include every actual landing, including long rolls. -/
structure Valid (board : Board) (potential : Potential) : Prop where
  nonpositive : ∀ cell, potential.boulder cell ≤ 0
  absorption : ∀ cell, potential.boulder cell + potential.hole cell ≤ 0
  edge : ∀ source ∈ board.floor, ∀ direction destination,
    destination ∈ pushTargets board source direction →
    potential.boulder source ≤ 1 + potential.boulder destination

theorem Valid.goalBound {board : Board} {potential : Potential}
    (valid : Valid board potential) : ∀ state, Goal state → potential.value state ≤ 0 :=
  fun state completed => potential.goal_nonpositive state valid.nonpositive completed

/-- The finite static inequalities cover every successful model action.
This proof uses the concrete roll/push specification; it does not assume an
external searcher's player-region compression or matching heuristic is sound. -/
theorem Valid.stepBound {board : Board} {potential : Potential}
    (valid : Valid board potential) : StepBound board potential.value := by
  intro state direction transition checked
  rcases step_cases_floor board state direction transition checked with walk | pushed
  · rcases walk with ⟨cost, boxes, holes⟩
    simp [Potential.value, Transition.pushCost, cost, boxes, holes]
  · rcases pushed with ⟨source, result, sourceFloor, member, pushed, cost, boxes, holes⟩
    have spec := pushBoulder_spec board state source direction result pushed
    have edge := valid.edge source sourceFloor direction result.landing spec.2
    rcases spec.1 with stays | consumes
    · rcases stays with ⟨filled, shape⟩
      have bound := potential.replace_bound state source result.landing member edge
      simpa [Potential.value, Transition.pushCost, cost, boxes, holes, filled, afterFill, shape] using bound
    · rcases consumes with ⟨filled, holeMember, shape⟩
      have bound := potential.consume_bound state source result.landing member holeMember edge
        (valid.absorption result.landing)
      simpa [Potential.value, Transition.pushCost, cost, boxes, holes, filled, afterFill, shape] using bound

theorem trace_bound {board : Board} {potential : State → Int}
    (localBound : StepBound board potential)
    {initial : State} {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) :
    potential initial ≤ Int.ofNat pushes + potential final := by
  induction trace with
  | nil => simp
  | cons head tail ih =>
    have bound := localBound _ _ _ head
    simp only [Int.ofNat_eq_natCast, Int.natCast_add] at bound ih ⊢
    omega

theorem goal_lower_bound {board : Board} {potential : State → Int}
    (localBound : StepBound board potential)
    (goalBound : ∀ state, Goal state → potential state ≤ 0)
    {initial : State} {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) (completed : Goal final) :
    potential initial ≤ Int.ofNat pushes := by
  have bound := trace_bound localBound trace
  have endpoint := goalBound final completed
  omega

/-- Matching a sound lower bound proves pushes-optimality against every
finite successful trace in the specified profile. This says nothing about
moves-optimality or actions excluded from that profile. -/
theorem pushes_minimal_of_potential {board : Board} {potential : State → Int}
    (localBound : StepBound board potential)
    (goalBound : ∀ state, Goal state → potential state ≤ 0)
    {initial : State} (cost : Nat) (attains : potential initial = Int.ofNat cost)
    {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) (completed : Goal final) :
    cost ≤ pushes := by
  have bound := goal_lower_bound localBound goalBound trace completed
  simp only [Int.ofNat_eq_natCast] at attains bound
  omega

end LowerBounds
end NetHack.Sokoban
