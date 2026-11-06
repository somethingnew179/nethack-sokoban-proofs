/- A finite exhaustive certificate for MOVES, using exact Model states.
Each layer covers every successor of the previous layer in all8directions.
All listed states are goal-free. A certificate with k layers excludes every
winning trace with fewer than k individual displacements. Lists may be
supersets and contain duplicates; no sorted-state/player-region quotient is
assumed in the proof. -/
import NetHack.Sokoban.Movement.API

namespace NetHack.Sokoban.Movement.Bounded

def noGoals (states : List State) : Bool := states.all (fun state => !goal state)

def successorsCovered (board : Board) (state : State) (next : List State) : Bool :=
  allDirs.all fun direction =>
    match step board state direction with
    | none => true
    | some transition => next.any fun candidate => decide (candidate = transition.state)

def covers (board : Board) (current next : List State) : Bool :=
  current.all fun state => successorsCovered board state next

def checkLayers (board : Board) : List (List State) → Bool
  | [] => true
  | [last] => noGoals last
  | current :: next :: rest => noGoals current && covers board current next && checkLayers board (next :: rest)

theorem allDirs_mem (direction : Dir) : direction ∈ allDirs := by
  cases direction <;> simp [allDirs, cardinalDirs]

theorem noGoals_sound (states : List State) (checked : noGoals states = true)
    (state : State) (member : state ∈ states) : ¬ Goal state := by
  intro completed
  have forbidden := List.all_eq_true.mp checked state member
  have reached := (goal_iff state).mpr completed
  simp [reached] at forbidden

theorem covers_sound (board : Board) (current next : List State)
    (checked : covers board current next = true) (state : State) (member : state ∈ current)
    (direction : Dir) (transition : Transition) (head : step board state direction = some transition) :
    transition.state ∈ next := by
  have source := List.all_eq_true.mp checked state member
  have edge := List.all_eq_true.mp source direction (allDirs_mem direction)
  rw [head] at edge
  rcases List.any_eq_true.mp edge with ⟨candidate, member, equal⟩
  have same := of_decide_eq_true equal
  simpa only [same] using member

theorem layers_bound (board : Board) (layers : List (List State)) :
    checkLayers board layers = true →
    ∀ initial ∈ layers.headD [], ∀ directions final pushes moves,
      Trace board initial directions final pushes moves → Goal final → layers.length ≤ moves := by
  induction layers with
  | nil =>
    intro checked initial member directions final pushes moves trace completed
    exact Nat.zero_le moves
  | cons current rest ih =>
    intro checked initial member directions final pushes moves trace completed
    cases rest with
    | nil =>
      have goalFree : noGoals current = true := by simpa only [checkLayers] using checked
      have initialMember : initial ∈ current := member
      cases trace with
      | nil state => exact False.elim (noGoals_sound current goalFree _ initialMember completed)
      | cons head tail => simp only [List.length_cons, List.length_nil]; omega
    | cons next more =>
      have checks : (noGoals current = true ∧ covers board current next = true) ∧
          checkLayers board (next :: more) = true := by
        simpa only [checkLayers, Bool.and_eq_true_iff] using checked
      have initialMember : initial ∈ current := member
      cases trace with
      | nil state => exact False.elim (noGoals_sound current checks.1.1 _ initialMember completed)
      | @cons state direction transition rest final pushes moves head tail =>
        have nextMember := covers_sound board current next checks.1.2 _ initialMember direction transition head
        have bound := ih checks.2 transition.state nextMember rest final pushes moves tail completed
        simp only [List.length_cons] at bound ⊢
        omega

end NetHack.Sokoban.Movement.Bounded
