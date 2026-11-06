/- Separate costs for the exact individual-displacement semantics.
These definitions do not assign walking cost to an abstract push edge and do
not identify profile moves with full NetHack game turns. -/
import NetHack.Sokoban.LowerBounds

namespace NetHack.Sokoban.Movement

structure Cost where
  pushes : Nat
  moves : Nat
  deriving Repr, DecidableEq, BEq

/-- Both costs belong to the SAME winning individual-move trace. -/
def Achievable (board : Board) (initial : State) (cost : Cost) : Prop :=
  ∃ directions final, Trace board initial directions final cost.pushes cost.moves ∧ Goal final

def Solvable (board : Board) (initial : State) : Prop := ∃ cost, Achievable board initial cost

def ComponentwiseLe (first second : Cost) : Prop :=
  first.pushes ≤ second.pushes ∧ first.moves ≤ second.moves

def StrictlyDominates (first second : Cost) : Prop :=
  ComponentwiseLe first second ∧ (first.pushes < second.pushes ∨ first.moves < second.moves)

def Incomparable (first second : Cost) : Prop :=
  ¬ ComponentwiseLe first second ∧ ¬ ComponentwiseLe second first

def PushLexLe (first second : Cost) : Prop :=
  first.pushes < second.pushes ∨ (first.pushes = second.pushes ∧ first.moves ≤ second.moves)

def MoveLexLe (first second : Cost) : Prop :=
  first.moves < second.moves ∨ (first.moves = second.moves ∧ first.pushes ≤ second.pushes)

def PushesOptimal (board : Board) (initial : State) (cost : Cost) : Prop :=
  Achievable board initial cost ∧ ∀ other, Achievable board initial other → cost.pushes ≤ other.pushes

def MovesOptimal (board : Board) (initial : State) (cost : Cost) : Prop :=
  Achievable board initial cost ∧ ∀ other, Achievable board initial other → cost.moves ≤ other.moves

def PushLexOptimal (board : Board) (initial : State) (cost : Cost) : Prop :=
  Achievable board initial cost ∧ ∀ other, Achievable board initial other → PushLexLe cost other

def MoveLexOptimal (board : Board) (initial : State) (cost : Cost) : Prop :=
  Achievable board initial cost ∧ ∀ other, Achievable board initial other → MoveLexLe cost other

def ParetoOptimal (board : Board) (initial : State) (cost : Cost) : Prop :=
  Achievable board initial cost ∧ ∀ other, Achievable board initial other → ¬ StrictlyDominates other cost

theorem pushLex_iff (board : Board) (initial : State) (cost : Cost) :
    PushLexOptimal board initial cost ↔ PushesOptimal board initial cost ∧
      (∀ other, Achievable board initial other → other.pushes = cost.pushes → cost.moves ≤ other.moves) := by
  constructor
  · rintro ⟨achieved, lower⟩
    refine ⟨⟨achieved, ?_⟩, ?_⟩
    · intro other winning
      have lex := lower other winning
      rcases lex with smaller | ⟨same, _⟩ <;> omega
    · intro other winning same
      have lex := lower other winning
      rcases lex with smaller | ⟨_, moves⟩ <;> omega
  · rintro ⟨⟨achieved, lower⟩, ties⟩
    refine ⟨achieved, ?_⟩
    intro other winning
    have bound := lower other winning
    by_cases same : other.pushes = cost.pushes
    · exact Or.inr ⟨same.symm, ties other winning same⟩
    · exact Or.inl (by omega)

theorem moveLex_iff (board : Board) (initial : State) (cost : Cost) :
    MoveLexOptimal board initial cost ↔ MovesOptimal board initial cost ∧
      (∀ other, Achievable board initial other → other.moves = cost.moves → cost.pushes ≤ other.pushes) := by
  constructor
  · rintro ⟨achieved, lower⟩
    refine ⟨⟨achieved, ?_⟩, ?_⟩
    · intro other winning
      have lex := lower other winning
      rcases lex with smaller | ⟨same, _⟩ <;> omega
    · intro other winning same
      have lex := lower other winning
      rcases lex with smaller | ⟨_, pushes⟩ <;> omega
  · rintro ⟨⟨achieved, lower⟩, ties⟩
    refine ⟨achieved, ?_⟩
    intro other winning
    have bound := lower other winning
    by_cases same : other.moves = cost.moves
    · exact Or.inr ⟨same.symm, ties other winning same⟩
    · exact Or.inl (by omega)

/-- Elementary least-natural existence, so no extra library or minimum axiom
is needed. Classical choice is used only to name the existing minimum. -/
theorem least_exists (predicate : Nat → Prop) (existsValue : ∃ value, predicate value) :
    ∃ value, predicate value ∧ ∀ other, predicate other → value ≤ other := by
  classical
  have bounded : ∀ bound, (∃ value, value ≤ bound ∧ predicate value) →
      ∃ value, predicate value ∧ ∀ other, predicate other → value ≤ other := by
    intro bound
    induction bound with
    | zero =>
      rintro ⟨value, upper, holds⟩
      have same : value = 0 := by omega
      exact ⟨value, holds, fun _ _ => by omega⟩
    | succ bound ih =>
      intro witness
      by_cases earlier : ∃ value, value ≤ bound ∧ predicate value
      · exact ih earlier
      · rcases witness with ⟨value, upper, holds⟩
        have same : value = bound + 1 := by
          by_cases same : value = bound + 1
          · exact same
          · exact False.elim (earlier ⟨value, by omega, holds⟩)
        refine ⟨value, holds, ?_⟩
        intro other otherHolds
        by_cases ordered : value ≤ other
        · exact ordered
        · exact False.elim (earlier ⟨other, by omega, otherHolds⟩)
  rcases existsValue with ⟨value, holds⟩
  exact bounded value ⟨value, Nat.le_refl _, holds⟩

private theorem moves_exist {board : Board} {initial : State} (solvable : Solvable board initial) :
    ∃ moves, ∃ pushes, Achievable board initial ⟨pushes,moves⟩ := by
  rcases solvable with ⟨⟨pushes,moves⟩, achieved⟩
  exact ⟨moves, pushes, achieved⟩

/-- The solvability argument excludes an ambiguous default on unsolvable
states. This number is a mathematical specification, not a search algorithm. -/
noncomputable def minimumMoves (board : Board) (initial : State) (solvable : Solvable board initial) : Nat :=
  Classical.choose (least_exists (fun moves => ∃ pushes, Achievable board initial ⟨pushes,moves⟩)
    (moves_exist solvable))

theorem minimumMoves_attained {board : Board} {initial : State} (solvable : Solvable board initial) :
    ∃ pushes, Achievable board initial ⟨pushes, minimumMoves board initial solvable⟩ :=
  (Classical.choose_spec (least_exists _ (moves_exist solvable))).1

theorem minimumMoves_le {board : Board} {initial : State} (solvable : Solvable board initial)
    (cost : Cost) (achieved : Achievable board initial cost) :
    minimumMoves board initial solvable ≤ cost.moves :=
  (Classical.choose_spec (least_exists _ (moves_exist solvable))).2 cost.moves ⟨cost.pushes, achieved⟩

theorem minimumMoves_lower_iff {board : Board} {initial : State} (solvable : Solvable board initial)
    (bound : Nat) : bound ≤ minimumMoves board initial solvable ↔
      ∀ cost, Achievable board initial cost → bound ≤ cost.moves := by
  constructor
  · intro lower cost achieved
    exact Nat.le_trans lower (minimumMoves_le solvable cost achieved)
  · intro lower
    rcases minimumMoves_attained solvable with ⟨pushes, achieved⟩
    exact lower ⟨pushes, minimumMoves board initial solvable⟩ achieved

theorem movesOptimal_iff_minimum {board : Board} {initial : State} (solvable : Solvable board initial)
    (cost : Cost) : MovesOptimal board initial cost ↔
      Achievable board initial cost ∧ cost.moves = minimumMoves board initial solvable := by
  constructor
  · rintro ⟨achieved, lower⟩
    refine ⟨achieved, Nat.le_antisymm ?_ (minimumMoves_le solvable cost achieved)⟩
    rcases minimumMoves_attained solvable with ⟨pushes, attained⟩
    exact lower ⟨pushes, minimumMoves board initial solvable⟩ attained
  · rintro ⟨achieved, exactMinimum⟩
    exact ⟨achieved, fun other winning => exactMinimum ▸ minimumMoves_le solvable other winning⟩

end NetHack.Sokoban.Movement
