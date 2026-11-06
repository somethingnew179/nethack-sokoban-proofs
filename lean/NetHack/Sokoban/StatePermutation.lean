/- List order is representation only. This module proves a simulation of the
unchanged Model, including rolling, consumption, diagonal corners and goals.
It does not identify different hero cells or identify pushes with moves. -/
import NetHack.Sokoban.LowerBounds

set_option linter.unusedSimpArgs false
namespace NetHack.Sokoban.StatePermutation

structure Equivalent (a b : State) : Prop where
  player : a.player = b.player
  boulders : a.boulders.Perm b.boulders
  holes : a.holes.Perm b.holes

theorem Equivalent.refl (s : State) : Equivalent s s := ⟨rfl, .rfl, .rfl⟩
theorem Equivalent.symm {a b : State} (h : Equivalent a b) : Equivalent b a :=
  ⟨h.player.symm, h.boulders.symm, h.holes.symm⟩
theorem Equivalent.trans {a b c : State} (h : Equivalent a b) (k : Equivalent b c) :
    Equivalent a c := ⟨h.player.trans k.player, h.boulders.trans k.boulders, h.holes.trans k.holes⟩

structure PushEquivalent (a b : PushResult) : Prop where
  boulders : a.boulders.Perm b.boulders
  filled : a.filled = b.filled
  landing : a.landing = b.landing

structure TransitionEquivalent (a b : Transition) : Prop where
  state : Equivalent a.state b.state
  pushed : a.pushed = b.pushed
  filled : a.filled = b.filled
  pushSource : a.pushSource = b.pushSource
  landing : a.landing = b.landing

theorem roll_permutation (board : Board) (a b h k : List Cell)
    (boxes : a.Perm b) (holes : h.Perm k) (direction : Dir) (fuel current : Nat) :
    Option.Rel PushEquivalent (roll board a h direction fuel current)
      (roll board b k direction fuel current) := by
  induction fuel generalizing current with
  | zero => exact .none
  | succ fuel ih =>
    simp only [bind, pure, roll, boxes.contains_eq, holes.contains_eq]
    split
    · exact .some ⟨boxes.cons _, rfl, rfl⟩
    · split
      · exact .none
      · split
        · exact .some ⟨boxes.cons _, rfl, rfl⟩
        · split
          · exact .none
          · split
            · exact .some ⟨boxes, rfl, rfl⟩
            · exact ih _

theorem push_permutation (board : Board) {a b : State} (h : Equivalent a b)
    (source : Cell) (direction : Dir) :
    Option.Rel PushEquivalent (pushBoulder board a source direction)
      (pushBoulder board b source direction) := by
  cases diagonal : direction.diagonal with
  | true => simp only [bind, pure, pushBoulder, diagonal, ↓reduceIte, Option.bind_none]; exact .none
  | false =>
    cases behind : advance board source direction.opposite with
    | none => simp only [bind, pure, pushBoulder, diagonal, Bool.false_eq_true, ↓reduceIte, Option.bind_some, behind, Option.bind_none]; exact .none
    | some cell =>
      simp only [bind, pure, pushBoulder, diagonal, Bool.false_eq_true, ↓reduceIte, Option.bind_some, behind,
        h.boulders.contains_eq, h.holes.contains_eq]
      split
      · simp only [bind, pure, Option.bind_none]; exact .none
      · try simp only [bind, pure, Option.bind_some]
        cases destination : advance board source direction with
        | none => simp only [bind, pure, destination, Option.bind_none]; exact .none
        | some first =>
          simp only [bind, pure, destination, Option.bind_some]
          split
          · simp only [bind, pure, Option.bind_none]; exact .none
          · try simp only [bind, pure, Option.bind_some]
            split
            · exact .some ⟨h.boulders.erase source, rfl, rfl⟩
            · split
              · exact roll_permutation board _ _ _ _ (h.boulders.erase source) h.holes _ _ _
              · exact .some ⟨(h.boulders.erase source).cons _, rfl, rfl⟩

private def rawCorner (board : Board) (s : State) (d : Dir) : Bool :=
  d.diagonal &&
    (match advance board s.player d.sides.1 with | none => true | some c => blocked board s c) &&
    (match advance board s.player d.sides.2 with | none => true | some c => blocked board s c)

theorem corner_permutation (board : Board) {a b : State} (h : Equivalent a b) (d : Dir) :
    cornerBlocked board a d = cornerBlocked board b d := by
  change rawCorner board a d = rawCorner board b d
  simp only [bind, pure, rawCorner, h.player, blocked, h.boulders.contains_eq]

private def rawStep (board : Board) (s : State) (d : Dir) : Option Transition := do
  if !standingAllowed board s then none else pure ()
  if goal s then none else pure ()
  let target ← advance board s.player d
  if !board.floor.contains target || board.doors.contains target || cornerBlocked board s d then
    none else pure ()
  if s.boulders.contains target then
    let p ← pushBoulder board s target d
    return {state := {player := target, boulders := p.boulders, holes := afterFill s.holes p.filled}, pushed := true, filled := p.filled, pushSource := some target, landing := some p.landing}
  else
    if s.holes.contains target then none
    else return {state := {s with player := target}, pushed := false, filled := none}

theorem step_permutation (board : Board) {a b : State} (h : Equivalent a b) (d : Dir) :
    Option.Rel TransitionEquivalent (step board a d) (step board b d) := by
  change Option.Rel TransitionEquivalent (rawStep board a d) (rawStep board b d)
  have standing : standingAllowed board a = standingAllowed board b := by
    simp only [bind, pure, standingAllowed, h.player, h.boulders.contains_eq, h.holes.contains_eq]
  have finished : goal a = goal b := h.holes.isEmpty_eq
  simp only [bind, pure, rawStep, standing, finished, h.player, corner_permutation board h d,
    h.boulders.contains_eq, h.holes.contains_eq]
  split
  · exact .none
  · try simp only [bind, pure, Option.bind_some]
    split
    · exact .none
    · try simp only [bind, pure, Option.bind_some]
      cases adjacent : advance board b.player d with
      | none => simp only [adjacent, Option.bind_none]; exact .none
      | some target =>
        simp only [adjacent, Option.bind_some]
        split
        · simp only [Option.bind_none]; exact .none
        · try simp only [Option.bind_some]
          split
          · have pushed := push_permutation board h target d
            generalize left : pushBoulder board a target d = px at pushed ⊢
            generalize right : pushBoulder board b target d = py at pushed ⊢
            cases pushed with
            | none => exact .none
            | @some x y hp =>
              simp only [Option.bind_some]
              apply Option.Rel.some
              refine ⟨⟨rfl, hp.boulders, ?_⟩, rfl, hp.filled, rfl, ?_⟩
              · rw [hp.filled]
                cases y.filled <;> simp only [afterFill]
                · exact h.holes
                · exact h.holes.erase _
              · simp only [hp.landing]
          · split
            · exact .none
            · exact .some ⟨⟨rfl, h.boulders, h.holes⟩, rfl, rfl, rfl, rfl⟩

theorem step_transport (board : Board) {a b : State} (h : Equivalent a b) (d : Dir)
    {t : Transition} (checked : step board a d = some t) :
    ∃ u, step board b d = some u ∧ TransitionEquivalent t u := by
  have related := step_permutation board h d
  rw [checked] at related
  cases candidate : step board b d with
  | none => rw [candidate] at related; cases related
  | some u =>
    rw [candidate] at related
    cases related with
    | some proof => exact ⟨u, rfl, proof⟩

theorem goal_permutation {a b : State} (h : Equivalent a b) : Goal a ↔ Goal b := by
  constructor
  · intro done
    exact h.holes.symm.trans (done ▸ List.Perm.rfl) |>.eq_nil
  · intro done
    exact h.holes.trans (done ▸ List.Perm.rfl) |>.eq_nil

theorem weightSum_permutation (w : Cell → Int) {a b : List Cell} (h : a.Perm b) :
    LowerBounds.weightSum w a = LowerBounds.weightSum w b := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [bind, pure, LowerBounds.weightSum, ih]
  | swap => simp only [bind, pure, LowerBounds.weightSum]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Reordering the representation preserves the full direction sequence and
both costs. This is not a player-region or push/move-cost quotient. -/
theorem trace_transport {board : Board} {a final : State} {directions : List Dir}
    {pushes moves : Nat} (trace : Trace board a directions final pushes moves)
    {b : State} (related : Equivalent a b) :
    ∃ other, Trace board b directions other pushes moves ∧ Equivalent final other := by
  induction trace generalizing b with
  | nil state => exact ⟨b, Trace.nil b, related⟩
  | @cons state direction next rest final pushes moves head tail ih =>
    rcases step_transport board related direction head with ⟨other, first, paired⟩
    rcases ih paired.state with ⟨last, trace, pairedLast⟩
    have costs : next.pushCost = other.pushCost := by
      simp only [Transition.pushCost, paired.pushed]
    exact ⟨last, costs ▸ Trace.cons first trace, pairedLast⟩

end NetHack.Sokoban.StatePermutation
