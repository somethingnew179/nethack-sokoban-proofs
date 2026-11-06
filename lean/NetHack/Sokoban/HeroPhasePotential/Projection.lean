/- A single boulder is retained only to inspect the scalar weight attached to
that ACTUAL boulder. Removing other boulders preserves every admitted walk's
corner clearance. This is a proved relaxation of the same Model, not a new
Trace assumption, a new move rule, or a search-completeness axiom. -/
import NetHack.Sokoban.HazardPhaseCountedCorrection
import NetHack.Sokoban.Geometry

namespace NetHack.Sokoban.HeroPhasePotential
open NetHack.Sokoban.LowerBounds

def single (state : State) (boulder : Cell) : State :=
  { state with boulders := [boulder] }

theorem single_corner_clear (board : Board) (state : State) (boulder : Cell)
    (present : boulder ∈ state.boulders) (direction : Dir)
    (clear : cornerBlocked board state direction = false) :
    cornerBlocked board (single state boulder) direction = false := by
  have blocked_imp (cell : Cell)
      (h : blocked board (single state boulder) cell = true) :
      blocked board state cell = true := by
    change ((!board.floor.contains cell && !board.doors.contains cell) ||
      ([boulder] : List Cell).contains cell) = true at h
    rcases Bool.or_eq_true_iff.mp h with wall | box
    · exact Bool.or_eq_true_iff.mpr (Or.inl wall)
    · have same : cell = boulder := by simpa using box
      subst cell
      exact Bool.or_eq_true_iff.mpr (Or.inr (by simpa only [List.contains_iff_mem] using present))
  have side_imp (d : Dir)
      (h : (match advance board state.player d with
        | none => true | some cell => blocked board (single state boulder) cell) = true) :
      (match advance board state.player d with
        | none => true | some cell => blocked board state cell) = true := by
    cases adjacent : advance board state.player d with
    | none => rfl
    | some cell =>
      simp only [adjacent] at h
      exact blocked_imp cell h
  cases smaller : cornerBlocked board (single state boulder) direction with
  | false => rfl
  | true =>
    change (direction.diagonal &&
      (match advance board state.player direction.sides.1 with
        | none => true | some cell => blocked board (single state boulder) cell) &&
      (match advance board state.player direction.sides.2 with
        | none => true | some cell => blocked board (single state boulder) cell)) = true at smaller
    rcases Bool.and_eq_true_iff.mp smaller with ⟨left, second⟩
    rcases Bool.and_eq_true_iff.mp left with ⟨diagonal, first⟩
    have actual : cornerBlocked board state direction = true :=
      Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
        ⟨diagonal, side_imp _ first⟩, side_imp _ second⟩
    simp only [clear, Bool.false_eq_true] at actual

theorem weightSum_mono (cells : List Cell) (before after : Cell → Int)
    (pointwise : ∀ cell ∈ cells, before cell ≤ after cell) :
    weightSum before cells ≤ weightSum after cells := by
  induction cells with
  | nil => exact Int.le_refl _
  | cons head tail ih =>
    have first := pointwise head (List.mem_cons_self)
    have rest := ih (fun cell member => pointwise cell (List.mem_cons_of_mem _ member))
    simp only [weightSum_cons]
    omega

end NetHack.Sokoban.HeroPhasePotential
