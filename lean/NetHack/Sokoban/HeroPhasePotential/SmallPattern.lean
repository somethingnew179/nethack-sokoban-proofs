import NetHack.Sokoban.HeroPhasePotential.Core
namespace NetHack.Sokoban.HeroPhasePotential
open HazardPattern PatternCorrection
private def smallSide (board : Board) (p : Pattern) (hero : Cell) (d : Dir) : Bool :=
  match advance board hero d with
  | none => true
  | some c => (!board.floor.contains c && !board.doors.contains c) || p c

theorem corner_clear_mono (board : Board) (small large : Pattern)
    (subset : ∀ cell, small cell = true → large cell = true)
    (hero : Cell) (direction : Dir) (clear : corner board large hero direction = false) :
    corner board small hero direction = false := by
  have sideImp (d : Dir) (selected : smallSide board small hero d = true) :
      smallSide board large hero d = true := by
    cases adjacent : advance board hero d with
    | none => simp only [smallSide, adjacent]
    | some cell =>
      simp only [smallSide, adjacent] at selected ⊢
      rcases Bool.or_eq_true_iff.mp selected with wall | box
      · exact Bool.or_eq_true_iff.mpr (Or.inl wall)
      · exact Bool.or_eq_true_iff.mpr (Or.inr (subset cell box))
  cases smaller : corner board small hero direction with
  | false => rfl
  | true =>
    rcases Bool.and_eq_true_iff.mp smaller with ⟨left, second⟩
    rcases Bool.and_eq_true_iff.mp left with ⟨diagonal, first⟩
    have impossible : corner board large hero direction = true :=
      Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
        ⟨diagonal, sideImp _ first⟩, sideImp _ second⟩
    rw [clear] at impossible
    cases impossible
end NetHack.Sokoban.HeroPhasePotential
