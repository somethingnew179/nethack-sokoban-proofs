import Owner1007.PricedCorral11
import NetHack.Sokoban.Reduction

namespace Owner1007.EastCorral12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open Owner1007.Corral11 Owner1007.PricedCorral11
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def positions : Fin 6 → Cell
  | 0 => 372 | 1 => 373 | 2 => 374 | 3 => 348 | 4 => 322 | 5 => 296
def locks (i : Fin 6) : List Cell := [positions i,192,193,218]
def base : List Cell :=
  [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,
   102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,163,164,180,184,
   185,186,187,189,190,191,206,210,211,212,213,214,215,216,232,236,237,238,239,
   241,242,258,262,263,264,265,284,288,289,290,291,292,293,294,310,317,318,319,
   320,336,345,370,371,396,397]
def region (i : Fin 6) : List Cell :=
  base ++ match i.val with
  | 0 => []
  | 1 => [372]
  | 2 => [372,373,399,400]
  | 3 => [372,373,374,399,400]
  | 4 => [348,372,373,374,399,400]
  | _ => [322,348,372,373,374,399,400]
def paid (source : Cell) (dir : Dir) : Prop := source = 296 ∧ dir = .north
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by
  unfold paid
  infer_instance

theorem geometry : checkExcept soko1_2.board soko1_2.initial.holes locks region paid = true := by
  decide +kernel
theorem closed : ClosedExcept soko1_2.board soko1_2.initial.holes locks region paid :=
  closed_of_checkExcept _ _ _ _ _ geometry
theorem unique : ∀ i : Fin 6, (locks i).Nodup := by decide +kernel
theorem sizes : ∀ i : Fin 6, (locks i).length = 4 := by decide +kernel

/-- From this east-entry cut, completing requires pushing296 north to270. -/
theorem completing_contains_last {state final : State} {history dirs : List Dir}
    {past pastMoves future futureMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (tail : Trace soko1_2.board state dirs final future futureMoves) (completed : Goal final)
    (good : Good locks region state) :
    PaidTrace soko1_2.board paid state dirs final future futureMoves := by
  rcases event_or_good closed unique tail good reached.holes_sublist.subset with found | finalGood
  · exact found
  · obtain ⟨i, _, inside⟩ := finalGood
    have card := List.Nodup.length_le_of_subset (unique i) inside
    rw [sizes] at card
    have conserved := (reached.append tail).conservation
    have empty : final.holes = [] := completed
    change 20 + final.holes.length = final.boulders.length + 18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega

#print axioms completing_contains_last
end Owner1007.EastCorral12
