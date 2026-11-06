/- All finite numeric premises are closed ordinary kernel proofs. -/
import NetHack.Sokoban21.RowBounds
import NetHack.Sokoban21.NumericGoal
import NetHack.Sokoban21.Optimality
namespace NetHack.Sokoban21.Numerics

def numericBounds : Optimality.NumericBounds := {
  walk_bounds := NetHack.Sokoban21.walk_bounds
  push_bounds := NetHack.Sokoban21.push_bounds
  consume_bounds := NetHack.Sokoban21.consume_bounds
  bonus_range := NetHack.Sokoban21.bonus_range
  goal_bound := NetHack.Sokoban21.goal_bound }

end NetHack.Sokoban21.Numerics
