/- Closed numeric certificate: each field has an ordinary kernel-checked proof. -/
import NetHack.Sokoban41.RowBounds
import NetHack.Sokoban41.NumericGoal
import NetHack.Sokoban41.Optimality
namespace NetHack.Sokoban41.Numerics

def numericBounds : Optimality.NumericBounds := {
  walk_bounds := NetHack.Sokoban41.walk_bounds
  push_bounds := NetHack.Sokoban41.push_bounds
  consume_bounds := NetHack.Sokoban41.consume_bounds
  bonus_range := NetHack.Sokoban41.bonus_range
  goal_bound := NetHack.Sokoban41.goal_bound }

end NetHack.Sokoban41.Numerics
