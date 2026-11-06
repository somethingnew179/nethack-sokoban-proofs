/- Literal pair-table reader, not a PDB correctness theorem. -/
import NetHack.Soko11Hero315.Verified
import NetHack.Sokoban.GhostProjection
import NetHack.Sokoban.StatePermutation
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
set_option maxRecDepth 100000
set_option maxHeartbeats 0
inductive Table where
  | empty
  | node (key word : Nat) (left right : Table)
def lookup : Table → Nat → Nat
  | .empty, _ => 0
  | .node k w left right, q => if q = k then w else if q < k then lookup left q else lookup right q
-- A symmetric executable index. No injectivity assumption is used in a proof.
def codeWeight (cell : Cell) : Int := Int.ofNat (cell + 1024*cell*cell)
def code (group : List Cell) : Nat := (weightSum codeWeight group).toNat
end NetHack.Soko11PairCandidate321
