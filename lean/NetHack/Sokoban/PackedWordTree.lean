/- An alternate representation of existing packed-word lookup code.
The page payloads, offsets, widths, moduli and branch cuts are unchanged.
No certificate validity is assumed: concrete clients must prove equality
with their original getter, before using any checked result semantically. -/
import Init

namespace NetHack.Sokoban.PackedWordTree

inductive Tree where
  | page (offset width modulus payload : Nat)
  | fork (cut : Nat) (left right : Tree)

def get : Tree → Nat → Nat
  | .page offset width modulus payload, index =>
    (payload / (2 ^ ((index - offset) * width))) % modulus
  | .fork cut left right, index =>
    if index < cut then get left index else get right index

end NetHack.Sokoban.PackedWordTree
