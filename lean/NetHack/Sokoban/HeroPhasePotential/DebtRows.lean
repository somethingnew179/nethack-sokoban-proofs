/- Transparent data representation of nonpositive scalar weights. Every
literal row and every finite inequality still needs its own kernel proof.
No equivalence to an external PDB or assignment computation is assumed. -/
import NetHack.Sokoban.HeroPhasePotential.Finite
import NetHack.Sokoban.IndexedCertificateTable

namespace NetHack.Sokoban.HeroPhasePotential
open IndexedCertificateTable

def decodeDebt (bits word hero : Nat) : Int :=
  -Int.ofNat ((word / (2 ^ (bits * hero))) % (2 ^ bits))

def packedWeight (rows : Table Nat) (horizon stride bits phase hero box : Nat) : Int :=
  if phase < horizon then decodeDebt bits (get 0 rows (phase * stride + box)) hero else 0

theorem decodeDebt_zero (bits hero : Nat) : decodeDebt bits 0 hero = 0 := by
  simp [decodeDebt]

theorem packed_row (rows : Table Nat) (horizon stride bits phase box word : Nat)
    (active : phase < horizon) (code : get 0 rows (phase*stride+box) = word) :
    (fun hero => packedWeight rows horizon stride bits phase hero box) = decodeDebt bits word := by
  funext hero
  simp only [packedWeight, if_pos active, code]

theorem packed_terminal (rows : Table Nat) (horizon stride bits hero box : Nat) :
    packedWeight rows horizon stride bits horizon hero box = 0 := by
  simp only [packedWeight, Nat.lt_irrefl, ↓reduceIte]

end NetHack.Sokoban.HeroPhasePotential
