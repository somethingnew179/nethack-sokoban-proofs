import Owner1007.AfterJ12CheckMatrix210
import Owner1007.AfterJ12CheckMatrix238
import Owner1007.AfterJ12CheckRingmatrix
namespace Owner1007.AfterJ12
open NetHack.Sokoban
theorem matrix (kind : Fin 2) : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes (locks kind) (region kind) (paid kind) = true := by
 obtain ⟨k,h⟩ := kind
 have choices : k=0 ∨ k=1 := by omega
 rcases choices with rfl|rfl
 · exact matrix210
 · exact matrix238
#print axioms matrix
end Owner1007.AfterJ12
