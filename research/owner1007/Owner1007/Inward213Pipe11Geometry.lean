import Owner1007.Inward213Pipe11Check00
import Owner1007.Inward213Pipe11Check01
import Owner1007.Inward213Pipe11Check02
import Owner1007.Inward213Pipe11Check03
import Owner1007.Inward213Pipe11Check04
import Owner1007.Inward213Pipe11Check05
import Owner1007.Inward213Pipe11Check06
import Owner1007.Inward213Pipe11Check07
import Owner1007.Inward213Pipe11Check08
import Owner1007.Inward213Pipe11Check09
namespace Owner1007.Inward213Pipe11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem checked (i : Fin 10) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true:=by
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6∨i=7∨i=8∨i=9:=by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 ·exact node0
 ·exact node1
 ·exact node2
 ·exact node3
 ·exact node4
 ·exact node5
 ·exact node6
 ·exact node7
 ·exact node8
 ·exact node9
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid:=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor checked
#print axioms closed
end Owner1007.Inward213Pipe11
