import Owner1007.CentralFirst11Checks
namespace Owner1007.CentralFirst11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem geometry_checked0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact w0
   | south => exact w1
   | east => exact w2
   | west => exact w3
   | northEast => exact w4
   | northWest => exact w5
   | southEast => exact w6
   | southWest => exact w7
 · exact p
theorem geometry_checked (i : Fin 1) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by
 have same : i=0 := Fin.ext (by have bound:=i.isLt; omega)
 simpa only [same] using geometry_checked0
theorem geometry_floor : ∀ i, region i⊆soko1_1.board.floor := by
 intro i c member
 have all : (region 0).all (fun c=>decide (c∈soko1_1.board.floor))=true := by decide +kernel
 exact of_decide_eq_true (List.all_eq_true.mp all c member)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked geometry_floor geometry_checked
#print axioms geometry_checked
#print axioms closed
end Owner1007.CentralFirst11
