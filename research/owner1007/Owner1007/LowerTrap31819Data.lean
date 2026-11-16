import Owner1007.LowerTrap31911Data
namespace Owner1007.LowerTrap31819
open NetHack.Sokoban
def locks (i : Fin 2) : List Cell := if i.val=0 then [266,268,293,318,321] else [266,268,293,319,321]
def region (i : Fin 2) : List Cell := if i.val=0 then (LowerTrap31911.region 0).filter (fun c=>c≠318) else LowerTrap31911.region 0
abbrev paid := LowerTrap31911.paid
theorem unique (i : Fin 2) : (locks i).Nodup := by unfold locks;split <;> decide +kernel
theorem size (i : Fin 2) : (locks i).length=5 := by unfold locks;split <;> rfl
theorem floor (i : Fin 2) : region i⊆soko1_1.board.floor := by
 intro c member
 unfold region at member
 split at member
 · exact LowerTrap31911.floor 0 (List.mem_filter.mp member).1
 · exact LowerTrap31911.floor 0 member
end Owner1007.LowerTrap31819
