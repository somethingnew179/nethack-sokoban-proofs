import Owner1007.LeftDeadSplit11
namespace Owner1007.Left184Pocket11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Two manually prescribed current footprints; all other stones are arbitrary. -/
def locks (i : Fin 2) : List Cell := if i.val=0 then [184,187,212] else [184,186,212]
def region (i : Fin 2) : List Cell := LeftPair11.H.filter fun c=> !(
 (if i.val=0 then [183,184,185,186,187,209,210,211,212] else [183,184,185,186,209,210,211,212]:List Cell).contains c)
def paid (source : Cell) (dir : Dir) : Prop := (source=212∨source=186)∧dir=.west
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true := by decide +kernel
theorem floor (i : Fin 2) : region i⊆soko1_1.board.floor := by
 have checked : (List.finRange 2).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked i (by simp)) c member)
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem nonempty : ∀i,locks i≠[] := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨v,bound⟩:=i
 have cases:v=0∨v=1:=by omega
 rcases cases with rfl|rfl
 ·exact node0
 ·exact node1
#print axioms closed
end Owner1007.Left184Pocket11
