import Owner1007.LeftInwardPipe11Data
namespace Owner1007.LeftInwardStart11
open NetHack.Sokoban
def other (i : Fin 2) : Cell := if i.val=0 then 139 else 137
def locks (i : Fin 2) : List Cell := [other i,138,185,187,189]
def region (i : Fin 2) : List Cell := PostCuts11.without Inward191Eight11.upper [other i,138,164]
def paid (source : Cell) (_dir : Dir) : Prop := source=137∨source=138∨source=139
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
def Shape (source : Cell) (dir : Dir) : Prop := (source=138∧dir=.south)∨(source=137∧dir=.west)∨(source=139∧dir=.east)
instance (source : Cell) (dir : Dir) : Decidable (Shape source dir) := by unfold Shape;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem nonempty : ∀i,locks i≠[] := by decide +kernel
theorem floor (i : Fin 2) : region i⊆soko1_1.board.floor := by
 have row : (List.finRange 2).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c member)
def moveCheck (i : Fin 2) : Bool := (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→paid source dir)
theorem moves : ∀i,moveCheck i=true := by decide +kernel
def headCheck (i : Fin 2) : Bool := ([137,138,139]:List Cell).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→paid source dir→Shape source dir)
theorem heads : ∀i,headCheck i=true := by decide +kernel
#print axioms moves
#print axioms heads
end Owner1007.LeftInwardStart11
