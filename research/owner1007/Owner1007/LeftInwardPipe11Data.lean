import Owner1007.Inward191Eight11
import Owner1007.LeftGate21311
namespace Owner1007.LeftInwardPipe11
open NetHack.Sokoban
def front (i : Fin 6) : Cell := match i.val with |0=>164|1=>190|2=>216|3=>215|4=>214|_=>213
def locks (i : Fin 6) : List Cell := if i.val=5 then [185,187,213] else [185,187,189,front i]
def region (i : Fin 6) : List Cell := match i.val with
 |0=>PostCuts11.without Inward191Eight11.upper [164]
 |1=>Inward191Eight11.upper
 |2=>Inward191Eight11.upper++[190,191,192,193,194,217,218,219,220]
 |3=>Inward191Eight11.upper++[190,191,192,193,194,217,218,219,220,216]
 |4=>Inward191Eight11.upper++[190,191,192,193,194,217,218,219,220,216,215]
 |_=>LeftGate21311.region 0
def paid (source : Cell) (_dir : Dir) : Prop := source=185∨source=187∨source=189∨source=213
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem nonempty : ∀i,locks i≠[] := by decide +kernel
theorem floor (i : Fin 6) : region i⊆soko1_1.board.floor := by
 have row : (List.finRange 6).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c member)
def headCheck (i : Fin 6) : Bool := ([185,187,189,213]:List Cell).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→paid source dir→i.val=5∨(source=189∧dir=.west))
theorem heads : ∀i,headCheck i=true := by decide +kernel
theorem terminal : locks (5:Fin 6)=[185,187,213] := rfl
theorem hero138 : (138:Cell)∈region 0 := by decide +kernel
#print axioms heads
end Owner1007.LeftInwardPipe11
