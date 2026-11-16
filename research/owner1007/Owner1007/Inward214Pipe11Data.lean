import Owner1007.LeftInwardPipe11Data
namespace Owner1007.Inward214Pipe11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def u (i : Fin 8) : Cell := if i.val<4 then 187 else 186
def phase (i : Fin 8) : Fin 4:=⟨i.val%4,Nat.mod_lt _ (by decide)⟩
def front (i : Fin 8) : Cell:=match (phase i).val with |0=>164|1=>190|2=>216|_=>215
def locks (i : Fin 8) : List Cell:=[u i,189,214,front i]
def region (i : Fin 8) : List Cell:=LeftInwardPipe11.region ⟨(phase i).val,by have b:=(phase i).isLt;omega⟩
def paid (source : Cell) (_dir : Dir) : Prop:=source=186∨source=187∨source=189∨source=214∨source=215
instance (source : Cell) (dir : Dir) : Decidable (paid source dir):=by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique : ∀i,(locks i).Nodup:=by decide +kernel
theorem nonempty : ∀i,locks i≠[]:=by decide +kernel
theorem floor (i : Fin 8) : region i⊆soko1_1.board.floor:=
 LeftInwardPipe11.floor ⟨(phase i).val,by have b:=(phase i).isLt;omega⟩
def headCheck (i : Fin 8) : Bool:=(locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→paid source dir→
  (phase i).val=3∨(source=189∧dir=.west))
theorem heads : (List.finRange 8).all headCheck=true:=by decide +kernel
#print axioms heads
end Owner1007.Inward214Pipe11
