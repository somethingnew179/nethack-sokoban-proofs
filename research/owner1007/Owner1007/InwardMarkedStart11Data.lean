import Owner1007.LeftInwardStart11
namespace Owner1007.InwardMarkedStart11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def gate (i : Fin 8) : Fin 2:=⟨i.val%2,Nat.mod_lt _ (by decide)⟩
def other (i : Fin 8) : Cell:=LeftInwardStart11.other (gate i)
def u (i : Fin 8) : Cell:=if i.val%4<2 then 187 else 186
def marker (i : Fin 8) : Cell:=if i.val<4 then 213 else 214
def locks (i : Fin 8) : List Cell:=[other i,138,u i,189,marker i]
def region (i : Fin 8) : List Cell:=LeftInwardStart11.region (gate i)
def paid (_source : Cell) (_dir : Dir) : Prop:=True
instance (source : Cell) (dir : Dir) : Decidable (paid source dir):=by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique : ∀i,(locks i).Nodup:=by decide +kernel
theorem nonempty : ∀i,locks i≠[]:=by decide +kernel
theorem floor (i : Fin 8) : region i⊆soko1_1.board.floor:=LeftInwardStart11.floor (gate i)
def headCheck (i : Fin 8) : Bool:=(locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→LeftInwardStart11.Shape source dir)
theorem heads : (List.finRange 8).all headCheck=true:=by decide +kernel
#print axioms heads
end Owner1007.InwardMarkedStart11
