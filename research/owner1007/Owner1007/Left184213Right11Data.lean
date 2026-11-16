import Owner1007.LeftGate21311
import Owner1007.Left184Pocket11
namespace Owner1007.Left184213Right11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def u (i : Fin 2) : Cell := if i.val=0 then 187 else 186
def locks (i : Fin 2) : List Cell := [184,u i,189,213]
def region (i : Fin 2) : List Cell := LeftPair11.H.filter fun c=>
 decide (c<239∨15≤c%26) && !((if i.val=0 then [183,184,185,186,187,189,209,210,211,212,213] else [183,184,185,186,189,209,210,211,212,213]:List Cell).contains c)
def paid (source : Cell) (dir : Dir) : Prop :=
 source=184∨source=186∨source=189∨source=213∨(source=187∧dir≠.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir):=by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true:=by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true:=by decide +kernel
theorem floor (i : Fin 2) : region i⊆soko1_1.board.floor:=by
 have all : (List.finRange 2).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true:=by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c h)
theorem unique : ∀i,(locks i).Nodup:=by decide +kernel
theorem size : ∀i,(locks i).length=4:=by intro i;rfl
theorem nonempty : ∀i,locks i≠[]:=by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid:=by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1:=by omega
 rcases cases with rfl|rfl
 ·exact node0
 ·exact node1
def Shape (source : Cell) (dir : Dir) : Prop :=
 (source=186∧dir=.west)∨(source=189∧(dir=.east∨dir=.west))∨(source=213∧(dir=.south∨dir=.west))
instance (source : Cell) (dir : Dir) : Decidable (Shape source dir):=by unfold Shape;infer_instance
def headCheck (i : Fin 2) : Bool:=(locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→paid source dir→Shape source dir)
theorem heads : (List.finRange 2).all headCheck=true:=by decide +kernel
theorem head_shape {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (i : Fin 2) (hero : state.player∈region i) (member : source∈locks i) (inside : locks i⊆state.boulders)
 (checked : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source) (pays : paid source dir) :
 Shape source dir:=by
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp heads i (by simp)) source member) dir (Geometry.all_directions dir)
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source (PairPost11.source_adjacent checked metadata)
 simp only [headCheck,behind] at row
 exact of_decide_eq_true row hero (WestRankHead11.source_unblocked checked metadata inside) pays
#print axioms closed
#print axioms head_shape
end Owner1007.Left184213Right11
