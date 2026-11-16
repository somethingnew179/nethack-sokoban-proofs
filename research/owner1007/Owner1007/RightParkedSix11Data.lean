import Owner1007.Inward191Eight11
import Owner1007.LeftQuietIdentity11
namespace Owner1007.RightParkedSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def u (i : Fin 4) : Cell:=if i.val%2=0 then 187 else 186
def marker (i : Fin 4) : Cell:=if i.val<2 then 213 else 214
def locks (i : Fin 4) : List Cell:=[137,139,184,u i,189,marker i]
def region (i : Fin 4) : List Cell:=
 PostCuts11.without (Inward191Eight11.upper++
 (if i.val<2 then (if i.val%2=0 then [188] else [187,188]) else [])++
 [190,191,192,193,194,214,215,216,217,218,219,220]) [137,139,marker i]
def paid (_ : Cell) (_ : Dir) : Prop:=True
instance (c : Cell) (d : Dir) : Decidable (paid c d):=by unfold paid;infer_instance
def Shape (i : Fin 4) (source : Cell) (dir : Dir) : Prop:=
 ((source=137∨source=139)∧(dir=.east∨dir=.west))∨
 (i.val=0∧source=187∧dir=.west)∨
 (i.val=1∧source=186∧dir=.west)∨
 (i.val<2∧source=189∧dir=.east)∨
 (source=189∧dir=.west)∨
 (i.val<2∧source=213∧dir=.west)∨
 (i.val=1∧source=213∧dir=.south)∨
 (2≤i.val∧source=214∧dir=.west)
instance (i : Fin 4) (c : Cell) (d : Dir) : Decidable (Shape i c d):=by unfold Shape;infer_instance
theorem unique : ∀i,(locks i).Nodup:=by decide +kernel
theorem size : ∀i,(locks i).length=6:=by decide +kernel
theorem nonempty : ∀i,locks i≠[]:=by decide +kernel
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true:=by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true:=by decide +kernel
theorem node2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 2=true:=by decide +kernel
theorem node3 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 3=true:=by decide +kernel
theorem floor (i : Fin 4) : region i⊆soko1_1.board.floor:=by
 have row : (List.finRange 4).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true:=by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c h)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid:=by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases:i=0∨i=1∨i=2∨i=3:=by omega
 rcases cases with rfl|rfl|rfl|rfl
 ·exact node0
 ·exact node1
 ·exact node2
 ·exact node3
theorem phase_closed (i : Fin 4) :
 PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes
  (fun _ : Fin 1=>locks i) (fun _ : Fin 1=>region i) paid:=by
 constructor
 ·intro j hero member dir target adjacent isFloor door notLock corner
  exact closed.1 i hero member dir target adjacent isFloor door notLock corner
 ·intro j hero member dir source owner adjacent
  exact Or.inr (Or.inl trivial)
def headCheck (i : Fin 4) : Bool:=(locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→Shape i source dir)
theorem heads : ∀i,headCheck i=true:=by decide +kernel
theorem head_shape {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (i : Fin 4) (hero : state.player∈region i) (physical : locks i⊆state.boulders)
 (member : source∈locks i) (checked : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source) :
 Shape i source dir:=by
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (heads i) source member) dir (Geometry.all_directions dir)
 have adjacent:=PairPost11.source_adjacent checked metadata
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source adjacent
 simp only [headCheck,behind] at row
 exact of_decide_eq_true row hero (WestRankHead11.source_unblocked checked metadata physical)
#print axioms closed
#print axioms head_shape
end Owner1007.RightParkedSix11
