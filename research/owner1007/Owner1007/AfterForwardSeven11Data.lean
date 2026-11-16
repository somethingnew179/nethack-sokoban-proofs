import Owner1007.LeftTwoLaneForward11
import Owner1007.ForwardResetEight11
import Owner1007.UpperLocalPrice11
namespace Owner1007.AfterForwardSeven11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def words : List (Cell×Cell×Cell) :=
 [(185,187,189),(185,187,190),(185,188,190),(185,189,190),(186,188,190),(186,189,190),(187,189,190)]
def left (i : Fin 7) : Cell := (words.getD i.val (185,187,189)).1
def upper (i : Fin 7) : Cell := (words.getD i.val (185,187,189)).2.1
def right (i : Fin 7) : Cell := (words.getD i.val (185,187,189)).2.2
def locks (i : Fin 7) : List Cell := [137,139,left i,upper i,right i]
def region (i : Fin 7) : List Cell :=
 (if right i=190 then Row19019111.region 0++[191] else LeftPair11.H).filter fun c=>!(locks i).contains c
def paid (source : Cell) (dir : Dir) : Prop :=
 source=137∨source=139∨((source=185∨source=186∨source=187∨source=188)∧dir=.west)∨
 (source=190∧(dir=.north∨dir=.east))
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
def frozen (i : Fin 4) : List Cell :=
 if i.val=0 then [185,186] else if i.val=1 then [186,187] else if i.val=2 then [187,188] else [188,189]
def Shape (i : Fin 7) (source : Cell) (dir : Dir) (dest : Cell) : Prop :=
 paid source dir∨
 (∃j : Fin 7,(update (locks i) (.push source (.stay dest))).Perm (locks j) ∧
  update [left i] (.push source (.stay dest))=[left j]∧
  update [upper i] (.push source (.stay dest))=[upper j]∧
  update [right i] (.push source (.stay dest))=[right j]∧source∈region j)∨
 (∃k : Fin 4,frozen k⊆update (locks i) (.push source (.stay dest)))
instance (i : Fin 7) (source : Cell) (dir : Dir) (dest : Cell) : Decidable (Shape i source dir dest) := by unfold Shape;infer_instance
def shapeCheck (i : Fin 7) : Bool := (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>if hero∈region i then (pushTargets soko1_1.board source dir).all fun dest=>
   decide (dest∉soko1_1.initial.holes∧(BlockedPush soko1_1.board (locks i) source dir∨Shape i source dir dest))
  else true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem shapes : (List.finRange 7).all shapeCheck=true := by decide +kernel
theorem walks : (List.finRange 7).all (fun i=>allDirs.all (FastCorral11.walkPart soko1_1.board locks region i))=true := by decide +kernel
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem size : ∀i,(locks i).length=5 := by intro i;rfl
theorem floor (i : Fin 7) : region i⊆soko1_1.board.floor := by
 have row : (List.finRange 7).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c member)
theorem walk_closed : ∀i hero,hero∈region i→∀dir target,
 advance soko1_1.board hero dir=some target→target∈soko1_1.board.floor→target∉soko1_1.board.doors→target∉locks i→
 corner soko1_1.board (PatternCorrection.project (locks i)) hero dir=false→target∈region i := by
 intro i hero member dir target adjacent isFloor notDoor notLock clear
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp walks i (by simp)) dir (Geometry.all_directions dir)) hero member
 by_cases next : target∈region i
 ·exact next
 ·simp only [FastCorral11.walkCheck,adjacent,if_neg next] at row
  exact False.elim (of_decide_eq_true row ⟨isFloor,notDoor,notLock,clear⟩)
theorem shape (i : Fin 7) (hero source dest : Cell) (dir : Dir)
 (heroInside : hero∈region i) (owner : source∈locks i) (adjacent : advance soko1_1.board hero dir=some source)
 (target : dest∈pushTargets soko1_1.board source dir) :
 dest∉soko1_1.initial.holes∧(BlockedPush soko1_1.board (locks i) source dir∨Shape i source dir dest) := by
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp shapes i (by simp)) source owner) dir (Geometry.all_directions dir)
 have reverse:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (floor i heroInside) dir source adjacent
 simp only [shapeCheck,reverse,if_pos heroInside] at row
 exact of_decide_eq_true (List.all_eq_true.mp row dest target)
#print axioms shapes
#print axioms walks
end Owner1007.AfterForwardSeven11
