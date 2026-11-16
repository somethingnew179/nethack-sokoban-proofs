import Owner1007.RankedCorral11
import Owner1007.LeftInwardPipe11
namespace Owner1007.LeftPre21411
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
def left (i : Fin 4) : Cell := if i.val%2=0 then 184 else 185
def front (i : Fin 4) : Cell := if i.val<2 then 212 else 213
def pair (i : Fin 4) : List Cell := [left i,front i]
def selected (i : Fin 4) : List Cell := pair i++[187,189]
def locks (i : Fin 4) : List Cell := [left i,187,189,front i]
def region (i : Fin 4) : List Cell := match i.val with
 |0=>[183,185,186,209,210,211]
 |1=>[183,184,209,210,211]
 |2=>[183,185,186,209,210,211,212]
 |_=>[183,184,186,209,210,211,212]
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=184∧dir=.west)∨(source=185∧dir=.east)∨source=187∨source=189∨(source=213∧dir=.east)
instance (c : Cell) (d : Dir) : Decidable (paid c d) := by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem size : ∀i,(locks i).length=4 := by intro i;rfl
theorem nonempty : ∀i,locks i≠[] := by decide +kernel
theorem selected_unique : ∀i,(selected i).Nodup := by decide +kernel
theorem selected_perm : ∀i,(selected i).Perm (locks i) := by decide +kernel
theorem pair_unique : ∀i,(pair i).Nodup := by decide +kernel
theorem pair_selected : ∀i,pair i⊆selected i := by decide +kernel
theorem floor (i : Fin 4) : region i⊆soko1_1.board.floor := by
 have all : (List.finRange 4).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c member)
theorem checked : ∀i,FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor checked
def Allowed (source : Cell) (dir : Dir) : Prop :=
 (source=184∧dir=.west)∨(source=185∧dir=.east)∨(source=187∧dir=.east)∨(source=213∧dir=.east)
instance (c : Cell) (d : Dir) : Decidable (Allowed c d) := by unfold Allowed;infer_instance
def headCheck (i : Fin 4) : Bool := (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→paid source dir→Allowed source dir)
theorem heads : ∀i,headCheck i=true := by decide +kernel
def refinementCheck (tag : Fin 4→Cell) (i : Fin 4) : Bool := (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>if hero∈region i then (List.finRange 4).all fun j=>
  (pushTargets soko1_1.board source dir).all fun dest=>decide
   (dir.diagonal=false→¬paid source dir→pushTargets soko1_1.board source dir=[dest]→
    dest∉soko1_1.initial.holes→locks j⊆dest::(locks i).erase source→source∈region j→
    update [tag i] (.push source (.stay dest))=[tag j])
  else true
theorem left_refinements : ∀i,refinementCheck left i=true := by decide +kernel
theorem front_refinements : ∀i,refinementCheck front i=true := by decide +kernel
theorem refined (tag : Fin 4→Cell) (rows : ∀i,refinementCheck tag i=true) :
 RankedCorral11.Refinement locks region tag (fun _=>0) paid := by
 intro i hero source dest dir j heroInside sourceInside adjacent cardinal unpaid target targets noHole nextLocks nextHero
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (rows i) source sourceInside) dir (Geometry.all_directions dir)
 have reverse:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (floor i heroInside) dir source adjacent
 simp only [refinementCheck,reverse,if_pos heroInside] at row
 have numeric:=List.all_eq_true.mp (List.all_eq_true.mp row j (by simp)) dest target
 exact ⟨of_decide_eq_true numeric cardinal unpaid targets noHole nextLocks nextHero,Or.inl (show (0:Int)≤0 from Int.le_refl _)⟩
#print axioms closed
#print axioms heads
#print axioms left_refinements
#print axioms front_refinements
end Owner1007.LeftPre21411
