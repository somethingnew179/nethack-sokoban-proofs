import Owner1007.RankedCorral11
import Owner1007.WestRankHead11
namespace Owner1007.RightEarlyWords11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def q (i : Fin 5) : Cell:=if i.val=0∨i.val=4 then 191 else 190
def r (i : Fin 5) : Cell:=match i.val with |0=>193 |1=>193 |2=>192 |3=>191 |_=>192
def locks (i : Fin 5) : List Cell:=[137,139,q i,r i]
def region (i : Fin 5) : List Cell:=PostCuts11.without
 (if i.val=0∨i.val=4 then PostCuts11.H else ZeroWord11.lowerTwo) (locks i)
def paid (source : Cell) (dir : Dir) : Prop:=
 source=137∨source=139∨(source=190∧(dir=.west∨dir=.north))∨
 (source=191∧dir=.east)∨(source=193∧dir=.east)
instance (c : Cell) (d : Dir) : Decidable (paid c d):=by unfold paid;infer_instance
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true:=by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true:=by decide +kernel
theorem node2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 2=true:=by decide +kernel
theorem node3 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 3=true:=by decide +kernel
theorem node4 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 4=true:=by decide +kernel
theorem floor (i : Fin 5) : region i⊆soko1_1.board.floor:=by
 have row : (List.finRange 5).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true:=by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c h)
theorem unique : ∀i,(locks i).Nodup:=by decide +kernel
theorem size : ∀i,(locks i).length=4:=by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid:=by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1∨i=2∨i=3∨i=4:=by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl
 ·exact node0
 ·exact node1
 ·exact node2
 ·exact node3
 ·exact node4

def marker (which : Bool) (i : Fin 5) : Cell:=if which then r i else q i
theorem markerInside : ∀which i,marker which i∈locks i:=by decide +kernel
def refinementCheck (which : Bool) (i : Fin 5) : Bool:=(locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>if hero∈region i then (List.finRange 5).all fun j=>
   (pushTargets soko1_1.board source dir).all fun dest=>decide
    (dir.diagonal=false→¬paid source dir→pushTargets soko1_1.board source dir=[dest]→
     dest∉soko1_1.initial.holes→locks j⊆dest::(locks i).erase source→source∈region j→
     update [marker which i] (.push source (.stay dest))=[marker which j])
   else true
theorem refinements : ∀which i,refinementCheck which i=true:=by decide +kernel
theorem refined (which : Bool) : RankedCorral11.Refinement locks region (marker which) (fun _=>0) paid:=by
 intro i hero source dest dir j heroInside sourceInside adjacent cardinal unpaid target targets noHole nextLocks nextHero
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (refinements which i) source sourceInside) dir (Geometry.all_directions dir)
 have reverse:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (floor i heroInside) dir source adjacent
 simp only [refinementCheck,reverse,if_pos heroInside] at row
 have numeric:=List.all_eq_true.mp (List.all_eq_true.mp row j (by simp)) dest target
 exact ⟨of_decide_eq_true numeric cardinal unpaid targets noHole nextLocks nextHero,Or.inl (show (0:Int)≤0 from Int.le_refl _)⟩

def Shape (i : Fin 5) (source : Cell) (dir : Dir) : Prop:=
 ((source=137∨source=139)∧i.val=0)∨
 (source=190∧dir=.west∧q i=190)∨
 (source=190∧dir=.north∧q i=190)∨
 (source=191∧dir=.east∧q i=191∧r i=193)∨
 (source=193∧dir=.east∧r i=193)∨i.val=4
instance (i : Fin 5) (c : Cell) (d : Dir) : Decidable (Shape i c d):=by unfold Shape;infer_instance
def headCheck (i : Fin 5) : Bool:=(locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→paid source dir→Shape i source dir)
theorem heads : ∀i,headCheck i=true:=by decide +kernel
theorem complete (i : Fin 5) (group : List Cell) (bounded : group.length≤4)
 (inside : locks i⊆group) (source : Cell) (owner : source∈group) : source∈locks i:=by
 by_cases member : source∈locks i
 ·exact member
 ·have all : source::locks i⊆group:=by
    intro c h
    rcases List.mem_cons.mp h with rfl|later
    ·exact owner
    ·exact inside later
  have card:=List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,unique i⟩) all
  simp only [List.length_cons,size i] at card
  omega
theorem head_shape {state : State} {dir : Dir} {t : Transition} {group : List Cell}
 (i : Fin 5) (hero : state.player∈region i) (selected : locks i⊆group)
 (inside : group⊆state.boulders) (bounded : group.length≤4)
 (checked : step soko1_1.board state dir=some t) (pays : OwnedCorral11.PaidStep paid group dir t) :
 ∃source,source∈group∧t.pushSource=some source∧Shape i source dir:=by
 obtain ⟨source,owner,metadata,pays⟩:=pays
 have member:=complete i group bounded selected source owner
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (heads i) source member) dir (Geometry.all_directions dir)
 have adjacent:=PairPost11.source_adjacent checked metadata
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source adjacent
 simp only [headCheck,behind] at row
 exact ⟨source,owner,metadata,of_decide_eq_true row hero (WestRankHead11.source_unblocked checked metadata (List.Subset.trans selected inside)) pays⟩
theorem initialHero : soko1_1.initial.player∈region 0:=by decide +kernel
theorem initialLocks : locks 0⊆soko1_1.initial.boulders:=by decide +kernel
#print axioms closed
#print axioms refined
#print axioms head_shape
end Owner1007.RightEarlyWords11

