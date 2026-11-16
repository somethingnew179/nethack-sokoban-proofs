import Owner1007.Upper187Cover11
import Owner1007.PairPost11
import Owner1007.WestRankHead11
namespace Owner1007.Q190Upper11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def coverIndex (i : Fin 3) : Fin 36 := ⟨8+i.val,by omega⟩
def u (i : Fin 3) : Cell := 187+i.val
def locks (i : Fin 3) : List Cell := [137,139,u i,190]
def region (i : Fin 3) : List Cell := Upper187Cover11.region (coverIndex i)
def paid (source : Cell) (dir : Dir) : Prop :=
 source=137∨source=139∨source=190∨((source=187∨source=188)∧dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true := by decide +kernel
theorem node2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 2=true := by decide +kernel
theorem floor (i : Fin 3) : region i⊆soko1_1.board.floor := Upper187Cover11.floors (coverIndex i)
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem size : ∀i,(locks i).length=4 := by intro i;rfl
theorem nonempty : ∀i,locks i≠[] := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1∨i=2 := by omega
 rcases cases with rfl|rfl|rfl
 ·exact node0
 ·exact node1
 ·exact node2
def Shape (source : Cell) (dir : Dir) : Prop :=
 ((source=187∨source=188)∧dir=.west)∨(source=190∧(dir=.north∨dir=.east∨dir=.west))
instance (source : Cell) (dir : Dir) : Decidable (Shape source dir) := by unfold Shape;infer_instance
def headCheck (i : Fin 3) : Bool := (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→paid source dir→Shape source dir)
theorem heads : (List.finRange 3).all headCheck=true := by decide +kernel
theorem complete (i : Fin 3) (group : List Cell) (bounded : group.length≤4)
 (selected : locks i⊆group) (source : Cell) (owner : source∈group) : source∈locks i := by
 by_cases member : source∈locks i
 ·exact member
 ·have all : source::locks i⊆group := by intro c h;rcases List.mem_cons.mp h with rfl|later;exact owner;exact selected later
  have card:=List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,unique i⟩) all
  simp only [List.length_cons,size i] at card
  omega
theorem head_shape {state : State} {dir : Dir} {t : Transition} {group : List Cell}
 (i : Fin 3) (hero : state.player∈region i) (selected : locks i⊆group)
 (inside : group⊆state.boulders) (bounded : group.length≤4)
 (head : step soko1_1.board state dir=some t) (pays : OwnedCorral11.PaidStep paid group dir t) :
 ∃source,source∈group∧t.pushSource=some source∧Shape source dir := by
 obtain ⟨source,owner,metadata,pays⟩:=pays
 have member:=complete i group bounded selected source owner
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp heads i (by simp)) source member) dir (Geometry.all_directions dir)
 have adjacent:=PairPost11.source_adjacent head metadata
 have reverse:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source adjacent
 simp only [headCheck,reverse] at row
 exact ⟨source,owner,metadata,of_decide_eq_true row hero
  (WestRankHead11.source_unblocked head metadata (List.Subset.trans selected inside)) pays⟩
#print axioms closed
#print axioms head_shape
end Owner1007.Q190Upper11
