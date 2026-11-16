import Owner1007.Gate265Transport11Data
import Owner1007.Shaft18711Data
import Owner1007.FastCorral11
namespace Owner1007.Front26511
open NetHack.Sokoban
def locks (i : Fin 3) : List Cell := match i.val with |0=>[265]|1=>[239]|2=>[213]|_=>[]
def region (i : Fin 3) : List Cell := match i.val with
 |0=>Gate265Transport11.lower
 |1=>265::Gate265Transport11.lower
 |2=>239::265::Gate265Transport11.lower
 |_=>[]
def paid := Shaft18711.paid
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique (i : Fin 3) : (locks i).Nodup := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1∨i=2 := by omega
 rcases choices with rfl|rfl|rfl <;> dsimp only [locks] <;> decide +kernel
theorem size (i : Fin 3) : (locks i).length=1 := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1∨i=2 := by omega
 rcases choices with rfl|rfl|rfl <;> rfl
theorem floor (i : Fin 3) : region i⊆soko1_1.board.floor := by
 have all : (List.finRange 3).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c member)
def growthCheck (i : Fin 3) (source : Cell) (dir : Dir) : Bool :=
 (pushTargets soko1_1.board source dir).all fun dest=>(List.finRange 3).all fun j=>
   if locks j⊆dest::(locks i).erase source then
     (region j).all (fun c=>decide (c∈region i++locks i))
   else true
theorem growing_checked : (List.finRange 3).all (fun i=>(locks i).all (fun source=>allDirs.all (growthCheck i source)))=true := by decide +kernel
theorem growth : ∀i source dir j dest,source∈locks i→dest∈pushTargets soko1_1.board source dir→
 locks j⊆dest::(locks i).erase source→region j⊆region i++locks i := by
 intro i source dir j dest sourceMember target nextLocks c member
 have a := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp growing_checked i (by simp)) source sourceMember) dir (Geometry.all_directions dir)
 have b := List.all_eq_true.mp (List.all_eq_true.mp a dest target) j (by simp)
 simp only [if_pos nextLocks] at b
 exact of_decide_eq_true (List.all_eq_true.mp b c member)
end Owner1007.Front26511
