import Owner1007.LeftFourLane11
import Owner1007.RankedCorral11
namespace Owner1007.LeftFourLane11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def refinementCheck (i : Fin 21) : Bool := (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>if hero∈region i then (List.finRange 21).all fun j=>
  (pushTargets soko1_1.board source dir).all fun dest=>decide
   (dir.diagonal=false→¬paid source dir→pushTargets soko1_1.board source dir=[dest]→
    dest∉soko1_1.initial.holes→locks j⊆dest::(locks i).erase source→source∈region j→
    update [left i] (.push source (.stay dest))=[left j])
  else true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem marker00 : refinementCheck 0=true := by decide +kernel
theorem marker01 : refinementCheck 1=true := by decide +kernel
theorem marker02 : refinementCheck 2=true := by decide +kernel
theorem marker03 : refinementCheck 3=true := by decide +kernel
theorem marker04 : refinementCheck 4=true := by decide +kernel
theorem marker05 : refinementCheck 5=true := by decide +kernel
theorem marker06 : refinementCheck 6=true := by decide +kernel
theorem marker07 : refinementCheck 7=true := by decide +kernel
theorem marker08 : refinementCheck 8=true := by decide +kernel
theorem marker09 : refinementCheck 9=true := by decide +kernel
theorem marker10 : refinementCheck 10=true := by decide +kernel
theorem marker11 : refinementCheck 11=true := by decide +kernel
theorem marker12 : refinementCheck 12=true := by decide +kernel
theorem marker13 : refinementCheck 13=true := by decide +kernel
theorem marker14 : refinementCheck 14=true := by decide +kernel
theorem marker15 : refinementCheck 15=true := by decide +kernel
theorem marker16 : refinementCheck 16=true := by decide +kernel
theorem marker17 : refinementCheck 17=true := by decide +kernel
theorem marker18 : refinementCheck 18=true := by decide +kernel
theorem marker19 : refinementCheck 19=true := by decide +kernel
theorem marker20 : refinementCheck 20=true := by decide +kernel
theorem refinements (i : Fin 21) : refinementCheck i=true := by
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6∨i=7∨i=8∨i=9∨i=10∨i=11∨i=12∨i=13∨i=14∨i=15∨i=16∨i=17∨i=18∨i=19∨i=20 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 ·exact marker00
 ·exact marker01
 ·exact marker02
 ·exact marker03
 ·exact marker04
 ·exact marker05
 ·exact marker06
 ·exact marker07
 ·exact marker08
 ·exact marker09
 ·exact marker10
 ·exact marker11
 ·exact marker12
 ·exact marker13
 ·exact marker14
 ·exact marker15
 ·exact marker16
 ·exact marker17
 ·exact marker18
 ·exact marker19
 ·exact marker20
theorem markerInside : ∀i,left i∈locks i := by intro i;simp [locks]
theorem size : ∀i,(locks i).length=2 := by intro i;rfl
theorem refined : RankedCorral11.Refinement locks region left (fun _=>0) paid := by
 intro i hero source dest dir j heroInside sourceInside adjacent cardinal unpaid target targets noHole nextLocks nextHero
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (refinements i) source sourceInside) dir (Geometry.all_directions dir)
 have reverse:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (floor i heroInside) dir source adjacent
 simp only [refinementCheck,reverse,if_pos heroInside] at row
 have numeric:=List.all_eq_true.mp (List.all_eq_true.mp row j (by simp)) dest target
 exact ⟨of_decide_eq_true numeric cardinal unpaid targets noHole nextLocks nextHero,Or.inl (show (0:Int)≤0 from Int.le_refl _)⟩
#print axioms refined
end Owner1007.LeftFourLane11
