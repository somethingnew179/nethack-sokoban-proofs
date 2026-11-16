import Owner1007.CageLedger12
import Owner1007.Vertical21223812
import Owner1007.TwoReserves12
namespace Owner1007.PreAccessFour12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev U := CageLedger12.Upper
def locks : Fin 3→List Cell
 |0=>[108,158,159,186,187,210,237,238,263,213]
 |1=>[108,158,159,186,187,210,237,238,264,213]
 |2=>[108,158,159,186,187,210,211,238,264,213]
def base : List Cell := [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,236,239,241,242,244,245,246,262,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
def region : Fin 3→List Cell |0=>base |1=>base.erase 264++[263] |2=>base.erase 264++[263,237]
def positive (source : Cell) (dir : Dir) : Prop :=
 (source=263∧dir=.west)∨(source=264∧(dir=.east∨dir=.west))∨(source=238∧(dir=.east∨dir=.west))
instance (source : Cell) (dir : Dir) : Decidable (positive source dir) := by unfold positive;infer_instance
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=210∧dir=.north)∨(source=211∧dir=.north)∨(source=213∧dir=.west)∨(source=238∧dir=.north)∨positive source dir
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem large : ∀ i,2<(locks i).length := by decide +kernel
theorem upper_inside : ∀ i,U⊆locks i := by decide +kernel
theorem hero371 : (371:Cell)∈region 0 := by decide +kernel
theorem foreign_shift : ∀ i,([108,158,159,186,187,184]:List Cell)⊆184::(locks i).erase 210 := by decide +kernel
theorem gate_shift : ∀ i,PriceTrap12Gate.locks 0⊆185::(locks i).erase 211 := by decide +kernel
theorem square_shift : ∀ i,([186,187,212,213]:List Cell)⊆212::(locks i).erase 238 := by decide +kernel
theorem pair_shift : ∀ i,([212,238]:List Cell)⊆212::(locks i).erase 213 := by decide +kernel
theorem gate_hero : (211:Cell)∈PriceTrap12Gate.region 0 := by decide +kernel
theorem pair_hero : (213:Cell)∈Vertical21223812.region 0 := by decide +kernel
theorem paid_outside {source dir} (h : paid source dir) : source∉U := by
 rcases h with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|h
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·decide +kernel
 ·rcases h with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;>decide +kernel
theorem positive_member {source dir} (h : positive source dir) : source∈([238,263,264]:List Cell) := by
 rcases h with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;>decide +kernel
theorem positive_price : ∀ source∈([238,263,264]:List Cell),∀ dir∈allDirs,positive source dir→
 ∀ dest∈pushTargets soko1_2.board source dir,dest∉soko1_2.initial.holes∧
 (2:Int)≤1+p.boulder dest-p.boulder source := by decide +kernel
theorem upper_bonus : ∀ hero∈([213,238,263,264]:List Cell),
 RightEnergy12.cert.bonus hero (NetHack.Sokoban.PatternCorrection.project U)=2 := by decide +kernel
#print axioms matrix
#print axioms upper_bonus
end Owner1007.PreAccessFour12
