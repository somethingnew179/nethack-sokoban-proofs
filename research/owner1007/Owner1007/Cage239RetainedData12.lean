import Owner1007.Cage23912
import Owner1007.Cage212Nine12
namespace Owner1007.Cage239RetainedNine12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def oldIndex (i:Fin 6) : Fin 10 := if h:i.val<4 then ⟨i.val,by omega⟩ else if i.val=4 then 8 else 9
def locks (i:Fin 6) : List Cell := Cage23912.locks (oldIndex i)
def region (i:Fin 6) : List Cell := Cage23912.region (oldIndex i)
def paid (source:Cell) (dir:Dir):Prop := Cage23912.paid source dir ∨ source=213
instance (source:Cell) (dir:Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
def matrixNode (i:Fin 6) : Bool :=
 (region i).all fun hero => allDirs.all fun dir =>
 Corral11.walkCheck soko1_2.board locks region i hero dir &&
 (locks i).all fun source=>decide (advance soko1_2.board hero dir≠some source ∨
 BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir ∨
 Corral11.Shift soko1_2.board soko1_2.initial.holes locks region i source dir)
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem size : ∀ i,i.val<4→(locks i).length=11 := by decide +kernel
theorem upperInside : ∀ i,CageLedger12.Upper⊆locks i := by decide +kernel
def priceSeven (source:Cell) (dir:Dir):Prop :=
 source∉CageLedger12.Upper ∧ ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧ (7:Int)≤1+Generated.soko1_2Potential.boulder dest-Generated.soko1_2Potential.boulder source
def classified (i:Fin 6) (source:Cell) (dir:Dir):Prop :=
 BlockedPush soko1_2.board (locks i) source dir ∨
 (source=213∧dir=.west) ∨
 Cage23912.gateEvent (oldIndex i) source dir ∨
 Cage23912.squareEvent (oldIndex i) source dir ∨ priceSeven source dir
instance (i:Fin 6) (source:Cell) (dir:Dir) : Decidable (classified i source dir) := by
 unfold classified Cage23912.gateEvent Cage23912.squareEvent Cage23912.squareDest priceSeven;infer_instance
def basic (i:Fin 4) : Fin 6 := ⟨i.val,by omega⟩
def classificationNode (i:Fin 4) : Bool :=
 (region (basic i)).all fun hero=>allDirs.all fun dir=>Cage23912.paidSources.all fun source=>
 decide (advance soko1_2.board hero dir=some source→paid source dir→classified (basic i) source dir)
theorem paid_sources (source:Cell) (dir:Dir) (pays:paid source dir):source∈Cage23912.paidSources := by
 rcases pays with old|rfl
 · exact Cage23912.paid_sources source dir old
 · decide +kernel
theorem pair : ∀ i,4≤i.val→([210,236]⊆locks i∨[184,210]⊆locks i) := by decide +kernel
def nextIndex (i:Fin 6) : Fin 4 := ⟨i.val%4,by omega⟩
theorem activation : ∀ i,i.val<4→Cage21212.locks (Cage212Nine12.normal (nextIndex i))⊆212::(locks i).erase 213 := by decide +kernel
theorem nextHero : ∀ i,i.val<4→(213:Cell)∈Cage21212.region (Cage212Nine12.normal (nextIndex i)) := by decide +kernel
theorem bonus : ∀ source∈Cage23912.paidSources,source∉CageLedger12.Upper→
 RightEnergy12.cert.bonus source (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by decide +kernel
theorem hero263 : (263:Cell)∈region 0 := by decide +kernel
end Owner1007.Cage239RetainedNine12
