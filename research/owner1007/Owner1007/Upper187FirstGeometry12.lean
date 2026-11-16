import Owner1007.UpperAfter187Bound12
import Owner1007.OwnedEvents12
namespace Owner1007.Upper187FirstGeometry12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def oldIndex (i : Fin 6) : Fin 11 := ⟨i.val,by omega⟩
def locks (i : Fin 6) : List Cell := (UpperAfter18712.locks (oldIndex i)).map (fun c=>if c=161 then 187 else c)
def region (i : Fin 6) : List Cell := (UpperAfter18712.region (oldIndex i)).erase 187
def paid (source : Cell) (dir : Dir) : Prop :=
 source∈([108,159,160,133,187] : List Cell) ∨
 (source=132∧dir≠.east) ∨ (source=158∧dir≠.north) ∨ (source=186∧dir≠.north)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem size : ∀ i,(locks i).length=5 := by decide +kernel
def priceTwo (source : Cell) (dir : Dir) : Prop :=
 ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧ (2:Int)≤1+p.boulder dest-p.boulder source
instance (source : Cell) (dir : Dir) : Decidable (priceTwo source dir) := by unfold priceTwo;infer_instance
def ticketIndex (i : Fin 6) (source : Cell) (dir : Dir) : Fin 11 :=
 if source=159 then
   if dir=.north then (if i.val=0∨i.val=2 then 6 else 7) else 8
 else 9
def ticketDest (source : Cell) (dir : Dir) : Cell := if source=159 then (if dir=.north then 133 else 160) else 134
def ticket (i : Fin 6) (source : Cell) (dir : Dir) : Prop :=
 ((source=159∧(dir=.north∨dir=.east)) ∨ (source=160∧dir=.north) ∨ (source=133∧dir=.east)) ∧
 pushTargets soko1_2.board source dir=[ticketDest source dir] ∧ticketDest source dir∉soko1_2.initial.holes ∧
 UpperAfter18712.locks (ticketIndex i source dir)⊆ticketDest source dir::(locks i).erase source ∧
 source∈UpperAfter18712.region (ticketIndex i source dir)
instance (i : Fin 6) (source : Cell) (dir : Dir) : Decidable (ticket i source dir) := by
 unfold ticket
 infer_instance
def classified (i : Fin 6) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (locks i) source dir ∨
 (source=187∧dir=.north) ∨priceTwo source dir∨ticket i source dir
instance (i : Fin 6) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by unfold classified;infer_instance
theorem classification : ∀ i,∀ hero∈region i,∀ dir∈allDirs,∀ source∈locks i,
 advance soko1_2.board hero dir=some source→paid source dir→classified i source dir := by decide +kernel
theorem ticket_credit (i : Fin 6) (source : Cell) (dir : Dir) : UpperAfter18712.credit (ticketIndex i source dir)=2 := by
 by_cases a : source=159 <;> by_cases b : dir=.north <;> by_cases c : i.val=0∨i.val=2 <;>
   simp only [ticketIndex,a,b,c,if_pos,if_neg] <;> decide +kernel
theorem ticket_no187 (i : Fin 6) (source : Cell) (dir : Dir) : (187:Cell)∉UpperAfter18712.locks (ticketIndex i source dir) := by
 by_cases a : source=159 <;> by_cases b : dir=.north <;> by_cases c : i.val=0∨i.val=2 <;>
   simp only [ticketIndex,a,b,c,if_pos,if_neg] <;> decide +kernel
theorem north_shift : ∀ i,UpperAfter18712.locks (oldIndex i)⊆161::(locks i).erase 187 := by decide +kernel
theorem north_hero : ∀ i,(187:Cell)∈UpperAfter18712.region (oldIndex i) := by decide +kernel
#print axioms matrix
#print axioms classification
end Owner1007.Upper187FirstGeometry12
