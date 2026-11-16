import Owner1007.Post187Seven12
import Owner1007.Post18712
import Owner1007.Cage23912
import Owner1007.RingUpperBound12
namespace Owner1007.Post187SevenMap12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def postIndex (i : Fin 10) : Fin 11 :=
 if i.val<8 then ⟨i.val%4,by omega⟩ else if i.val=8 then 7 else 5
theorem post_inside : ∀ i, Post187Seven12.locks (postIndex i)⊆Post18712.locks i := by decide +kernel
theorem post_region : ∀ i, Post18712.region i⊆Post187Seven12.region (postIndex i) := by decide +kernel
theorem post_credit : ∀ i, Post187Seven12.credit (postIndex i)=7 := by decide +kernel
def cageIndex (i : Fin 10) : Fin 11 := ⟨i.val%4,by omega⟩
theorem cage_inside : ∀ i : Fin 10, 4≤i.val → i.val<8 →
 Post187Seven12.locks (cageIndex i)⊆161::(Cage10.locks i).erase 187 := by decide +kernel
theorem cage239_inside : ∀ i : Fin 10, 4≤i.val → i.val<8 →
 Post187Seven12.locks (cageIndex i)⊆161::(Cage23912.locks i).erase 187 := by decide +kernel
theorem cage_hero : ∀ i, (187:Cell)∈Post187Seven12.region (cageIndex i) := by decide +kernel
theorem cage_credit : ∀ i, Post187Seven12.credit (cageIndex i)=7 := by decide +kernel
theorem ring_inside : ∀ i : Fin 3,
 Post187Seven12.locks 0⊆262::(RingUpper12.locks i).erase 263 := by decide +kernel
theorem ring_hero : (263:Cell)∈Post187Seven12.region 0 := by decide +kernel
theorem ring_credit : Post187Seven12.credit 0=7 := by decide +kernel
#print axioms post_inside
#print axioms cage_inside
#print axioms ring_inside
end Owner1007.Post187SevenMap12

