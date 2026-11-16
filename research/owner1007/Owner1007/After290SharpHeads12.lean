import Owner1007.After290Bound12
import Owner1007.FarUpperBound12
import Owner1007.Cage212Nine12
namespace Owner1007.After290Strong12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def classified (i:Fin 4)(source:Cell)(dir:Dir):Prop :=
 BlockedPush soko1_2.board (After29012.locks i) source dir ∨
 (source=263∧dir=.west) ∨ (source=187∧dir=.north∧i.val%2=1) ∨
 (source=212∧dir=.west) ∨ (source=265∧dir=.south∧i.val=1) ∨ (source=239∧dir=.south∧i.val=3) ∨
 (source=289∧dir=.west) ∨ After29012.square i source dir
instance (i:Fin 4)(source:Cell)(dir:Dir) : Decidable (classified i source dir):=by
 unfold classified After29012.square After29012.squareDest;infer_instance
theorem check : ∀ i, ∀ hero∈After29012.region i, ∀ dir∈allDirs, ∀ source∈After29012.sources,
 advance soko1_2.board hero dir=some source → After29012.paid source dir → classified i source dir := by decide +kernel
theorem classification (i:Fin 4)(hero:Cell)(heroIn:hero∈After29012.region i)(dir source)
 (sourceIn:source∈After29012.sources)(adjacent:advance soko1_2.board hero dir=some source)(paid:After29012.paid source dir) :
 classified i source dir := check i hero heroIn dir (Geometry.all_directions dir) source sourceIn adjacent paid
def upperIndex (i:Fin 4):Fin 3 := if i.val<2 then 0 else 1
theorem upper_only : ∀ i hero, hero∈After29012.region i→ advance soko1_2.board hero .north=some 187→ i.val%2=1 := by decide +kernel
theorem upper_shift : ∀ i : Fin 4, i.val%2=1→ FarUpper12.locks (upperIndex i)⊆161::(After29012.locks i).erase 187 := by decide +kernel
theorem upper_hero : ∀ i, (187:Cell)∈FarUpper12.region (upperIndex i) := by decide +kernel
theorem cage_s212 : ∀ i, i.val%2=1→ Cage21212.locks (Cage212Nine12.normal 0)⊆262::(After29012.locks i).erase 263 := by decide +kernel
theorem cage212hero : (263:Cell)∈Cage21212.region (Cage212Nine12.normal 0) := by decide +kernel
theorem quad_shift : ∀ i, Quad28912.locks 0⊆211::(After29012.locks i).erase 212 := by decide +kernel
theorem quad_hero : (212:Cell)∈Quad28912.region 0 := by decide +kernel
theorem t_only : ∀ i hero,hero∈After29012.region i→ advance soko1_2.board hero .south=some 265→ i.val=1 := by decide +kernel
theorem after_return : After29012.locks 1⊆265::(After29012.locks 3).erase 239 := by decide +kernel
theorem after_return_hero : (239:Cell)∈After29012.region 1 := by decide +kernel
#print axioms classification
end Owner1007.After290Strong12
