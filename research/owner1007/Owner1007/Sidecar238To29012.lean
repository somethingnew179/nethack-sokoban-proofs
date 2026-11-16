import Owner1007.FastCorral11
import Owner1007.OwnedEventsMore12
namespace Owner1007.Sidecar238To29012
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def locks (i : Fin 3) : List Cell := if i.val=0 then [210,211,213,237,238,263,265] else if i.val=1 then [210,211,213,237,263,264,265] else [210,211,213,237,263,265,290]
def region (i : Fin 3) : List Cell := if i.val=0 then [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,180,184,185,186,187,206,212,232,258,284,310,336] else if i.val=1 then [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,180,184,185,186,187,206,212,232,238,239,258,284,310,336] else [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,180,184,185,186,187,206,212,232,238,239,258,264,284,310,336]
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=210∧dir=.south)∨(source=237∧dir=.west)∨(source=263∧dir=.west)∨
 (source=265∧dir=.south)∨(source=290∧dir=.west)∨
 (source=213∧(dir=.north∨dir=.south∨dir=.east))
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem heroes : (187:Cell)∈region 0 ∧(264:Cell)∈region 2 := by decide +kernel
theorem inaccessible : ∀ i,(214:Cell)∉region i := by decide +kernel
theorem shift264 : locks 2⊆290::(locks 1).erase 264 ∧(264:Cell)∈region 2 := by decide +kernel
theorem shift238 : locks 1⊆264::(locks 0).erase 238 ∧(238:Cell)∈region 1 := by decide +kernel
theorem markers_inside : ∀ i,([211,213]:List Cell)⊆locks i := by decide +kernel
theorem markers_check : ∀ i, ∀ hero∈region i, ∀ dir∈allDirs, ∀ source∈([211,213]:List Cell),
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (locks i) source dir∨paid source dir := by decide +kernel
theorem markers_guard : ∀ i hero, hero∈region i →∀ dir source,source∈([211,213]:List Cell) →
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (locks i) source dir∨paid source dir := by
 intro i hero h dir source m ad
 exact markers_check i hero h dir (Geometry.all_directions dir) source m ad
theorem paid_source {source dir} (h : paid source dir) : source∈([210,237,263,265,290,213]:List Cell) := by
 rcases h with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩
 all_goals decide +kernel
theorem not_critical {source dir} (h : paid source dir) : source≠264 := by
 have m:=paid_source h
 have check : ∀ c∈([210,237,263,265,290,213]:List Cell),c≠264 := by decide +kernel
 exact check source m
theorem priced : ∀ source∈([210,237,263,265,290,213]:List Cell), ∀ dir∈allDirs,
 paid source dir →∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧(2:Int)≤1+Generated.soko1_2Potential.boulder dest-Generated.soko1_2Potential.boulder source := by decide +kernel

/-- The prescribed238South264 and264South290 clearances both leave support214 sealed. Any later access must cross a separate priced event. -/
theorem support_has_event {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 {i : Fin 3} (hero : state.player∈region i) (inside : locks i⊆group)
 (support : final.player=214) :
 EventLog locks region paid group state dirs final pushes moves outcomes := by
 have closed:=PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 ·exact event
 ·obtain ⟨j,heroEnd,_⟩:=terminal
  rw[support] at heroEnd
  exact False.elim (inaccessible j heroEnd)
#print axioms matrix
#print axioms support_has_event
end Owner1007.Sidecar238To29012
