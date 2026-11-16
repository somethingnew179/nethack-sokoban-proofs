import Owner1007.NorthPrepared12
import Owner1007.FastCorral11
import Owner1007.Quad29012
namespace Owner1007.North21112
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def locks (i : Fin 5) : List Cell := NorthEvents12.locks i ++ [211]
def region (i : Fin 5) : List Cell := (NorthEvents12.region i).filter fun c => c != 211
abbrev paid := NorthEvents12.paid
theorem checked : ∀ i, FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes locks region paid i=true := by decide +kernel
theorem floors : ∀ i, region i ⊆ soko1_2.board.floor := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ PreCage12.reverse_checked floors checked
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem size : ∀ i, (locks i).length=8 := by decide +kernel
def fixed : List Cell := [210,237,238,263,265,318,211]
theorem fixed_inside : ∀ i, fixed ⊆ locks i := by decide +kernel
theorem fixed_guard_check : ∀ i, ∀ hero∈region i, ∀ dir∈allDirs, ∀ source∈fixed,
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir := by decide +kernel
theorem fixed_guard : ∀ i hero, hero∈region i → ∀ dir source, source∈fixed →
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir := by
 intro i hero h dir source member adjacent
 exact fixed_guard_check i hero h dir (Geometry.all_directions dir) source member adjacent
theorem start_activation : ∀ i : Fin 10, PreCage12.northS i=212 →
 locks (NorthPrepared12.oldIndex i) ⊆ 211::(PreCage12.northLocks i).erase 212 ∧
 212∈region (NorthPrepared12.oldIndex i) := by decide +kernel
theorem old_region : ∀ i, region i ⊆ NorthEvents12.region i := by
 intro i c h
 exact (List.mem_filter.mp h).1
theorem old_locks : ∀ i, NorthEvents12.locks i ⊆ locks i := by
 intro i c h
 exact List.mem_append_left _ h
theorem quad_activation : ∀ i, 291∈locks i →
 Quad29012.locks 0 ⊆ 290::(locks i).erase 291 := by decide +kernel
theorem quad_hero : 291∈Quad29012.region 0 := by decide +kernel

theorem has_event {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group ⊆ state.boulders)
 (completed : Goal final) {i : Fin 5}
 (hero : state.player∈region i) (inside : locks i⊆group) :
 EventLog locks region paid group state dirs final pushes moves outcomes := by
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 · exact event
 · obtain ⟨j,_,kept⟩ := terminal
   have finalInside := logged.end_subset (reached.boulders_nodup (by decide +kernel)) group gUnique subset
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept finalInside.2)
   have amount := size j
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms closed
#print axioms has_event
end Owner1007.North21112
