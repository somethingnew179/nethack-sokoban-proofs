import Owner1007.RingPrepared12
namespace Owner1007.Sidecar26412
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def locks (_ : Fin 1) : List Cell := [210,237,263,264,290]
def region (_ : Fin 1) : List Cell :=
 soko1_2.board.floor.filter fun c => !([236,262,288,289,210,237,263,264,290] : List Cell).contains c
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=210 ∧ dir=.south) ∨ (source=237 ∧ dir=.west) ∨ (source=290 ∧ dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem old_inside : RingCut12.locks 0⊆locks 0 := by decide +kernel
theorem hero291 : (291:Cell)∈region 0 := by decide +kernel
theorem paid_main {source dir} (h : paid source dir) : RingCut12.paid source dir ∧ source≠263 := by
 rcases h with h|h|h <;> simp_all [RingCut12.paid]
theorem paid_price : ∀ source∈locks 0, ∀ dir∈allDirs, paid source dir →
 ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧ (2:Int)≤1+p.boulder dest-p.boulder source := by decide +kernel

theorem energy_four {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) (hero : state.player∈region 0) (inside : locks 0⊆group) :
 4≤energy p group outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,i,shape,first,checked,effect,last,heroOne,locksOne,pays⟩:=event.split
   have only : i=0 := Subsingleton.elim i 0
   subst i
   have middleReached := reached.append first.trace
   have oldGroup := first.end_subset actualUnique group gUnique subset
   cases outcome with
   | walk target => exact False.elim pays
   | push source ending =>
     obtain ⟨owner,paid⟩:=pays
     have main := paid_main paid
     have later := RingPrepared12.after_paid_two middleReached checked effect last
       (endGroup group before) oldGroup.1 oldGroup.2
       (List.Subset.trans old_inside locksOne) main.1 main.2 completed
     change 2≤energy p (update (endGroup group before) (.push source ending)) after at later
     have price := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset
       (NorthBound12.ring_priced source dir main.1) checked effect
     have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
     change 0≤ownSlack p group before at nn
     rw [shape,energy_at_split]
     simp only [projectedOutcome,if_pos owner]
     omega
 · obtain ⟨i,hero,locksOne⟩:=terminal
   have only : i=0 := Subsingleton.elim i 0
   subst i
   have finalInside := logged.end_subset actualUnique group gUnique subset
   have count := List.Nodup.length_le_of_subset (unique 0) (List.Subset.trans locksOne finalInside.2)
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   change 5≤final.boulders.length at count
   omega
#print axioms energy_four
end Owner1007.Sidecar26412

