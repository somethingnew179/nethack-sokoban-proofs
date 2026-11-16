import Owner1007.RingAfter12
import Owner1007.TwoReserves12
namespace Owner1007.S211Corner12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def C : List Cell := [210,237,262,289]
def locks (_ : Fin 1) : List Cell := [210,211,237,262,289]
def region (_ : Fin 1) : List Cell :=
 soko1_2.board.floor.filter fun c=>!([210,211,237,262,289,236,288]:List Cell).contains c
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=210∧dir=.south)∨(source=237∧dir=.west)∨(source=289∧dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem guard : ∀ i,∀ hero∈region i,∀ dir∈allDirs,∀ source∈locks 0,
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (locks i) source dir∨paid source dir := by decide +kernel
theorem priced : ∀ source∈C,∀ dir∈allDirs,paid source dir→∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes∧(2:Int)≤1+p.boulder dest-p.boulder source := by decide +kernel
theorem paid_core {source dir} (h : paid source dir) : source∈C := by
 rcases h with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;>decide +kernel
theorem hero263 : (263:Cell)∈region 0 := by decide +kernel

theorem core_two {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (hero : state.player∈region 0)
 (inside : locks 0⊆state.boulders) :2≤energy p C outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached (locks 0) (unique 0) inside hero (fun _ h=>h) with event|terminal
 · obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroHead,locksHead,pays,fixed⟩ :=
     event.split_fixed (locks 0) (fun _=>fun _ h=>h)
       (fun i hero h dir source m a=>guard i hero h dir (Geometry.all_directions dir) source m a)
       reached (unique 0) inside
   have atReached := reached.append first.trace
   cases outcome with
   | walk target=>exact False.elim pays
   | push source ending=>
     obtain ⟨_,headPaid⟩:=pays
     have member := paid_core headPaid
     have price := push_effect_price p soko1_2.initial.holes 2 atReached.holes_sublist.subset
       (priced source member dir (Geometry.all_directions dir) headPaid) checked effect
     have prior := fixed C (by decide +kernel)
     have bound := event_energy_le Generated.soko1_2_potential_valid C first last (.push source ending)
     rw [prior] at bound
     simp only [projectedOutcome,if_pos member] at bound
     rw [←shape] at bound
     change slack p (.push source ending)≤energy p C outcomes at bound
     omega
 · obtain ⟨j,_,kept⟩:=terminal
   have endInside := logged.end_subset actualUnique (locks 0) (unique 0) inside
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept endInside.2)
   have size : ∀ i,(locks i).length=5 := by decide +kernel
   rw [size j] at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega

theorem owned_two {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) (hero : state.player∈region 0)
 (inside : C⊆group) (s211 : (211:Cell)∈state.boulders) :2≤energy p group outcomes := by
 have physical : locks 0⊆state.boulders := by
   have check : locks 0⊆C++[211] := by decide +kernel
   intro c member
   rcases List.mem_append.mp (check member) with old|single
   ·exact subset (inside old)
   ·have same : c=211 := List.mem_singleton.mp single
    simpa only [same] using s211
 have lower := core_two logged reached completed hero physical
 have mono := logged.energy_mono Generated.soko1_2_potential_valid
   (reached.boulders_nodup (by decide +kernel)) C group (by decide +kernel) gUnique
   (List.Subset.trans inside subset) subset inside
 change energy p C outcomes≤energy p group outcomes at mono
 omega
#print axioms matrix
#print axioms owned_two
end Owner1007.S211Corner12
