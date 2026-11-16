import Owner1007.S211FarFour12
import Owner1007.Sidecar26412
import Owner1007.Residual290Any12
namespace Owner1007.S211SidecarSix12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def C : List Cell := [210,237,263,264,290]
def locks (_ : Fin 1) : List Cell := [210,211,237,263,264,290]
def region (_ : Fin 1) : List Cell :=
 (Sidecar26412.region 0).filter fun c => c != 211
abbrev paid := Sidecar26412.paid
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem guard : ∀ i,∀ hero∈region i,∀ dir∈allDirs,∀ source∈locks 0,
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (locks i) source dir∨paid source dir := by decide +kernel
theorem paid_core {source dir} (h : paid source dir) : source∈C := by
 simp only [paid,Sidecar26412.paid] at h
 rcases h with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;>decide +kernel
theorem hero291 : (291:Cell)∈region 0 := by decide +kernel

theorem core_six {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (hero : state.player∈region 0)
 (inside : locks 0⊆state.boulders) :6≤energy p C outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached (locks 0) (unique 0) inside hero (fun _ h=>h) with event|terminal
 · obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroHead,locksHead,pays,fixed⟩ :=
     event.split_fixed (locks 0) (fun _=>fun _ h=>h)
       (fun i hero h dir source m a=>guard i hero h dir (Geometry.all_directions dir) source m a)
       reached (unique 0) inside
   have atReached := reached.append first.trace
   have atUnique := atReached.boulders_nodup (by decide +kernel)
   cases outcome with
   | walk target=>exact False.elim pays
   | push source ending=>
     obtain ⟨_,headPaid⟩:=pays
     have member := paid_core headPaid
     have prior := fixed C (by decide +kernel)
     have coreActual : C⊆state.boulders := List.Subset.trans (by decide +kernel : C⊆locks 0) inside
     have old := first.end_subset actualUnique C (by decide +kernel) coreActual
     rw [prior] at old
     have nextActual := step_boulders_nodup _ _ _ _ atUnique checked
     have nextUnique := GhostSubset.update_unique middle t (.push source ending) effect nextActual C (by decide +kernel) old.2
     have nextSubset := GhostSubset.update_subset middle t (.push source ending) effect C (by decide +kernel) old.2
     have nextReached := atReached.append (Trace.cons checked (Trace.nil t.state))
     have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid C
     change 0≤ownSlack p C before at nn
     have whole : energy p C outcomes=ownSlack p C before+slack p (.push source ending)+
         energy p (update C (.push source ending)) after := by
       rw [shape,energy_at_split,prior]
       simp only [projectedOutcome,if_pos member]
     have sActual : [211]⊆state.boulders := List.Subset.trans (by decide +kernel : ([211]:List Cell)⊆locks 0) inside
     have sFacts := first.end_subset actualUnique [211] (by decide +kernel) sActual
     have sPrior := fixed [211] (by decide +kernel)
     rw [sPrior] at sFacts
     have notS : (211:Cell)∉C := by decide +kernel
     have sourceNotS : source≠211 := fun h=>notS (h ▸ member)
     have sNext := GhostSubset.update_subset middle t (.push source ending) effect [211] (by decide +kernel) sFacts.2
     have sSame : update [211] (.push source ending)=[211] := by
       have absent : source∉([211]:List Cell) := by simpa only [List.mem_singleton] using sourceNotS
       simp only [update,move,if_neg absent]
     rw [sSame] at sNext
     have present211 : (211:Cell)∈t.state.boulders := sNext (by simp)
     simp only [paid,Sidecar26412.paid] at headPaid
     rcases headPaid with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
     · have sameEnding := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 210 .south=[236] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept : Residual29012.locks 0⊆update C (.push 210 (.stay 236)) := by decide +kernel
       have nextHero : t.state.player∈Residual29012.region 0 := by
         rw [matches_hero middle t (.push 210 (.stay 236)) effect]
         decide +kernel
       have later := Residual290Any12.owned_energy_credit Residual29012.matrix last nextReached
         (update C (.push 210 (.stay 236))) nextUnique nextSubset 0 nextHero kept
       change 5≤energy p (update C (.push 210 (.stay 236))) after at later
       have one : slack p (.push 210 (.stay 236))=2 := by decide +kernel
       rw [one] at whole
       omega
     · have sameEnding := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 237 .west=[236] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept : ([210,236]:List Cell)⊆update C (.push 237 (.stay 236)) := by decide +kernel
       have later := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
         (update C (.push 237 (.stay 236))) nextUnique nextSubset [210,236] RingAfter12.locked_pair (by decide +kernel) kept
       change 15≤energy p (update C (.push 237 (.stay 236))) after at later
       have one : slack p (.push 237 (.stay 236))=2 := by decide +kernel
       rw [one] at whole
       omega
     · have sameEnding := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 290 .west=[289] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept : S211FarFour12.C⊆update C (.push 290 (.stay 289)) := by decide +kernel
       have nextHero : t.state.player∈S211FarFour12.region 0 := by
         rw [matches_hero middle t (.push 290 (.stay 289)) effect]
         exact S211FarFour12.hero290
       have later := S211FarFour12.owned_four last nextReached (update C (.push 290 (.stay 289)))
         nextUnique nextSubset completed nextHero kept present211
       change 4≤energy p (update C (.push 290 (.stay 289))) after at later
       have one : slack p (.push 290 (.stay 289))=2 := by decide +kernel
       rw [one] at whole
       omega
 · obtain ⟨j,_,kept⟩:=terminal
   have endInside := logged.end_subset actualUnique (locks 0) (unique 0) inside
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept endInside.2)
   have size : ∀ i,(locks i).length=6 := by decide +kernel
   rw [size j] at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
theorem owned_six {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) (hero : state.player∈region 0)
 (inside : C⊆group) (s211 : (211:Cell)∈state.boulders) :6≤energy p group outcomes := by
 have physical : locks 0⊆state.boulders := by
   have check : locks 0⊆C++[211] := by decide +kernel
   intro c member
   rcases List.mem_append.mp (check member) with old|single
   ·exact subset (inside old)
   ·have same : c=211 := List.mem_singleton.mp single
    simpa only [same] using s211
 have lower := core_six logged reached completed hero physical
 have mono := logged.energy_mono Generated.soko1_2_potential_valid
   (reached.boulders_nodup (by decide +kernel)) C group (by decide +kernel) gUnique
   (List.Subset.trans inside subset) subset inside
 change energy p C outcomes≤energy p group outcomes at mono
 omega
#print axioms matrix
#print axioms owned_six
end Owner1007.S211SidecarSix12
