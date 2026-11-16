import Owner1007.NorthMain23012
import Owner1007.NorthPrepared12
namespace Owner1007.NorthFirstException22912
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.PreCage12
open Owner1007.NorthTagFacts12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- The two actual exceptional heads left below230. The Upper187North
alternative is retained explicitly; the oldP228 exclusion is not reused at229. -/
def Choice (i : Fin 10) (source : Cell) (dir : Dir) (ending : Ending) : Prop :=
 (source=187∧dir=.north∧ending=.stay 161∧northS i=212) ∨
 (source=212∧dir=.west∧ending=.stay 211∧northS i=212)

theorem canonical {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤229) :
 ∃ beforeDirs beforePushes beforeMoves before middle dir t source ending after afterDirs afterPushes afterMoves,
 ∃ i : Fin 10,
 outcomes=before++.push source ending::after ∧
 Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before ∧
 step soko1_2.board middle dir=some t ∧Matches middle t (.push source ending) ∧
 Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
 middle.player∈northRegion i ∧northLocks i⊆endGroup selected before ∧
 endGroup [213] before=[northS i] ∧endGroup [345] before=[northTag i] ∧
 (∀small:List Cell,small⊆fixed→endGroup small before=small) ∧Choice i source dir ending := by
  have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
  have selectedUnique : selected.Nodup := by decide +kernel
  have selectedSubset : selected⊆FirstSplit12.afterN.boulders := by decide +kernel
  rcases TaggedFlow12.event_or_good north_closed north_unique tag_inside north_tag_sound tag_update
    logged NorthBound12.north_reached selected [213] [345] selectedUnique selectedSubset
    (i:=0) (by decide +kernel) (by decide +kernel) rfl rfl with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,i,shape,first,checked,effect,last,hero,locks,pays,sAt,tAt,unchanged⟩ :=
      event.split_fixed fixed fixed_inside fixed_guard NorthBound12.north_reached selectedUnique selectedSubset
    have reached := NorthBound12.north_reached.append first.trace
    have actualUnique := reached.boulders_nodup (by decide +kernel)
    have physical := first.end_subset initialUnique selected selectedUnique selectedSubset
    have sourceMember (source : Cell) (owner : source∈endGroup selected before) : source∈northLocks i := by
      apply Classical.byContradiction
      intro absent
      have allInside : source::northLocks i⊆endGroup selected before := by
        intro cell found
        rcases List.mem_cons.mp found with rfl | member
        · exact owner
        · exact locks member
      have count := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨absent,north_unique i⟩) allInside
      have size := north_size i
      have bound := endGroup_length_le selected before
      have total : selected.length=13 := by decide +kernel
      simp only [List.length_cons] at count
      omega
    cases outcome with
    |walk target=>exact False.elim pays
    |push source ending=>
      obtain ⟨owner,paid⟩:=pays
      obtain ⟨result,adjacent,push⟩:=effect_push_data checked effect
      rcases paid with northPaid|upper|sPaid
      ·have lower:=NorthMain23012.event_lower230 logged completed i shape first checked effect last
          hero locks (sourceMember source owner) northPaid sAt tAt unchanged
       omega
      ·rcases north_upper_heads i middle.player hero dir (Geometry.all_directions dir) source upper adjacent with blocked|actual
       ·exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locks physical.2) checked effect blocked)
       ·obtain ⟨rfl,rfl,at212⟩:=actual
        have endingSame:=push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
          (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel) (by decide +kernel) checked effect
        subst ending
        exact ⟨beforeDirs,beforePushes,beforeMoves,before,middle,.north,t,187,.stay 161,after,
          afterDirs,afterPushes,afterMoves,i,shape,first,checked,effect,last,hero,locks,sAt,tAt,unchanged,
          Or.inl ⟨rfl,rfl,rfl,at212⟩⟩
      ·have inS:source∈([213,212]:List Cell):=by rcases sPaid with h|h <;> simp_all
       rcases NorthActivation12.pre_s_heads i middle.player hero dir (Geometry.all_directions dir)
          source inS sPaid adjacent with blocked|actual
       ·exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locks physical.2) checked effect blocked)
       ·obtain ⟨rfl,rfl,at212⟩:=actual
        have endingSame:=push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
          (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel) (by decide +kernel) checked effect
        subst ending
        exact ⟨beforeDirs,beforePushes,beforeMoves,before,middle,.west,t,212,.stay 211,after,
          afterDirs,afterPushes,afterMoves,i,shape,first,checked,effect,last,hero,locks,sAt,tAt,unchanged,
          Or.inr ⟨rfl,rfl,rfl,at212⟩⟩
  · obtain ⟨i,hero,locks,_,_⟩ := terminal
    have finalInside := logged.end_subset initialUnique selected selectedUnique selectedSubset
    have count := List.Nodup.length_le_of_subset (north_unique i) (List.Subset.trans locks finalInside.2)
    have large := north_size i
    have finalReached := NorthBound12.north_reached.append logged.trace
    have conserved := finalReached.conservation
    have empty : final.holes=[] := completed
    change 20+final.holes.length=final.boulders.length+18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega
#print axioms canonical
end Owner1007.NorthFirstException22912
