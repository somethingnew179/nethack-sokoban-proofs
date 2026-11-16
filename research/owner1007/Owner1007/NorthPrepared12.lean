import Owner1007.TaggedFlow12
import Owner1007.NorthTagFacts12
import Owner1007.NorthBound12
import Owner1007.CageLedger12
import Owner1007.VerticalPair12
import Owner1007.Token213Gate12
import Owner1007.TokenBounds32
namespace Owner1007.NorthPrepared12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.PreCage12
open Owner1007.NorthTagFacts12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem prepared {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    (completed : Goal final)
    (cheapUP : energy p U outcomes + energy p [213] outcomes ≤ 3)
    (cheapS : energy p [213] outcomes ≤ 1) :
    ∃ beforeDirs beforePushes beforeMoves before middle dir t source ending after afterDirs afterPushes afterMoves,
      ∃ i : Fin 10,
      outcomes=before++(.push source ending)::after ∧
      Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before ∧
      step soko1_2.board middle dir=some t ∧ Matches middle t (.push source ending) ∧
      Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
      middle.player∈northRegion i ∧ northLocks i⊆endGroup selected before ∧
      source∈northLocks i ∧ source∈endGroup selected before ∧ NorthEvents12.paid source dir ∧
      endGroup [213] before=[northS i] ∧ endGroup [345] before=[northTag i] ∧
      (∀ small : List Cell, small⊆fixed → endGroup small before=small) := by
  have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
  have selectedUnique : selected.Nodup := by decide +kernel
  have selectedSubset : selected⊆FirstSplit12.afterN.boulders := by decide +kernel
  have upUnique : UP.Nodup := by decide +kernel
  have upSubset : UP⊆FirstSplit12.afterN.boulders := by decide +kernel
  have splitUP := logged.energy_split initialUnique p U [213] upUnique upSubset
  change energy p UP outcomes=energy p U outcomes+energy p [213] outcomes at splitUP
  have cheapBoth : energy p UP outcomes≤3 := by omega
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
    | walk target => exact False.elim pays
    | push source ending =>
      obtain ⟨owner,paid⟩ := pays
      obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
      rcases paid with northPaid | upper | sPaid
      · exact ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,source,ending,after,
          afterDirs,afterPushes,afterMoves,i,shape,first,checked,effect,last,hero,locks,sourceMember source owner,owner,
          northPaid,sAt,tAt,unchanged⟩
      · rcases north_upper_heads i middle.player hero dir (Geometry.all_directions dir) source upper adjacent with blocked | exceptional
        · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locks physical.2) checked effect blocked)
        · obtain ⟨rfl,rfl,at212⟩ := exceptional
          have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
            (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel)
            (by decide +kernel) checked effect
          subst ending
          have upperSame := unchanged U (by intro c h; exact List.mem_append_left _ h)
          have identity := first.end_split initialUnique U [213] upUnique upSubset
          rw [upperSame,sAt,at212] at identity
          change (U++[212]).Perm (endGroup UP before) at identity
          have pairInside : ([186,212] : List Cell)⊆endGroup UP before := by
            intro c member
            apply identity.mem_iff.mp
            have all : ([186,212] : List Cell)⊆U++[212] := by decide +kernel
            exact all member
          have ownerUP : (187 : Cell)∈endGroup UP before :=
            identity.mem_iff.mp (by decide +kernel)
          have oldUP := first.end_subset initialUnique UP upUnique upSubset
          have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
          have nextUPUnique := GhostSubset.update_unique middle t (.push 187 (.stay 161)) effect nextActual
            (endGroup UP before) oldUP.1 oldUP.2
          have nextUPSubset := GhostSubset.update_subset middle t (.push 187 (.stay 161)) effect
            (endGroup UP before) oldUP.1 oldUP.2
          have pairAfter := update_mono [186,212] (endGroup UP before) (by decide +kernel)
            pairInside (.push 187 (.stay 161))
          simp only [update,move,if_neg (show (187 : Cell)∉[186,212] by decide)] at pairAfter
          have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
          have heroPair : t.state.player∈VerticalPair12.region false 0 := by
            rw [matches_hero middle t (.push 187 (.stay 161)) effect]
            decide +kernel
          have later := VerticalPair12.owned_energy_two false last nextReached
            (update (endGroup UP before) (.push 187 (.stay 161))) nextUPUnique nextUPSubset heroPair pairAfter
          change 2≤energy p (update (endGroup UP before) (.push 187 (.stay 161))) after at later
          have one : (2 : Int)≤slack p (.push 187 (.stay 161)) := by decide +kernel
          have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid UP
          change 0≤ownSlack p UP before at prefixNN
          rw [shape,energy_at_split] at cheapBoth
          simp only [projectedOutcome,if_pos ownerUP] at cheapBoth
          omega
      · have inS : source∈([213,212] : List Cell) := by rcases sPaid with h | h <;> simp_all
        have sourceTag := s_only i source inS (sourceMember source owner)
        have ownerS : source∈endGroup [213] before := by rw [sAt]; simpa using sourceTag
        by_cases blocked : source=212 ∧ dir=.north
        · obtain ⟨rfl,rfl⟩ := blocked
          exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locks physical.2) checked effect
            (blocked_s_north i))
        · have one := push_effect_price p soko1_2.initial.holes 2 reached.holes_sublist.subset
            (Token213Gate12.bad_price source inS dir (Geometry.all_directions dir) sPaid blocked) checked effect
          have eventBound := event_energy_le Generated.soko1_2_potential_valid [213] first last (.push source ending)
          simp only [projectedOutcome,if_pos ownerS] at eventBound
          change slack p (.push source ending)≤energy p [213] (before++(.push source ending)::after) at eventBound
          rw [shape] at cheapS
          omega
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

def oldIndex (i : Fin 10) : Fin 5 := ⟨i.val/2,by have h:=i.isLt; omega⟩
def J6 : List Cell := [210,237,238,263,265,318]
theorem old_region : ∀ i, northRegion i⊆NorthEvents12.region (oldIndex i) := by decide +kernel
theorem old_locks : ∀ i, NorthEvents12.locks (oldIndex i)=J6++[northTag i] := by decide +kernel
theorem old_paid_member : ∀ i, ∀ source∈northLocks i, ∀ dir∈allDirs,
    NorthEvents12.paid source dir → source∈NorthEvents12.locks (oldIndex i) := by decide +kernel

theorem g_end_subset {beforeDirs middle beforePushes beforeMoves before}
    (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
    (i : Fin 10) (tag : endGroup [345] before=[northTag i])
    (unchanged : ∀ small : List Cell, small⊆fixed → endGroup small before=small) :
    NorthEvents12.locks (oldIndex i)⊆endGroup NorthBound12.G before := by
  have identity := first.end_split (by decide +kernel) J6 [345] (by decide +kernel) (by decide +kernel)
  rw [unchanged J6 (by decide +kernel),tag] at identity
  change (J6++[northTag i]).Perm (endGroup NorthBound12.G before) at identity
  rw [←old_locks i] at identity
  exact fun _ h => identity.mem_iff.mp h

#print axioms g_end_subset
#print axioms prepared
end Owner1007.NorthPrepared12
