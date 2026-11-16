import Owner1007.NorthPrepared12
import Owner1007.North187Strong12
import Owner1007.North211Priced12
namespace Owner1007.NorthPrepared22612
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
    (cheap : 1+pushes≤225) :
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
          let before1 : List Outcome := before++[.push 187 (.stay 161)]
          have lead1 := first.append (Logged.cons checked effect (Logged.nil t.state))
          have shape1 : outcomes=before1++after := by
            rw [shape]
            simp only [before1,List.append_assoc,List.cons_append,List.nil_append]
          have perm : selected.Perm NorthLeftBudget22512.Left := by decide +kernel
          have finalPerm := endGroup_perm perm before
          have locksL : northLocks i⊆endGroup NorthLeftBudget22512.Left before :=
            fun _ h=>finalPerm.mem_iff.mp (locks h)
          have ownerL : 187∈endGroup NorthLeftBudget22512.Left before :=
            locksL (PreCage12.north_upper_inside i (by decide +kernel))
          obtain ⟨shift,newHero⟩ := North18712.start_activation i at212
          have kept := CageFour12.shifted_inside (north_unique i) locksL ownerL shift
          have inside1 : North18712.locks (NorthPrepared12.oldIndex i)⊆
              endGroup NorthLeftBudget22512.Left before1 := by
            simpa only [before1,endGroup_append,endGroup] using kept
          have upperSame := unchanged U (by intro c h; exact List.mem_append_left _ h)
          have u1 : endGroup U before1=North187Strong12.UA := by
            rw [show before1=before++[.push 187 (.stay 161)] from rfl,endGroup_append,upperSame]
            decide +kernel
          have s1 : endGroup [213] before1=[212] := by
            rw [show before1=before++[.push 187 (.stay 161)] from rfl,endGroup_append,sAt,at212]
            decide +kernel
          have fixed1 : ∀ small : List Cell, small⊆NorthEvents12.J → endGroup small before1=small := by
            intro small h
            rw [show before1=before++[.push 187 (.stay 161)] from rfl,endGroup_append,
              unchanged small (List.Subset.trans h (by decide +kernel))]
            have absent : (187:Cell)∉small := fun found=>(show (187:Cell)∉NorthEvents12.J by decide +kernel) (h found)
            simp only [endGroup,update,move,if_neg absent]
          have priced1 : 2≤ownSlack p NorthLeftBudget22512.Left before1 := by
            have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthLeftBudget22512.Left
            change 0≤ownSlack p NorthLeftBudget22512.Left before at nn
            rw [show before1=before++[.push 187 (.stay 161)] from rfl,ownSlack_append]
            have one : ownSlack p (endGroup NorthLeftBudget22512.Left before) [.push 187 (.stay 161)]=2 := by
              simp only [ownSlack,projectedOutcome,if_pos ownerL,Int.add_zero]
              decide +kernel
            rw [one]
            omega
          have hero1 : t.state.player∈North18712.region (NorthPrepared12.oldIndex i) := by
            rw [matches_hero middle t (.push 187 (.stay 161)) effect]
            exact newHero
          exact False.elim (North187Strong12.impossible logged completed cheap shape1 lead1 last
            (NorthPrepared12.oldIndex i) hero1 inside1 u1 s1 fixed1 priced1)
      · have inS : source∈([213,212]:List Cell) := by rcases sPaid with h|h <;> simp_all
        rcases NorthActivation12.pre_s_heads i middle.player hero dir (Geometry.all_directions dir)
          source inS sPaid adjacent with blocked | actual
        · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locks physical.2) checked effect blocked)
        · obtain ⟨rfl,rfl,at212⟩ := actual
          have endingSame := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
            (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel)
            (by decide +kernel) checked effect
          subst ending
          let before1 : List Outcome := before++[.push 212 (.stay 211)]
          have lead1 := first.append (Logged.cons checked effect (Logged.nil t.state))
          have shape1 : outcomes=before1++after := by
            rw [shape]
            simp only [before1,List.append_assoc,List.cons_append,List.nil_append]
          have oldG := NorthPrepared12.g_end_subset first i tAt unchanged
          have gsUnique : NorthActivation12.GS.Nodup := by decide +kernel
          have gsSubset : NorthActivation12.GS⊆FirstSplit12.afterN.boulders := by decide +kernel
          have split := first.end_split initialUnique NorthBound12.G [213] gsUnique gsSubset
          change (endGroup NorthBound12.G before++endGroup [213] before).Perm
            (endGroup NorthActivation12.GS before) at split
          rw [sAt,at212] at split
          have preInside : NorthEvents12.locks (NorthPrepared12.oldIndex i)++[212]⊆
              endGroup NorthActivation12.GS before := by
            intro c found
            apply split.mem_iff.mp
            rcases List.mem_append.mp found with old|same
            · exact List.mem_append_left _ (oldG old)
            · exact List.mem_append_right _ same
          have ownerGS : 212∈endGroup NorthActivation12.GS before :=
            preInside (List.mem_append_right _ (by simp))
          have preUnique : (NorthEvents12.locks (NorthPrepared12.oldIndex i)++[212]).Nodup := by
            have all : ∀ j, (NorthEvents12.locks j++[212]).Nodup := by decide +kernel
            exact all _
          have shift : North21112.locks (NorthPrepared12.oldIndex i)⊆
              211::(NorthEvents12.locks (NorthPrepared12.oldIndex i)++[212]).erase 212 := by
            have all : ∀ j, North21112.locks j⊆211::(NorthEvents12.locks j++[212]).erase 212 := by decide +kernel
            exact all _
          have kept := CageFour12.shifted_inside preUnique preInside ownerGS shift
          have inside1 : North21112.locks (NorthPrepared12.oldIndex i)⊆endGroup NorthActivation12.GS before1 := by
            simpa only [before1,endGroup_append,endGroup] using kept
          have s1 : endGroup [213] before1=[211] := by
            rw [show before1=before++[.push 212 (.stay 211)] from rfl,endGroup_append,sAt,at212]
            decide +kernel
          have fixed1 : ∀ small : List Cell, small⊆NorthEvents12.J → endGroup small before1=small := by
            intro small h
            rw [show before1=before++[.push 212 (.stay 211)] from rfl,endGroup_append,
              unchanged small (List.Subset.trans h (by decide +kernel))]
            have absent : (212:Cell)∉small := fun found=>(show (212:Cell)∉NorthEvents12.J by decide +kernel) (h found)
            simp only [endGroup,update,move,if_neg absent]
          have priced1 : 2≤ownSlack p [213] before1 := by
            have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid [213]
            change 0≤ownSlack p [213] before at nn
            rw [show before1=before++[.push 212 (.stay 211)] from rfl,ownSlack_append,sAt,at212]
            have one : ownSlack p [212] [.push 212 (.stay 211)]=2 := by decide +kernel
            rw [one]
            omega
          have hero1 : t.state.player∈North21112.region (NorthPrepared12.oldIndex i) := by
            rw [matches_hero middle t (.push 212 (.stay 211)) effect]
            exact (North21112.start_activation i at212).2
          exact False.elim (North211Priced12.impossible logged completed (by omega) shape1 lead1 last
            (NorthPrepared12.oldIndex i) hero1 inside1 s1 fixed1 priced1)
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


#print axioms prepared
end Owner1007.NorthPrepared22612
