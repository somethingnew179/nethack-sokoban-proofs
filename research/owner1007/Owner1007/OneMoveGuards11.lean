import Owner1007.StationaryGuards11
namespace Owner1007.OneMoveGuards11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.StationaryGuards11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guard138 : (List.range 16).all (guardCheck 138 [141,140,139])=true := by decide +kernel
theorem guard190 : (List.range 16).all (guardCheck 190 [193,192,191])=true := by decide +kernel
theorem guard_one_move {fixed moved box : Cell} {cells expanded : List Cell}
 (matrix : (List.range 16).all (guardCheck fixed cells) = true)
 (nextMatrix : (List.range 16).all (guardCheck moved expanded)=true)
 (cellsSubset : cells⊆expanded)
 {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (fixedPresent : fixed∈state.boulders) (present : box∈state.boulders) (member : box∈cells)
 (limited : ownPushes [fixed] outcomes≤1)
 (fixedTag : endGroup [fixed] outcomes=[moved])
 (cheap : energy state final [box] outcomes<2) :
 ∃ next, next∈expanded ∧ endGroup [box] outcomes=[next] := by
 induction logged generalizing box with
 | nil => exact ⟨box,cellsSubset member,rfl⟩
 | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
   let cert := groupCertificate 1
   have nextValid := cert.preserved state dir t valid head
   have actual := step_boulders_nodup _ _ _ _ valid.1 head
   have subset : [box] ⊆ state.boulders := by simpa using present
   have nextUnique := GhostSubset.update_unique state t outcome effect actual [box] (by simp) subset
   have nextSubset := GhostSubset.update_subset state t outcome effect [box] (by simp) subset
   have nextSize : (update [box] outcome).length≤1 := Nat.le_trans (update_length _ _) (by simp)
   have nonnegative := HeroLedger.Logged.energy_nonnegative tail cert nextValid
     (update [box] outcome) nextUnique nextSubset nextSize
   have one := cert.row state dir t outcome [box] valid (by simp) subset (by simp) head effect
   change value state [box] ≤ charge NetHack.Soko11Hero315.holeWeight [box] outcome +
     value t.state (update [box] outcome) at one
   have decomposition := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight
     state t.state final [box] outcome outcomes
   change energy state final [box] (outcome :: outcomes) =
     charge NetHack.Soko11Hero315.holeWeight [box] outcome + value t.state (update [box] outcome) -
       value state [box] + energy t.state final (update [box] outcome) outcomes at decomposition
   change 0≤energy t.state final (update [box] outcome) outcomes at nonnegative
   have firstCheap : charge NetHack.Soko11Hero315.holeWeight [box] outcome +
     value t.state (update [box] outcome) - value state [box]<2 := by omega
   obtain ⟨next,nextMember,updated⟩ := one_step matrix valid head effect fixedPresent present member firstCheap
   have nextPresent : next∈t.state.boulders := nextSubset (by rw [updated]; simp)
   have tailCheap : energy t.state final [next] outcomes<2 := by rw [←updated]; omega
   by_cases ownZero : ownPush [fixed] outcome=0
   · have fixedSame := ownPush_zero_update [fixed] outcome ownZero
     have limitedTail : ownPushes [fixed] outcomes≤1 := by
       simpa only [ownPushes,ownZero,fixedSame,Nat.zero_add] using limited
     have tagTail : endGroup [fixed] outcomes=[moved] := by
       simpa only [endGroup,fixedSame] using fixedTag
     have fixedSubset : [fixed]⊆state.boulders := by simpa using fixedPresent
     have nextFixedSubset := GhostSubset.update_subset state t outcome effect [fixed] (by simp) fixedSubset
     have nextFixed : fixed∈t.state.boulders := by
       rw [fixedSame] at nextFixedSubset
       exact nextFixedSubset (by simp)
     obtain ⟨last,lastMember,lastGroup⟩ := ih nextValid nextFixed nextPresent nextMember limitedTail tagTail tailCheap
     exact ⟨last,lastMember,by simpa only [endGroup,updated] using lastGroup⟩
   · have positive : 1≤ownPush [fixed] outcome := by omega
     have stationaryUpdate : ownPushes (update [fixed] outcome) outcomes=0 := by
       change ownPush [fixed] outcome+ownPushes (update [fixed] outcome) outcomes≤1 at limited
       omega
     have fixedUpdated : update [fixed] outcome=[moved] := by
       change endGroup (update [fixed] outcome) outcomes=[moved] at fixedTag
       rw [no_push_unchanged _ _ stationaryUpdate] at fixedTag
       exact fixedTag
     have stationaryTail : ownPushes [moved] outcomes=0 := by rw [←fixedUpdated]; exact stationaryUpdate
     have fixedSubset : [fixed]⊆state.boulders := by simpa using fixedPresent
     have nextFixedSubset := GhostSubset.update_subset state t outcome effect [fixed] (by simp) fixedSubset
     have nextFixed : moved∈t.state.boulders := by
       rw [fixedUpdated] at nextFixedSubset
       exact nextFixedSubset (by simp)
     obtain ⟨last,lastMember,lastGroup⟩ := StationaryGuards11.guard_logged nextMatrix tail nextValid
       nextFixed nextPresent (cellsSubset nextMember) stationaryTail tailCheap
     exact ⟨last,lastMember,by simpa only [endGroup,updated] using lastGroup⟩

theorem guard141_one {dirs state pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (limited : ownPushes [139] outcomes≤1)
 (fixedTag : endGroup [139] outcomes=[138])
 (cheap : energy soko1_1.initial state [141] outcomes<2) :
 ∃ next, next∈([141,140,139] : List Cell) ∧ endGroup [141] outcomes=[next] := by
 exact guard_one_move StationaryGuards11.guards141 guard138 (by decide) first
   NetHack.SokobanLinearPhases.Map11.initial_good (by decide +kernel) (by decide +kernel)
   (by simp) limited fixedTag cheap
#print axioms guard141_one

theorem guard193_one {dirs state pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (limited : ownPushes [191] outcomes≤1)
 (fixedTag : endGroup [191] outcomes=[190])
 (cheap : energy soko1_1.initial state [193] outcomes<2) :
 ∃ next, next∈([193,192,191] : List Cell) ∧ endGroup [193] outcomes=[next] := by
 exact guard_one_move StationaryGuards11.guards193 guard190 (by decide) first
   NetHack.SokobanLinearPhases.Map11.initial_good (by decide +kernel) (by decide +kernel)
   (by simp) limited fixedTag cheap
#print axioms guard193_one

#print axioms guard138
#print axioms guard190
#print axioms guard_one_move
end Owner1007.OneMoveGuards11
