import Owner1007.LeftFirstTwo11
import Owner1007.WestRankHead11
namespace Owner1007.LeftQuietIdentity11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A static corral whose owned pushes all pay preserves the identities too. -/
theorem quiet_zero_static (locks region : List Cell) (paid : Cell→Dir→Prop)
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes
   (fun _ : Fin 1=>locks) (fun _ : Fin 1=>region) paid)
 (uniqueLocks : locks.Nodup)
 (noMove : ∀hero∈region,∀source∈locks,∀dir,
   advance soko1_1.board hero dir=some source→BlockedPush soko1_1.board locks source dir∨paid source dir)
 {state group dirs final pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (inside : group⊆state.boulders) (same : group.Perm locks)
 (hero : state.player∈region) (holes : state.holes⊆soko1_1.initial.holes) :
 ownPushes group outcomes=0 ∧ final.player∈region := by
 induction quiet with
 | nil => exact ⟨rfl,hero⟩
 | @cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih =>
   have firstZero : ownPush group outcome=0 := by
     cases outcome with
     | walk target => rfl
     | push source ending =>
       by_cases owner : source∈group
       · have metadata : t.pushSource=some source := by
           cases ending with
           | stay landing => rw [effect.2]
           | fill hole => rw [effect.2.2]
         have member := same.mem_iff.mp owner
         have row := noMove state.player hero source member dir (PairPost11.source_adjacent head metadata)
         rcases row with blocked|pays
         · exact False.elim ((WestRankHead11.source_unblocked head metadata
             (List.Subset.trans (fun _ h=>same.mem_iff.mpr h) inside)) blocked)
         · exact False.elim (avoid ⟨source,owner,metadata,pays⟩)
       · simp only [ownPush,if_neg owner]
   have unchanged := ownPush_zero_update group outcome firstZero
   have good : OwnedCorral11.Good (fun _ : Fin 1=>locks) (fun _ : Fin 1=>region) state group :=
     ⟨0,hero,fun _ h=>same.mem_iff.mpr h⟩
   have nextGood := OwnedCorralAny11.step_good_except closed (fun _=>uniqueLocks)
     good inside holes head effect avoid
   obtain ⟨_,nextHero,nextLocks⟩ := nextGood
   have nextInside := GhostSubset.update_subset state t outcome effect group (same.nodup_iff.mpr uniqueLocks) inside
   have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holes
   have later := ih nextInside (by simpa only [unchanged] using same) nextHero nextHoles
   simpa only [ownPushes,firstZero,unchanged,Nat.zero_add] using later

theorem subset_zero (small large : List Cell) (outcomes : List Outcome)
 (subset : small⊆large) (zero : ownPushes large outcomes=0) : ownPushes small outcomes=0 := by
 induction outcomes generalizing small large with
 | nil => rfl
 | cons outcome rest ih =>
   have firstLarge : ownPush large outcome=0 := by simp only [ownPushes] at zero;omega
   have firstSmall : ownPush small outcome=0 := by
     cases outcome with
     | walk target => rfl
     | push source ending =>
       have absentLarge : source∉large := by
         intro owner
         simp only [ownPush,if_pos owner] at firstLarge
         omega
       have absentSmall : source∉small := fun h=>absentLarge (subset h)
       simp only [ownPush,if_neg absentSmall]
   have sameLarge := ownPush_zero_update large outcome firstLarge
   have sameSmall := ownPush_zero_update small outcome firstSmall
   simp only [ownPushes,firstLarge,sameLarge,Nat.zero_add] at zero
   simpa only [ownPushes,firstSmall,sameSmall,Nat.zero_add] using ih small large subset zero

def firstNoMove : Bool :=
 (LeftPair11.cut0Locks 0).all fun source=>allDirs.all fun dir=>
   match advance soko1_1.board source dir.opposite with
   | none=>true
   | some hero=>decide (hero∉LeftPair11.cut0Region 0 ∨
       BlockedPush soko1_1.board (LeftPair11.cut0Locks 0) source dir ∨ LeftPair11.cut0Paid source dir)
theorem firstNoMove_checked : firstNoMove=true := by decide +kernel
theorem first_floor : LeftPair11.cut0Region 0⊆soko1_1.board.floor := by
 have check : (LeftPair11.cut0Region 0).all (fun c=>decide (c∈soko1_1.board.floor))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp check c member)
theorem first_row : ∀hero∈LeftPair11.cut0Region 0,∀source∈LeftPair11.cut0Locks 0,∀dir,
 advance soko1_1.board hero dir=some source→
 BlockedPush soko1_1.board (LeftPair11.cut0Locks 0) source dir∨LeftPair11.cut0Paid source dir := by
 intro hero member source owner dir adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp firstNoMove_checked source owner) dir (Geometry.all_directions dir)
 have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (first_floor member) dir source adjacent
 simp only [firstNoMove,behind] at row
 exact (of_decide_eq_true row).resolve_left (fun h=>h member)

theorem first_quiet_zero {state group dirs final pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet LeftPair11.cut0Paid state group dirs final pushes moves outcomes)
 (inside : group⊆state.boulders) (same : group.Perm [186,212])
 (hero : state.player∈LeftPair11.cut0Region 0) (holes : state.holes⊆soko1_1.initial.holes) :
 ownPushes group outcomes=0 :=
 (quiet_zero_static (LeftPair11.cut0Locks 0) (LeftPair11.cut0Region 0) LeftPair11.cut0Paid
   LeftPair11.first_closed (by decide) first_row quiet inside same hero holes).1

theorem phase_row (i : Fin 2) : ∀hero∈LeftPair11.region i,∀source∈LeftPair11.locks i,∀dir,
 advance soko1_1.board hero dir=some source→
 BlockedPush soko1_1.board (LeftPair11.locks i) source dir∨LeftPair11.paid source dir := by
 intro hero member source owner dir adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp (LeftFirstTwo11.noMove i) source owner) dir (Geometry.all_directions dir)
 have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (LeftPair11.region_floor i member) dir source adjacent
 simp only [LeftFirstTwo11.noMoveCheck,behind] at row
 exact (of_decide_eq_true row).resolve_left (fun h=>h member)

theorem phase_quiet_zero {state group dirs final pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet LeftPair11.paid state group dirs final pushes moves outcomes)
 (inside : group⊆state.boulders) (i : Fin 2) (same : group.Perm (LeftPair11.locks i))
 (hero : state.player∈LeftPair11.region i) (holes : state.holes⊆soko1_1.initial.holes) :
 ownPushes group outcomes=0 :=
 (quiet_zero_static (LeftPair11.locks i) (LeftPair11.region i) LeftPair11.paid
   (LeftFirstTwo11.phase_closed i) (LeftPair11.unique i) (phase_row i) quiet inside same hero holes).1
#print axioms firstNoMove_checked
#print axioms first_quiet_zero
#print axioms phase_quiet_zero
#print axioms subset_zero
end Owner1007.LeftQuietIdentity11
