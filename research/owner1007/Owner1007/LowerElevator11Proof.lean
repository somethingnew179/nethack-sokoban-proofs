import Owner1007.LowerElevator11Data
import Owner1007.LowerElevator11Prices
import Owner1007.WestRankHead11
import Owner1007.QuietFixed11
import NetHack.Sokoban.Reduction
namespace Owner1007.LowerElevator11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def shapeCheck (i : Fin 4) (source : Cell) (dir : Dir) : Bool :=
 if paid source dir then match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i ∨BlockedPush soko1_1.board (locks i) source dir ∨Shape i source dir)
 else true
theorem shapes : (List.finRange 4).all (fun i=>(locks i).all (fun source=>allDirs.all (shapeCheck i source)))=true := by decide +kernel
theorem complete (i : Fin 4) (group : List Cell) (bounded : group.length≤3)
 (inside : locks i⊆group) (source : Cell) (owner : source∈group) : source∈locks i := by
 by_cases member : source∈locks i
 · exact member
 · have all : source::locks i⊆group := by
     intro c found
     rcases List.mem_cons.mp found with rfl|later
     · exact owner
     · exact inside later
   have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,unique i⟩) all
   simp only [List.length_cons,size i] at card
   omega
theorem canonical (i : Fin 4) (group : List Cell) (groupUnique : group.Nodup) (bounded : group.length≤3)
 (inside : locks i⊆group) : group.Perm (locks i) := by
 apply (List.perm_ext_iff_of_nodup groupUnique (unique i)).mpr
 intro c
 exact ⟨fun member=>complete i group bounded inside c member,fun member=>inside member⟩
theorem head_shape {state : State} {group : List Cell} {dir : Dir} {t : Transition}
 (i : Fin 4) (heroInside : state.player∈region i) (locksInside : locks i⊆group)
 (inside : group⊆state.boulders) (bounded : group.length≤3) (head : step soko1_1.board state dir=some t)
 (pays : OwnedCorral11.PaidStep paid group dir t) :
 ∃source, source∈group ∧ t.pushSource=some source ∧Shape i source dir := by
 obtain ⟨source,owner,metadata,pays⟩ := pays
 have member := complete i group bounded locksInside source owner
 have adjacent := PairPost11.source_adjacent head metadata
 have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player
   (step_player_clear _ _ _ _ head).1 dir source adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp shapes i (by simp)) source member) dir (Geometry.all_directions dir)
 simp only [shapeCheck,if_pos pays,behind] at row
 rcases of_decide_eq_true row with outside|blocked|shape
 · exact False.elim (outside heroInside)
 · exact False.elim (WestRankHead11.source_unblocked head metadata (List.Subset.trans locksInside inside) blocked)
 · exact ⟨source,owner,metadata,shape⟩
theorem first_cut
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 {prior state dirs final pushes moves outcomes priorPushes priorMoves}
 (reached : Trace soko1_1.board soko1_1.initial prior state priorPushes priorMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤3)
 (good : OwnedCorral11.Good locks region state group) :
 Nonempty (FirstCut paid state group dirs final pushes moves outcomes) := by
 rcases first_cut_or_quiet logged group with found|quiet
 · exact found
 · have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   obtain ⟨i,_,selected⟩ := PairFirstCut11.quiet_good closed unique size quiet valid.1 groupUnique inside bounded good reached.holes_sublist.subset
   have actual := (logged.end_subset valid.1 group groupUnique inside).2
   have card := List.Nodup.length_le_of_subset (unique i) (List.Subset.trans selected actual)
   rw [size i] at card
   have conservation := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   rw [empty] at conservation
   change 18+0=final.boulders.length+16 at conservation
   omega
theorem useful
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 {prior state dirs final pushes moves outcomes priorPushes priorMoves}
 (reached : Trace soko1_1.board soko1_1.initial prior state priorPushes priorMoves)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤3)
 (good : OwnedCorral11.Good locks region state group)
 (zero : energy state final group outcomes=0)
 (cut : FirstCut paid state group dirs final pushes moves outcomes) :
 cut.actor.pushSource=some 292 ∧cut.direction=.north ∧cut.headOutcome=.push 292 (.stay 266) ∧
 (update (endGroup group cut.beforeOutcomes) cut.headOutcome).Perm [265,266,317] ∧
 ownPushes [317] cut.beforeOutcomes=0 := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have currentGood := PairFirstCut11.quiet_good closed unique size cut.before valid.1 groupUnique inside bounded good reached.holes_sublist.subset
 obtain ⟨i,heroInside,locksInside⟩ := currentGood
 have currentSelected := cut.before.logged.end_subset valid.1 group groupUnique inside
 have currentBound : (endGroup group cut.beforeOutcomes).length≤3 := Nat.le_trans (endGroup_length_le group cut.beforeOutcomes) bounded
 obtain ⟨source,owner,metadata,shape⟩ := head_shape i heroInside locksInside currentSelected.2 currentBound cut.headChecked cut.headPaid
 have currentReached := reached.append cut.before.logged.trace
 have currentValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant currentReached
 rcases shape with positive|⟨node,rfl,north⟩
 · have cost := exit_row currentValid currentSelected.1 currentSelected.2 cut.headChecked cut.headEffect ⟨source,owner,metadata,positive⟩
   have prefixNN := HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 3) valid group groupUnique inside bounded
   change 0≤energy state cut.middle group cut.beforeOutcomes at prefixNN
   have actual := step_boulders_nodup _ _ _ _ currentValid.1 cut.headChecked
   have nextUnique := GhostSubset.update_unique _ _ _ cut.headEffect actual _ currentSelected.1 currentSelected.2
   have nextInside := GhostSubset.update_subset _ _ _ cut.headEffect _ currentSelected.1 currentSelected.2
   have nextBound := Nat.le_trans (update_length (endGroup group cut.beforeOutcomes) cut.headOutcome) currentBound
   have afterValid := (groupCertificate 3).preserved _ _ _ currentValid cut.headChecked
   have afterNN := HeroLedger.Logged.energy_nonnegative cut.after (groupCertificate 3) afterValid _ nextUnique nextInside nextBound
   change 0≤energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at afterNN
   have split := energy_append state cut.middle final group cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
   have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
     (endGroup group cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
   change energy cut.middle final (endGroup group cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
     charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome+
     value cut.actor.state (update (endGroup group cut.beforeOutcomes) cut.headOutcome)-
     value cut.middle (endGroup group cut.beforeOutcomes)+
     energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
   rw [cut.outcomesEq] at zero
   omega
 · have nodeEq : i=⟨1,by decide⟩ := Fin.ext node
   have beforePerm := canonical i (endGroup group cut.beforeOutcomes) currentSelected.1 currentBound locksInside
   have specific : (endGroup group cut.beforeOutcomes).Perm [265,292,317] := by simpa only [nodeEq,locks] using beforePerm
   have target : pushTargets soko1_1.board 292 cut.direction=[266] := by rw [north];decide +kernel
   have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) currentReached.holes_sublist.subset
   have nextPerm := update_perm specific cut.headOutcome
   rw [headEq] at nextPerm
   have perm : (update (endGroup group cut.beforeOutcomes) cut.headOutcome).Perm [265,266,317] := by
     rw [headEq]
     exact nextPerm.trans (by decide +kernel)
   have markerMember : 317∈group := by
     obtain ⟨j,_,initialLocks⟩ := good
     have all : (List.finRange 4).all (fun j=>decide (317∈locks j))=true := by decide +kernel
     exact initialLocks (of_decide_eq_true (List.all_eq_true.mp all j (by simp)))
   have fixed := cut.before.fixed markerMember (fun _=>Or.inl rfl)
   exact ⟨metadata,north,headEq,perm,fixed⟩
#print axioms useful
end Owner1007.LowerElevator11
