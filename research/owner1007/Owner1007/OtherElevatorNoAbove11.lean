import Owner1007.LowerElevator11Geometry
import Owner1007.LowerElevator11Proof
import Owner1007.Upper216Eight11
namespace Owner1007.OtherElevatorNoAbove11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def G : List Cell := [266,292,317]
theorem no_upper {history state past pastMoves dirs middle pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs middle pushes moves outcomes)
 (inside : G⊆state.boulders)
 (good : OwnedCorral11.Good LowerElevator11.locks LowerElevator11.region state G)
 (zero : energy state middle G outcomes=0)
 (stationary : ownPushes [266] outcomes=0) (hero : middle.player=213) : False := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 rcases first_cut_or_quiet (paid:=LowerElevator11.paid) logged G with found|quiet
 ·obtain ⟨cut⟩ := found
  obtain ⟨metadata,north,headEq,_,_⟩ := LowerElevator11.useful LowerElevator11.closed reached G
    (by decide) inside (by decide) good zero cut
  have beforeZero : ownPushes [266] cut.beforeOutcomes=0 := by
   rw [cut.outcomesEq,ownPushes_append] at stationary
   omega
  have tag := no_push_unchanged [266] cut.beforeOutcomes beforeZero
  have selected := (cut.before.logged.end_subset valid.1 [266] (by decide) (by intro c h;have same:=List.mem_singleton.mp h;subst c;exact inside (by decide))).2
  have present : 266∈cut.middle.boulders := selected (by rw [tag];simp)
  have checked : step soko1_1.board cut.middle .north=some cut.actor := by simpa only [north] using cut.headChecked
  have effect : Matches cut.middle cut.actor (.push 292 (.stay 266)) := by simpa only [headEq] using cut.headEffect
  obtain ⟨result,_,push⟩ := effect_push_data checked effect
  obtain ⟨dest,adjacent,_,_,clear⟩ := (push_first_clear _ _ _ _ _ push).2
  have same : dest=266 := Option.some.inj (adjacent.symm.trans (show advance soko1_1.board 292 .north=some 266 by decide +kernel))
  exact clear (same.symm ▸ present)
 ·obtain ⟨i,member,_⟩ := Upper216Eight11.quiet_good_any LowerElevator11.closed LowerElevator11.unique quiet
    valid.1 (by decide) inside good reached.holes_sublist.subset
  have excluded : ∀i,(213:Cell)∉LowerElevator11.region i := by decide +kernel
  rw [hero] at member
  exact excluded i member
#print axioms no_upper
end Owner1007.OtherElevatorNoAbove11
