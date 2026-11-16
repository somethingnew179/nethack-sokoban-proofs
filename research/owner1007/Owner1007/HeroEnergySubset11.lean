import Owner1007.HeroEnergyTrace11
namespace Owner1007.Hero315Frame11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

theorem selected_complement (small big : List Cell) (smallUnique : small.Nodup)
 (bigUnique : big.Nodup) (subset : small⊆big) :
 (small ++ big.filter (fun c => !decide (c∈small))).Perm big := by
 let keep : Cell → Bool := fun c => decide (c∈small)
 have filteredUnique : (big.filter keep).Nodup := bigUnique.filter _
 have same : (big.filter keep).Perm small := by
   apply (List.perm_ext_iff_of_nodup filteredUnique smallUnique).mpr
   intro cell
   constructor
   · intro member
     have row := List.mem_filter.mp member
     exact of_decide_eq_true row.2
   · intro member
     apply List.mem_filter.mpr
     exact ⟨subset member,by simpa only [keep,decide_eq_true_eq] using member⟩
 exact (same.symm.append_right _).trans (List.filter_append_perm keep big)

/-- Subsets of initial identities carry at most the energy of their selected whole,
also at arbitrary reached intermediate states and through all hole phases. -/
theorem energy_subset {state final : State} {history dirs : List Dir}
 {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (small big : List Cell) (smallUnique : small.Nodup) (bigUnique : big.Nodup)
 (subset : small⊆big) (inside : big⊆state.boulders) (bounded : big.length≤18) :
 energy state final small outcomes≤energy state final big outcomes := by
 let rest := big.filter (fun c => !decide (c∈small))
 have perm : (small++rest).Perm big := selected_complement small big smallUnique bigUnique subset
 have unique : (small++rest).Nodup := perm.nodup_iff.mpr bigUnique
 have bothInside : small++rest⊆state.boulders := fun _ h => inside (perm.mem_iff.mp h)
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have split := HeroLedger.Logged.energy_split logged valid.1 weightAt NetHack.Soko11Hero315.holeWeight
   small rest unique bothInside
 change energy state final (small++rest) outcomes = energy state final small outcomes +
   energy state final rest outcomes at split
 have same := energy_perm perm state final outcomes
 have restUnique : rest.Nodup := (List.nodup_append.mp unique).2.1
 have restInside : rest⊆state.boulders := fun _ h => bothInside (List.mem_append_right _ h)
 have restSize : rest.length≤18 := Nat.le_trans (List.length_filter_le _ _) bounded
 have nonnegative := HeroLedger.Logged.energy_nonnegative logged (groupCertificate 18) valid
   rest restUnique restInside restSize
 change 0≤energy state final rest outcomes at nonnegative
 omega

#print axioms selected_complement
#print axioms energy_subset
end Owner1007.Hero315Frame11
