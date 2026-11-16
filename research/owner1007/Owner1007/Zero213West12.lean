import Owner1007.Upper187ForcedSouth12
namespace Owner1007.Zero213West12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
abbrev p := Generated.soko1_2Potential
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem classification : ∀ hero∈soko1_2.board.floor,∀ dir∈allDirs,
 advance soko1_2.board hero dir=some 213→
 BlockedPush soko1_2.board [213] 213 dir∨dir=.west∨Upper187FirstGeometry12.priceTwo 213 dir := by decide +kernel
theorem support214 : ∀ hero∈soko1_2.board.floor,advance soko1_2.board hero .west=some 213→hero=214 := by decide +kernel
/-- Zero owned energy at213 forces an actual West push, hence player support214. -/
theorem first_west {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (zero : energy p [213] outcomes=0) :
 ∃ beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves,
 outcomes=before++.push 213 (.stay 212)::after ∧
 Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before ∧
 step soko1_2.board middle .west=some t ∧Matches middle t (.push 213 (.stay 212)) ∧
 Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
 ownPushes [213] before=0 ∧middle.player=214 := by
 have moved : 0<ownPushes [213] outcomes := by
   apply Nat.pos_of_ne_zero
   intro none
   have tag := no_push_unchanged [213] outcomes none
   have alive : endGroup [213] outcomes≠[] := by rw [tag];simp
   have ledger := survivor_energy p 213 outcomes alive
   have debt : -p.boulder 213=9 := by decide +kernel
   rw [debt] at ledger
   simp only [Int.ofNat_eq_natCast] at ledger
   omega
 obtain ⟨bd,bp,bm,before,middle,dir,t,source,ending,after,ad,ap,am,shape,first,checked,effect,last,stationary,member⟩ :=
   FirstOwnedPush.first_push logged [213] moved
 have same : source=213 := List.mem_singleton.mp member
 subst source
 have middleReached := reached.append first.trace
 have standing := step_player_clear soko1_2.board middle dir t checked
 have present : (213:Cell)∈middle.boulders := by cases ending <;> exact effect.1
 obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
 rcases classification middle.player standing.1 dir (Geometry.all_directions dir) adjacent with blocked|west|priced
 · exact False.elim (CageFour12.blocked_impossible (by simpa using present) checked effect blocked)
 · subst dir
   have sameEnding := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
     (show pushTargets soko1_2.board 213 .west=[212] by decide +kernel) (by decide +kernel) checked effect
   subst ending
   exact ⟨bd,bp,bm,before,middle,t,after,ad,ap,am,shape,first,checked,effect,last,stationary,
     support214 middle.player standing.1 adjacent⟩
 · have one := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset priced checked effect
   have lower := event_energy_le Generated.soko1_2_potential_valid [213] first last (.push 213 ending)
   have tag := no_push_unchanged [213] before stationary
   change slack p (projectedOutcome (endGroup [213] before) (.push 213 ending))≤energy p [213] (before++.push 213 ending::after) at lower
   rw [tag] at lower
   simp only [projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true] at lower
   rw [←shape,zero] at lower
   omega
#print axioms first_west
end Owner1007.Zero213West12
