import Owner1007.Upper187StartQuiet12
import Owner1007.FirstOwnedPush
namespace Owner1007.Upper187StartForcedSouth12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.Upper187Start12 (U Others)
abbrev p := Generated.soko1_2Potential
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem direction_cases : ∀ hero∈soko1_2.board.floor,∀ dir∈allDirs,
 advance soko1_2.board hero dir=some 187→
 BlockedPush soko1_2.board [187] 187 dir∨dir=.north∨dir=.south := by decide +kernel
/-- A tight Upper budget forces the original187 South and gives it zero whole energy. -/
theorem all_consumed {initial : State} {initialDirs : List Dir} {initialPushes initialMoves : Nat}
 (initialReached : Trace soko1_2.board soko1_2.initial initialDirs initial initialPushes initialMoves)
 (uInside : U⊆initial.boulders) {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board initial dirs final pushes moves outcomes)
 (small : energy p U outcomes≤2) :
 ∀ cell∈U, endGroup [cell] outcomes=[] := by
 intro cell member
 apply Classical.byContradiction
 intro alive
 have singleton : [cell]⊆U := by simpa using member
 have actualUnique := initialReached.boulders_nodup (by decide +kernel)
 have mono := logged.energy_mono Generated.soko1_2_potential_valid actualUnique
   [cell] U (by simp) (by decide +kernel) (List.Subset.trans singleton uInside) uInside singleton
 change energy p [cell] outcomes≤energy p U outcomes at mono
 have ledger := survivor_energy p cell outcomes alive
 have minDebt : ∀ cell∈U, (8:Int)≤-p.boulder cell := by decide +kernel
 have positive := minDebt cell member
 simp only [Int.ofNat_eq_natCast] at ledger
 have nn := Int.ofNat_nonneg (ownPushes [cell] outcomes)
 omega

theorem forced_south
 {initial : State} {initialDirs : List Dir} {initialPushes initialMoves : Nat}
 (initialReached : Trace soko1_2.board soko1_2.initial initialDirs initial initialPushes initialMoves)
 (uInside : U⊆initial.boulders) (heroInitial : initial.player∈Upper187FirstGeometry12.region 0)
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board initial dirs final pushes moves outcomes)
 (small : energy p U outcomes≤2) :
 ∃ beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves,
 outcomes=before++.push 187 (.stay 213)::after ∧
 Logged soko1_2.board initial beforeDirs middle beforePushes beforeMoves before ∧
 step soko1_2.board middle .south=some t ∧Matches middle t (.push 187 (.stay 213)) ∧
 Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
 ownPushes [187] before=0 ∧energy p [187] outcomes=0 := by
 have gone := all_consumed initialReached uInside logged small 187 (by decide +kernel)
 have moved : 0<ownPushes [187] outcomes := by
   apply Nat.pos_of_ne_zero
   intro zero
   have tag := no_push_unchanged [187] outcomes zero
   rw [tag] at gone
   cases gone
 obtain ⟨bd,bp,bm,before,middle,dir,t,source,ending,after,ad,ap,am,shape,first,checked,effect,last,stationary,member⟩ :=
   FirstOwnedPush.first_push logged [187] moved
 have same : source=187 := List.mem_singleton.mp member
 subst source
 have reached := initialReached.append first.trace
 have standing := step_player_clear soko1_2.board middle dir t checked
 have present : (187:Cell)∈middle.boulders := by cases ending <;> exact effect.1
 obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
 rcases direction_cases middle.player standing.1 dir (Geometry.all_directions dir) adjacent with blocked|north|south
 · exact False.elim (CageFour12.blocked_impossible (by simpa using present) checked effect blocked)
 · subst dir
   have sameEnding := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel) (by decide +kernel) checked effect
   subst ending
   have lower := Upper187Start12.first_north_four initialReached uInside heroInitial first checked effect last stationary
   change 4≤energy p U (before++.push 187 (.stay 161)::after) at lower
   rw [←shape] at lower
   omega
 · subst dir
   have sameEnding := push_effect_singleton soko1_2.initial.holes reached.holes_sublist.subset
     (show pushTargets soko1_2.board 187 .south=[213] by decide +kernel) (by decide +kernel) checked effect
   subst ending
   have zero := Upper187StartQuiet12.south_original_energy_zero initialReached uInside heroInitial first checked effect last stationary (by simpa only [←shape] using small)
   change energy p [187] (before++.push 187 (.stay 213)::after)=0 at zero
   rw [←shape] at zero
   exact ⟨bd,bp,bm,before,middle,t,after,ad,ap,am,shape,first,checked,effect,last,stationary,zero⟩
#print axioms forced_south
end Owner1007.Upper187StartForcedSouth12
