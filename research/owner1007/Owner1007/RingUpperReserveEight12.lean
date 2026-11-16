import Owner1007.RingUpperSharp12
import Owner1007.FarUpperBound12
namespace Owner1007.RingUpperReserveEight12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.RingUpper12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem far_inside : ∀ i, FarUpper12.locks i⊆289::(RingUpper12.locks i).erase 290 := by decide +kernel
theorem far_hero : ∀ i, (290:Cell)∈FarUpper12.region i := by decide +kernel
theorem energy_eight
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 3}
 (hero : state.player∈region i) (inside : locks i⊆group) :
 8≤energy p group outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ RingUpper12.matrix
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locksOne,pays⟩ := event.split
   have middleReached := reached.append first.trace
   have middleUnique := middleReached.boulders_nodup (by decide +kernel)
   have oldGroup := first.end_subset actualUnique group gUnique subset
   have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
   have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual
     (endGroup group before) oldGroup.1 oldGroup.2
   have nextSubset := GhostSubset.update_subset middle t outcome effect
     (endGroup group before) oldGroup.1 oldGroup.2
   have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
   have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
   change 0≤ownSlack p group before at prefixNN
   cases outcome with
   | walk target => exact False.elim pays
   | push source ending =>
     obtain ⟨owner,pays⟩ := pays
     obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
     have cases := RingUpperSharp12.classification j middle.player heroBefore dir (Geometry.all_directions dir) source (sources_paid source dir pays) adjacent pays
     have oneNN := logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
     have keep (dest : Cell) (small : List Cell) (smallShift : small⊆dest::(locks j).erase source) :
        small⊆update (endGroup group before) (.push source (.stay dest)) :=
       CageFour12.shifted_inside (unique j) locksOne owner smallShift
     have reserve (a b : Int) (one : a≤slack p (.push source ending))
       (later : b≤energy p (update (endGroup group before) (.push source ending)) after) :
       a+b≤energy p group outcomes := by
       rw [shape,energy_at_split]
       simp only [projectedOutcome,if_pos owner]
       omega

     rcases cases with blocked | gateCase | high | sWest | main | far | tSouth | tBack | trap | extra
     · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne oldGroup.2) checked effect blocked)
     · obtain ⟨rfl,rfl⟩ := gateCase
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 186 .west=[185] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := keep 185 ([158,159,185,210]) (RingUpperSharp12.gate j)
       have heroNext : t.state.player∈PriceTrap12Gate.region 0 := by
         rw [matches_hero middle t (.push 186 (.stay 185)) effect]
         decide +kernel
       have later := CageLedger12.gate_owned_nineteen last nextReached (update (endGroup group before) (.push 186 (.stay 185))) nextUnique nextSubset heroNext kept
       change 19≤energy p (update (endGroup group before) (.push 186 (.stay 185))) after at later
       have bound := reserve 2 19 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := high
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 161 .north=[135] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have later := last.energy_nonnegative Generated.soko1_2_potential_valid (update (endGroup group before) (.push 161 (.stay 135)))
       change 0≤energy p (update (endGroup group before) (.push 161 (.stay 135))) after at later
       have bound := reserve 8 0 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := sWest
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := keep 211 (Quad29012.locks 0) (RingUpperSharp12.quad j)
       have heroNext : t.state.player∈Quad29012.region 0 := by
         rw [matches_hero middle t (.push 212 (.stay 211)) effect]
         decide +kernel
       have later := Quad29012.energy_seven last nextReached (update (endGroup group before) (.push 212 (.stay 211))) nextUnique nextSubset completed heroNext kept
       change 7≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after at later
       have bound := reserve 2 7 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := main
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := keep 262 (Post187Seven12.locks 0) (RingUpperSharp12.seven j)
       have heroNext : t.state.player∈Post187Seven12.region 0 := by
         rw [matches_hero middle t (.push 263 (.stay 262)) effect]
         decide +kernel
       have later := Post187Seven12.owned_energy_seven last nextReached (update (endGroup group before) (.push 263 (.stay 262))) nextUnique nextSubset (by decide +kernel) heroNext kept
       change 7≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
       have bound := reserve 2 7 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := far
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 290 .west=[289] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := keep 289 (FarUpper12.locks j) (far_inside j)
       have heroNext : t.state.player∈FarUpper12.region j := by
         rw [matches_hero middle t (.push 290 (.stay 289)) effect]
         exact far_hero j
       have later := FarUpper12.energy_six FarUpper12.matrix FarUpper12.classification last nextReached (update (endGroup group before) (.push 290 (.stay 289))) nextUnique nextSubset completed heroNext kept
       change 6≤energy p (update (endGroup group before) (.push 290 (.stay 289))) after at later
       have bound := reserve 2 6 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := tSouth
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := keep 291 (PostUpper29112.locks 0) (RingUpperSharp12.t291 j)
       have heroNext : t.state.player∈PostUpper29112.region 0 := by
         rw [matches_hero middle t (.push 265 (.stay 291)) effect]
         decide +kernel
       have later := PostUpper29112.energy_six last nextReached (update (endGroup group before) (.push 265 (.stay 291))) nextUnique nextSubset completed heroNext kept
       change 6≤energy p (update (endGroup group before) (.push 265 (.stay 291))) after at later
       have bound := reserve 2 6 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := tBack
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 239 .south=[265] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := keep 265 (RingUpper12.locks 0) (RingUpperSharp12.reset j)
       have heroNext : t.state.player∈RingUpper12.region 0 := by
         rw [matches_hero middle t (.push 239 (.stay 265)) effect]
         decide +kernel
       have later := RingUpper12.energy_six RingUpper12.matrix RingUpper12.classification last nextReached (update (endGroup group before) (.push 239 (.stay 265))) nextUnique nextSubset completed heroNext kept
       change 6≤energy p (update (endGroup group before) (.push 239 (.stay 265))) after at later
       have bound := reserve 2 6 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := trap
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 213 .north=[187] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := keep 187 [161,187] (RingUpperSharp12.trapped j)
       have later := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
         (update (endGroup group before) (.push 213 (.stay 187))) nextUnique nextSubset [161,187] RingUpperSharp12.locked161187 (by decide +kernel) kept
       change debtOf p [161,187]≤energy p (update (endGroup group before) (.push 213 (.stay 187))) after at later
       have amount : debtOf p [161,187]=15 := by decide +kernel
       rw [amount] at later
       have bound := reserve 2 15 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := extra
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 213 .south=[239] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := keep 239 (RingUpper12.locks 1) (RingUpperSharp12.extra_reset j)
       have heroNext : t.state.player∈RingUpper12.region 1 := by
         rw [matches_hero middle t (.push 213 (.stay 239)) effect]; decide +kernel
       have later := RingUpper12.energy_six RingUpper12.matrix RingUpper12.classification last nextReached
         (update (endGroup group before) (.push 213 (.stay 239))) nextUnique nextSubset completed heroNext kept
       change 6≤energy p (update (endGroup group before) (.push 213 (.stay 239))) after at later
       have bound := reserve 2 6 (by decide +kernel) later
       omega
 · obtain ⟨j,hero,locksOne⟩ := terminal
   have finalInside := logged.end_subset actualUnique group gUnique subset
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans locksOne finalInside.2)
   have size : ∀ j, (locks j).length=12 := by decide +kernel
   rw [size j] at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms energy_eight
end Owner1007.RingUpperReserveEight12
