import Owner1007.RingUpper12
import Owner1007.Quad29012

namespace Owner1007.RingUpper12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem energy_six
 (matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true)
 (classification : ∀ (i : Fin 3) (hero : Cell), hero∈region i → ∀ dir source, source∈sources → advance soko1_2.board hero dir=some source → paid source dir → classified i source dir)
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 3}
 (hero : state.player∈region i) (inside : locks i⊆group) :
 6≤energy p group outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
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
     have cases := classification j middle.player heroBefore dir source (sources_paid source dir pays) adjacent pays
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

     rcases cases with blocked | gate | quad | cage | far | foreign | expensive
     · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne oldGroup.2) checked effect blocked)
     · obtain ⟨rfl,rfl,gate⟩ := gate
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 186 .west=[185] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 185 [158,159,185,210] gate
       have heroNext : t.state.player∈PriceTrap12Gate.region 0 := by
         rw [matches_hero middle t (.push 186 (.stay 185)) effect]
         decide +kernel
       have later := CageLedger12.gate_owned_nineteen last nextReached
         (update (endGroup group before) (.push 186 (.stay 185))) nextUnique nextSubset heroNext kept
       change 19≤energy p (update (endGroup group before) (.push 186 (.stay 185))) after at later
       have bound := reserve 0 19 oneNN later
       omega
     · obtain ⟨rfl,rfl,quad⟩ := quad
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 211 (Quad29012.locks 0) quad
       have heroNext : t.state.player∈Quad29012.region 0 := by
         rw [matches_hero middle t (.push 212 (.stay 211)) effect]
         decide +kernel
       have later := Quad29012.energy_seven last nextReached
         (update (endGroup group before) (.push 212 (.stay 211))) nextUnique nextSubset completed heroNext kept
       change 7≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after at later
       have bound := reserve 0 7 oneNN later
       omega
     · obtain ⟨rfl,rfl,stage⟩ := cage
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 262 (Post18712.locks (cageIndex j)) (cage_activation j stage)
       have heroNext : t.state.player∈Post18712.region (cageIndex j) := by
         rw [matches_hero middle t (.push 263 (.stay 262)) effect]
         exact cage_hero j stage
       have later := Post187Four12.energy_four last nextReached
         (update (endGroup group before) (.push 263 (.stay 262))) nextUnique nextSubset completed heroNext kept
       change 4≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
       have one : (2:Int)≤slack p (.push 263 (.stay 262)) := by decide +kernel
       exact reserve 2 4 one later
     · obtain ⟨rfl,rfl⟩ := far
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 290 .west=[289] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have pairAfter := keep 289 [186,212] (pair_after290 j)
       have ringAfter := keep 289 (RingAfter12.locks true 0) (ring_after290 j)
       have heroRing : t.state.player∈TwoReserves12.region true := by
         rw [matches_hero middle t (.push 290 (.stay 289)) effect]
         decide +kernel
       have heroPair : t.state.player∈VerticalPair12.region false 0 := by
         rw [matches_hero middle t (.push 290 (.stay 289)) effect]
         decide +kernel
       have later := TwoReserves12.pair_ring_four false true last nextReached
         (update (endGroup group before) (.push 290 (.stay 289))) nextUnique nextSubset completed
         heroRing heroPair pairAfter ringAfter
       change 4≤energy p (update (endGroup group before) (.push 290 (.stay 289))) after at later
       have one : (2:Int)≤slack p (.push 290 (.stay 289)) := by decide +kernel
       exact reserve 2 4 one later
     · obtain ⟨notPair,notRing,priced⟩ := foreign
       have pairBefore := List.Subset.trans (pairInside j) locksOne
       have pairAfter := update_mono ([186,212]:List Cell) (endGroup group before)
         (by decide +kernel) pairBefore (.push source ending)
       simp only [update,move,if_neg notPair] at pairAfter
       have ringBefore := List.Subset.trans (ringInside j) locksOne
       have ringAfter := update_mono (RingCut12.locks 0) (endGroup group before)
         (by decide +kernel) ringBefore (.push source ending)
       simp only [update,move,if_neg notRing] at ringAfter
       have heroRing : t.state.player∈TwoReserves12.region false := by
         rw [matches_hero middle t (.push source ending) effect]
         exact foreign_ring_hero source (sources_paid source dir pays) notPair notRing
       have heroPair : t.state.player∈VerticalPair12.region false 0 := by
         rw [matches_hero middle t (.push source ending) effect]
         exact foreign_pair_hero source (sources_paid source dir pays) notPair notRing
       have later := TwoReserves12.pair_ring_four false false last nextReached
         (update (endGroup group before) (.push source ending)) nextUnique nextSubset completed
         heroRing heroPair pairAfter ringAfter
       change 4≤energy p (update (endGroup group before) (.push source ending)) after at later
       have one := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset priced checked effect
       exact reserve 2 4 one later
     · have one := push_effect_price p soko1_2.initial.holes 6 middleReached.holes_sublist.subset expensive checked effect
       have bound := event_energy_le Generated.soko1_2_potential_valid group first last (.push source ending)
       simp only [projectedOutcome,if_pos owner] at bound
       rw [shape]
       change slack p (.push source ending)≤energy p group (before++(.push source ending)::after) at bound
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
#print axioms energy_six
end Owner1007.RingUpper12

