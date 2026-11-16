import Owner1007.RingPrepared12
import Owner1007.TwoReserves12
namespace Owner1007.T29112
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def spos (i : Fin 2) : Cell := if i.val=0 then 213 else 212
def locks (i : Fin 2) : List Cell := [108,158,159,186,187,spos i,291,210,237,238,263,290]
def region (i : Fin 2) : List Cell :=
 if i.val=0 then [239,264,265] else
 [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,264,265,270,271,272,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
def sources : List Cell := [108,158,159,186,187,213,212,291,210,237,238,263,290]
def paid (source : Cell) (_ : Dir) : Prop := source∈sources
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
def priceSix (source : Cell) (dir : Dir) : Prop :=
 ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧
 (6:Int)≤1+Generated.soko1_2Potential.boulder dest-Generated.soko1_2Potential.boulder source
def classified (i : Fin 2) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (locks i) source dir ∨
 (source=263 ∧ dir=.west) ∨ (source=187 ∧ dir=.north) ∨
 (source=212 ∧ dir=.west) ∨ (source=291 ∧ dir=.north) ∨
 (source=238 ∧ dir=.north ∧ [186,187,212,213]⊆212::(locks i).erase source) ∨ priceSix source dir
instance (i : Fin 2) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by
 unfold classified priceSix
 infer_instance
theorem classifier_check : ∀ i, ∀ hero∈region i, ∀ dir∈allDirs, ∀ source∈sources,
 advance soko1_2.board hero dir=some source → classified i source dir := by decide +kernel
theorem classification (i : Fin 2) (hero : Cell) (heroIn : hero∈region i) (dir source)
 (sourceIn : source∈sources) (adjacent : advance soko1_2.board hero dir=some source) :
 classified i source dir := classifier_check i hero heroIn dir (Geometry.all_directions dir) source sourceIn adjacent
def cageIndex (i : Fin 2) : Fin 10 := if i.val=0 then 0 else 4
def oldIndex (i : Fin 2) : Fin 4 := if i.val=0 then 0 else 1
theorem cage_activation : ∀ i, Cage10.locks (cageIndex i)⊆262::(locks i).erase 263 := by decide +kernel
theorem cage_hero : ∀ i, (263:Cell)∈Cage10.region (cageIndex i) := by decide +kernel
theorem ring_activation : ∀ i, PreCage12.ringLocks (oldIndex i)⊆265::(locks i).erase 291 := by decide +kernel
theorem ring_hero : ∀ i, (291:Cell)∈PreCage12.ringRegion (oldIndex i) := by decide +kernel
theorem upper_activation : ∀ i, CageLedger12.Upper⊆211::(locks i).erase 212 := by decide +kernel
theorem ring_after187 : ∀ i, RingCut12.locks 0⊆161::(locks i).erase 187 := by decide +kernel
theorem ring_after212 : ∀ i, RingCut12.locks 0⊆211::(locks i).erase 212 := by decide +kernel
theorem pair_activation : ∀ i, ([186,212]:List Cell)⊆locks i → [186,212]⊆161::(locks i).erase 187 := by decide +kernel
theorem pair_before : ∀ i, i.val=1 → ([186,212]:List Cell)⊆locks i := by decide +kernel
theorem upper_only : ∀ i hero, hero∈region i → advance soko1_2.board hero .north=some 187 → i.val=1 := by decide +kernel
end Owner1007.T29112

namespace Owner1007.T29112
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem energy_six {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 2}
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
     have cases := classification j middle.player heroBefore dir source pays adjacent
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
     rcases cases with blocked | main | upper | sWest | tNorth | square | expensive
     · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne oldGroup.2) checked effect blocked)
     · obtain ⟨rfl,rfl⟩ := main
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 262 (Cage10.locks (cageIndex j)) (cage_activation j)
       have heroNext : t.state.player∈Cage10.region (cageIndex j) := by
         rw [matches_hero middle t (.push 263 (.stay 262)) effect]
         exact cage_hero j
       have later := CageFour12.energy_four last nextReached
         (update (endGroup group before) (.push 263 (.stay 262))) nextUnique nextSubset completed heroNext kept
       change 4≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
       have one : (2:Int)≤slack p (.push 263 (.stay 262)) := by decide +kernel
       exact reserve 2 4 one later
     · obtain ⟨rfl,rfl⟩ := upper
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have stage := upper_only j middle.player heroBefore adjacent
       have pair := pair_activation j (pair_before j stage)
       have pairInside := keep 161 [186,212] pair
       have ringInside := keep 161 (RingCut12.locks 0) (ring_after187 j)
       have heroRing : t.state.player∈TwoReserves12.region false := by
         rw [matches_hero middle t (.push 187 (.stay 161)) effect]
         decide +kernel
       have heroPair : t.state.player∈VerticalPair12.region false 0 := by
         rw [matches_hero middle t (.push 187 (.stay 161)) effect]
         decide +kernel
       have later := TwoReserves12.pair_ring_four false false last nextReached
         (update (endGroup group before) (.push 187 (.stay 161))) nextUnique nextSubset completed
         heroRing heroPair pairInside ringInside
       change 4≤energy p (update (endGroup group before) (.push 187 (.stay 161))) after at later
       have one : (2:Int)≤slack p (.push 187 (.stay 161)) := by decide +kernel
       exact reserve 2 4 one later
     · obtain ⟨rfl,rfl⟩ := sWest
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have upperInside := keep 211 CageLedger12.Upper (upper_activation j)
       have ringInside := keep 211 (RingCut12.locks 0) (ring_after212 j)
       have heroRing : t.state.player∈TwoReserves12.region false := by
         rw [matches_hero middle t (.push 212 (.stay 211)) effect]
         decide +kernel
       have bonus : RightEnergy12.cert.bonus t.state.player
         (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by
         rw [matches_hero middle t (.push 212 (.stay 211)) effect]
         exact CageLedger12.upper_bonus 212 (by decide +kernel)
       have later := TwoReserves12.upper_ring_four false last nextReached
         (update (endGroup group before) (.push 212 (.stay 211))) nextUnique nextSubset completed
         heroRing bonus upperInside ringInside
       change 4≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after at later
       have one : (2:Int)≤slack p (.push 212 (.stay 211)) := by decide +kernel
       exact reserve 2 4 one later
     · obtain ⟨rfl,rfl⟩ := tNorth
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 291 .north=[265] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 265 (PreCage12.ringLocks (oldIndex j)) (ring_activation j)
       have heroNext : t.state.player∈PreCage12.ringRegion (oldIndex j) := by
         rw [matches_hero middle t (.push 291 (.stay 265)) effect]
         exact ring_hero j
       have later := RingPrepared12.ring_energy_six last nextReached
         (update (endGroup group before) (.push 291 (.stay 265))) nextUnique nextSubset completed heroNext kept
       change 6≤energy p (update (endGroup group before) (.push 291 (.stay 265))) after at later
       have bound := reserve 0 6 oneNN later
       omega
     · obtain ⟨rfl,rfl,square⟩ := square
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 238 .north=[212] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 212 [186,187,212,213] square
       have later := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
         (update (endGroup group before) (.push 238 (.stay 212))) nextUnique nextSubset
         [186,187,212,213] CageLedger12.locked_middle_square (by decide +kernel) kept
       have bound := reserve 0 (debtOf p [186,187,212,213]) oneNN later
       have amount : (6:Int)≤debtOf p [186,187,212,213] := by decide +kernel
       omega
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
end Owner1007.T29112

namespace Owner1007.T29112
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def entryIndex (i : Fin 4) : Fin 2 := if PreCage12.ringS i=213 then 0 else 1
theorem entry_inside : ∀ i, PreCage12.ringTag i=265 →
 locks (entryIndex i)⊆291::(PreCage12.ringLocks i).erase 265 := by decide +kernel
theorem entry_hero : ∀ i, (265:Cell)∈region (entryIndex i) := by decide +kernel
theorem entry_source : ∀ i, PreCage12.ringTag i=265 → (265:Cell)∈PreCage12.ringLocks i := by decide +kernel
theorem entry_tag : ∀ i : Fin 4, ∀ hero∈PreCage12.ringRegion i,
 advance soko1_2.board hero .south=some 265 → PreCage12.ringTag i=265 := by decide +kernel

theorem after_south265_eight
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (.push 265 (.stay 291)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 4) (inside : PreCage12.ringLocks i⊆endGroup group before)
 (heroBefore : middle.player∈PreCage12.ringRegion i)
 (completed : Goal final) :
 8≤energy p group (before++(.push 265 (.stay 291))::after) := by
 have stateUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset stateUnique group gUnique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 265 (.stay 291)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 265 (.stay 291)) effect
   (endGroup group before) old.1 old.2
 obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
 have tag := entry_tag i middle.player heroBefore adjacent
 have owner : (265:Cell)∈endGroup group before := inside (entry_source i tag)
 have kept := CageFour12.shifted_inside (PreCage12.ring_unique i) inside owner (entry_inside i tag)
 have heroNext : t.state.player∈region (entryIndex i) := by
   rw [matches_hero middle t (.push 265 (.stay 291)) effect]
   exact entry_hero i
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have later := energy_six last nextReached
   (update (endGroup group before) (.push 265 (.stay 291))) nextUnique nextSubset completed heroNext kept
 change 6≤energy p (update (endGroup group before) (.push 265 (.stay 291))) after at later
 have one : (2:Int)≤slack p (.push 265 (.stay 291)) := by decide +kernel
 have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group before at prefixNN
 rw [energy_at_split]
 simp only [projectedOutcome,if_pos owner]
 omega
#print axioms after_south265_eight
end Owner1007.T29112

