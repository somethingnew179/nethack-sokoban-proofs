import Owner1007.T29112
import Owner1007.RingEight12
import Owner1007.PostUpper29112
import Owner1007.Cage212Nine12
namespace Owner1007.T291Eight12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def locks (_ : Fin 1) : List Cell := T29112.locks 1
def region (_ : Fin 1) : List Cell := T29112.region 1
def paid (source : Cell) (_ : Dir) : Prop := source∈locks 0
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
def classified (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (locks 0) source dir ∨
 (source=263 ∧ dir=.west) ∨ (source=187 ∧ dir=.north) ∨
 (source=212 ∧ dir=.west) ∨ (source=291 ∧ dir=.north) ∨
 (source=291 ∧ dir=.south)
instance (source : Cell) (dir : Dir) : Decidable (classified source dir) := by unfold classified;infer_instance
theorem check : ∀ hero∈region 0, ∀ dir∈allDirs, ∀ source∈locks 0,
 advance soko1_2.board hero dir=some source→classified source dir := by decide +kernel
theorem cage_shift : ∀ i, Cage21212.locks (Cage212Nine12.normal 0)⊆262::(locks i).erase 263 := by decide +kernel
theorem cage_hero : (263:Cell)∈Cage21212.region (Cage212Nine12.normal 0) := by decide +kernel
theorem upper_shift : ∀ i, PostUpper29112.locks 0⊆161::(locks i).erase 187 := by decide +kernel
theorem upper_hero : (187:Cell)∈PostUpper29112.region 0 := by decide +kernel
theorem quad_shift : ∀ i, Quad29012.locks 0⊆211::(locks i).erase 212 := by decide +kernel
theorem quad_hero : (212:Cell)∈Quad29012.region 0 := by decide +kernel
theorem return_shift : ∀ i, PreCage12.ringLocks 1⊆265::(locks i).erase 291 := by decide +kernel
theorem return_hero : (291:Cell)∈PreCage12.ringRegion 1 := by decide +kernel
theorem south_upper : ∀ i, CageLedger12.Upper⊆317::(locks i).erase 291 := by decide +kernel
theorem south_bonus : RightEnergy12.cert.bonus 291
 (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by decide +kernel
theorem entry_stage : ∀ i hero,hero∈PreCage12.ringRegion i→advance soko1_2.board hero .south=some 265→i=1 := by decide +kernel
theorem entry_shift : locks 0⊆291::(PreCage12.ringLocks 1).erase 265 := by decide +kernel
theorem entry_hero : (265:Cell)∈region 0 := by decide +kernel
end Owner1007.T291Eight12


namespace Owner1007.T291Eight12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem energy_eight
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 1}
 (hero : state.player∈region i) (inside : locks i⊆group) :
 8≤energy p group outcomes := by
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
     have cases := check middle.player heroBefore dir (Geometry.all_directions dir) source pays adjacent
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

     rcases cases with blocked | main | upper | sWest | tNorth | south
     · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne oldGroup.2) checked effect blocked)
     · obtain ⟨rfl,rfl⟩ := main
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 262 (Cage21212.locks (Cage212Nine12.normal 0)) (cage_shift j)
       have heroNext : t.state.player∈Cage21212.region (Cage212Nine12.normal 0) := by
         rw [matches_hero middle t (.push 263 (.stay 262)) effect]
         exact cage_hero
       have later := Cage212Nine12.energy_nine last nextReached
         (update (endGroup group before) (.push 263 (.stay 262))) nextUnique nextSubset completed 0 heroNext kept
       change 9≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
       have one : (2:Int)≤slack p (.push 263 (.stay 262)) := by decide +kernel
       have bound := reserve 2 9 one later
       omega
     · obtain ⟨rfl,rfl⟩ := upper
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 161 (PostUpper29112.locks 0) (upper_shift j)
       have heroNext : t.state.player∈PostUpper29112.region 0 := by
         rw [matches_hero middle t (.push 187 (.stay 161)) effect]
         exact upper_hero
       have later := PostUpper29112.energy_six last nextReached
         (update (endGroup group before) (.push 187 (.stay 161))) nextUnique nextSubset completed heroNext kept
       change 6≤energy p (update (endGroup group before) (.push 187 (.stay 161))) after at later
       have one : (2:Int)≤slack p (.push 187 (.stay 161)) := by decide +kernel
       have bound := reserve 2 6 one later
       omega
     · obtain ⟨rfl,rfl⟩ := sWest
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 211 (Quad29012.locks 0) (quad_shift j)
       have heroNext : t.state.player∈Quad29012.region 0 := by
         rw [matches_hero middle t (.push 212 (.stay 211)) effect]
         exact quad_hero
       have later := Quad29012.energy_seven last nextReached
         (update (endGroup group before) (.push 212 (.stay 211))) nextUnique nextSubset completed heroNext kept
       change 7≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after at later
       have one : (2:Int)≤slack p (.push 212 (.stay 211)) := by decide +kernel
       have bound := reserve 2 7 one later
       omega
     · obtain ⟨rfl,rfl⟩ := tNorth
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 291 .north=[265] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 265 (PreCage12.ringLocks 1) (return_shift j)
       have heroNext : t.state.player∈PreCage12.ringRegion 1 := by
         rw [matches_hero middle t (.push 291 (.stay 265)) effect]
         exact return_hero
       have later := RingEight12.ring_energy_eight last nextReached
         (update (endGroup group before) (.push 291 (.stay 265))) nextUnique nextSubset completed heroNext kept
       change 8≤energy p (update (endGroup group before) (.push 291 (.stay 265))) after at later
       have one : (0:Int)≤slack p (.push 291 (.stay 265)) := by decide +kernel
       have bound := reserve 0 8 one later
       omega
     · obtain ⟨rfl,rfl⟩ := south
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 291 .south=[317] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have upperAfter := keep 317 CageLedger12.Upper (south_upper j)
       have upperActual := List.Subset.trans upperAfter nextSubset
       have bonus : RightEnergy12.cert.bonus t.state.player
         (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by
         rw [matches_hero middle t (.push 291 (.stay 317)) effect]
         exact south_bonus
       have upperBound := RightEnergy12.raw_group_energy last nextReached CageLedger12.Upper
         (by decide +kernel) upperActual completed
       rw [bonus] at upperBound
       change 2≤energy p CageLedger12.Upper after at upperBound
       have mono := last.energy_mono Generated.soko1_2_potential_valid nextActual
         CageLedger12.Upper (update (endGroup group before) (.push 291 (.stay 317)))
         (by decide +kernel) nextUnique upperActual nextSubset upperAfter
       have later : (2:Int)≤energy p (update (endGroup group before) (.push 291 (.stay 317))) after := Int.le_trans upperBound mono
       have one : (7:Int)≤slack p (.push 291 (.stay 317)) := by decide +kernel
       have bound := reserve 7 2 one later
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
end Owner1007.T291Eight12


namespace Owner1007.T291Eight12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem after_south265_ten
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
 10≤energy p group (before++(.push 265 (.stay 291))::after) := by
 have stateUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset stateUnique group gUnique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
 have stage : i=1 := entry_stage i middle.player heroBefore adjacent
 subst i
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 265 (.stay 291)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 265 (.stay 291)) effect
   (endGroup group before) old.1 old.2
 have owner : (265:Cell)∈endGroup group before := inside (by decide +kernel)
 have kept := CageFour12.shifted_inside (PreCage12.ring_unique 1) inside owner entry_shift
 have heroNext : t.state.player∈region 0 := by
   rw [matches_hero middle t (.push 265 (.stay 291)) effect]
   exact entry_hero
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have later := energy_eight last nextReached
   (update (endGroup group before) (.push 265 (.stay 291))) nextUnique nextSubset completed heroNext kept
 change 8≤energy p (update (endGroup group before) (.push 265 (.stay 291))) after at later
 have one : (2:Int)≤slack p (.push 265 (.stay 291)) := by decide +kernel
 have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group before at prefixNN
 rw [energy_at_split]
 simp only [projectedOutcome,if_pos owner]
 omega

#print axioms after_south265_ten
end Owner1007.T291Eight12
