import Owner1007.RingEleven12
import Owner1007.After290Eleven12
import Owner1007.RingUpperElevenStrong12
import Owner1007.T291ElevenStrong12
import Owner1007.Cage239Eleven12
import Owner1007.Cage212RetainedEleven12
import Owner1007.Quad290Nine12
namespace Owner1007.RingThirteen12.Cage
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def cageIndex (i : Fin 4) : Fin 10 := if PreCage12.ringS i=213 then 0 else 4
theorem shift_inside : ∀ i, PreCage12.ringTag i=239 → Owner1007.Cage23912.locks (cageIndex i)⊆262::(PreCage12.ringLocks i).erase 263 := by decide +kernel
theorem hero_inside : ∀ i, (263 : Cell)∈Owner1007.Cage23912.region (cageIndex i) := by decide +kernel
theorem source_inside : ∀ i, (263 : Cell)∈PreCage12.ringLocks i := by decide +kernel


theorem head_tag : ∀ i : Fin 4, ∀ hero∈PreCage12.ringRegion i,
 advance soko1_2.board hero .west=some 263 → PreCage12.ringTag i=239 := by decide +kernel

theorem actual_main_sources : ∀ i : Fin 4, ∀ hero∈PreCage12.ringRegion i,
 ∀ dir∈allDirs, ∀ source∈PreRingHeads12.sources,
 advance soko1_2.board hero dir=some source → RingCut12.paid source dir → source=263 ∨ source=290 := by decide +kernel

theorem energy_thirteen
    {state middle final : State} {t : Transition}
    {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
    {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
    (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .west=some t)
    (effect : Matches middle t (.push 263 (.stay 262)))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
    (i : Fin 4) (inside : PreCage12.ringLocks i⊆endGroup group before)
    (heroBefore : middle.player∈PreCage12.ringRegion i)
    (completed : Goal final) :
    13≤energy p group (before++(.push 263 (.stay 262))::after) := by
  have stateUnique := reached.boulders_nodup (by decide +kernel)
  have old := first.end_subset stateUnique group unique subset
  have middleReached := reached.append first.trace
  have middleUnique := middleReached.boulders_nodup (by decide +kernel)
  have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
  have nextUnique := GhostSubset.update_unique middle t (.push 263 (.stay 262)) effect nextActual
    (endGroup group before) old.1 old.2
  have nextSubset := GhostSubset.update_subset middle t (.push 263 (.stay 262)) effect
    (endGroup group before) old.1 old.2
  have owner : (263 : Cell)∈endGroup group before := inside (source_inside i)
  obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
  have tag := head_tag i middle.player heroBefore adjacent
  have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
  have later : 11≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after := by
    by_cases side : PreCage12.ringS i=213
    · have activation : ∀ i, PreCage12.ringTag i=239 → PreCage12.ringS i=213 →
        Cage23912.locks 0⊆262::(PreCage12.ringLocks i).erase 263 := by decide +kernel
      have kept := CageFour12.shifted_inside (PreCage12.ring_unique i) inside owner (activation i tag side)
      have hero : t.state.player∈Cage23912.region 0 := by
        rw [matches_hero middle t (.push 263 (.stay 262)) effect]; decide +kernel
      exact Cage239Eleven12.energy_eleven last nextReached
        (update (endGroup group before) (.push 263 (.stay 262))) nextUnique nextSubset completed hero kept
    · have activation : ∀ i, PreCage12.ringTag i=239 → PreCage12.ringS i≠213 →
        Cage212RetainedEleven12.locks (Cage212RetainedEleven12.normal 0)⊆262::(PreCage12.ringLocks i).erase 263 := by decide +kernel
      have kept := CageFour12.shifted_inside (PreCage12.ring_unique i) inside owner (activation i tag side)
      have hero : t.state.player∈Cage212RetainedEleven12.region (Cage212RetainedEleven12.normal 0) := by
        rw [matches_hero middle t (.push 263 (.stay 262)) effect]; decide +kernel
      exact Cage212RetainedEleven12.energy_eleven last nextReached
        (update (endGroup group before) (.push 263 (.stay 262))) nextUnique nextSubset completed 0 hero kept
  have one : (2 : Int)≤slack p (.push 263 (.stay 262)) := by decide +kernel
  have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
  change 0≤ownSlack p group before at prefixNN
  rw [energy_at_split]
  simp only [projectedOutcome,if_pos owner]
  omega
#print axioms energy_thirteen
end Owner1007.RingThirteen12.Cage

namespace Owner1007.RingThirteen12.T239
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem head_stage : ∀ i : Fin 4, ∀ hero∈PreCage12.ringRegion i,
 advance soko1_2.board hero .south=some 239 →
 BlockedPush soko1_2.board (PreCage12.ringLocks i) 239 .south ∨ i=3 := by decide +kernel
theorem activation : PreCage12.ringLocks 1⊆265::(PreCage12.ringLocks 3).erase 239 := by decide +kernel
theorem hero : (239:Cell)∈PreCage12.ringRegion 1 := by decide +kernel
theorem after_south239_thirteen
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (.push 239 (.stay 265)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 4) (inside : PreCage12.ringLocks i⊆endGroup group before)
 (heroBefore : middle.player∈PreCage12.ringRegion i)
 (completed : Goal final) :
 13≤energy p group (before++(.push 239 (.stay 265))::after) := by
 have stateUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset stateUnique group gUnique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
 have stage : i=3 := by
   rcases head_stage i middle.player heroBefore adjacent with blocked | stage
   · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans inside old.2) checked effect blocked)
   · exact stage
 subst i
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 239 (.stay 265)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 239 (.stay 265)) effect
   (endGroup group before) old.1 old.2
 have owner : (239:Cell)∈endGroup group before := inside (by decide +kernel)
 have kept := CageFour12.shifted_inside (PreCage12.ring_unique 3) inside owner activation
 have heroNext : t.state.player∈PreCage12.ringRegion 1 := by
   rw [matches_hero middle t (.push 239 (.stay 265)) effect]
   exact hero
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have later := RingEleven12.ring_energy_eleven last nextReached
   (update (endGroup group before) (.push 239 (.stay 265))) nextUnique nextSubset completed heroNext kept
 change 11≤energy p (update (endGroup group before) (.push 239 (.stay 265))) after at later
 have one : (2:Int)≤slack p (.push 239 (.stay 265)) := by decide +kernel
 have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group before at prefixNN
 rw [energy_at_split]
 simp only [projectedOutcome,if_pos owner]
 omega
#print axioms after_south239_thirteen
end Owner1007.RingThirteen12.T239


namespace Owner1007.RingThirteen12.After
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def cageIndex (i : Fin 4) : Fin 4 := i
theorem shift_inside : ∀ i, After29012.locks (cageIndex i)⊆289::(PreCage12.ringLocks i).erase 290 := by decide +kernel
theorem hero_inside : ∀ i, (290 : Cell)∈After29012.region (cageIndex i) := by decide +kernel
theorem source_inside : ∀ i, (290 : Cell)∈PreCage12.ringLocks i := by decide +kernel


theorem energy_thirteen
    {state middle final : State} {t : Transition}
    {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
    {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
    (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .west=some t)
    (effect : Matches middle t (.push 290 (.stay 289)))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
    (i : Fin 4) (inside : PreCage12.ringLocks i⊆endGroup group before)
    (completed : Goal final) :
    13≤energy p group (before++(.push 290 (.stay 289))::after) := by
  have stateUnique := reached.boulders_nodup (by decide +kernel)
  have old := first.end_subset stateUnique group unique subset
  have middleReached := reached.append first.trace
  have middleUnique := middleReached.boulders_nodup (by decide +kernel)
  have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
  have nextUnique := GhostSubset.update_unique middle t (.push 290 (.stay 289)) effect nextActual
    (endGroup group before) old.1 old.2
  have nextSubset := GhostSubset.update_subset middle t (.push 290 (.stay 289)) effect
    (endGroup group before) old.1 old.2
  have owner : (290 : Cell)∈endGroup group before := inside (source_inside i)
  have kept := CageFour12.shifted_inside (PreCage12.ring_unique i) inside owner (shift_inside i)
  have hero : t.state.player∈After29012.region (cageIndex i) := by
    rw [matches_hero middle t (.push 290 (.stay 289)) effect]
    exact hero_inside i
  have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
  have later := After290Eleven12.energy_eleven last nextReached
    (update (endGroup group before) (.push 290 (.stay 289))) nextUnique nextSubset completed hero kept
  change 11≤energy p (update (endGroup group before) (.push 290 (.stay 289))) after at later
  have one : (2 : Int)≤slack p (.push 290 (.stay 289)) := by decide +kernel
  have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
  change 0≤ownSlack p group before at prefixNN
  rw [energy_at_split]
  simp only [projectedOutcome,if_pos owner]
  omega
#print axioms energy_thirteen
end Owner1007.RingThirteen12.After


namespace Owner1007.RingThirteen12.Upper
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def upperIndex (i : Fin 4) : Fin 3 := if PreCage12.ringTag i=265 then 0 else 1
theorem shift_inside : ∀ i, PreCage12.ringS i=212 →
 RingUpper12.locks (upperIndex i)⊆161::(PreCage12.ringLocks i).erase 187 := by decide +kernel
theorem hero_inside : ∀ i, (187:Cell)∈RingUpper12.region (upperIndex i) := by decide +kernel
theorem source_inside : ∀ i, (187:Cell)∈PreCage12.ringLocks i := by decide +kernel
theorem head_s : ∀ i : Fin 4, ∀ hero∈PreCage12.ringRegion i,
 advance soko1_2.board hero .north=some 187 → PreCage12.ringS i=212 := by decide +kernel

theorem energy_thirteen
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .north=some t)
 (effect : Matches middle t (.push 187 (.stay 161)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 4) (inside : PreCage12.ringLocks i⊆endGroup group before)
 (heroBefore : middle.player∈PreCage12.ringRegion i) (completed : Goal final) :
 13≤energy p group (before++(.push 187 (.stay 161))::after) := by
 have stateUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset stateUnique group gUnique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 187 (.stay 161)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 187 (.stay 161)) effect
   (endGroup group before) old.1 old.2
 obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
 have stage := head_s i middle.player heroBefore adjacent
 have owner : (187:Cell)∈endGroup group before := inside (source_inside i)
 have kept := CageFour12.shifted_inside (PreCage12.ring_unique i) inside owner (shift_inside i stage)
 have heroNext : t.state.player∈RingUpper12.region (upperIndex i) := by
   rw [matches_hero middle t (.push 187 (.stay 161)) effect]
   exact hero_inside i
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have later := RingUpperElevenStrong12.energy_eleven last nextReached
   (update (endGroup group before) (.push 187 (.stay 161))) nextUnique nextSubset completed heroNext kept
 change 11≤energy p (update (endGroup group before) (.push 187 (.stay 161))) after at later
 have one : (2:Int)≤slack p (.push 187 (.stay 161)) := by decide +kernel
 have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group before at prefixNN
 rw [energy_at_split]
 simp only [projectedOutcome,if_pos owner]
 omega
#print axioms energy_thirteen
end Owner1007.RingThirteen12.Upper

namespace Owner1007.RingThirteen12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem ring_energy_thirteen
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 4}
 (hero : state.player∈PreCage12.ringRegion i) (inside : PreCage12.ringLocks i⊆group) :
 13≤energy p group outcomes := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good PreCage12.ring_closed PreCage12.ring_unique
   logged reached group gUnique subset hero inside with event|terminal
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
     obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
     have cases := RingSharpHeads12.classification j middle.player heroBefore dir source
       (PreRingHeads12.source_cases source dir pays) adjacent pays
     have keep (dest : Cell) (small : List Cell) (smallShift : small⊆dest::(PreCage12.ringLocks j).erase source) :
        small⊆update (endGroup group before) (.push source (.stay dest)) :=
       CageFour12.shifted_inside (PreCage12.ring_unique j) locksOne owner smallShift
     rcases cases with blocked | cage | far | upper | sWest | tSouth | tBack | square
     · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne oldGroup.2) checked effect blocked)
     · obtain ⟨rfl,rfl⟩ := cage
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       rw [shape]
       have bound := Cage.energy_thirteen first checked effect last reached group gUnique subset j locksOne heroBefore completed
       change 13≤energy p group (before++(.push 263 (.stay 262))::after) at bound
       omega
     · obtain ⟨rfl,rfl⟩ := far
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 290 .west=[289] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       rw [shape]
       exact After.energy_thirteen first checked effect last reached group gUnique subset j locksOne completed
     · obtain ⟨rfl,rfl⟩ := upper
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       rw [shape]
       exact Upper.energy_thirteen first checked effect last reached group gUnique subset j locksOne heroBefore completed
     · obtain ⟨rfl,rfl⟩ := sWest
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have activation : ∀ j, Quad29012.locks 0⊆211::(PreCage12.ringLocks j).erase 212 := by decide +kernel
       have kept := keep 211 (Quad29012.locks 0) (activation j)
       have heroNext : t.state.player∈Quad29012.region 0 := by
         rw [matches_hero middle t (.push 212 (.stay 211)) effect]
         decide +kernel
       have qActual := List.Subset.trans kept nextSubset
       have quad := Quad290Nine12.energy_nine last nextReached (Quad29012.locks 0)
         (Quad29012.unique 0) qActual completed heroNext (fun _ h=>h)
       change 9≤energy p (Quad29012.locks 0) after at quad
       have upShift : ∀ j, CageLedger12.Upper⊆211::(PreCage12.ringLocks j).erase 212 := by decide +kernel
       have upInside := keep 211 CageLedger12.Upper (upShift j)
       have upActual := List.Subset.trans upInside nextSubset
       have upper := RightEnergy12.raw_group_energy last nextReached CageLedger12.Upper
         (by decide +kernel) upActual completed
       have bonus : RightEnergy12.cert.bonus t.state.player
           (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by
         rw [matches_hero middle t (.push 212 (.stay 211)) effect]; decide +kernel
       rw [bonus] at upper
       change 2≤energy p CageLedger12.Upper after at upper
       have sum := TwoReserves12.add_le_energy last Generated.soko1_2_potential_valid nextActual
         CageLedger12.Upper (Quad29012.locks 0) (update (endGroup group before) (.push 212 (.stay 211)))
         (by decide +kernel) nextUnique nextSubset (List.append_subset.mpr ⟨upInside,kept⟩)
       change energy p CageLedger12.Upper after+energy p (Quad29012.locks 0) after≤
         energy p (update (endGroup group before) (.push 212 (.stay 211))) after at sum
       have later : 11≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after := by omega
       have one : (2:Int)≤slack p (.push 212 (.stay 211)) := by decide +kernel
       rw [shape,energy_at_split]
       simp only [projectedOutcome,if_pos owner]
       omega
     · obtain ⟨rfl,rfl⟩ := tSouth
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       rw [shape]
       exact T291ElevenStrong12.after_south265_thirteen first checked effect last reached group gUnique subset j locksOne heroBefore completed
     · obtain ⟨rfl,rfl⟩ := tBack
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 239 .south=[265] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       rw [shape]
       have bound := T239.after_south239_thirteen first checked effect last reached group gUnique subset j locksOne heroBefore completed
       change 13≤energy p group (before++(.push 239 (.stay 265))::after) at bound
       omega
     · have reserve (dest : Cell) (targets : pushTargets soko1_2.board source dir=[dest])
         (clear : dest∉soko1_2.initial.holes)
         (shift : [186,187,212,213]⊆dest::(PreCage12.ringLocks j).erase source) :
         13≤energy p group outcomes := by
         have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
           targets clear checked effect
         subst ending
         have kept := keep dest [186,187,212,213] shift
         have later := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
           (update (endGroup group before) (.push source (.stay dest))) nextUnique nextSubset
           [186,187,212,213] CageLedger12.locked_middle_square (by decide +kernel) kept
         change debtOf p [186,187,212,213]≤energy p (update (endGroup group before) (.push source (.stay dest))) after at later
         have amount : (13:Int)≤debtOf p [186,187,212,213] := by decide +kernel
         have nn := logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
         change 0≤slack p (.push source (.stay dest)) at nn
         rw [shape,energy_at_split]
         simp only [projectedOutcome,if_pos owner]
         omega
       rcases square with ⟨rfl,rfl,shift⟩ | ⟨rfl,rfl,shift⟩
       · exact reserve 213 (by decide +kernel) (by decide +kernel) shift
       · exact reserve 212 (by decide +kernel) (by decide +kernel) shift
 · obtain ⟨j,hero,locksOne⟩ := terminal
   have finalInside := logged.end_subset actualUnique group gUnique subset
   have count := List.Nodup.length_le_of_subset (PreCage12.ring_unique j) (List.Subset.trans locksOne finalInside.2)
   rw [PreCage12.ring_size j] at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms ring_energy_thirteen
end Owner1007.RingThirteen12

