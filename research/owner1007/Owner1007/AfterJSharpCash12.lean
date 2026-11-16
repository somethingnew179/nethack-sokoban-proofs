import Owner1007.AfterJTightCash12
import Owner1007.AfterMixedSeven12
import Owner1007.After236Seven12
namespace Owner1007.AfterJSharpCash12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.AfterJ12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

/-- An actual retained-264/290 continuation, not a custom start. -/
structure SidecarCut (initial : State) (group : List Cell) (final : State) (outcomes : List Outcome) where
 middle : State
 actor : Transition
 beforeDirs : List Dir
 beforePushes : Nat
 beforeMoves : Nat
 before : List Outcome
 afterDirs : List Dir
 afterPushes : Nat
 afterMoves : Nat
 after : List Outcome
 phase : Fin 5
 shape : outcomes=before++.push 291 (.stay 290)::after
 first : Logged soko1_2.board initial beforeDirs middle beforePushes beforeMoves before
 checked : step soko1_2.board middle .west=some actor
 effect : Matches middle actor (.push 291 (.stay 290))
 last : Logged soko1_2.board actor.state afterDirs final afterPushes afterMoves after
 hero : middle.player∈region 1 phase
 locks : AfterJ12.locks 1 phase⊆endGroup group before
 owner : (291:Cell)∈endGroup group before
 fixedBefore : ∀small : List Cell,small⊆fixed 1→endGroup small before=small

theorem cash_four_or_sidecar {state final dirs pushes moves outcomes history past pastMoves}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (kind : Fin 2)
 (group : List Cell) (gUnique : group.Nodup) (gSubset : group⊆state.boulders)
 (i : Fin 5) (hero : state.player∈region kind i) (inside : locks kind i⊆group)
 (cheap : energy p group outcomes≤6) :
 4≤energy p (ordinary kind) outcomes ∨(kind=1∧Nonempty (SidecarCut state group final outcomes)) := by
 obtain ⟨bd,bp,bm,before,middle,dir,t,source,ending,after,ad,ap,am,j,shape,first,checked,effect,last,
   heroOne,locksOne,owner,paid,unchanged,not318,not265,onlyOne⟩ :=
   AfterJTightCash12.split logged reached completed kind group gUnique gSubset i hero inside cheap
 have middleReached := reached.append first.trace
 have actual := reached.boulders_nodup (by decide +kernel)
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have selected := first.end_subset actual group gUnique gSubset
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push source ending) effect nextActual
   (endGroup group before) selected.1 selected.2
 have nextSubset := GhostSubset.update_subset middle t (.push source ending) effect
   (endGroup group before) selected.1 selected.2
 have budget : energy p group (before++.push source ending::after)≤6 := by rw [←shape];exact cheap
 rcases paid with ordinaryPaid|park|ring
 · obtain ⟨member,direction⟩ := ordinaryPaid
   have prior := unchanged (ordinary kind) (fun _ h=>List.mem_append_left _ h)
   rcases direction with ⟨choices,south⟩|⟨rfl,west⟩
   · subst dir
     rcases choices with rfl|rfl|rfl|rfl|rfl
     · have kindEq : kind=(1:Fin 2) :=
         (show ∀kind,(210:Cell)∈ordinary kind→kind=1 from by decide +kernel) kind member
       subst kind
       have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 210 .south=[236] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have deep := AfterMixedSeven12.after210_seven first checked effect last reached group gUnique gSubset j locksOne prior completed
       change 4≤energy p (ordinary 1) (before++.push 210 (.stay 236)::after) ∨
         7≤energy p group (before++.push 210 (.stay 236)::after) at deep
       rcases deep with ordinaryFour|seven
       · exact Or.inl (by simpa only [shape] using ordinaryFour)
       · omega
     · have kindEq : kind=(0:Fin 2) :=
         (show ∀kind,(236:Cell)∈ordinary kind→kind=0 from by decide +kernel) kind member
       subst kind
       have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 236 .south=[262] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have deep := After236Seven12.after236_seven first checked effect last reached group gUnique gSubset j locksOne prior completed
       change 4≤energy p (ordinary 0) (before++.push 236 (.stay 262)::after) ∨
         7≤energy p group (before++.push 236 (.stay 262)::after) at deep
       rcases deep with ordinaryFour|seven
       · exact Or.inl (by simpa only [shape] using ordinaryFour)
       · omega
     · have kindEq : kind=(0:Fin 2) :=
         (show ∀kind,(238:Cell)∈ordinary kind→kind=0 from by decide +kernel) kind member
       subst kind
       have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 238 .south=[264] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have deep := AfterMixedSeven12.after238_seven first checked effect last reached group gUnique gSubset j locksOne prior completed
       change 4≤energy p (ordinary 0) (before++.push 238 (.stay 264)::after) ∨
         7≤energy p group (before++.push 238 (.stay 264)::after) at deep
       rcases deep with ordinaryFour|seven
       · exact Or.inl (by simpa only [shape] using ordinaryFour)
       · omega
     · have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 264 .south=[290] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have bound := event_energy_le Generated.soko1_2_potential_valid (ordinary kind) first last (.push 264 (.stay 290))
       simp only [prior,projectedOutcome,if_pos member] at bound
       have price : slack p (.push 264 (.stay 290))=4 := by decide +kernel
       change slack p (.push 264 (.stay 290))≤energy p (ordinary kind) (before++.push 264 (.stay 290)::after) at bound
       rw [price] at bound
       exact Or.inl (by simpa only [shape] using bound)
     · exact False.elim (not265 rfl)
   · subst dir
     obtain ⟨kind,bound⟩ := kind
     have cases : kind=0∨kind=1 := by omega
     rcases cases with rfl|rfl
     · have blocked : ∀j : Fin 5,BlockedPush soko1_2.board (locks 0 j) 237 .west := by decide +kernel
       exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne selected.2) checked effect (blocked j))
     · have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 237 .west=[236] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have activation : ∀j : Fin 5,([210,236]:List Cell)⊆236::(locks 1 j).erase 237 := by decide +kernel
       have kept := CageFour12.shifted_inside (unique 1 j) locksOne owner (activation j)
       have future := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
         (update (endGroup group before) (.push 237 (.stay 236))) nextUnique nextSubset
         [210,236] RingAfter12.locked_pair (by decide +kernel) kept
       change 15≤energy p (update (endGroup group before) (.push 237 (.stay 236))) after at future
       have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
       change 0≤ownSlack p group before at prefixNN
       have price : slack p (.push 237 (.stay 236))=2 := by decide +kernel
       rw [energy_at_split] at budget
       simp only [projectedOutcome,if_pos owner,price] at budget
       omega
 · exact False.elim (not318 park.1)
 · obtain ⟨rfl,west⟩ := ring
   have kindEq := onlyOne rfl
   subst kind
   subst dir
   have same := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
     NorthEvents12.ring_activation (by decide +kernel) checked effect
   subst ending
   exact Or.inr ⟨rfl,⟨{
     middle:=middle,actor:=t,beforeDirs:=bd,beforePushes:=bp,beforeMoves:=bm,before:=before,
     afterDirs:=ad,afterPushes:=ap,afterMoves:=am,after:=after,phase:=j,shape:=shape,
     first:=first,checked:=checked,effect:=effect,last:=last,hero:=heroOne,locks:=locksOne,
     owner:=owner,fixedBefore:=unchanged }⟩⟩
#print axioms cash_four_or_sidecar
end Owner1007.AfterJSharpCash12
