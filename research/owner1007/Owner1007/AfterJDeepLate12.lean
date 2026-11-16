import Owner1007.AfterJDeepLeaves12
namespace Owner1007.AfterJDeepLate12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem after291_five
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .west=some t)
 (effect : Matches middle t (.push 291 (.stay 290)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (kind : Fin 2) (i : Fin 5) (inside : AfterJ12.locks kind i⊆endGroup group before)
 (owner : (291:Cell)∈endGroup group before)
 (heroBefore : middle.player∈AfterJ12.region kind i)
 (completed : Goal final) :
 5≤energy p group (before++(.push 291 (.stay 290))::after) := by
 have stateUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset stateUnique group unique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 291 (.stay 290)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 291 (.stay 290)) effect
   (endGroup group before) old.1 old.2
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have hero : t.state.player=291 := matches_hero middle t (.push 291 (.stay 290)) effect
 have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group before at prefixNN
 have price : slack p (.push 291 (.stay 290))=2 := by decide +kernel
 have later : 3≤energy p (update (endGroup group before) (.push 291 (.stay 290))) after := by
   obtain ⟨k,bound⟩ := kind
   have choices : k=0∨k=1 := by omega
   rcases choices with rfl|rfl
   · have activation : ∀ i : Fin 5, Residual29012.locks 0⊆290::(AfterJ12.locks 0 i).erase 291 := by decide +kernel
     have kept := CageFour12.shifted_inside (AfterJ12.unique 0 i) inside owner (activation i)
     have heroNext : t.state.player∈Residual29012.region 0 := by rw [hero]; decide +kernel
     have future := Residual290Any12.owned_energy_credit Residual29012.matrix last nextReached
       (update (endGroup group before) (.push 291 (.stay 290))) nextUnique nextSubset 0 heroNext kept
     change 5≤energy p (update (endGroup group before) (.push 291 (.stay 290))) after at future
     omega
   · have activation : ∀ i : Fin 5, Sidecar26412.locks 0⊆290::(AfterJ12.locks 1 i).erase 291 := by decide +kernel
     have kept := CageFour12.shifted_inside (AfterJ12.unique 1 i) inside owner (activation i)
     have heroNext : t.state.player∈Sidecar26412.region 0 := by rw [hero]; decide +kernel
     have future := Sidecar26412.energy_four last nextReached
       (update (endGroup group before) (.push 291 (.stay 290))) nextUnique nextSubset completed heroNext kept
     change 4≤energy p (update (endGroup group before) (.push 291 (.stay 290))) after at future
     omega
 rw [energy_at_split]
 simp only [projectedOutcome,if_pos owner,price]
 omega
#print axioms after291_five

theorem after318_seven
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .west=some t)
 (effect : Matches middle t (.push 318 (.stay 317)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (kind : Fin 2) (i : Fin 5) (inside : AfterJ12.locks kind i⊆endGroup group before)
 (owner : (318:Cell)∈endGroup group before)
 (heroBefore : middle.player∈AfterJ12.region kind i)
 (completed : Goal final) :
 7≤energy p group (before++(.push 318 (.stay 317))::after) := by
 have stateUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset stateUnique group unique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 318 (.stay 317)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 318 (.stay 317)) effect
   (endGroup group before) old.1 old.2
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have hero : t.state.player=318 := matches_hero middle t (.push 318 (.stay 317)) effect
 have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group before at prefixNN
 have price : slack p (.push 318 (.stay 317))=3 := by decide +kernel
 obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
 have facts : NorthEvents12.current i∈DeadCorridor12.corridor ∧
     4≤-p.boulder (NorthEvents12.current i) := by
   exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp
     (show (List.finRange 2).all (fun kind => (List.finRange 5).all (fun i =>
       (AfterJ12.region kind i).all (fun hero => decide
         (advance soko1_2.board hero .west=some 318 →
          NorthEvents12.current i∈DeadCorridor12.corridor ∧ 4≤-p.boulder (NorthEvents12.current i)))))=true by decide +kernel)
     kind (by simp)) i (by simp) |> fun h => List.all_eq_true.mp h middle.player heroBefore) adjacent
 have present : (317:Cell)∈t.state.boulders := by rw [effect.2]; simp
 have survives := DeadCorridor12.trapped_survives last present nextReached.holes_sublist.subset
   (NorthEvents12.current i) facts.1
 have ledger := survivor_energy p (NorthEvents12.current i) after survives
 have nonnegative : (0:Int)≤Int.ofNat (ownPushes [NorthEvents12.current i] after) := Int.ofNat_nonneg _
 have currentEnergy : 4≤energy p [NorthEvents12.current i] after := by omega
 have currentBefore : NorthEvents12.current i∈endGroup group before :=
   inside ((show ∀ kind : Fin 2, ∀ i : Fin 5, NorthEvents12.current i∈AfterJ12.locks kind i from by decide +kernel) kind i)
 have different : NorthEvents12.current i≠318 :=
   (show ∀ i : Fin 5, NorthEvents12.current i≠318 from by decide +kernel) i
 have currentNext : [NorthEvents12.current i]⊆update (endGroup group before) (.push 318 (.stay 317)) := by
   simp only [update,move,if_pos owner,post]
   intro c found
   have same : c=NorthEvents12.current i := List.mem_singleton.mp found
   subst c
   exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne different).mpr currentBefore)
 have mono := last.energy_mono Generated.soko1_2_potential_valid nextActual
   [NorthEvents12.current i] (update (endGroup group before) (.push 318 (.stay 317)))
   (by simp) nextUnique (List.Subset.trans currentNext nextSubset) nextSubset currentNext
 change energy p [NorthEvents12.current i] after≤energy p (update (endGroup group before) (.push 318 (.stay 317))) after at mono
 have later : 4≤energy p (update (endGroup group before) (.push 318 (.stay 317))) after := by omega
 rw [energy_at_split]
 simp only [projectedOutcome,if_pos owner,price]
 omega
#print axioms after318_seven
end Owner1007.AfterJDeepLate12
