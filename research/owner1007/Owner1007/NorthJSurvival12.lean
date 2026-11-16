import Owner1007.AfterJSurvivalDeep12
import Owner1007.NorthJSeven12
import Owner1007.NorthReserveCount12
namespace Owner1007.NorthJSurvival12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.AfterJ12 Owner1007.AfterJBound12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem firstJ_eight_or_survivor {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    (completed : Goal final) (kind : Fin 2)
    {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
    (shape : outcomes=before ++ headOutcome kind :: after)
    (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .south=some t)
    (effect : Matches middle t (headOutcome kind))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (i : Fin 5) (locksInside : NorthEvents12.locks i ⊆ endGroup NorthBound12.G before)
    (unchanged : ∀ small : List Cell, small ⊆ NorthEvents12.J → endGroup small before=small) :
    8≤energy p NorthBound12.G outcomes ∨
      (7≤energy p NorthBound12.G outcomes ∧ endGroup NorthBound12.G outcomes≠[]) := by
  have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
  have middleReached := NorthBound12.north_reached.append first.trace
  have middleUnique := middleReached.boulders_nodup (by decide +kernel)
  have oldInside := first.end_subset initialUnique NorthBound12.G (by decide +kernel) (by decide +kernel)
  have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
  have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
  have nextUnique := GhostSubset.update_unique middle t (headOutcome kind) effect nextActual
    (endGroup NorthBound12.G before) oldInside.1 oldInside.2
  have nextSubset := GhostSubset.update_subset middle t (headOutcome kind) effect
    (endGroup NorthBound12.G before) oldInside.1 oldInside.2
  have owner : startSource kind ∈ endGroup NorthBound12.G before := locksInside (source_inside kind i)
  have erased := GhostSubset.erase_subset locksInside (NorthEvents12.unique i) (startSource kind)
  have nextLocks : locks kind i ⊆ update (endGroup NorthBound12.G before) (headOutcome kind) := by
    simp only [headOutcome,update,move,if_pos owner,post]
    exact List.Subset.trans (activation kind i) (List.cons_subset_cons (startDest kind) erased)
  have heroNext : t.state.player=startSource kind :=
    matches_hero middle t (headOutcome kind) effect
  have nextHero : t.state.player∈region kind i := by
    rw [heroNext]
    change startSource kind∈NorthEvents12.region i ++ [startSource kind]
    exact List.mem_append_right _ (by simp)
  have later := AfterJSurvivalDeep12.cash_cases_survival last nextReached completed kind
    (update (endGroup NorthBound12.G before) (headOutcome kind)) nextUnique nextSubset i nextHero nextLocks
  change 4≤energy p (ordinary kind) after ∨
    6≤energy p (update (endGroup NorthBound12.G before) (headOutcome kind)) after ∨
    (5≤energy p (update (endGroup NorthBound12.G before) (headOutcome kind)) after ∧
      endGroup (update (endGroup NorthBound12.G before) (headOutcome kind)) after≠[]) at later
  have priorJ := unchanged NorthBound12.J (by decide +kernel)
  have prior318 := unchanged [318] (by decide +kernel)
  have wholeJ : energy p NorthBound12.J outcomes =
      ownSlack p NorthBound12.J before + 2 + energy p (ordinary kind) after := by
    rw [shape,energy_at_split,priorJ]
    have member := source_J kind
    simp only [headOutcome,projectedOutcome,if_pos member]
    change ownSlack p NorthBound12.J before + slack p (headOutcome kind) +
      energy p (update NorthBound12.J (headOutcome kind)) after =
      ownSlack p NorthBound12.J before + 2 + energy p (ordinary kind) after
    rw [first_price,energy_perm p (ordinary_after kind) after]
  have wholeG : energy p NorthBound12.G outcomes =
      ownSlack p NorthBound12.G before + 2 +
        energy p (update (endGroup NorthBound12.G before) (headOutcome kind)) after := by
    rw [shape,energy_at_split]
    simp only [headOutcome,projectedOutcome,if_pos owner]
    change ownSlack p NorthBound12.G before + slack p (headOutcome kind) +
      energy p (update (endGroup NorthBound12.G before) (headOutcome kind)) after =
      ownSlack p NorthBound12.G before + 2 +
      energy p (update (endGroup NorthBound12.G before) (headOutcome kind)) after
    rw [first_price]
  have nnJ := first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthBound12.J
  have nnG := first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthBound12.G
  change 0≤ownSlack p NorthBound12.J before at nnJ
  change 0≤ownSlack p NorthBound12.G before at nnG
  have bottom := NorthBound12.bottom_north_energy_two logged
  change 2≤energy p NorthBound12.BottomN outcomes at bottom
  have gSplit := logged.energy_split initialUnique p NorthBound12.J NorthBound12.BottomN
    (by decide +kernel) (by decide +kernel)
  change energy p NorthBound12.G outcomes =
    energy p NorthBound12.J outcomes + energy p NorthBound12.BottomN outcomes at gSplit
  rcases later with ordinaryFour | groupSix | ⟨groupFive,survives⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · apply Or.inr
    constructor
    · omega
    · rw[shape,endGroup_append]
      exact survives


#print axioms firstJ_eight_or_survivor
end Owner1007.NorthJSurvival12
