import Owner1007.North318BoundPlus12
namespace Owner1007.Park318Prefix12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
abbrev p := Generated.soko1_2Potential
/-- The corridor trap works after arbitrary earlier payments in other tokens. -/
theorem cases_seven {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
 (shape : outcomes=before ++ .push 318 (.stay 317) :: after)
 (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .west=some t)
 (effect : Matches middle t (.push 318 (.stay 317)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (current : Cell) (tag345 : endGroup [345] before=[current])
 (member : current∈DeadCorridor12.corridor) (different : current≠318)
 (currentDebt : 4≤-p.boulder current) (prior318 : endGroup [318] before=[318]) :
 7≤energy p NorthBound12.G outcomes ∧ endGroup [318] outcomes≠[] ∧ endGroup [345] outcomes≠[] := by
  have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
  have middleReached := NorthBound12.north_reached.append first.trace
  have middleUnique := middleReached.boulders_nodup (by decide +kernel)
  have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
  have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
  have shapeNext : t.state.boulders=317::middle.boulders.erase 318 := by
    simpa only [Matches] using congrArg (fun h : Transition => h.state.boulders) effect.2
  have present : (317:Cell)∈t.state.boulders := by rw [shapeNext]; simp
  have survivesCurrent := DeadCorridor12.trapped_survives last present nextReached.holes_sublist.subset
    current member
  have absent : (318:Cell)∉[current] := by simp [Ne.symm different]
  have survives345 : endGroup [345] outcomes≠[] := by
    rw [shape,endGroup_append,tag345]
    simpa only [endGroup,update,move,if_neg absent] using survivesCurrent
  have survives318 := NorthBound12.after_park_survives last nextActual 318 317 present
    NorthBound12.locked317 before prior318
  have bound318 := event_energy_le Generated.soko1_2_potential_valid [318] first last (.push 318 (.stay 317))
  simp only [prior318,projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true] at bound318
  change slack p (.push 318 (.stay 317))≤energy p [318] (before ++ .push 318 (.stay 317) :: after) at bound318
  have price : slack p (.push 318 (.stay 317))=3 := by decide +kernel
  rw [price,←shape] at bound318
  have allSurvives : endGroup [345] (before++ .push 318 (.stay 317)::after)≠[] := by
    rw [←shape]
    exact survives345
  have stronger := SurvivorPrefix12.quantitative345 first (.push 318 (.stay 317)::after)
    current tag345 currentDebt allSurvives
  have bound345 : 4≤energy p [345] outcomes := by rw [shape]; exact stronger
  have bottomSplit := logged.energy_split initialUnique p [318] [345] (by decide +kernel) (by decide +kernel)
  change energy p NorthBound12.BottomN outcomes = energy p [318] outcomes + energy p [345] outcomes at bottomSplit
  have jNN := logged.energy_nonnegative Generated.soko1_2_potential_valid NorthBound12.J
  change 0≤energy p NorthBound12.J outcomes at jNN
  have gSplit := logged.energy_split initialUnique p NorthBound12.J NorthBound12.BottomN
    (by decide +kernel) (by decide +kernel)
  change energy p NorthBound12.G outcomes =
    energy p NorthBound12.J outcomes + energy p NorthBound12.BottomN outcomes at gSplit
  exact ⟨by omega,by rw [shape]; exact survives318,survives345⟩
#print axioms cases_seven
end Owner1007.Park318Prefix12
