import Owner1007.North31823112
import Owner1007.AfterJDeepLate12
namespace Owner1007.NorthAfterJPark23112
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.North318Bound12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem bottom_cases {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
    (shape : outcomes=before ++ .push 318 (.stay 317) :: after)
    (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .west=some t)
    (effect : Matches middle t (.push 318 (.stay 317)))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (kind : Fin 2) (i : Fin 5) (hero : middle.player∈AfterJ12.region kind i)
    (prior318 : endGroup [318] before=[318])
    (prior345 : endGroup [345] before=[NorthEvents12.current i]) :
    7≤energy p NorthBound12.BottomN outcomes ∧ endGroup [318] outcomes≠[] ∧ endGroup [345] outcomes≠[] := by
  have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
  have middleReached := NorthBound12.north_reached.append first.trace
  have middleUnique := middleReached.boulders_nodup (by decide +kernel)
  have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
  have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
  obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
  have facts : NorthEvents12.current i∈DeadCorridor12.corridor ∧
      4≤-p.boulder (NorthEvents12.current i) := by
    have rows : (List.finRange 2).all (fun kind=>(List.finRange 5).all (fun i=>
      (AfterJ12.region kind i).all (fun hero=>decide (advance soko1_2.board hero .west=some 318→
       NorthEvents12.current i∈DeadCorridor12.corridor∧4≤-p.boulder (NorthEvents12.current i)))))=true := by decide +kernel
    have row:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp rows kind (by simp)) i (by simp)) middle.player hero
    exact of_decide_eq_true row adjacent
  have member:=facts.1
  have shapeNext : t.state.boulders=317::middle.boulders.erase 318 := by
    simpa only [Matches] using congrArg (fun h : Transition => h.state.boulders) effect.2
  have present : (317:Cell)∈t.state.boulders := by rw [shapeNext]; simp
  have survivesCurrent := DeadCorridor12.trapped_survives last present nextReached.holes_sublist.subset
    (NorthEvents12.current i) member
  have survives345 : endGroup [345] outcomes≠[] := by
    rw [shape,endGroup_append,prior345]
    simpa only [endGroup,update,move,if_neg (current_not318 i)] using survivesCurrent
  have survives318 := NorthBound12.after_park_survives last nextActual 318 317 present
    NorthBound12.locked317 before prior318
  have bound318 := event_energy_le Generated.soko1_2_potential_valid [318] first last (.push 318 (.stay 317))
  simp only [prior318,projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true] at bound318
  change slack p (.push 318 (.stay 317))≤energy p [318] (before ++ .push 318 (.stay 317) :: after) at bound318
  have price : slack p (.push 318 (.stay 317))=3 := by decide +kernel
  rw [price,←shape] at bound318
  have currentDebt := facts.2
  have allSurvives : endGroup [345] (before++ .push 318 (.stay 317)::after)≠[] := by
    rw [←shape]
    exact survives345
  have stronger := SurvivorPrefix12.quantitative345 first (.push 318 (.stay 317)::after)
    (NorthEvents12.current i) prior345 currentDebt allSurvives
  have bound345 : 4≤energy p [345] outcomes := by rw [shape]; exact stronger
  have bottomSplit := logged.energy_split initialUnique p [318] [345] (by decide +kernel) (by decide +kernel)
  change energy p NorthBound12.BottomN outcomes = energy p [318] outcomes + energy p [345] outcomes at bottomSplit
  exact ⟨by omega,by rw [shape]; exact survives318,survives345⟩

#print axioms bottom_cases
end Owner1007.NorthAfterJPark23112
