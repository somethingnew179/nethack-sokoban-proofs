import Owner1007.DeadCorridor12
import Owner1007.NorthBound12
import Owner1007.TokenCounting
namespace Owner1007.North318Bound12

open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem current_away : ∀ i, NorthEvents12.current i∉NorthEvents12.J := by decide +kernel
theorem current_member : ∀ i, NorthEvents12.current i∈NorthEvents12.locks i := by decide +kernel
theorem current_not318 : ∀ i, (318:Cell)∉[NorthEvents12.current i] := by decide +kernel
theorem current_for318 : ∀ i, ∀ hero∈NorthEvents12.region i,
    advance soko1_2.board hero .west=some 318 →
      NorthEvents12.current i∈DeadCorridor12.corridor := by decide +kernel

theorem singleton_complement (fixed token whole : List Cell) (current : Cell)
    (split : (fixed ++ token).Perm whole) (currentInside : current ∈ whole)
    (outside : current ∉ fixed) (small : token.length ≤ 1) : token=[current] := by
  have member : current ∈ token := by
    have both := split.mem_iff.mpr currentInside
    exact (List.mem_append.mp both).resolve_left outside
  cases token with
  | nil => simp only [List.not_mem_nil] at member
  | cons c rest =>
    have empty : rest=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at small; omega)
    rw [empty] at member ⊢
    have same : current=c := List.mem_singleton.mp member
    exact congrArg (fun n => [n]) same.symm

theorem first318_cases {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
    (shape : outcomes=before ++ .push 318 (.stay 317) :: after)
    (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .west=some t)
    (effect : Matches middle t (.push 318 (.stay 317)))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (i : Fin 5) (hero : middle.player∈NorthEvents12.region i)
    (locksInside : NorthEvents12.locks i ⊆ endGroup NorthBound12.G before)
    (unchanged : ∀ small : List Cell, small ⊆ NorthEvents12.J → endGroup small before=small) :
    5≤energy p NorthBound12.G outcomes ∧ endGroup [318] outcomes≠[] := by
  have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
  have middleReached := NorthBound12.north_reached.append first.trace
  have middleUnique := middleReached.boulders_nodup (by decide +kernel)
  have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
  have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
  have prior318 := unchanged [318] (by decide +kernel)
  have fixedWhole := unchanged NorthEvents12.J (fun _ h => h)
  have splitBefore := first.end_split initialUnique NorthEvents12.J [345]
    (by decide +kernel) (by decide +kernel)
  change (endGroup NorthEvents12.J before ++ endGroup [345] before).Perm
    (endGroup NorthBound12.G before) at splitBefore
  rw [fixedWhole] at splitBefore
  have small : (endGroup [345] before).length≤1 :=
    Nat.le_trans (endGroup_length_le [345] before) (by simp)
  have prior345 := singleton_complement NorthEvents12.J (endGroup [345] before)
    (endGroup NorthBound12.G before) (NorthEvents12.current i) splitBefore
    (locksInside (current_member i)) (current_away i) small
  obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
  have member := current_for318 i middle.player hero adjacent
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
  have ledger := survivor_energy p 345 outcomes survives345
  have debt : -p.boulder 345=2 := by decide +kernel
  rw [debt] at ledger
  simp only [Int.ofNat_eq_natCast] at ledger
  have bound345 : 2≤energy p [345] outcomes := by omega
  have bottomSplit := logged.energy_split initialUnique p [318] [345] (by decide +kernel) (by decide +kernel)
  change energy p NorthBound12.BottomN outcomes = energy p [318] outcomes + energy p [345] outcomes at bottomSplit
  have jNN := logged.energy_nonnegative Generated.soko1_2_potential_valid NorthBound12.J
  change 0≤energy p NorthBound12.J outcomes at jNN
  have gSplit := logged.energy_split initialUnique p NorthBound12.J NorthBound12.BottomN
    (by decide +kernel) (by decide +kernel)
  change energy p NorthBound12.G outcomes =
    energy p NorthBound12.J outcomes + energy p NorthBound12.BottomN outcomes at gSplit
  exact ⟨by omega,by rw [shape]; exact survives318⟩

#print axioms first318_cases
end Owner1007.North318Bound12

