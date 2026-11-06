import NetHack.Soko11PairCandidate321.Phase00
import NetHack.Soko11PairCandidate321.Phase01
import NetHack.Soko11PairCandidate321.Phase02
import NetHack.Soko11PairCandidate321.Phase03
import NetHack.Soko11PairCandidate321.Phase04
import NetHack.Soko11PairCandidate321.Phase05
import NetHack.Soko11PairCandidate321.Phase06
import NetHack.Soko11PairCandidate321.Phase07
import NetHack.Soko11PairCandidate321.Phase08
import NetHack.Soko11PairCandidate321.Phase09
import NetHack.Soko11PairCandidate321.Phase10
import NetHack.Soko11PairCandidate321.Phase11
import NetHack.Soko11PairCandidate321.Phase12
import NetHack.Soko11PairCandidate321.Phase13
import NetHack.Soko11PairCandidate321.Phase14
import NetHack.Soko11PairCandidate321.Phase15
import NetHack.Soko11PairCandidate321.Phase16
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.GhostPartition
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def tables (phase : Nat) : Table :=
  if phase = 0 then table00 else
  if phase = 1 then table01 else
  if phase = 2 then table02 else
  if phase = 3 then table03 else
  if phase = 4 then table04 else
  if phase = 5 then table05 else
  if phase = 6 then table06 else
  if phase = 7 then table07 else
  if phase = 8 then table08 else
  if phase = 9 then table09 else
  if phase = 10 then table10 else
  if phase = 11 then table11 else
  if phase = 12 then table12 else
  if phase = 13 then table13 else
  if phase = 14 then table14 else
  if phase = 15 then table15 else
  .empty
def bonus (phase hero : Nat) (group : List Cell) : Nat :=
  if group.length = 2 then (lookup (tables phase) (code group) >>> (3*hero)) % 8 else 0
def groupValue (state : State) (group : List Cell) : Int :=
  let phase := NetHack.Sokoban.HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state
  weightSum (NetHack.Soko11Hero315.weight phase state.player) group + Int.ofNat (bonus phase state.player group)
def candidateValue (state : State) (groups : List (List Cell)) : Int :=
  sumGroups (groupValue state) groups + weightSum NetHack.Soko11Hero315.holeWeight state.holes
def initialGroups : List (List Cell) := [[139, 191], [186, 212], [133], [135], [137], [141], [188], [193], [315], [264], [317], [266], [293], [268], [321], [367]]
theorem initial_coupled : Coupled soko1_1.initial initialGroups := by unfold Coupled; decide +kernel
theorem initial_capacity : Capacity 2 initialGroups := by unfold Capacity; decide +kernel
/-- Only the value of proposed literal data. This is NOT lower321. -/
theorem candidate_initial_value : candidateValue soko1_1.initial initialGroups = 321 := by decide +kernel

theorem groupValue_respects (state : State) (a b : List Cell) (related : a.Perm b) :
    groupValue state a = groupValue state b := by
  have main := NetHack.Sokoban.StatePermutation.weightSum_permutation
    (NetHack.Soko11Hero315.weight (NetHack.Sokoban.HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state.player) related
  have index := NetHack.Sokoban.StatePermutation.weightSum_permutation codeWeight related
  simp only [groupValue,bonus,code,main,index,related.length_eq]
end NetHack.Soko11PairCandidate321
