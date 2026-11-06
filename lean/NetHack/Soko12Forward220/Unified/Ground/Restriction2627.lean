import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2627_0_checked : (List.range' 1345024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2627_1_checked : (List.range' 1345152 83).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2627_range (index : Nat) (lower : 1345024 ≤ index) (upper : index < 1345235) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1345152 then
    exact segment_sound _ 1345024 128 Restriction2627_0_checked index (by omega) (by omega)
  else
    exact segment_sound _ 1345152 83 Restriction2627_1_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
