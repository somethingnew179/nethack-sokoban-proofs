import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1542_0_checked : (List.range' 789504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1542_1_checked : (List.range' 789632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1542_2_checked : (List.range' 789760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1542_3_checked : (List.range' 789888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1542_range (index : Nat) (lower : 789504 ≤ index) (upper : index < 790016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 789760 then
    if cut : index < 789632 then
      exact segment_sound _ 789504 128 Restriction1542_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 789632 128 Restriction1542_1_checked index (by omega) (by omega)
  else
    if cut : index < 789888 then
      exact segment_sound _ 789760 128 Restriction1542_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 789888 128 Restriction1542_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
