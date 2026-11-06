import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1414_0_checked : (List.range' 723968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1414_1_checked : (List.range' 724096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1414_2_checked : (List.range' 724224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1414_3_checked : (List.range' 724352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1414_range (index : Nat) (lower : 723968 ≤ index) (upper : index < 724480) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 724224 then
    if cut : index < 724096 then
      exact segment_sound _ 723968 128 Restriction1414_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 724096 128 Restriction1414_1_checked index (by omega) (by omega)
  else
    if cut : index < 724352 then
      exact segment_sound _ 724224 128 Restriction1414_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 724352 128 Restriction1414_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
