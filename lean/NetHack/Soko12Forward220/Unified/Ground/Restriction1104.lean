import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1104_0_checked : (List.range' 565248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1104_1_checked : (List.range' 565376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1104_2_checked : (List.range' 565504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1104_3_checked : (List.range' 565632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1104_range (index : Nat) (lower : 565248 ≤ index) (upper : index < 565760) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 565504 then
    if cut : index < 565376 then
      exact segment_sound _ 565248 128 Restriction1104_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 565376 128 Restriction1104_1_checked index (by omega) (by omega)
  else
    if cut : index < 565632 then
      exact segment_sound _ 565504 128 Restriction1104_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 565632 128 Restriction1104_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
