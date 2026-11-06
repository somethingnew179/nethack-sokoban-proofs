import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1073_0_checked : (List.range' 549376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1073_1_checked : (List.range' 549504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1073_2_checked : (List.range' 549632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1073_3_checked : (List.range' 549760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1073_range (index : Nat) (lower : 549376 ≤ index) (upper : index < 549888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 549632 then
    if cut : index < 549504 then
      exact segment_sound _ 549376 128 Restriction1073_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 549504 128 Restriction1073_1_checked index (by omega) (by omega)
  else
    if cut : index < 549760 then
      exact segment_sound _ 549632 128 Restriction1073_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 549760 128 Restriction1073_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
