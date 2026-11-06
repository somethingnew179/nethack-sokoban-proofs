import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1748_0_checked : (List.range' 894976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1748_1_checked : (List.range' 895104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1748_2_checked : (List.range' 895232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1748_3_checked : (List.range' 895360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1748_range (index : Nat) (lower : 894976 ≤ index) (upper : index < 895488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 895232 then
    if cut : index < 895104 then
      exact segment_sound _ 894976 128 Restriction1748_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 895104 128 Restriction1748_1_checked index (by omega) (by omega)
  else
    if cut : index < 895360 then
      exact segment_sound _ 895232 128 Restriction1748_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 895360 128 Restriction1748_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
