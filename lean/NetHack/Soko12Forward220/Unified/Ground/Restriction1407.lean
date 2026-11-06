import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1407_0_checked : (List.range' 720384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1407_1_checked : (List.range' 720512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1407_2_checked : (List.range' 720640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1407_3_checked : (List.range' 720768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1407_range (index : Nat) (lower : 720384 ≤ index) (upper : index < 720896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 720640 then
    if cut : index < 720512 then
      exact segment_sound _ 720384 128 Restriction1407_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 720512 128 Restriction1407_1_checked index (by omega) (by omega)
  else
    if cut : index < 720768 then
      exact segment_sound _ 720640 128 Restriction1407_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 720768 128 Restriction1407_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
