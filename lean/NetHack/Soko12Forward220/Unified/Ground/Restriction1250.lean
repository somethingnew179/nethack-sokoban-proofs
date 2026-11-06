import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1250_0_checked : (List.range' 640000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1250_1_checked : (List.range' 640128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1250_2_checked : (List.range' 640256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1250_3_checked : (List.range' 640384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1250_range (index : Nat) (lower : 640000 ≤ index) (upper : index < 640512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 640256 then
    if cut : index < 640128 then
      exact segment_sound _ 640000 128 Restriction1250_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 640128 128 Restriction1250_1_checked index (by omega) (by omega)
  else
    if cut : index < 640384 then
      exact segment_sound _ 640256 128 Restriction1250_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 640384 128 Restriction1250_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
