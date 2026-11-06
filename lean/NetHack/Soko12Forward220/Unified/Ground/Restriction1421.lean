import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1421_0_checked : (List.range' 727552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1421_1_checked : (List.range' 727680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1421_2_checked : (List.range' 727808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1421_3_checked : (List.range' 727936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1421_range (index : Nat) (lower : 727552 ≤ index) (upper : index < 728064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 727808 then
    if cut : index < 727680 then
      exact segment_sound _ 727552 128 Restriction1421_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 727680 128 Restriction1421_1_checked index (by omega) (by omega)
  else
    if cut : index < 727936 then
      exact segment_sound _ 727808 128 Restriction1421_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 727936 128 Restriction1421_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
