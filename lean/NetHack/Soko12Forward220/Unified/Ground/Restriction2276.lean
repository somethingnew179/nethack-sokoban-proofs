import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2276_0_checked : (List.range' 1165312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2276_1_checked : (List.range' 1165440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2276_2_checked : (List.range' 1165568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2276_3_checked : (List.range' 1165696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2276_range (index : Nat) (lower : 1165312 ≤ index) (upper : index < 1165824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1165568 then
    if cut : index < 1165440 then
      exact segment_sound _ 1165312 128 Restriction2276_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1165440 128 Restriction2276_1_checked index (by omega) (by omega)
  else
    if cut : index < 1165696 then
      exact segment_sound _ 1165568 128 Restriction2276_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1165696 128 Restriction2276_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
