import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2147_0_checked : (List.range' 1099264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2147_1_checked : (List.range' 1099392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2147_2_checked : (List.range' 1099520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2147_3_checked : (List.range' 1099648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2147_range (index : Nat) (lower : 1099264 ≤ index) (upper : index < 1099776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1099520 then
    if cut : index < 1099392 then
      exact segment_sound _ 1099264 128 Restriction2147_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1099392 128 Restriction2147_1_checked index (by omega) (by omega)
  else
    if cut : index < 1099648 then
      exact segment_sound _ 1099520 128 Restriction2147_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1099648 128 Restriction2147_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
