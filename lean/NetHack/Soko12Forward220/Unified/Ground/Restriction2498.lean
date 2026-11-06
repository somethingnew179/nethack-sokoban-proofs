import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2498_0_checked : (List.range' 1278976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2498_1_checked : (List.range' 1279104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2498_2_checked : (List.range' 1279232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2498_3_checked : (List.range' 1279360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2498_range (index : Nat) (lower : 1278976 ≤ index) (upper : index < 1279488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1279232 then
    if cut : index < 1279104 then
      exact segment_sound _ 1278976 128 Restriction2498_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1279104 128 Restriction2498_1_checked index (by omega) (by omega)
  else
    if cut : index < 1279360 then
      exact segment_sound _ 1279232 128 Restriction2498_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1279360 128 Restriction2498_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
