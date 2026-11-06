import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2065_0_checked : (List.range' 1057280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2065_1_checked : (List.range' 1057408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2065_2_checked : (List.range' 1057536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2065_3_checked : (List.range' 1057664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2065_range (index : Nat) (lower : 1057280 ≤ index) (upper : index < 1057792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1057536 then
    if cut : index < 1057408 then
      exact segment_sound _ 1057280 128 Restriction2065_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1057408 128 Restriction2065_1_checked index (by omega) (by omega)
  else
    if cut : index < 1057664 then
      exact segment_sound _ 1057536 128 Restriction2065_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1057664 128 Restriction2065_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
