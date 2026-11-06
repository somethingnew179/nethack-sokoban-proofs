import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2135_0_checked : (List.range' 1093120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2135_1_checked : (List.range' 1093248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2135_2_checked : (List.range' 1093376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2135_3_checked : (List.range' 1093504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2135_range (index : Nat) (lower : 1093120 ≤ index) (upper : index < 1093632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1093376 then
    if cut : index < 1093248 then
      exact segment_sound _ 1093120 128 Restriction2135_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1093248 128 Restriction2135_1_checked index (by omega) (by omega)
  else
    if cut : index < 1093504 then
      exact segment_sound _ 1093376 128 Restriction2135_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1093504 128 Restriction2135_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
