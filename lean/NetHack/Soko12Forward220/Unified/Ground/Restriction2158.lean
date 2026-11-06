import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2158_0_checked : (List.range' 1104896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2158_1_checked : (List.range' 1105024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2158_2_checked : (List.range' 1105152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2158_3_checked : (List.range' 1105280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2158_range (index : Nat) (lower : 1104896 ≤ index) (upper : index < 1105408) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1105152 then
    if cut : index < 1105024 then
      exact segment_sound _ 1104896 128 Restriction2158_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1105024 128 Restriction2158_1_checked index (by omega) (by omega)
  else
    if cut : index < 1105280 then
      exact segment_sound _ 1105152 128 Restriction2158_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1105280 128 Restriction2158_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
