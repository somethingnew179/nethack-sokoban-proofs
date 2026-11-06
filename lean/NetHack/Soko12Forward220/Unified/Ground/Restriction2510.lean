import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2510_0_checked : (List.range' 1285120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2510_1_checked : (List.range' 1285248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2510_2_checked : (List.range' 1285376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2510_3_checked : (List.range' 1285504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2510_range (index : Nat) (lower : 1285120 ≤ index) (upper : index < 1285632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1285376 then
    if cut : index < 1285248 then
      exact segment_sound _ 1285120 128 Restriction2510_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1285248 128 Restriction2510_1_checked index (by omega) (by omega)
  else
    if cut : index < 1285504 then
      exact segment_sound _ 1285376 128 Restriction2510_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1285504 128 Restriction2510_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
