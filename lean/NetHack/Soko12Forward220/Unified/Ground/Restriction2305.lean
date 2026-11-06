import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2305_0_checked : (List.range' 1180160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2305_1_checked : (List.range' 1180288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2305_2_checked : (List.range' 1180416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2305_3_checked : (List.range' 1180544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2305_range (index : Nat) (lower : 1180160 ≤ index) (upper : index < 1180672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1180416 then
    if cut : index < 1180288 then
      exact segment_sound _ 1180160 128 Restriction2305_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1180288 128 Restriction2305_1_checked index (by omega) (by omega)
  else
    if cut : index < 1180544 then
      exact segment_sound _ 1180416 128 Restriction2305_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1180544 128 Restriction2305_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
