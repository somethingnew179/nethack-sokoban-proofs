import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2625_0_checked : (List.range' 1344000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2625_1_checked : (List.range' 1344128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2625_2_checked : (List.range' 1344256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2625_3_checked : (List.range' 1344384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2625_range (index : Nat) (lower : 1344000 ≤ index) (upper : index < 1344512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1344256 then
    if cut : index < 1344128 then
      exact segment_sound _ 1344000 128 Restriction2625_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1344128 128 Restriction2625_1_checked index (by omega) (by omega)
  else
    if cut : index < 1344384 then
      exact segment_sound _ 1344256 128 Restriction2625_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1344384 128 Restriction2625_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
