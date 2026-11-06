import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0311_0_checked : (List.range' 159232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0311_1_checked : (List.range' 159360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0311_2_checked : (List.range' 159488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0311_3_checked : (List.range' 159616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0311_range (index : Nat) (lower : 159232 ≤ index) (upper : index < 159744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 159488 then
    if cut : index < 159360 then
      exact segment_sound _ 159232 128 Restriction0311_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 159360 128 Restriction0311_1_checked index (by omega) (by omega)
  else
    if cut : index < 159616 then
      exact segment_sound _ 159488 128 Restriction0311_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 159616 128 Restriction0311_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
