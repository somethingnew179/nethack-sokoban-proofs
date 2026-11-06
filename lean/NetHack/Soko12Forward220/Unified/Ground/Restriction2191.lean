import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2191_0_checked : (List.range' 1121792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2191_1_checked : (List.range' 1121920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2191_2_checked : (List.range' 1122048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2191_3_checked : (List.range' 1122176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2191_range (index : Nat) (lower : 1121792 ≤ index) (upper : index < 1122304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1122048 then
    if cut : index < 1121920 then
      exact segment_sound _ 1121792 128 Restriction2191_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1121920 128 Restriction2191_1_checked index (by omega) (by omega)
  else
    if cut : index < 1122176 then
      exact segment_sound _ 1122048 128 Restriction2191_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1122176 128 Restriction2191_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
