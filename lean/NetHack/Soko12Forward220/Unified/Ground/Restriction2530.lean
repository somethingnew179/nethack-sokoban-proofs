import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2530_0_checked : (List.range' 1295360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2530_1_checked : (List.range' 1295488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2530_2_checked : (List.range' 1295616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2530_3_checked : (List.range' 1295744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2530_range (index : Nat) (lower : 1295360 ≤ index) (upper : index < 1295872) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1295616 then
    if cut : index < 1295488 then
      exact segment_sound _ 1295360 128 Restriction2530_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1295488 128 Restriction2530_1_checked index (by omega) (by omega)
  else
    if cut : index < 1295744 then
      exact segment_sound _ 1295616 128 Restriction2530_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1295744 128 Restriction2530_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
