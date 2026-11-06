import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2566_0_checked : (List.range' 1313792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2566_1_checked : (List.range' 1313920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2566_2_checked : (List.range' 1314048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2566_3_checked : (List.range' 1314176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2566_range (index : Nat) (lower : 1313792 ≤ index) (upper : index < 1314304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1314048 then
    if cut : index < 1313920 then
      exact segment_sound _ 1313792 128 Restriction2566_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1313920 128 Restriction2566_1_checked index (by omega) (by omega)
  else
    if cut : index < 1314176 then
      exact segment_sound _ 1314048 128 Restriction2566_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1314176 128 Restriction2566_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
