import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0540_0_checked : (List.range' 276480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0540_1_checked : (List.range' 276608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0540_2_checked : (List.range' 276736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0540_3_checked : (List.range' 276864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0540_range (index : Nat) (lower : 276480 ≤ index) (upper : index < 276992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 276736 then
    if cut : index < 276608 then
      exact segment_sound _ 276480 128 Restriction0540_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 276608 128 Restriction0540_1_checked index (by omega) (by omega)
  else
    if cut : index < 276864 then
      exact segment_sound _ 276736 128 Restriction0540_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 276864 128 Restriction0540_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
