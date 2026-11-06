import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2540_0_checked : (List.range' 1300480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2540_1_checked : (List.range' 1300608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2540_2_checked : (List.range' 1300736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2540_3_checked : (List.range' 1300864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2540_range (index : Nat) (lower : 1300480 ≤ index) (upper : index < 1300992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1300736 then
    if cut : index < 1300608 then
      exact segment_sound _ 1300480 128 Restriction2540_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1300608 128 Restriction2540_1_checked index (by omega) (by omega)
  else
    if cut : index < 1300864 then
      exact segment_sound _ 1300736 128 Restriction2540_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1300864 128 Restriction2540_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
