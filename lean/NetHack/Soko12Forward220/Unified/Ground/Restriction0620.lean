import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0620_0_checked : (List.range' 317440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0620_1_checked : (List.range' 317568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0620_2_checked : (List.range' 317696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0620_3_checked : (List.range' 317824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0620_range (index : Nat) (lower : 317440 ≤ index) (upper : index < 317952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 317696 then
    if cut : index < 317568 then
      exact segment_sound _ 317440 128 Restriction0620_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 317568 128 Restriction0620_1_checked index (by omega) (by omega)
  else
    if cut : index < 317824 then
      exact segment_sound _ 317696 128 Restriction0620_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 317824 128 Restriction0620_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
