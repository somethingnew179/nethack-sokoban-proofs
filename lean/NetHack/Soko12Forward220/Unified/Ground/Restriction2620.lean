import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2620_0_checked : (List.range' 1341440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2620_1_checked : (List.range' 1341568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2620_2_checked : (List.range' 1341696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2620_3_checked : (List.range' 1341824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2620_range (index : Nat) (lower : 1341440 ≤ index) (upper : index < 1341952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1341696 then
    if cut : index < 1341568 then
      exact segment_sound _ 1341440 128 Restriction2620_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1341568 128 Restriction2620_1_checked index (by omega) (by omega)
  else
    if cut : index < 1341824 then
      exact segment_sound _ 1341696 128 Restriction2620_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1341824 128 Restriction2620_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
