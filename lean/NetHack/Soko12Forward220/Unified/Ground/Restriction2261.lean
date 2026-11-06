import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2261_0_checked : (List.range' 1157632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2261_1_checked : (List.range' 1157760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2261_2_checked : (List.range' 1157888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2261_3_checked : (List.range' 1158016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2261_range (index : Nat) (lower : 1157632 ≤ index) (upper : index < 1158144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1157888 then
    if cut : index < 1157760 then
      exact segment_sound _ 1157632 128 Restriction2261_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1157760 128 Restriction2261_1_checked index (by omega) (by omega)
  else
    if cut : index < 1158016 then
      exact segment_sound _ 1157888 128 Restriction2261_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1158016 128 Restriction2261_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
