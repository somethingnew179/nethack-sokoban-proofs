import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1803_0_checked : (List.range' 923136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1803_1_checked : (List.range' 923264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1803_2_checked : (List.range' 923392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1803_3_checked : (List.range' 923520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1803_range (index : Nat) (lower : 923136 ≤ index) (upper : index < 923648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 923392 then
    if cut : index < 923264 then
      exact segment_sound _ 923136 128 Restriction1803_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 923264 128 Restriction1803_1_checked index (by omega) (by omega)
  else
    if cut : index < 923520 then
      exact segment_sound _ 923392 128 Restriction1803_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 923520 128 Restriction1803_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
