import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1436_0_checked : (List.range' 735232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1436_1_checked : (List.range' 735360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1436_2_checked : (List.range' 735488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1436_3_checked : (List.range' 735616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1436_range (index : Nat) (lower : 735232 ≤ index) (upper : index < 735744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 735488 then
    if cut : index < 735360 then
      exact segment_sound _ 735232 128 Restriction1436_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 735360 128 Restriction1436_1_checked index (by omega) (by omega)
  else
    if cut : index < 735616 then
      exact segment_sound _ 735488 128 Restriction1436_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 735616 128 Restriction1436_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
