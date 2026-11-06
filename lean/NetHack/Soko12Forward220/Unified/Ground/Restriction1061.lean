import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1061_0_checked : (List.range' 543232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1061_1_checked : (List.range' 543360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1061_2_checked : (List.range' 543488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1061_3_checked : (List.range' 543616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1061_range (index : Nat) (lower : 543232 ≤ index) (upper : index < 543744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 543488 then
    if cut : index < 543360 then
      exact segment_sound _ 543232 128 Restriction1061_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 543360 128 Restriction1061_1_checked index (by omega) (by omega)
  else
    if cut : index < 543616 then
      exact segment_sound _ 543488 128 Restriction1061_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 543616 128 Restriction1061_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
