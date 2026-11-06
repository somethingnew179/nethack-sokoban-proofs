import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1784_0_checked : (List.range' 913408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1784_1_checked : (List.range' 913536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1784_2_checked : (List.range' 913664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1784_3_checked : (List.range' 913792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1784_range (index : Nat) (lower : 913408 ≤ index) (upper : index < 913920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 913664 then
    if cut : index < 913536 then
      exact segment_sound _ 913408 128 Restriction1784_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 913536 128 Restriction1784_1_checked index (by omega) (by omega)
  else
    if cut : index < 913792 then
      exact segment_sound _ 913664 128 Restriction1784_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 913792 128 Restriction1784_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
