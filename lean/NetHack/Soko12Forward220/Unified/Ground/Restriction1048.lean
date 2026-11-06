import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1048_0_checked : (List.range' 536576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1048_1_checked : (List.range' 536704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1048_2_checked : (List.range' 536832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1048_3_checked : (List.range' 536960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1048_range (index : Nat) (lower : 536576 ≤ index) (upper : index < 537088) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 536832 then
    if cut : index < 536704 then
      exact segment_sound _ 536576 128 Restriction1048_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 536704 128 Restriction1048_1_checked index (by omega) (by omega)
  else
    if cut : index < 536960 then
      exact segment_sound _ 536832 128 Restriction1048_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 536960 128 Restriction1048_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
