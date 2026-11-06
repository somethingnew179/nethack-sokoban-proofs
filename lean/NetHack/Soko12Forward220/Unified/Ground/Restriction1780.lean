import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1780_0_checked : (List.range' 911360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1780_1_checked : (List.range' 911488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1780_2_checked : (List.range' 911616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1780_3_checked : (List.range' 911744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1780_range (index : Nat) (lower : 911360 ≤ index) (upper : index < 911872) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 911616 then
    if cut : index < 911488 then
      exact segment_sound _ 911360 128 Restriction1780_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 911488 128 Restriction1780_1_checked index (by omega) (by omega)
  else
    if cut : index < 911744 then
      exact segment_sound _ 911616 128 Restriction1780_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 911744 128 Restriction1780_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
