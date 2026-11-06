import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1655_0_checked : (List.range' 847360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1655_1_checked : (List.range' 847488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1655_2_checked : (List.range' 847616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1655_3_checked : (List.range' 847744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1655_range (index : Nat) (lower : 847360 ≤ index) (upper : index < 847872) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 847616 then
    if cut : index < 847488 then
      exact segment_sound _ 847360 128 Restriction1655_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 847488 128 Restriction1655_1_checked index (by omega) (by omega)
  else
    if cut : index < 847744 then
      exact segment_sound _ 847616 128 Restriction1655_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 847744 128 Restriction1655_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
