import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1038_0_checked : (List.range' 531456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1038_1_checked : (List.range' 531584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1038_2_checked : (List.range' 531712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1038_3_checked : (List.range' 531840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1038_range (index : Nat) (lower : 531456 ≤ index) (upper : index < 531968) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 531712 then
    if cut : index < 531584 then
      exact segment_sound _ 531456 128 Restriction1038_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 531584 128 Restriction1038_1_checked index (by omega) (by omega)
  else
    if cut : index < 531840 then
      exact segment_sound _ 531712 128 Restriction1038_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 531840 128 Restriction1038_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
