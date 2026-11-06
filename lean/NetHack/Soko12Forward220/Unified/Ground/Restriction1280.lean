import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1280_0_checked : (List.range' 655360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1280_1_checked : (List.range' 655488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1280_2_checked : (List.range' 655616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1280_3_checked : (List.range' 655744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1280_range (index : Nat) (lower : 655360 ≤ index) (upper : index < 655872) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 655616 then
    if cut : index < 655488 then
      exact segment_sound _ 655360 128 Restriction1280_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 655488 128 Restriction1280_1_checked index (by omega) (by omega)
  else
    if cut : index < 655744 then
      exact segment_sound _ 655616 128 Restriction1280_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 655744 128 Restriction1280_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
