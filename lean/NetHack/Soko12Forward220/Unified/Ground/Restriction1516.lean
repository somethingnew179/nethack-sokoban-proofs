import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1516_0_checked : (List.range' 776192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1516_1_checked : (List.range' 776320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1516_2_checked : (List.range' 776448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1516_3_checked : (List.range' 776576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1516_range (index : Nat) (lower : 776192 ≤ index) (upper : index < 776704) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 776448 then
    if cut : index < 776320 then
      exact segment_sound _ 776192 128 Restriction1516_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 776320 128 Restriction1516_1_checked index (by omega) (by omega)
  else
    if cut : index < 776576 then
      exact segment_sound _ 776448 128 Restriction1516_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 776576 128 Restriction1516_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
