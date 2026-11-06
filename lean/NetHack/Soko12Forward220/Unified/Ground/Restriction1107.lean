import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1107_0_checked : (List.range' 566784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1107_1_checked : (List.range' 566912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1107_2_checked : (List.range' 567040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1107_3_checked : (List.range' 567168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1107_range (index : Nat) (lower : 566784 ≤ index) (upper : index < 567296) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 567040 then
    if cut : index < 566912 then
      exact segment_sound _ 566784 128 Restriction1107_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 566912 128 Restriction1107_1_checked index (by omega) (by omega)
  else
    if cut : index < 567168 then
      exact segment_sound _ 567040 128 Restriction1107_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 567168 128 Restriction1107_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
