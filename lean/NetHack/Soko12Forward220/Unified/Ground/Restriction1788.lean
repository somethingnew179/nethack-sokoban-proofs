import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1788_0_checked : (List.range' 915456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1788_1_checked : (List.range' 915584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1788_2_checked : (List.range' 915712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1788_3_checked : (List.range' 915840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1788_range (index : Nat) (lower : 915456 ≤ index) (upper : index < 915968) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 915712 then
    if cut : index < 915584 then
      exact segment_sound _ 915456 128 Restriction1788_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 915584 128 Restriction1788_1_checked index (by omega) (by omega)
  else
    if cut : index < 915840 then
      exact segment_sound _ 915712 128 Restriction1788_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 915840 128 Restriction1788_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
