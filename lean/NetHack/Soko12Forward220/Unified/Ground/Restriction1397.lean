import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1397_0_checked : (List.range' 715264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1397_1_checked : (List.range' 715392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1397_2_checked : (List.range' 715520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1397_3_checked : (List.range' 715648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1397_range (index : Nat) (lower : 715264 ≤ index) (upper : index < 715776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 715520 then
    if cut : index < 715392 then
      exact segment_sound _ 715264 128 Restriction1397_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 715392 128 Restriction1397_1_checked index (by omega) (by omega)
  else
    if cut : index < 715648 then
      exact segment_sound _ 715520 128 Restriction1397_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 715648 128 Restriction1397_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
