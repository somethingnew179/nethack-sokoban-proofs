import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1868_0_checked : (List.range' 956416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1868_1_checked : (List.range' 956544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1868_2_checked : (List.range' 956672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1868_3_checked : (List.range' 956800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1868_range (index : Nat) (lower : 956416 ≤ index) (upper : index < 956928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 956672 then
    if cut : index < 956544 then
      exact segment_sound _ 956416 128 Restriction1868_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 956544 128 Restriction1868_1_checked index (by omega) (by omega)
  else
    if cut : index < 956800 then
      exact segment_sound _ 956672 128 Restriction1868_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 956800 128 Restriction1868_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
