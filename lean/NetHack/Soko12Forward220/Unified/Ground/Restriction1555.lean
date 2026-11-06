import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1555_0_checked : (List.range' 796160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1555_1_checked : (List.range' 796288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1555_2_checked : (List.range' 796416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1555_3_checked : (List.range' 796544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1555_range (index : Nat) (lower : 796160 ≤ index) (upper : index < 796672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 796416 then
    if cut : index < 796288 then
      exact segment_sound _ 796160 128 Restriction1555_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 796288 128 Restriction1555_1_checked index (by omega) (by omega)
  else
    if cut : index < 796544 then
      exact segment_sound _ 796416 128 Restriction1555_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 796544 128 Restriction1555_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
