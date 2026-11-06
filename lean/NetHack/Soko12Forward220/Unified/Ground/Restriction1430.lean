import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1430_0_checked : (List.range' 732160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1430_1_checked : (List.range' 732288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1430_2_checked : (List.range' 732416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1430_3_checked : (List.range' 732544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1430_range (index : Nat) (lower : 732160 ≤ index) (upper : index < 732672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 732416 then
    if cut : index < 732288 then
      exact segment_sound _ 732160 128 Restriction1430_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 732288 128 Restriction1430_1_checked index (by omega) (by omega)
  else
    if cut : index < 732544 then
      exact segment_sound _ 732416 128 Restriction1430_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 732544 128 Restriction1430_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
