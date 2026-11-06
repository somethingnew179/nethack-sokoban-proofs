import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1317_0_checked : (List.range' 674304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1317_1_checked : (List.range' 674432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1317_2_checked : (List.range' 674560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1317_3_checked : (List.range' 674688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1317_range (index : Nat) (lower : 674304 ≤ index) (upper : index < 674816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 674560 then
    if cut : index < 674432 then
      exact segment_sound _ 674304 128 Restriction1317_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 674432 128 Restriction1317_1_checked index (by omega) (by omega)
  else
    if cut : index < 674688 then
      exact segment_sound _ 674560 128 Restriction1317_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 674688 128 Restriction1317_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
