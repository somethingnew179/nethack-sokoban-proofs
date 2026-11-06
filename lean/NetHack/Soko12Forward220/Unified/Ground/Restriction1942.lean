import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1942_0_checked : (List.range' 994304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1942_1_checked : (List.range' 994432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1942_2_checked : (List.range' 994560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1942_3_checked : (List.range' 994688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1942_range (index : Nat) (lower : 994304 ≤ index) (upper : index < 994816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 994560 then
    if cut : index < 994432 then
      exact segment_sound _ 994304 128 Restriction1942_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 994432 128 Restriction1942_1_checked index (by omega) (by omega)
  else
    if cut : index < 994688 then
      exact segment_sound _ 994560 128 Restriction1942_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 994688 128 Restriction1942_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
