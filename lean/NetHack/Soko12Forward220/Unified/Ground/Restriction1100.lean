import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1100_0_checked : (List.range' 563200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1100_1_checked : (List.range' 563328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1100_2_checked : (List.range' 563456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1100_3_checked : (List.range' 563584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1100_range (index : Nat) (lower : 563200 ≤ index) (upper : index < 563712) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 563456 then
    if cut : index < 563328 then
      exact segment_sound _ 563200 128 Restriction1100_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 563328 128 Restriction1100_1_checked index (by omega) (by omega)
  else
    if cut : index < 563584 then
      exact segment_sound _ 563456 128 Restriction1100_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 563584 128 Restriction1100_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
