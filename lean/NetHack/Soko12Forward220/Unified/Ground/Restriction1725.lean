import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1725_0_checked : (List.range' 883200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1725_1_checked : (List.range' 883328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1725_2_checked : (List.range' 883456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1725_3_checked : (List.range' 883584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1725_range (index : Nat) (lower : 883200 ≤ index) (upper : index < 883712) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 883456 then
    if cut : index < 883328 then
      exact segment_sound _ 883200 128 Restriction1725_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 883328 128 Restriction1725_1_checked index (by omega) (by omega)
  else
    if cut : index < 883584 then
      exact segment_sound _ 883456 128 Restriction1725_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 883584 128 Restriction1725_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
