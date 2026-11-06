import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1303_0_checked : (List.range' 667136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1303_1_checked : (List.range' 667264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1303_2_checked : (List.range' 667392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1303_3_checked : (List.range' 667520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1303_range (index : Nat) (lower : 667136 ≤ index) (upper : index < 667648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 667392 then
    if cut : index < 667264 then
      exact segment_sound _ 667136 128 Restriction1303_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 667264 128 Restriction1303_1_checked index (by omega) (by omega)
  else
    if cut : index < 667520 then
      exact segment_sound _ 667392 128 Restriction1303_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 667520 128 Restriction1303_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
