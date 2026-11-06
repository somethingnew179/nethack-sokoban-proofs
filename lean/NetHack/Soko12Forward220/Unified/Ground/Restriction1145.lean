import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1145_0_checked : (List.range' 586240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1145_1_checked : (List.range' 586368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1145_2_checked : (List.range' 586496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1145_3_checked : (List.range' 586624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1145_range (index : Nat) (lower : 586240 ≤ index) (upper : index < 586752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 586496 then
    if cut : index < 586368 then
      exact segment_sound _ 586240 128 Restriction1145_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 586368 128 Restriction1145_1_checked index (by omega) (by omega)
  else
    if cut : index < 586624 then
      exact segment_sound _ 586496 128 Restriction1145_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 586624 128 Restriction1145_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
