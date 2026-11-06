import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1181_0_checked : (List.range' 604672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1181_1_checked : (List.range' 604800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1181_2_checked : (List.range' 604928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1181_3_checked : (List.range' 605056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1181_range (index : Nat) (lower : 604672 ≤ index) (upper : index < 605184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 604928 then
    if cut : index < 604800 then
      exact segment_sound _ 604672 128 Restriction1181_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 604800 128 Restriction1181_1_checked index (by omega) (by omega)
  else
    if cut : index < 605056 then
      exact segment_sound _ 604928 128 Restriction1181_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 605056 128 Restriction1181_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
