import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1994_0_checked : (List.range' 1020928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1994_1_checked : (List.range' 1021056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1994_2_checked : (List.range' 1021184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1994_3_checked : (List.range' 1021312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1994_range (index : Nat) (lower : 1020928 ≤ index) (upper : index < 1021440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1021184 then
    if cut : index < 1021056 then
      exact segment_sound _ 1020928 128 Restriction1994_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1021056 128 Restriction1994_1_checked index (by omega) (by omega)
  else
    if cut : index < 1021312 then
      exact segment_sound _ 1021184 128 Restriction1994_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1021312 128 Restriction1994_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
