import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1369_0_checked : (List.range' 700928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1369_1_checked : (List.range' 701056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1369_2_checked : (List.range' 701184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1369_3_checked : (List.range' 701312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1369_range (index : Nat) (lower : 700928 ≤ index) (upper : index < 701440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 701184 then
    if cut : index < 701056 then
      exact segment_sound _ 700928 128 Restriction1369_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 701056 128 Restriction1369_1_checked index (by omega) (by omega)
  else
    if cut : index < 701312 then
      exact segment_sound _ 701184 128 Restriction1369_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 701312 128 Restriction1369_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
