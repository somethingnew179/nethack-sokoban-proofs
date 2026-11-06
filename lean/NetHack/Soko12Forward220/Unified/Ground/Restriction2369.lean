import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2369_0_checked : (List.range' 1212928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2369_1_checked : (List.range' 1213056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2369_2_checked : (List.range' 1213184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2369_3_checked : (List.range' 1213312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2369_range (index : Nat) (lower : 1212928 ≤ index) (upper : index < 1213440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1213184 then
    if cut : index < 1213056 then
      exact segment_sound _ 1212928 128 Restriction2369_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1213056 128 Restriction2369_1_checked index (by omega) (by omega)
  else
    if cut : index < 1213312 then
      exact segment_sound _ 1213184 128 Restriction2369_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1213312 128 Restriction2369_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
