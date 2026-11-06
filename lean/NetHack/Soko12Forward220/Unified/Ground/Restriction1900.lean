import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1900_0_checked : (List.range' 972800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1900_1_checked : (List.range' 972928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1900_2_checked : (List.range' 973056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1900_3_checked : (List.range' 973184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1900_range (index : Nat) (lower : 972800 ≤ index) (upper : index < 973312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 973056 then
    if cut : index < 972928 then
      exact segment_sound _ 972800 128 Restriction1900_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 972928 128 Restriction1900_1_checked index (by omega) (by omega)
  else
    if cut : index < 973184 then
      exact segment_sound _ 973056 128 Restriction1900_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 973184 128 Restriction1900_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
