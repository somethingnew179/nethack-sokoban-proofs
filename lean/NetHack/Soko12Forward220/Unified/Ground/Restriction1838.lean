import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1838_0_checked : (List.range' 941056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1838_1_checked : (List.range' 941184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1838_2_checked : (List.range' 941312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1838_3_checked : (List.range' 941440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1838_range (index : Nat) (lower : 941056 ≤ index) (upper : index < 941568) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 941312 then
    if cut : index < 941184 then
      exact segment_sound _ 941056 128 Restriction1838_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 941184 128 Restriction1838_1_checked index (by omega) (by omega)
  else
    if cut : index < 941440 then
      exact segment_sound _ 941312 128 Restriction1838_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 941440 128 Restriction1838_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
