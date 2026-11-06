import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1262_0_checked : (List.range' 646144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1262_1_checked : (List.range' 646272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1262_2_checked : (List.range' 646400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1262_3_checked : (List.range' 646528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1262_range (index : Nat) (lower : 646144 ≤ index) (upper : index < 646656) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 646400 then
    if cut : index < 646272 then
      exact segment_sound _ 646144 128 Restriction1262_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 646272 128 Restriction1262_1_checked index (by omega) (by omega)
  else
    if cut : index < 646528 then
      exact segment_sound _ 646400 128 Restriction1262_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 646528 128 Restriction1262_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
