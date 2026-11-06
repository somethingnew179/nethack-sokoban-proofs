import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1043_0_checked : (List.range' 534016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1043_1_checked : (List.range' 534144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1043_2_checked : (List.range' 534272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1043_3_checked : (List.range' 534400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1043_range (index : Nat) (lower : 534016 ≤ index) (upper : index < 534528) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 534272 then
    if cut : index < 534144 then
      exact segment_sound _ 534016 128 Restriction1043_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 534144 128 Restriction1043_1_checked index (by omega) (by omega)
  else
    if cut : index < 534400 then
      exact segment_sound _ 534272 128 Restriction1043_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 534400 128 Restriction1043_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
