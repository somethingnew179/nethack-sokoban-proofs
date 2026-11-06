import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1198_0_checked : (List.range' 613376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1198_1_checked : (List.range' 613504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1198_2_checked : (List.range' 613632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1198_3_checked : (List.range' 613760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1198_range (index : Nat) (lower : 613376 ≤ index) (upper : index < 613888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 613632 then
    if cut : index < 613504 then
      exact segment_sound _ 613376 128 Restriction1198_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 613504 128 Restriction1198_1_checked index (by omega) (by omega)
  else
    if cut : index < 613760 then
      exact segment_sound _ 613632 128 Restriction1198_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 613760 128 Restriction1198_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
