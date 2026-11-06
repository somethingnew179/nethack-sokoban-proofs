import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1106_0_checked : (List.range' 566272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1106_1_checked : (List.range' 566400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1106_2_checked : (List.range' 566528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1106_3_checked : (List.range' 566656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1106_range (index : Nat) (lower : 566272 ≤ index) (upper : index < 566784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 566528 then
    if cut : index < 566400 then
      exact segment_sound _ 566272 128 Restriction1106_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 566400 128 Restriction1106_1_checked index (by omega) (by omega)
  else
    if cut : index < 566656 then
      exact segment_sound _ 566528 128 Restriction1106_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 566656 128 Restriction1106_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
