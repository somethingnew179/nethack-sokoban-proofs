import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1199_0_checked : (List.range' 613888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1199_1_checked : (List.range' 614016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1199_2_checked : (List.range' 614144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1199_3_checked : (List.range' 614272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1199_range (index : Nat) (lower : 613888 ≤ index) (upper : index < 614400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 614144 then
    if cut : index < 614016 then
      exact segment_sound _ 613888 128 Restriction1199_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 614016 128 Restriction1199_1_checked index (by omega) (by omega)
  else
    if cut : index < 614272 then
      exact segment_sound _ 614144 128 Restriction1199_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 614272 128 Restriction1199_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
