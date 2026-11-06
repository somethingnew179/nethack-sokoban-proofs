import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1415_0_checked : (List.range' 724480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1415_1_checked : (List.range' 724608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1415_2_checked : (List.range' 724736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1415_3_checked : (List.range' 724864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1415_range (index : Nat) (lower : 724480 ≤ index) (upper : index < 724992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 724736 then
    if cut : index < 724608 then
      exact segment_sound _ 724480 128 Restriction1415_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 724608 128 Restriction1415_1_checked index (by omega) (by omega)
  else
    if cut : index < 724864 then
      exact segment_sound _ 724736 128 Restriction1415_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 724864 128 Restriction1415_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
