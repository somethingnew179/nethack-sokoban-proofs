import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1227_0_checked : (List.range' 628224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1227_1_checked : (List.range' 628352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1227_2_checked : (List.range' 628480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1227_3_checked : (List.range' 628608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1227_range (index : Nat) (lower : 628224 ≤ index) (upper : index < 628736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 628480 then
    if cut : index < 628352 then
      exact segment_sound _ 628224 128 Restriction1227_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 628352 128 Restriction1227_1_checked index (by omega) (by omega)
  else
    if cut : index < 628608 then
      exact segment_sound _ 628480 128 Restriction1227_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 628608 128 Restriction1227_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
