import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1086_0_checked : (List.range' 556032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1086_1_checked : (List.range' 556160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1086_2_checked : (List.range' 556288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1086_3_checked : (List.range' 556416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1086_range (index : Nat) (lower : 556032 ≤ index) (upper : index < 556544) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 556288 then
    if cut : index < 556160 then
      exact segment_sound _ 556032 128 Restriction1086_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 556160 128 Restriction1086_1_checked index (by omega) (by omega)
  else
    if cut : index < 556416 then
      exact segment_sound _ 556288 128 Restriction1086_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 556416 128 Restriction1086_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
