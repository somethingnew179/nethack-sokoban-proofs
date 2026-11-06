import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1291_0_checked : (List.range' 660992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1291_1_checked : (List.range' 661120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1291_2_checked : (List.range' 661248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1291_3_checked : (List.range' 661376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1291_range (index : Nat) (lower : 660992 ≤ index) (upper : index < 661504) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 661248 then
    if cut : index < 661120 then
      exact segment_sound _ 660992 128 Restriction1291_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 661120 128 Restriction1291_1_checked index (by omega) (by omega)
  else
    if cut : index < 661376 then
      exact segment_sound _ 661248 128 Restriction1291_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 661376 128 Restriction1291_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
