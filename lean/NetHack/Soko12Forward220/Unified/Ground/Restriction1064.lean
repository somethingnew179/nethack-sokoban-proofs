import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1064_0_checked : (List.range' 544768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1064_1_checked : (List.range' 544896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1064_2_checked : (List.range' 545024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1064_3_checked : (List.range' 545152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1064_range (index : Nat) (lower : 544768 ≤ index) (upper : index < 545280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 545024 then
    if cut : index < 544896 then
      exact segment_sound _ 544768 128 Restriction1064_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 544896 128 Restriction1064_1_checked index (by omega) (by omega)
  else
    if cut : index < 545152 then
      exact segment_sound _ 545024 128 Restriction1064_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 545152 128 Restriction1064_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
