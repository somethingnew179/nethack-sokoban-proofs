import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1156_0_checked : (List.range' 591872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1156_1_checked : (List.range' 592000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1156_2_checked : (List.range' 592128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1156_3_checked : (List.range' 592256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1156_range (index : Nat) (lower : 591872 ≤ index) (upper : index < 592384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 592128 then
    if cut : index < 592000 then
      exact segment_sound _ 591872 128 Restriction1156_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 592000 128 Restriction1156_1_checked index (by omega) (by omega)
  else
    if cut : index < 592256 then
      exact segment_sound _ 592128 128 Restriction1156_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 592256 128 Restriction1156_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
