import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1288_0_checked : (List.range' 659456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1288_1_checked : (List.range' 659584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1288_2_checked : (List.range' 659712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1288_3_checked : (List.range' 659840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1288_range (index : Nat) (lower : 659456 ≤ index) (upper : index < 659968) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 659712 then
    if cut : index < 659584 then
      exact segment_sound _ 659456 128 Restriction1288_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 659584 128 Restriction1288_1_checked index (by omega) (by omega)
  else
    if cut : index < 659840 then
      exact segment_sound _ 659712 128 Restriction1288_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 659840 128 Restriction1288_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
