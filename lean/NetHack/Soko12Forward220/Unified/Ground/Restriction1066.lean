import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1066_0_checked : (List.range' 545792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1066_1_checked : (List.range' 545920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1066_2_checked : (List.range' 546048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1066_3_checked : (List.range' 546176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1066_range (index : Nat) (lower : 545792 ≤ index) (upper : index < 546304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 546048 then
    if cut : index < 545920 then
      exact segment_sound _ 545792 128 Restriction1066_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 545920 128 Restriction1066_1_checked index (by omega) (by omega)
  else
    if cut : index < 546176 then
      exact segment_sound _ 546048 128 Restriction1066_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 546176 128 Restriction1066_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
