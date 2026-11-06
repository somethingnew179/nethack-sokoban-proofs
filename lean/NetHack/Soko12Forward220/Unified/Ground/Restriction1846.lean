import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1846_0_checked : (List.range' 945152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1846_1_checked : (List.range' 945280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1846_2_checked : (List.range' 945408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1846_3_checked : (List.range' 945536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1846_range (index : Nat) (lower : 945152 ≤ index) (upper : index < 945664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 945408 then
    if cut : index < 945280 then
      exact segment_sound _ 945152 128 Restriction1846_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 945280 128 Restriction1846_1_checked index (by omega) (by omega)
  else
    if cut : index < 945536 then
      exact segment_sound _ 945408 128 Restriction1846_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 945536 128 Restriction1846_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
