import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1596_0_checked : (List.range' 817152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1596_1_checked : (List.range' 817280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1596_2_checked : (List.range' 817408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1596_3_checked : (List.range' 817536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1596_range (index : Nat) (lower : 817152 ≤ index) (upper : index < 817664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 817408 then
    if cut : index < 817280 then
      exact segment_sound _ 817152 128 Restriction1596_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 817280 128 Restriction1596_1_checked index (by omega) (by omega)
  else
    if cut : index < 817536 then
      exact segment_sound _ 817408 128 Restriction1596_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 817536 128 Restriction1596_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
