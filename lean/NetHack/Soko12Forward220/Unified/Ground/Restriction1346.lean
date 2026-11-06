import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1346_0_checked : (List.range' 689152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1346_1_checked : (List.range' 689280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1346_2_checked : (List.range' 689408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1346_3_checked : (List.range' 689536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1346_range (index : Nat) (lower : 689152 ≤ index) (upper : index < 689664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 689408 then
    if cut : index < 689280 then
      exact segment_sound _ 689152 128 Restriction1346_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 689280 128 Restriction1346_1_checked index (by omega) (by omega)
  else
    if cut : index < 689536 then
      exact segment_sound _ 689408 128 Restriction1346_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 689536 128 Restriction1346_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
