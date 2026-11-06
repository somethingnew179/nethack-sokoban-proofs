import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1221_0_checked : (List.range' 625152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1221_1_checked : (List.range' 625280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1221_2_checked : (List.range' 625408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1221_3_checked : (List.range' 625536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1221_range (index : Nat) (lower : 625152 ≤ index) (upper : index < 625664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 625408 then
    if cut : index < 625280 then
      exact segment_sound _ 625152 128 Restriction1221_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 625280 128 Restriction1221_1_checked index (by omega) (by omega)
  else
    if cut : index < 625536 then
      exact segment_sound _ 625408 128 Restriction1221_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 625536 128 Restriction1221_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
