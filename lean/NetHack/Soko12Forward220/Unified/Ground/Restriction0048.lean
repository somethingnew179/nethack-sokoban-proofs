import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0048_0_checked : (List.range' 24576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0048_1_checked : (List.range' 24704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0048_2_checked : (List.range' 24832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0048_3_checked : (List.range' 24960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0048_range (index : Nat) (lower : 24576 ≤ index) (upper : index < 25088) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 24832 then
    if cut : index < 24704 then
      exact segment_sound _ 24576 128 Restriction0048_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 24704 128 Restriction0048_1_checked index (by omega) (by omega)
  else
    if cut : index < 24960 then
      exact segment_sound _ 24832 128 Restriction0048_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 24960 128 Restriction0048_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
