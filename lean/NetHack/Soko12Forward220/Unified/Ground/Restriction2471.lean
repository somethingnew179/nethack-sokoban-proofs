import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2471_0_checked : (List.range' 1265152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2471_1_checked : (List.range' 1265280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2471_2_checked : (List.range' 1265408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2471_3_checked : (List.range' 1265536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2471_range (index : Nat) (lower : 1265152 ≤ index) (upper : index < 1265664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1265408 then
    if cut : index < 1265280 then
      exact segment_sound _ 1265152 128 Restriction2471_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1265280 128 Restriction2471_1_checked index (by omega) (by omega)
  else
    if cut : index < 1265536 then
      exact segment_sound _ 1265408 128 Restriction2471_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1265536 128 Restriction2471_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
