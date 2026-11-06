import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2508_0_checked : (List.range' 1284096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2508_1_checked : (List.range' 1284224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2508_2_checked : (List.range' 1284352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2508_3_checked : (List.range' 1284480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2508_range (index : Nat) (lower : 1284096 ≤ index) (upper : index < 1284608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1284352 then
    if cut : index < 1284224 then
      exact segment_sound _ 1284096 128 Restriction2508_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1284224 128 Restriction2508_1_checked index (by omega) (by omega)
  else
    if cut : index < 1284480 then
      exact segment_sound _ 1284352 128 Restriction2508_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1284480 128 Restriction2508_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
