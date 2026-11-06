import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2571_0_checked : (List.range' 1316352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2571_1_checked : (List.range' 1316480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2571_2_checked : (List.range' 1316608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2571_3_checked : (List.range' 1316736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2571_range (index : Nat) (lower : 1316352 ≤ index) (upper : index < 1316864) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1316608 then
    if cut : index < 1316480 then
      exact segment_sound _ 1316352 128 Restriction2571_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1316480 128 Restriction2571_1_checked index (by omega) (by omega)
  else
    if cut : index < 1316736 then
      exact segment_sound _ 1316608 128 Restriction2571_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1316736 128 Restriction2571_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
