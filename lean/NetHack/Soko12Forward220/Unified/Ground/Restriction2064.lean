import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2064_0_checked : (List.range' 1056768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2064_1_checked : (List.range' 1056896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2064_2_checked : (List.range' 1057024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2064_3_checked : (List.range' 1057152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2064_range (index : Nat) (lower : 1056768 ≤ index) (upper : index < 1057280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1057024 then
    if cut : index < 1056896 then
      exact segment_sound _ 1056768 128 Restriction2064_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1056896 128 Restriction2064_1_checked index (by omega) (by omega)
  else
    if cut : index < 1057152 then
      exact segment_sound _ 1057024 128 Restriction2064_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1057152 128 Restriction2064_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
