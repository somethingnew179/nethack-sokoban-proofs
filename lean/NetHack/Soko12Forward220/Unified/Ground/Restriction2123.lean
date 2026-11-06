import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2123_0_checked : (List.range' 1086976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2123_1_checked : (List.range' 1087104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2123_2_checked : (List.range' 1087232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2123_3_checked : (List.range' 1087360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2123_range (index : Nat) (lower : 1086976 ≤ index) (upper : index < 1087488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1087232 then
    if cut : index < 1087104 then
      exact segment_sound _ 1086976 128 Restriction2123_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1087104 128 Restriction2123_1_checked index (by omega) (by omega)
  else
    if cut : index < 1087360 then
      exact segment_sound _ 1087232 128 Restriction2123_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1087360 128 Restriction2123_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
