import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0814_0_checked : (List.range' 416768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0814_1_checked : (List.range' 416896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0814_2_checked : (List.range' 417024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0814_3_checked : (List.range' 417152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0814_range (index : Nat) (lower : 416768 ≤ index) (upper : index < 417280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 417024 then
    if cut : index < 416896 then
      exact segment_sound _ 416768 128 Restriction0814_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 416896 128 Restriction0814_1_checked index (by omega) (by omega)
  else
    if cut : index < 417152 then
      exact segment_sound _ 417024 128 Restriction0814_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 417152 128 Restriction0814_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
