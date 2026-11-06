import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0749_0_checked : (List.range' 383488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0749_1_checked : (List.range' 383616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0749_2_checked : (List.range' 383744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0749_3_checked : (List.range' 383872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0749_range (index : Nat) (lower : 383488 ≤ index) (upper : index < 384000) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 383744 then
    if cut : index < 383616 then
      exact segment_sound _ 383488 128 Restriction0749_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 383616 128 Restriction0749_1_checked index (by omega) (by omega)
  else
    if cut : index < 383872 then
      exact segment_sound _ 383744 128 Restriction0749_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 383872 128 Restriction0749_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
