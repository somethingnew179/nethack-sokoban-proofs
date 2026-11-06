import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0176_0_checked : (List.range' 90112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0176_1_checked : (List.range' 90240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0176_2_checked : (List.range' 90368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0176_3_checked : (List.range' 90496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0176_range (index : Nat) (lower : 90112 ≤ index) (upper : index < 90624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 90368 then
    if cut : index < 90240 then
      exact segment_sound _ 90112 128 Restriction0176_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 90240 128 Restriction0176_1_checked index (by omega) (by omega)
  else
    if cut : index < 90496 then
      exact segment_sound _ 90368 128 Restriction0176_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 90496 128 Restriction0176_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
