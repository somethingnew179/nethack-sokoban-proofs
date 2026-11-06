import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0097_0_checked : (List.range' 49664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0097_1_checked : (List.range' 49792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0097_2_checked : (List.range' 49920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0097_3_checked : (List.range' 50048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0097_range (index : Nat) (lower : 49664 ≤ index) (upper : index < 50176) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 49920 then
    if cut : index < 49792 then
      exact segment_sound _ 49664 128 Restriction0097_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 49792 128 Restriction0097_1_checked index (by omega) (by omega)
  else
    if cut : index < 50048 then
      exact segment_sound _ 49920 128 Restriction0097_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 50048 128 Restriction0097_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
