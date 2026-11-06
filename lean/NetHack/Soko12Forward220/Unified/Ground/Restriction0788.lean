import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0788_0_checked : (List.range' 403456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0788_1_checked : (List.range' 403584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0788_2_checked : (List.range' 403712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0788_3_checked : (List.range' 403840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0788_range (index : Nat) (lower : 403456 ≤ index) (upper : index < 403968) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 403712 then
    if cut : index < 403584 then
      exact segment_sound _ 403456 128 Restriction0788_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 403584 128 Restriction0788_1_checked index (by omega) (by omega)
  else
    if cut : index < 403840 then
      exact segment_sound _ 403712 128 Restriction0788_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 403840 128 Restriction0788_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
