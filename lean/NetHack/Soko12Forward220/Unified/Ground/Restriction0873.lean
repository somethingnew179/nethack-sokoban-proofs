import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0873_0_checked : (List.range' 446976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0873_1_checked : (List.range' 447104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0873_2_checked : (List.range' 447232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0873_3_checked : (List.range' 447360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0873_range (index : Nat) (lower : 446976 ≤ index) (upper : index < 447488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 447232 then
    if cut : index < 447104 then
      exact segment_sound _ 446976 128 Restriction0873_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 447104 128 Restriction0873_1_checked index (by omega) (by omega)
  else
    if cut : index < 447360 then
      exact segment_sound _ 447232 128 Restriction0873_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 447360 128 Restriction0873_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
