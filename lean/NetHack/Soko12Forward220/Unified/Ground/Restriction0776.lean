import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0776_0_checked : (List.range' 397312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0776_1_checked : (List.range' 397440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0776_2_checked : (List.range' 397568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0776_3_checked : (List.range' 397696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0776_range (index : Nat) (lower : 397312 ≤ index) (upper : index < 397824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 397568 then
    if cut : index < 397440 then
      exact segment_sound _ 397312 128 Restriction0776_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 397440 128 Restriction0776_1_checked index (by omega) (by omega)
  else
    if cut : index < 397696 then
      exact segment_sound _ 397568 128 Restriction0776_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 397696 128 Restriction0776_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
