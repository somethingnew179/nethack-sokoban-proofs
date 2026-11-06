import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0383_0_checked : (List.range' 196096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0383_1_checked : (List.range' 196224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0383_2_checked : (List.range' 196352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0383_3_checked : (List.range' 196480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0383_range (index : Nat) (lower : 196096 ≤ index) (upper : index < 196608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 196352 then
    if cut : index < 196224 then
      exact segment_sound _ 196096 128 Restriction0383_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 196224 128 Restriction0383_1_checked index (by omega) (by omega)
  else
    if cut : index < 196480 then
      exact segment_sound _ 196352 128 Restriction0383_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 196480 128 Restriction0383_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
