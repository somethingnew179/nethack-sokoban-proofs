import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0553_0_checked : (List.range' 283136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0553_1_checked : (List.range' 283264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0553_2_checked : (List.range' 283392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0553_3_checked : (List.range' 283520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0553_range (index : Nat) (lower : 283136 ≤ index) (upper : index < 283648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 283392 then
    if cut : index < 283264 then
      exact segment_sound _ 283136 128 Restriction0553_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 283264 128 Restriction0553_1_checked index (by omega) (by omega)
  else
    if cut : index < 283520 then
      exact segment_sound _ 283392 128 Restriction0553_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 283520 128 Restriction0553_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
