import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0440_0_checked : (List.range' 225280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0440_1_checked : (List.range' 225408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0440_2_checked : (List.range' 225536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0440_3_checked : (List.range' 225664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0440_range (index : Nat) (lower : 225280 ≤ index) (upper : index < 225792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 225536 then
    if cut : index < 225408 then
      exact segment_sound _ 225280 128 Restriction0440_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 225408 128 Restriction0440_1_checked index (by omega) (by omega)
  else
    if cut : index < 225664 then
      exact segment_sound _ 225536 128 Restriction0440_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 225664 128 Restriction0440_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
