import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0809_0_checked : (List.range' 414208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0809_1_checked : (List.range' 414336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0809_2_checked : (List.range' 414464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0809_3_checked : (List.range' 414592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0809_range (index : Nat) (lower : 414208 ≤ index) (upper : index < 414720) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 414464 then
    if cut : index < 414336 then
      exact segment_sound _ 414208 128 Restriction0809_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 414336 128 Restriction0809_1_checked index (by omega) (by omega)
  else
    if cut : index < 414592 then
      exact segment_sound _ 414464 128 Restriction0809_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 414592 128 Restriction0809_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
