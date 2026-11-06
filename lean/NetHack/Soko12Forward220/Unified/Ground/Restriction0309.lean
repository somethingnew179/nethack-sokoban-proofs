import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0309_0_checked : (List.range' 158208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0309_1_checked : (List.range' 158336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0309_2_checked : (List.range' 158464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0309_3_checked : (List.range' 158592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0309_range (index : Nat) (lower : 158208 ≤ index) (upper : index < 158720) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 158464 then
    if cut : index < 158336 then
      exact segment_sound _ 158208 128 Restriction0309_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 158336 128 Restriction0309_1_checked index (by omega) (by omega)
  else
    if cut : index < 158592 then
      exact segment_sound _ 158464 128 Restriction0309_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 158592 128 Restriction0309_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
