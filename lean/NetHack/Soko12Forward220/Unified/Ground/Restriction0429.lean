import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0429_0_checked : (List.range' 219648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0429_1_checked : (List.range' 219776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0429_2_checked : (List.range' 219904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0429_3_checked : (List.range' 220032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0429_range (index : Nat) (lower : 219648 ≤ index) (upper : index < 220160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 219904 then
    if cut : index < 219776 then
      exact segment_sound _ 219648 128 Restriction0429_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 219776 128 Restriction0429_1_checked index (by omega) (by omega)
  else
    if cut : index < 220032 then
      exact segment_sound _ 219904 128 Restriction0429_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 220032 128 Restriction0429_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
