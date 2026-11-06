import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0960_0_checked : (List.range' 491520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0960_1_checked : (List.range' 491648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0960_2_checked : (List.range' 491776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0960_3_checked : (List.range' 491904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0960_range (index : Nat) (lower : 491520 ≤ index) (upper : index < 492032) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 491776 then
    if cut : index < 491648 then
      exact segment_sound _ 491520 128 Restriction0960_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 491648 128 Restriction0960_1_checked index (by omega) (by omega)
  else
    if cut : index < 491904 then
      exact segment_sound _ 491776 128 Restriction0960_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 491904 128 Restriction0960_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
