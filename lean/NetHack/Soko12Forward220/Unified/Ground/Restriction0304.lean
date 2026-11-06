import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0304_0_checked : (List.range' 155648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0304_1_checked : (List.range' 155776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0304_2_checked : (List.range' 155904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0304_3_checked : (List.range' 156032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0304_range (index : Nat) (lower : 155648 ≤ index) (upper : index < 156160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 155904 then
    if cut : index < 155776 then
      exact segment_sound _ 155648 128 Restriction0304_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 155776 128 Restriction0304_1_checked index (by omega) (by omega)
  else
    if cut : index < 156032 then
      exact segment_sound _ 155904 128 Restriction0304_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 156032 128 Restriction0304_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
