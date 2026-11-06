import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0993_0_checked : (List.range' 508416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0993_1_checked : (List.range' 508544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0993_2_checked : (List.range' 508672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0993_3_checked : (List.range' 508800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0993_range (index : Nat) (lower : 508416 ≤ index) (upper : index < 508928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 508672 then
    if cut : index < 508544 then
      exact segment_sound _ 508416 128 Restriction0993_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 508544 128 Restriction0993_1_checked index (by omega) (by omega)
  else
    if cut : index < 508800 then
      exact segment_sound _ 508672 128 Restriction0993_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 508800 128 Restriction0993_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
