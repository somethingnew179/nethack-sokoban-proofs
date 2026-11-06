import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0852_0_checked : (List.range' 436224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0852_1_checked : (List.range' 436352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0852_2_checked : (List.range' 436480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0852_3_checked : (List.range' 436608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0852_range (index : Nat) (lower : 436224 ≤ index) (upper : index < 436736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 436480 then
    if cut : index < 436352 then
      exact segment_sound _ 436224 128 Restriction0852_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 436352 128 Restriction0852_1_checked index (by omega) (by omega)
  else
    if cut : index < 436608 then
      exact segment_sound _ 436480 128 Restriction0852_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 436608 128 Restriction0852_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
