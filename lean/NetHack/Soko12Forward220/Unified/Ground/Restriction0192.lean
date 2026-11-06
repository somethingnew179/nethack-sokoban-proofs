import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0192_0_checked : (List.range' 98304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0192_1_checked : (List.range' 98432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0192_2_checked : (List.range' 98560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0192_3_checked : (List.range' 98688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0192_range (index : Nat) (lower : 98304 ≤ index) (upper : index < 98816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 98560 then
    if cut : index < 98432 then
      exact segment_sound _ 98304 128 Restriction0192_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 98432 128 Restriction0192_1_checked index (by omega) (by omega)
  else
    if cut : index < 98688 then
      exact segment_sound _ 98560 128 Restriction0192_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 98688 128 Restriction0192_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
