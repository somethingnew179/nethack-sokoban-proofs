import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0638_0_checked : (List.range' 326656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0638_1_checked : (List.range' 326784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0638_2_checked : (List.range' 326912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0638_3_checked : (List.range' 327040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0638_range (index : Nat) (lower : 326656 ≤ index) (upper : index < 327168) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 326912 then
    if cut : index < 326784 then
      exact segment_sound _ 326656 128 Restriction0638_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 326784 128 Restriction0638_1_checked index (by omega) (by omega)
  else
    if cut : index < 327040 then
      exact segment_sound _ 326912 128 Restriction0638_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 327040 128 Restriction0638_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
