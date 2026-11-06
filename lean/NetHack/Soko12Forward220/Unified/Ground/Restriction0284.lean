import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0284_0_checked : (List.range' 145408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0284_1_checked : (List.range' 145536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0284_2_checked : (List.range' 145664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0284_3_checked : (List.range' 145792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0284_range (index : Nat) (lower : 145408 ≤ index) (upper : index < 145920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 145664 then
    if cut : index < 145536 then
      exact segment_sound _ 145408 128 Restriction0284_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 145536 128 Restriction0284_1_checked index (by omega) (by omega)
  else
    if cut : index < 145792 then
      exact segment_sound _ 145664 128 Restriction0284_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 145792 128 Restriction0284_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
