import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0634_0_checked : (List.range' 324608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0634_1_checked : (List.range' 324736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0634_2_checked : (List.range' 324864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0634_3_checked : (List.range' 324992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0634_range (index : Nat) (lower : 324608 ≤ index) (upper : index < 325120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 324864 then
    if cut : index < 324736 then
      exact segment_sound _ 324608 128 Restriction0634_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 324736 128 Restriction0634_1_checked index (by omega) (by omega)
  else
    if cut : index < 324992 then
      exact segment_sound _ 324864 128 Restriction0634_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 324992 128 Restriction0634_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
