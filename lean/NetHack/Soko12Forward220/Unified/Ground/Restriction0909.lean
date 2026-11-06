import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0909_0_checked : (List.range' 465408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0909_1_checked : (List.range' 465536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0909_2_checked : (List.range' 465664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0909_3_checked : (List.range' 465792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0909_range (index : Nat) (lower : 465408 ≤ index) (upper : index < 465920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 465664 then
    if cut : index < 465536 then
      exact segment_sound _ 465408 128 Restriction0909_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 465536 128 Restriction0909_1_checked index (by omega) (by omega)
  else
    if cut : index < 465792 then
      exact segment_sound _ 465664 128 Restriction0909_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 465792 128 Restriction0909_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
