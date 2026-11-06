import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0706_0_checked : (List.range' 361472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0706_1_checked : (List.range' 361600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0706_2_checked : (List.range' 361728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0706_3_checked : (List.range' 361856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0706_range (index : Nat) (lower : 361472 ≤ index) (upper : index < 361984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 361728 then
    if cut : index < 361600 then
      exact segment_sound _ 361472 128 Restriction0706_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 361600 128 Restriction0706_1_checked index (by omega) (by omega)
  else
    if cut : index < 361856 then
      exact segment_sound _ 361728 128 Restriction0706_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 361856 128 Restriction0706_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
