import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0477_0_checked : (List.range' 244224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0477_1_checked : (List.range' 244352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0477_2_checked : (List.range' 244480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0477_3_checked : (List.range' 244608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0477_range (index : Nat) (lower : 244224 ≤ index) (upper : index < 244736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 244480 then
    if cut : index < 244352 then
      exact segment_sound _ 244224 128 Restriction0477_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 244352 128 Restriction0477_1_checked index (by omega) (by omega)
  else
    if cut : index < 244608 then
      exact segment_sound _ 244480 128 Restriction0477_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 244608 128 Restriction0477_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
