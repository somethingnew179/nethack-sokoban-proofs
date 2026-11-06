import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0731_0_checked : (List.range' 374272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0731_1_checked : (List.range' 374400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0731_2_checked : (List.range' 374528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0731_3_checked : (List.range' 374656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0731_range (index : Nat) (lower : 374272 ≤ index) (upper : index < 374784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 374528 then
    if cut : index < 374400 then
      exact segment_sound _ 374272 128 Restriction0731_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 374400 128 Restriction0731_1_checked index (by omega) (by omega)
  else
    if cut : index < 374656 then
      exact segment_sound _ 374528 128 Restriction0731_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 374656 128 Restriction0731_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
