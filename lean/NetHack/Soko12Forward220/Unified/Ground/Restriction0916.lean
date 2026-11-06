import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0916_0_checked : (List.range' 468992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0916_1_checked : (List.range' 469120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0916_2_checked : (List.range' 469248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0916_3_checked : (List.range' 469376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0916_range (index : Nat) (lower : 468992 ≤ index) (upper : index < 469504) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 469248 then
    if cut : index < 469120 then
      exact segment_sound _ 468992 128 Restriction0916_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 469120 128 Restriction0916_1_checked index (by omega) (by omega)
  else
    if cut : index < 469376 then
      exact segment_sound _ 469248 128 Restriction0916_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 469376 128 Restriction0916_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
