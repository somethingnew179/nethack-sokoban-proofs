import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2444_0_checked : (List.range' 1251328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2444_1_checked : (List.range' 1251456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2444_2_checked : (List.range' 1251584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2444_3_checked : (List.range' 1251712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2444_range (index : Nat) (lower : 1251328 ≤ index) (upper : index < 1251840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1251584 then
    if cut : index < 1251456 then
      exact segment_sound _ 1251328 128 Restriction2444_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1251456 128 Restriction2444_1_checked index (by omega) (by omega)
  else
    if cut : index < 1251712 then
      exact segment_sound _ 1251584 128 Restriction2444_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1251712 128 Restriction2444_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
