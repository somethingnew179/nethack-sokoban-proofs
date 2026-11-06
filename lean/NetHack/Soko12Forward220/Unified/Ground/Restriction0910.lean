import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0910_0_checked : (List.range' 465920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0910_1_checked : (List.range' 466048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0910_2_checked : (List.range' 466176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0910_3_checked : (List.range' 466304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0910_range (index : Nat) (lower : 465920 ≤ index) (upper : index < 466432) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 466176 then
    if cut : index < 466048 then
      exact segment_sound _ 465920 128 Restriction0910_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 466048 128 Restriction0910_1_checked index (by omega) (by omega)
  else
    if cut : index < 466304 then
      exact segment_sound _ 466176 128 Restriction0910_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 466304 128 Restriction0910_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
