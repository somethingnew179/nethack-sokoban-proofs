import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0941_0_checked : (List.range' 481792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0941_1_checked : (List.range' 481920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0941_2_checked : (List.range' 482048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0941_3_checked : (List.range' 482176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0941_range (index : Nat) (lower : 481792 ≤ index) (upper : index < 482304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 482048 then
    if cut : index < 481920 then
      exact segment_sound _ 481792 128 Restriction0941_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 481920 128 Restriction0941_1_checked index (by omega) (by omega)
  else
    if cut : index < 482176 then
      exact segment_sound _ 482048 128 Restriction0941_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 482176 128 Restriction0941_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
