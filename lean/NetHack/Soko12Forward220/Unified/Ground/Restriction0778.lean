import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0778_0_checked : (List.range' 398336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0778_1_checked : (List.range' 398464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0778_2_checked : (List.range' 398592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0778_3_checked : (List.range' 398720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0778_range (index : Nat) (lower : 398336 ≤ index) (upper : index < 398848) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 398592 then
    if cut : index < 398464 then
      exact segment_sound _ 398336 128 Restriction0778_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 398464 128 Restriction0778_1_checked index (by omega) (by omega)
  else
    if cut : index < 398720 then
      exact segment_sound _ 398592 128 Restriction0778_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 398720 128 Restriction0778_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
