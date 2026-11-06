import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2553_0_checked : (List.range' 1307136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2553_1_checked : (List.range' 1307264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2553_2_checked : (List.range' 1307392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2553_3_checked : (List.range' 1307520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2553_range (index : Nat) (lower : 1307136 ≤ index) (upper : index < 1307648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1307392 then
    if cut : index < 1307264 then
      exact segment_sound _ 1307136 128 Restriction2553_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1307264 128 Restriction2553_1_checked index (by omega) (by omega)
  else
    if cut : index < 1307520 then
      exact segment_sound _ 1307392 128 Restriction2553_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1307520 128 Restriction2553_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
