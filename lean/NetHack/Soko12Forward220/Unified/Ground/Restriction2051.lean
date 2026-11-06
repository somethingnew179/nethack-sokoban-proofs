import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2051_0_checked : (List.range' 1050112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2051_1_checked : (List.range' 1050240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2051_2_checked : (List.range' 1050368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2051_3_checked : (List.range' 1050496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2051_range (index : Nat) (lower : 1050112 ≤ index) (upper : index < 1050624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1050368 then
    if cut : index < 1050240 then
      exact segment_sound _ 1050112 128 Restriction2051_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1050240 128 Restriction2051_1_checked index (by omega) (by omega)
  else
    if cut : index < 1050496 then
      exact segment_sound _ 1050368 128 Restriction2051_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1050496 128 Restriction2051_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
