import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2106_0_checked : (List.range' 1078272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2106_1_checked : (List.range' 1078400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2106_2_checked : (List.range' 1078528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2106_3_checked : (List.range' 1078656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2106_range (index : Nat) (lower : 1078272 ≤ index) (upper : index < 1078784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1078528 then
    if cut : index < 1078400 then
      exact segment_sound _ 1078272 128 Restriction2106_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1078400 128 Restriction2106_1_checked index (by omega) (by omega)
  else
    if cut : index < 1078656 then
      exact segment_sound _ 1078528 128 Restriction2106_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1078656 128 Restriction2106_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
