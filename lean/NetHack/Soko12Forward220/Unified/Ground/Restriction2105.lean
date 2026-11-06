import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2105_0_checked : (List.range' 1077760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2105_1_checked : (List.range' 1077888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2105_2_checked : (List.range' 1078016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2105_3_checked : (List.range' 1078144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2105_range (index : Nat) (lower : 1077760 ≤ index) (upper : index < 1078272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1078016 then
    if cut : index < 1077888 then
      exact segment_sound _ 1077760 128 Restriction2105_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1077888 128 Restriction2105_1_checked index (by omega) (by omega)
  else
    if cut : index < 1078144 then
      exact segment_sound _ 1078016 128 Restriction2105_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1078144 128 Restriction2105_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
