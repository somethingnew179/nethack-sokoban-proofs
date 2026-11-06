import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2107_0_checked : (List.range' 1078784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2107_1_checked : (List.range' 1078912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2107_2_checked : (List.range' 1079040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2107_3_checked : (List.range' 1079168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2107_range (index : Nat) (lower : 1078784 ≤ index) (upper : index < 1079296) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1079040 then
    if cut : index < 1078912 then
      exact segment_sound _ 1078784 128 Restriction2107_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1078912 128 Restriction2107_1_checked index (by omega) (by omega)
  else
    if cut : index < 1079168 then
      exact segment_sound _ 1079040 128 Restriction2107_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1079168 128 Restriction2107_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
