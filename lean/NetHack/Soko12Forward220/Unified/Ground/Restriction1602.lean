import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1602_0_checked : (List.range' 820224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1602_1_checked : (List.range' 820352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1602_2_checked : (List.range' 820480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1602_3_checked : (List.range' 820608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1602_range (index : Nat) (lower : 820224 ≤ index) (upper : index < 820736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 820480 then
    if cut : index < 820352 then
      exact segment_sound _ 820224 128 Restriction1602_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 820352 128 Restriction1602_1_checked index (by omega) (by omega)
  else
    if cut : index < 820608 then
      exact segment_sound _ 820480 128 Restriction1602_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 820608 128 Restriction1602_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
