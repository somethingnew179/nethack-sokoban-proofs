import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1960_0_checked : (List.range' 1003520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1960_1_checked : (List.range' 1003648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1960_2_checked : (List.range' 1003776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1960_3_checked : (List.range' 1003904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1960_range (index : Nat) (lower : 1003520 ≤ index) (upper : index < 1004032) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1003776 then
    if cut : index < 1003648 then
      exact segment_sound _ 1003520 128 Restriction1960_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1003648 128 Restriction1960_1_checked index (by omega) (by omega)
  else
    if cut : index < 1003904 then
      exact segment_sound _ 1003776 128 Restriction1960_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1003904 128 Restriction1960_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
