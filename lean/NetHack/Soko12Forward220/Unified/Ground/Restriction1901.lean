import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1901_0_checked : (List.range' 973312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1901_1_checked : (List.range' 973440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1901_2_checked : (List.range' 973568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1901_3_checked : (List.range' 973696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1901_range (index : Nat) (lower : 973312 ≤ index) (upper : index < 973824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 973568 then
    if cut : index < 973440 then
      exact segment_sound _ 973312 128 Restriction1901_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 973440 128 Restriction1901_1_checked index (by omega) (by omega)
  else
    if cut : index < 973696 then
      exact segment_sound _ 973568 128 Restriction1901_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 973696 128 Restriction1901_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
