import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1814_0_checked : (List.range' 928768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1814_1_checked : (List.range' 928896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1814_2_checked : (List.range' 929024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1814_3_checked : (List.range' 929152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1814_range (index : Nat) (lower : 928768 ≤ index) (upper : index < 929280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 929024 then
    if cut : index < 928896 then
      exact segment_sound _ 928768 128 Restriction1814_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 928896 128 Restriction1814_1_checked index (by omega) (by omega)
  else
    if cut : index < 929152 then
      exact segment_sound _ 929024 128 Restriction1814_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 929152 128 Restriction1814_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
