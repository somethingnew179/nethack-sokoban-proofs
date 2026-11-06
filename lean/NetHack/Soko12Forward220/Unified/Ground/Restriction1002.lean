import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1002_0_checked : (List.range' 513024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1002_1_checked : (List.range' 513152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1002_2_checked : (List.range' 513280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1002_3_checked : (List.range' 513408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1002_range (index : Nat) (lower : 513024 ≤ index) (upper : index < 513536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 513280 then
    if cut : index < 513152 then
      exact segment_sound _ 513024 128 Restriction1002_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 513152 128 Restriction1002_1_checked index (by omega) (by omega)
  else
    if cut : index < 513408 then
      exact segment_sound _ 513280 128 Restriction1002_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 513408 128 Restriction1002_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
