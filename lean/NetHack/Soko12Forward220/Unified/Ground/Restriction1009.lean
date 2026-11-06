import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1009_0_checked : (List.range' 516608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1009_1_checked : (List.range' 516736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1009_2_checked : (List.range' 516864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1009_3_checked : (List.range' 516992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1009_range (index : Nat) (lower : 516608 ≤ index) (upper : index < 517120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 516864 then
    if cut : index < 516736 then
      exact segment_sound _ 516608 128 Restriction1009_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 516736 128 Restriction1009_1_checked index (by omega) (by omega)
  else
    if cut : index < 516992 then
      exact segment_sound _ 516864 128 Restriction1009_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 516992 128 Restriction1009_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
