import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1971_0_checked : (List.range' 1009152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1971_1_checked : (List.range' 1009280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1971_2_checked : (List.range' 1009408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1971_3_checked : (List.range' 1009536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1971_range (index : Nat) (lower : 1009152 ≤ index) (upper : index < 1009664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1009408 then
    if cut : index < 1009280 then
      exact segment_sound _ 1009152 128 Restriction1971_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1009280 128 Restriction1971_1_checked index (by omega) (by omega)
  else
    if cut : index < 1009536 then
      exact segment_sound _ 1009408 128 Restriction1971_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1009536 128 Restriction1971_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
