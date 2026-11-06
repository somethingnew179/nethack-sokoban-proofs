import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2221_0_checked : (List.range' 1137152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2221_1_checked : (List.range' 1137280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2221_2_checked : (List.range' 1137408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2221_3_checked : (List.range' 1137536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2221_range (index : Nat) (lower : 1137152 ≤ index) (upper : index < 1137664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1137408 then
    if cut : index < 1137280 then
      exact segment_sound _ 1137152 128 Restriction2221_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1137280 128 Restriction2221_1_checked index (by omega) (by omega)
  else
    if cut : index < 1137536 then
      exact segment_sound _ 1137408 128 Restriction2221_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1137536 128 Restriction2221_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
