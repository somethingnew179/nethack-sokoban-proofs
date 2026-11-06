import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2048_0_checked : (List.range' 1048576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2048_1_checked : (List.range' 1048704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2048_2_checked : (List.range' 1048832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2048_3_checked : (List.range' 1048960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2048_range (index : Nat) (lower : 1048576 ≤ index) (upper : index < 1049088) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1048832 then
    if cut : index < 1048704 then
      exact segment_sound _ 1048576 128 Restriction2048_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1048704 128 Restriction2048_1_checked index (by omega) (by omega)
  else
    if cut : index < 1048960 then
      exact segment_sound _ 1048832 128 Restriction2048_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1048960 128 Restriction2048_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
