import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2013_0_checked : (List.range' 1030656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2013_1_checked : (List.range' 1030784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2013_2_checked : (List.range' 1030912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2013_3_checked : (List.range' 1031040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2013_range (index : Nat) (lower : 1030656 ≤ index) (upper : index < 1031168) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1030912 then
    if cut : index < 1030784 then
      exact segment_sound _ 1030656 128 Restriction2013_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1030784 128 Restriction2013_1_checked index (by omega) (by omega)
  else
    if cut : index < 1031040 then
      exact segment_sound _ 1030912 128 Restriction2013_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1031040 128 Restriction2013_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
