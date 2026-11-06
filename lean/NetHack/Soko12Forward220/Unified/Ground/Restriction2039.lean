import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2039_0_checked : (List.range' 1043968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2039_1_checked : (List.range' 1044096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2039_2_checked : (List.range' 1044224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2039_3_checked : (List.range' 1044352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2039_range (index : Nat) (lower : 1043968 ≤ index) (upper : index < 1044480) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1044224 then
    if cut : index < 1044096 then
      exact segment_sound _ 1043968 128 Restriction2039_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1044096 128 Restriction2039_1_checked index (by omega) (by omega)
  else
    if cut : index < 1044352 then
      exact segment_sound _ 1044224 128 Restriction2039_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1044352 128 Restriction2039_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
