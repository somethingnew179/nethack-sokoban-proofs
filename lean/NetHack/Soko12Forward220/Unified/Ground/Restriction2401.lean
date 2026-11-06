import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2401_0_checked : (List.range' 1229312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2401_1_checked : (List.range' 1229440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2401_2_checked : (List.range' 1229568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2401_3_checked : (List.range' 1229696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2401_range (index : Nat) (lower : 1229312 ≤ index) (upper : index < 1229824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1229568 then
    if cut : index < 1229440 then
      exact segment_sound _ 1229312 128 Restriction2401_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1229440 128 Restriction2401_1_checked index (by omega) (by omega)
  else
    if cut : index < 1229696 then
      exact segment_sound _ 1229568 128 Restriction2401_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1229696 128 Restriction2401_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
