import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2564_0_checked : (List.range' 1312768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2564_1_checked : (List.range' 1312896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2564_2_checked : (List.range' 1313024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2564_3_checked : (List.range' 1313152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2564_range (index : Nat) (lower : 1312768 ≤ index) (upper : index < 1313280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1313024 then
    if cut : index < 1312896 then
      exact segment_sound _ 1312768 128 Restriction2564_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1312896 128 Restriction2564_1_checked index (by omega) (by omega)
  else
    if cut : index < 1313152 then
      exact segment_sound _ 1313024 128 Restriction2564_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1313152 128 Restriction2564_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
