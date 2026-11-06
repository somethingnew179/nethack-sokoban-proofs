import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2029_0_checked : (List.range' 1038848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2029_1_checked : (List.range' 1038976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2029_2_checked : (List.range' 1039104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2029_3_checked : (List.range' 1039232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2029_range (index : Nat) (lower : 1038848 ≤ index) (upper : index < 1039360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1039104 then
    if cut : index < 1038976 then
      exact segment_sound _ 1038848 128 Restriction2029_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1038976 128 Restriction2029_1_checked index (by omega) (by omega)
  else
    if cut : index < 1039232 then
      exact segment_sound _ 1039104 128 Restriction2029_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1039232 128 Restriction2029_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
