import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2134_0_checked : (List.range' 1092608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2134_1_checked : (List.range' 1092736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2134_2_checked : (List.range' 1092864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2134_3_checked : (List.range' 1092992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2134_range (index : Nat) (lower : 1092608 ≤ index) (upper : index < 1093120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1092864 then
    if cut : index < 1092736 then
      exact segment_sound _ 1092608 128 Restriction2134_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1092736 128 Restriction2134_1_checked index (by omega) (by omega)
  else
    if cut : index < 1092992 then
      exact segment_sound _ 1092864 128 Restriction2134_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1092992 128 Restriction2134_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
