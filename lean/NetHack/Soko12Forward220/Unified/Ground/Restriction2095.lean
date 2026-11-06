import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2095_0_checked : (List.range' 1072640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2095_1_checked : (List.range' 1072768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2095_2_checked : (List.range' 1072896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2095_3_checked : (List.range' 1073024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2095_range (index : Nat) (lower : 1072640 ≤ index) (upper : index < 1073152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1072896 then
    if cut : index < 1072768 then
      exact segment_sound _ 1072640 128 Restriction2095_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1072768 128 Restriction2095_1_checked index (by omega) (by omega)
  else
    if cut : index < 1073024 then
      exact segment_sound _ 1072896 128 Restriction2095_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1073024 128 Restriction2095_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
