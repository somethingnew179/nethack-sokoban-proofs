import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2578_0_checked : (List.range' 1319936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2578_1_checked : (List.range' 1320064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2578_2_checked : (List.range' 1320192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2578_3_checked : (List.range' 1320320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2578_range (index : Nat) (lower : 1319936 ≤ index) (upper : index < 1320448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1320192 then
    if cut : index < 1320064 then
      exact segment_sound _ 1319936 128 Restriction2578_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1320064 128 Restriction2578_1_checked index (by omega) (by omega)
  else
    if cut : index < 1320320 then
      exact segment_sound _ 1320192 128 Restriction2578_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1320320 128 Restriction2578_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
