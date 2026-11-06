import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2443_0_checked : (List.range' 1250816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2443_1_checked : (List.range' 1250944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2443_2_checked : (List.range' 1251072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2443_3_checked : (List.range' 1251200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2443_range (index : Nat) (lower : 1250816 ≤ index) (upper : index < 1251328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1251072 then
    if cut : index < 1250944 then
      exact segment_sound _ 1250816 128 Restriction2443_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1250944 128 Restriction2443_1_checked index (by omega) (by omega)
  else
    if cut : index < 1251200 then
      exact segment_sound _ 1251072 128 Restriction2443_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1251200 128 Restriction2443_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
