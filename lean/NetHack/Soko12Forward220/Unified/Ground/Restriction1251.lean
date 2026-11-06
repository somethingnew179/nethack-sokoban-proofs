import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1251_0_checked : (List.range' 640512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1251_1_checked : (List.range' 640640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1251_2_checked : (List.range' 640768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1251_3_checked : (List.range' 640896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1251_range (index : Nat) (lower : 640512 ≤ index) (upper : index < 641024) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 640768 then
    if cut : index < 640640 then
      exact segment_sound _ 640512 128 Restriction1251_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 640640 128 Restriction1251_1_checked index (by omega) (by omega)
  else
    if cut : index < 640896 then
      exact segment_sound _ 640768 128 Restriction1251_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 640896 128 Restriction1251_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
