import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2433_0_checked : (List.range' 1245696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2433_1_checked : (List.range' 1245824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2433_2_checked : (List.range' 1245952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2433_3_checked : (List.range' 1246080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2433_range (index : Nat) (lower : 1245696 ≤ index) (upper : index < 1246208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1245952 then
    if cut : index < 1245824 then
      exact segment_sound _ 1245696 128 Restriction2433_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1245824 128 Restriction2433_1_checked index (by omega) (by omega)
  else
    if cut : index < 1246080 then
      exact segment_sound _ 1245952 128 Restriction2433_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1246080 128 Restriction2433_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
