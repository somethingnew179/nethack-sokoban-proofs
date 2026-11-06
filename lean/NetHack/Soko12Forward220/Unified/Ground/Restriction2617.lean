import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2617_0_checked : (List.range' 1339904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2617_1_checked : (List.range' 1340032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2617_2_checked : (List.range' 1340160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2617_3_checked : (List.range' 1340288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2617_range (index : Nat) (lower : 1339904 ≤ index) (upper : index < 1340416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1340160 then
    if cut : index < 1340032 then
      exact segment_sound _ 1339904 128 Restriction2617_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1340032 128 Restriction2617_1_checked index (by omega) (by omega)
  else
    if cut : index < 1340288 then
      exact segment_sound _ 1340160 128 Restriction2617_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1340288 128 Restriction2617_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
