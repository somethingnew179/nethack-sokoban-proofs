import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2388_0_checked : (List.range' 1222656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2388_1_checked : (List.range' 1222784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2388_2_checked : (List.range' 1222912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2388_3_checked : (List.range' 1223040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2388_range (index : Nat) (lower : 1222656 ≤ index) (upper : index < 1223168) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1222912 then
    if cut : index < 1222784 then
      exact segment_sound _ 1222656 128 Restriction2388_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1222784 128 Restriction2388_1_checked index (by omega) (by omega)
  else
    if cut : index < 1223040 then
      exact segment_sound _ 1222912 128 Restriction2388_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1223040 128 Restriction2388_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
