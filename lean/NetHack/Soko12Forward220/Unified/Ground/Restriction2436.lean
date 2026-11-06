import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2436_0_checked : (List.range' 1247232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2436_1_checked : (List.range' 1247360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2436_2_checked : (List.range' 1247488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2436_3_checked : (List.range' 1247616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2436_range (index : Nat) (lower : 1247232 ≤ index) (upper : index < 1247744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1247488 then
    if cut : index < 1247360 then
      exact segment_sound _ 1247232 128 Restriction2436_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1247360 128 Restriction2436_1_checked index (by omega) (by omega)
  else
    if cut : index < 1247616 then
      exact segment_sound _ 1247488 128 Restriction2436_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1247616 128 Restriction2436_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
