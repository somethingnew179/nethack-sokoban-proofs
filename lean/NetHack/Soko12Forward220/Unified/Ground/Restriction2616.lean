import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2616_0_checked : (List.range' 1339392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2616_1_checked : (List.range' 1339520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2616_2_checked : (List.range' 1339648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2616_3_checked : (List.range' 1339776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2616_range (index : Nat) (lower : 1339392 ≤ index) (upper : index < 1339904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1339648 then
    if cut : index < 1339520 then
      exact segment_sound _ 1339392 128 Restriction2616_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1339520 128 Restriction2616_1_checked index (by omega) (by omega)
  else
    if cut : index < 1339776 then
      exact segment_sound _ 1339648 128 Restriction2616_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1339776 128 Restriction2616_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
