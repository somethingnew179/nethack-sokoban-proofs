import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2545_0_checked : (List.range' 1303040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2545_1_checked : (List.range' 1303168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2545_2_checked : (List.range' 1303296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2545_3_checked : (List.range' 1303424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2545_range (index : Nat) (lower : 1303040 ≤ index) (upper : index < 1303552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1303296 then
    if cut : index < 1303168 then
      exact segment_sound _ 1303040 128 Restriction2545_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1303168 128 Restriction2545_1_checked index (by omega) (by omega)
  else
    if cut : index < 1303424 then
      exact segment_sound _ 1303296 128 Restriction2545_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1303424 128 Restriction2545_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
