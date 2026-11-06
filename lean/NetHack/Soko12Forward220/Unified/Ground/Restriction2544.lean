import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2544_0_checked : (List.range' 1302528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2544_1_checked : (List.range' 1302656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2544_2_checked : (List.range' 1302784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2544_3_checked : (List.range' 1302912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2544_range (index : Nat) (lower : 1302528 ≤ index) (upper : index < 1303040) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1302784 then
    if cut : index < 1302656 then
      exact segment_sound _ 1302528 128 Restriction2544_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1302656 128 Restriction2544_1_checked index (by omega) (by omega)
  else
    if cut : index < 1302912 then
      exact segment_sound _ 1302784 128 Restriction2544_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1302912 128 Restriction2544_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
