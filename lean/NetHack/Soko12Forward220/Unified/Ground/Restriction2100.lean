import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2100_0_checked : (List.range' 1075200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2100_1_checked : (List.range' 1075328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2100_2_checked : (List.range' 1075456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2100_3_checked : (List.range' 1075584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2100_range (index : Nat) (lower : 1075200 ≤ index) (upper : index < 1075712) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1075456 then
    if cut : index < 1075328 then
      exact segment_sound _ 1075200 128 Restriction2100_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1075328 128 Restriction2100_1_checked index (by omega) (by omega)
  else
    if cut : index < 1075584 then
      exact segment_sound _ 1075456 128 Restriction2100_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1075584 128 Restriction2100_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
