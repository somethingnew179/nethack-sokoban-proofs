import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2505_0_checked : (List.range' 1282560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2505_1_checked : (List.range' 1282688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2505_2_checked : (List.range' 1282816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2505_3_checked : (List.range' 1282944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2505_range (index : Nat) (lower : 1282560 ≤ index) (upper : index < 1283072) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1282816 then
    if cut : index < 1282688 then
      exact segment_sound _ 1282560 128 Restriction2505_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1282688 128 Restriction2505_1_checked index (by omega) (by omega)
  else
    if cut : index < 1282944 then
      exact segment_sound _ 1282816 128 Restriction2505_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1282944 128 Restriction2505_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
