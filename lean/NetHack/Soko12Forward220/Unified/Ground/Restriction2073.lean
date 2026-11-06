import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2073_0_checked : (List.range' 1061376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2073_1_checked : (List.range' 1061504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2073_2_checked : (List.range' 1061632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2073_3_checked : (List.range' 1061760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2073_range (index : Nat) (lower : 1061376 ≤ index) (upper : index < 1061888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1061632 then
    if cut : index < 1061504 then
      exact segment_sound _ 1061376 128 Restriction2073_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1061504 128 Restriction2073_1_checked index (by omega) (by omega)
  else
    if cut : index < 1061760 then
      exact segment_sound _ 1061632 128 Restriction2073_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1061760 128 Restriction2073_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
