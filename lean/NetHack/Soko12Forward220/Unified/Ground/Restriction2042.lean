import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2042_0_checked : (List.range' 1045504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2042_1_checked : (List.range' 1045632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2042_2_checked : (List.range' 1045760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2042_3_checked : (List.range' 1045888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2042_range (index : Nat) (lower : 1045504 ≤ index) (upper : index < 1046016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1045760 then
    if cut : index < 1045632 then
      exact segment_sound _ 1045504 128 Restriction2042_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1045632 128 Restriction2042_1_checked index (by omega) (by omega)
  else
    if cut : index < 1045888 then
      exact segment_sound _ 1045760 128 Restriction2042_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1045888 128 Restriction2042_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
