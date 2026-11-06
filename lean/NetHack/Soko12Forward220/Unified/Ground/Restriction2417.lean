import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2417_0_checked : (List.range' 1237504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2417_1_checked : (List.range' 1237632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2417_2_checked : (List.range' 1237760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2417_3_checked : (List.range' 1237888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2417_range (index : Nat) (lower : 1237504 ≤ index) (upper : index < 1238016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1237760 then
    if cut : index < 1237632 then
      exact segment_sound _ 1237504 128 Restriction2417_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1237632 128 Restriction2417_1_checked index (by omega) (by omega)
  else
    if cut : index < 1237888 then
      exact segment_sound _ 1237760 128 Restriction2417_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1237888 128 Restriction2417_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
