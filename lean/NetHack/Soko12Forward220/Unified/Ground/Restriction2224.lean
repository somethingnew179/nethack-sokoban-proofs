import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2224_0_checked : (List.range' 1138688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2224_1_checked : (List.range' 1138816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2224_2_checked : (List.range' 1138944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2224_3_checked : (List.range' 1139072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2224_range (index : Nat) (lower : 1138688 ≤ index) (upper : index < 1139200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1138944 then
    if cut : index < 1138816 then
      exact segment_sound _ 1138688 128 Restriction2224_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1138816 128 Restriction2224_1_checked index (by omega) (by omega)
  else
    if cut : index < 1139072 then
      exact segment_sound _ 1138944 128 Restriction2224_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1139072 128 Restriction2224_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
