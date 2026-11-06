import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2227_0_checked : (List.range' 1140224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2227_1_checked : (List.range' 1140352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2227_2_checked : (List.range' 1140480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2227_3_checked : (List.range' 1140608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2227_range (index : Nat) (lower : 1140224 ≤ index) (upper : index < 1140736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1140480 then
    if cut : index < 1140352 then
      exact segment_sound _ 1140224 128 Restriction2227_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1140352 128 Restriction2227_1_checked index (by omega) (by omega)
  else
    if cut : index < 1140608 then
      exact segment_sound _ 1140480 128 Restriction2227_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1140608 128 Restriction2227_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
