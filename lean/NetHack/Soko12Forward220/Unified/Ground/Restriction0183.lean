import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0183_0_checked : (List.range' 93696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0183_1_checked : (List.range' 93824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0183_2_checked : (List.range' 93952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0183_3_checked : (List.range' 94080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0183_range (index : Nat) (lower : 93696 ≤ index) (upper : index < 94208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 93952 then
    if cut : index < 93824 then
      exact segment_sound _ 93696 128 Restriction0183_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 93824 128 Restriction0183_1_checked index (by omega) (by omega)
  else
    if cut : index < 94080 then
      exact segment_sound _ 93952 128 Restriction0183_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 94080 128 Restriction0183_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
