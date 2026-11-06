import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0861_0_checked : (List.range' 440832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0861_1_checked : (List.range' 440960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0861_2_checked : (List.range' 441088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0861_3_checked : (List.range' 441216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0861_range (index : Nat) (lower : 440832 ≤ index) (upper : index < 441344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 441088 then
    if cut : index < 440960 then
      exact segment_sound _ 440832 128 Restriction0861_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 440960 128 Restriction0861_1_checked index (by omega) (by omega)
  else
    if cut : index < 441216 then
      exact segment_sound _ 441088 128 Restriction0861_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 441216 128 Restriction0861_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
