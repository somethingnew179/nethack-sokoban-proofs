import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0106_0_checked : (List.range' 54272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0106_1_checked : (List.range' 54400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0106_2_checked : (List.range' 54528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0106_3_checked : (List.range' 54656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0106_range (index : Nat) (lower : 54272 ≤ index) (upper : index < 54784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 54528 then
    if cut : index < 54400 then
      exact segment_sound _ 54272 128 Restriction0106_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 54400 128 Restriction0106_1_checked index (by omega) (by omega)
  else
    if cut : index < 54656 then
      exact segment_sound _ 54528 128 Restriction0106_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 54656 128 Restriction0106_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
