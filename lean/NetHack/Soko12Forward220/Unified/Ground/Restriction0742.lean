import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0742_0_checked : (List.range' 379904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0742_1_checked : (List.range' 380032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0742_2_checked : (List.range' 380160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0742_3_checked : (List.range' 380288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0742_range (index : Nat) (lower : 379904 ≤ index) (upper : index < 380416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 380160 then
    if cut : index < 380032 then
      exact segment_sound _ 379904 128 Restriction0742_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 380032 128 Restriction0742_1_checked index (by omega) (by omega)
  else
    if cut : index < 380288 then
      exact segment_sound _ 380160 128 Restriction0742_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 380288 128 Restriction0742_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
