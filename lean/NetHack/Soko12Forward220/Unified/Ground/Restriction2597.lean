import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2597_0_checked : (List.range' 1329664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2597_1_checked : (List.range' 1329792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2597_2_checked : (List.range' 1329920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2597_3_checked : (List.range' 1330048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2597_range (index : Nat) (lower : 1329664 ≤ index) (upper : index < 1330176) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1329920 then
    if cut : index < 1329792 then
      exact segment_sound _ 1329664 128 Restriction2597_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1329792 128 Restriction2597_1_checked index (by omega) (by omega)
  else
    if cut : index < 1330048 then
      exact segment_sound _ 1329920 128 Restriction2597_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1330048 128 Restriction2597_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
