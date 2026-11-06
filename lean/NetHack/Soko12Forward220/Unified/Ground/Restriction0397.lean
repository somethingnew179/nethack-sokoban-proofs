import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0397_0_checked : (List.range' 203264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0397_1_checked : (List.range' 203392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0397_2_checked : (List.range' 203520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0397_3_checked : (List.range' 203648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0397_range (index : Nat) (lower : 203264 ≤ index) (upper : index < 203776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 203520 then
    if cut : index < 203392 then
      exact segment_sound _ 203264 128 Restriction0397_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 203392 128 Restriction0397_1_checked index (by omega) (by omega)
  else
    if cut : index < 203648 then
      exact segment_sound _ 203520 128 Restriction0397_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 203648 128 Restriction0397_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
