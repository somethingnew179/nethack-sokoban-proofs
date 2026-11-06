import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0827_0_checked : (List.range' 423424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0827_1_checked : (List.range' 423552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0827_2_checked : (List.range' 423680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0827_3_checked : (List.range' 423808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0827_range (index : Nat) (lower : 423424 ≤ index) (upper : index < 423936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 423680 then
    if cut : index < 423552 then
      exact segment_sound _ 423424 128 Restriction0827_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 423552 128 Restriction0827_1_checked index (by omega) (by omega)
  else
    if cut : index < 423808 then
      exact segment_sound _ 423680 128 Restriction0827_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 423808 128 Restriction0827_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
