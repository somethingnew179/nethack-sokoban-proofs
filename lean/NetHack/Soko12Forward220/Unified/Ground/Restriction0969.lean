import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0969_0_checked : (List.range' 496128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0969_1_checked : (List.range' 496256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0969_2_checked : (List.range' 496384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0969_3_checked : (List.range' 496512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0969_range (index : Nat) (lower : 496128 ≤ index) (upper : index < 496640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 496384 then
    if cut : index < 496256 then
      exact segment_sound _ 496128 128 Restriction0969_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 496256 128 Restriction0969_1_checked index (by omega) (by omega)
  else
    if cut : index < 496512 then
      exact segment_sound _ 496384 128 Restriction0969_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 496512 128 Restriction0969_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
