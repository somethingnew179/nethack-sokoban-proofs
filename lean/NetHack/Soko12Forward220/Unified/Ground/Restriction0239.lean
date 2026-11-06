import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0239_0_checked : (List.range' 122368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0239_1_checked : (List.range' 122496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0239_2_checked : (List.range' 122624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0239_3_checked : (List.range' 122752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0239_range (index : Nat) (lower : 122368 ≤ index) (upper : index < 122880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 122624 then
    if cut : index < 122496 then
      exact segment_sound _ 122368 128 Restriction0239_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 122496 128 Restriction0239_1_checked index (by omega) (by omega)
  else
    if cut : index < 122752 then
      exact segment_sound _ 122624 128 Restriction0239_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 122752 128 Restriction0239_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
