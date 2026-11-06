import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0844_0_checked : (List.range' 432128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0844_1_checked : (List.range' 432256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0844_2_checked : (List.range' 432384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0844_3_checked : (List.range' 432512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0844_range (index : Nat) (lower : 432128 ≤ index) (upper : index < 432640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 432384 then
    if cut : index < 432256 then
      exact segment_sound _ 432128 128 Restriction0844_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 432256 128 Restriction0844_1_checked index (by omega) (by omega)
  else
    if cut : index < 432512 then
      exact segment_sound _ 432384 128 Restriction0844_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 432512 128 Restriction0844_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
