import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0349_0_checked : (List.range' 178688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0349_1_checked : (List.range' 178816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0349_2_checked : (List.range' 178944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0349_3_checked : (List.range' 179072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0349_range (index : Nat) (lower : 178688 ≤ index) (upper : index < 179200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 178944 then
    if cut : index < 178816 then
      exact segment_sound _ 178688 128 Restriction0349_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 178816 128 Restriction0349_1_checked index (by omega) (by omega)
  else
    if cut : index < 179072 then
      exact segment_sound _ 178944 128 Restriction0349_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 179072 128 Restriction0349_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
