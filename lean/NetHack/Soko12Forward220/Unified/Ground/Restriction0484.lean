import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0484_0_checked : (List.range' 247808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0484_1_checked : (List.range' 247936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0484_2_checked : (List.range' 248064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0484_3_checked : (List.range' 248192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0484_range (index : Nat) (lower : 247808 ≤ index) (upper : index < 248320) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 248064 then
    if cut : index < 247936 then
      exact segment_sound _ 247808 128 Restriction0484_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 247936 128 Restriction0484_1_checked index (by omega) (by omega)
  else
    if cut : index < 248192 then
      exact segment_sound _ 248064 128 Restriction0484_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 248192 128 Restriction0484_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
