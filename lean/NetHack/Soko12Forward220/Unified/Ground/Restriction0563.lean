import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0563_0_checked : (List.range' 288256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0563_1_checked : (List.range' 288384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0563_2_checked : (List.range' 288512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0563_3_checked : (List.range' 288640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0563_range (index : Nat) (lower : 288256 ≤ index) (upper : index < 288768) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 288512 then
    if cut : index < 288384 then
      exact segment_sound _ 288256 128 Restriction0563_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 288384 128 Restriction0563_1_checked index (by omega) (by omega)
  else
    if cut : index < 288640 then
      exact segment_sound _ 288512 128 Restriction0563_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 288640 128 Restriction0563_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
