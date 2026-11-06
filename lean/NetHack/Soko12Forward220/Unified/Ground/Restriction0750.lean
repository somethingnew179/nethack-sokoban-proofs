import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0750_0_checked : (List.range' 384000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0750_1_checked : (List.range' 384128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0750_2_checked : (List.range' 384256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0750_3_checked : (List.range' 384384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0750_range (index : Nat) (lower : 384000 ≤ index) (upper : index < 384512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 384256 then
    if cut : index < 384128 then
      exact segment_sound _ 384000 128 Restriction0750_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 384128 128 Restriction0750_1_checked index (by omega) (by omega)
  else
    if cut : index < 384384 then
      exact segment_sound _ 384256 128 Restriction0750_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 384384 128 Restriction0750_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
