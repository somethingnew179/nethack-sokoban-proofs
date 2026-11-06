import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0728_0_checked : (List.range' 372736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0728_1_checked : (List.range' 372864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0728_2_checked : (List.range' 372992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0728_3_checked : (List.range' 373120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0728_range (index : Nat) (lower : 372736 ≤ index) (upper : index < 373248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 372992 then
    if cut : index < 372864 then
      exact segment_sound _ 372736 128 Restriction0728_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 372864 128 Restriction0728_1_checked index (by omega) (by omega)
  else
    if cut : index < 373120 then
      exact segment_sound _ 372992 128 Restriction0728_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 373120 128 Restriction0728_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
