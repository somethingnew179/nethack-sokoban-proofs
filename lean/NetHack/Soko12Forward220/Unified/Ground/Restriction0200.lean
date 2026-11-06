import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0200_0_checked : (List.range' 102400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0200_1_checked : (List.range' 102528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0200_2_checked : (List.range' 102656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0200_3_checked : (List.range' 102784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0200_range (index : Nat) (lower : 102400 ≤ index) (upper : index < 102912) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 102656 then
    if cut : index < 102528 then
      exact segment_sound _ 102400 128 Restriction0200_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 102528 128 Restriction0200_1_checked index (by omega) (by omega)
  else
    if cut : index < 102784 then
      exact segment_sound _ 102656 128 Restriction0200_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 102784 128 Restriction0200_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
