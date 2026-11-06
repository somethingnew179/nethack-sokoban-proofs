import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2151_0_checked : (List.range' 1101312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2151_1_checked : (List.range' 1101440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2151_2_checked : (List.range' 1101568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2151_3_checked : (List.range' 1101696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2151_range (index : Nat) (lower : 1101312 ≤ index) (upper : index < 1101824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1101568 then
    if cut : index < 1101440 then
      exact segment_sound _ 1101312 128 Restriction2151_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1101440 128 Restriction2151_1_checked index (by omega) (by omega)
  else
    if cut : index < 1101696 then
      exact segment_sound _ 1101568 128 Restriction2151_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1101696 128 Restriction2151_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
