import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0267_0_checked : (List.range' 136704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0267_1_checked : (List.range' 136832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0267_2_checked : (List.range' 136960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0267_3_checked : (List.range' 137088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0267_range (index : Nat) (lower : 136704 ≤ index) (upper : index < 137216) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 136960 then
    if cut : index < 136832 then
      exact segment_sound _ 136704 128 Restriction0267_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 136832 128 Restriction0267_1_checked index (by omega) (by omega)
  else
    if cut : index < 137088 then
      exact segment_sound _ 136960 128 Restriction0267_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 137088 128 Restriction0267_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
