import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0691_0_checked : (List.range' 353792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0691_1_checked : (List.range' 353920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0691_2_checked : (List.range' 354048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0691_3_checked : (List.range' 354176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0691_range (index : Nat) (lower : 353792 ≤ index) (upper : index < 354304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 354048 then
    if cut : index < 353920 then
      exact segment_sound _ 353792 128 Restriction0691_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 353920 128 Restriction0691_1_checked index (by omega) (by omega)
  else
    if cut : index < 354176 then
      exact segment_sound _ 354048 128 Restriction0691_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 354176 128 Restriction0691_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
