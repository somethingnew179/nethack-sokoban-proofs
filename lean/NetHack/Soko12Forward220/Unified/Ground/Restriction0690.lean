import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0690_0_checked : (List.range' 353280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0690_1_checked : (List.range' 353408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0690_2_checked : (List.range' 353536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0690_3_checked : (List.range' 353664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0690_range (index : Nat) (lower : 353280 ≤ index) (upper : index < 353792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 353536 then
    if cut : index < 353408 then
      exact segment_sound _ 353280 128 Restriction0690_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 353408 128 Restriction0690_1_checked index (by omega) (by omega)
  else
    if cut : index < 353664 then
      exact segment_sound _ 353536 128 Restriction0690_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 353664 128 Restriction0690_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
