import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0940_0_checked : (List.range' 481280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0940_1_checked : (List.range' 481408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0940_2_checked : (List.range' 481536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0940_3_checked : (List.range' 481664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0940_range (index : Nat) (lower : 481280 ≤ index) (upper : index < 481792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 481536 then
    if cut : index < 481408 then
      exact segment_sound _ 481280 128 Restriction0940_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 481408 128 Restriction0940_1_checked index (by omega) (by omega)
  else
    if cut : index < 481664 then
      exact segment_sound _ 481536 128 Restriction0940_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 481664 128 Restriction0940_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
