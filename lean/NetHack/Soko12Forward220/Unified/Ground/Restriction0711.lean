import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0711_0_checked : (List.range' 364032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0711_1_checked : (List.range' 364160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0711_2_checked : (List.range' 364288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0711_3_checked : (List.range' 364416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0711_range (index : Nat) (lower : 364032 ≤ index) (upper : index < 364544) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 364288 then
    if cut : index < 364160 then
      exact segment_sound _ 364032 128 Restriction0711_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 364160 128 Restriction0711_1_checked index (by omega) (by omega)
  else
    if cut : index < 364416 then
      exact segment_sound _ 364288 128 Restriction0711_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 364416 128 Restriction0711_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
