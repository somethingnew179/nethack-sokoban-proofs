import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0368_0_checked : (List.range' 188416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0368_1_checked : (List.range' 188544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0368_2_checked : (List.range' 188672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0368_3_checked : (List.range' 188800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0368_range (index : Nat) (lower : 188416 ≤ index) (upper : index < 188928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 188672 then
    if cut : index < 188544 then
      exact segment_sound _ 188416 128 Restriction0368_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 188544 128 Restriction0368_1_checked index (by omega) (by omega)
  else
    if cut : index < 188800 then
      exact segment_sound _ 188672 128 Restriction0368_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 188800 128 Restriction0368_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
