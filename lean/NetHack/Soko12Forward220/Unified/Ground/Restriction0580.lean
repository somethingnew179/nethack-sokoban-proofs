import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0580_0_checked : (List.range' 296960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0580_1_checked : (List.range' 297088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0580_2_checked : (List.range' 297216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0580_3_checked : (List.range' 297344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0580_range (index : Nat) (lower : 296960 ≤ index) (upper : index < 297472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 297216 then
    if cut : index < 297088 then
      exact segment_sound _ 296960 128 Restriction0580_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 297088 128 Restriction0580_1_checked index (by omega) (by omega)
  else
    if cut : index < 297344 then
      exact segment_sound _ 297216 128 Restriction0580_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 297344 128 Restriction0580_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
