import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0275_0_checked : (List.range' 140800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0275_1_checked : (List.range' 140928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0275_2_checked : (List.range' 141056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0275_3_checked : (List.range' 141184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0275_range (index : Nat) (lower : 140800 ≤ index) (upper : index < 141312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 141056 then
    if cut : index < 140928 then
      exact segment_sound _ 140800 128 Restriction0275_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 140928 128 Restriction0275_1_checked index (by omega) (by omega)
  else
    if cut : index < 141184 then
      exact segment_sound _ 141056 128 Restriction0275_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 141184 128 Restriction0275_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
