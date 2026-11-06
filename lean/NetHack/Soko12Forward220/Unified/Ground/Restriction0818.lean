import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0818_0_checked : (List.range' 418816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0818_1_checked : (List.range' 418944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0818_2_checked : (List.range' 419072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0818_3_checked : (List.range' 419200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0818_range (index : Nat) (lower : 418816 ≤ index) (upper : index < 419328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 419072 then
    if cut : index < 418944 then
      exact segment_sound _ 418816 128 Restriction0818_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 418944 128 Restriction0818_1_checked index (by omega) (by omega)
  else
    if cut : index < 419200 then
      exact segment_sound _ 419072 128 Restriction0818_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 419200 128 Restriction0818_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
