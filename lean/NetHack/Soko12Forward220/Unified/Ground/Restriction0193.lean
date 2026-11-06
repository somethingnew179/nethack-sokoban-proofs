import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0193_0_checked : (List.range' 98816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0193_1_checked : (List.range' 98944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0193_2_checked : (List.range' 99072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0193_3_checked : (List.range' 99200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0193_range (index : Nat) (lower : 98816 ≤ index) (upper : index < 99328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 99072 then
    if cut : index < 98944 then
      exact segment_sound _ 98816 128 Restriction0193_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 98944 128 Restriction0193_1_checked index (by omega) (by omega)
  else
    if cut : index < 99200 then
      exact segment_sound _ 99072 128 Restriction0193_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 99200 128 Restriction0193_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
