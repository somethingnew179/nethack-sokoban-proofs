import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0314_0_checked : (List.range' 160768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0314_1_checked : (List.range' 160896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0314_2_checked : (List.range' 161024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0314_3_checked : (List.range' 161152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0314_range (index : Nat) (lower : 160768 ≤ index) (upper : index < 161280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 161024 then
    if cut : index < 160896 then
      exact segment_sound _ 160768 128 Restriction0314_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 160896 128 Restriction0314_1_checked index (by omega) (by omega)
  else
    if cut : index < 161152 then
      exact segment_sound _ 161024 128 Restriction0314_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 161152 128 Restriction0314_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
