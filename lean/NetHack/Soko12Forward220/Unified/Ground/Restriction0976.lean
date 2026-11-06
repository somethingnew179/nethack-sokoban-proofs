import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0976_0_checked : (List.range' 499712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0976_1_checked : (List.range' 499840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0976_2_checked : (List.range' 499968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0976_3_checked : (List.range' 500096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0976_range (index : Nat) (lower : 499712 ≤ index) (upper : index < 500224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 499968 then
    if cut : index < 499840 then
      exact segment_sound _ 499712 128 Restriction0976_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 499840 128 Restriction0976_1_checked index (by omega) (by omega)
  else
    if cut : index < 500096 then
      exact segment_sound _ 499968 128 Restriction0976_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 500096 128 Restriction0976_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
