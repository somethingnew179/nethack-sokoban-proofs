import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0800_0_checked : (List.range' 409600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0800_1_checked : (List.range' 409728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0800_2_checked : (List.range' 409856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0800_3_checked : (List.range' 409984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0800_range (index : Nat) (lower : 409600 ≤ index) (upper : index < 410112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 409856 then
    if cut : index < 409728 then
      exact segment_sound _ 409600 128 Restriction0800_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 409728 128 Restriction0800_1_checked index (by omega) (by omega)
  else
    if cut : index < 409984 then
      exact segment_sound _ 409856 128 Restriction0800_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 409984 128 Restriction0800_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
