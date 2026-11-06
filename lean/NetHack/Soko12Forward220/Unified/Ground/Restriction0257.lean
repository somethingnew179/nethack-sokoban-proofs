import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0257_0_checked : (List.range' 131584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0257_1_checked : (List.range' 131712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0257_2_checked : (List.range' 131840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0257_3_checked : (List.range' 131968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0257_range (index : Nat) (lower : 131584 ≤ index) (upper : index < 132096) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 131840 then
    if cut : index < 131712 then
      exact segment_sound _ 131584 128 Restriction0257_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 131712 128 Restriction0257_1_checked index (by omega) (by omega)
  else
    if cut : index < 131968 then
      exact segment_sound _ 131840 128 Restriction0257_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 131968 128 Restriction0257_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
