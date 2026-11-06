import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0848_0_checked : (List.range' 434176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0848_1_checked : (List.range' 434304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0848_2_checked : (List.range' 434432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0848_3_checked : (List.range' 434560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0848_range (index : Nat) (lower : 434176 ≤ index) (upper : index < 434688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 434432 then
    if cut : index < 434304 then
      exact segment_sound _ 434176 128 Restriction0848_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 434304 128 Restriction0848_1_checked index (by omega) (by omega)
  else
    if cut : index < 434560 then
      exact segment_sound _ 434432 128 Restriction0848_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 434560 128 Restriction0848_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
