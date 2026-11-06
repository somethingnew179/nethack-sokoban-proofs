import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0378_0_checked : (List.range' 193536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0378_1_checked : (List.range' 193664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0378_2_checked : (List.range' 193792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0378_3_checked : (List.range' 193920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0378_range (index : Nat) (lower : 193536 ≤ index) (upper : index < 194048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 193792 then
    if cut : index < 193664 then
      exact segment_sound _ 193536 128 Restriction0378_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 193664 128 Restriction0378_1_checked index (by omega) (by omega)
  else
    if cut : index < 193920 then
      exact segment_sound _ 193792 128 Restriction0378_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 193920 128 Restriction0378_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
