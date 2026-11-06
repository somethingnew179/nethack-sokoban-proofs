import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0488_0_checked : (List.range' 249856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0488_1_checked : (List.range' 249984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0488_2_checked : (List.range' 250112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0488_3_checked : (List.range' 250240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0488_range (index : Nat) (lower : 249856 ≤ index) (upper : index < 250368) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 250112 then
    if cut : index < 249984 then
      exact segment_sound _ 249856 128 Restriction0488_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 249984 128 Restriction0488_1_checked index (by omega) (by omega)
  else
    if cut : index < 250240 then
      exact segment_sound _ 250112 128 Restriction0488_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 250240 128 Restriction0488_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
