import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0570_0_checked : (List.range' 291840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0570_1_checked : (List.range' 291968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0570_2_checked : (List.range' 292096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0570_3_checked : (List.range' 292224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0570_range (index : Nat) (lower : 291840 ≤ index) (upper : index < 292352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 292096 then
    if cut : index < 291968 then
      exact segment_sound _ 291840 128 Restriction0570_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 291968 128 Restriction0570_1_checked index (by omega) (by omega)
  else
    if cut : index < 292224 then
      exact segment_sound _ 292096 128 Restriction0570_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 292224 128 Restriction0570_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
