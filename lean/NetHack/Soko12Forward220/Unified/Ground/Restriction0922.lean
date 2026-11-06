import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0922_0_checked : (List.range' 472064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0922_1_checked : (List.range' 472192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0922_2_checked : (List.range' 472320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0922_3_checked : (List.range' 472448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0922_range (index : Nat) (lower : 472064 ≤ index) (upper : index < 472576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 472320 then
    if cut : index < 472192 then
      exact segment_sound _ 472064 128 Restriction0922_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 472192 128 Restriction0922_1_checked index (by omega) (by omega)
  else
    if cut : index < 472448 then
      exact segment_sound _ 472320 128 Restriction0922_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 472448 128 Restriction0922_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
