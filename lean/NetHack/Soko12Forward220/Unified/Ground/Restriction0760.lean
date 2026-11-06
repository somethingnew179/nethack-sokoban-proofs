import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0760_0_checked : (List.range' 389120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0760_1_checked : (List.range' 389248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0760_2_checked : (List.range' 389376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0760_3_checked : (List.range' 389504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0760_range (index : Nat) (lower : 389120 ≤ index) (upper : index < 389632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 389376 then
    if cut : index < 389248 then
      exact segment_sound _ 389120 128 Restriction0760_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 389248 128 Restriction0760_1_checked index (by omega) (by omega)
  else
    if cut : index < 389504 then
      exact segment_sound _ 389376 128 Restriction0760_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 389504 128 Restriction0760_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
