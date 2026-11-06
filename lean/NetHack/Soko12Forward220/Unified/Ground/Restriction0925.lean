import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0925_0_checked : (List.range' 473600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0925_1_checked : (List.range' 473728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0925_2_checked : (List.range' 473856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0925_3_checked : (List.range' 473984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0925_range (index : Nat) (lower : 473600 ≤ index) (upper : index < 474112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 473856 then
    if cut : index < 473728 then
      exact segment_sound _ 473600 128 Restriction0925_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 473728 128 Restriction0925_1_checked index (by omega) (by omega)
  else
    if cut : index < 473984 then
      exact segment_sound _ 473856 128 Restriction0925_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 473984 128 Restriction0925_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
