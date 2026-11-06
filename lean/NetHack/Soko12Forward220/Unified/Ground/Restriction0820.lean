import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0820_0_checked : (List.range' 419840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0820_1_checked : (List.range' 419968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0820_2_checked : (List.range' 420096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0820_3_checked : (List.range' 420224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0820_range (index : Nat) (lower : 419840 ≤ index) (upper : index < 420352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 420096 then
    if cut : index < 419968 then
      exact segment_sound _ 419840 128 Restriction0820_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 419968 128 Restriction0820_1_checked index (by omega) (by omega)
  else
    if cut : index < 420224 then
      exact segment_sound _ 420096 128 Restriction0820_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 420224 128 Restriction0820_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
