import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1165_0_checked : (List.range' 596480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1165_1_checked : (List.range' 596608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1165_2_checked : (List.range' 596736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1165_3_checked : (List.range' 596864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1165_range (index : Nat) (lower : 596480 ≤ index) (upper : index < 596992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 596736 then
    if cut : index < 596608 then
      exact segment_sound _ 596480 128 Restriction1165_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 596608 128 Restriction1165_1_checked index (by omega) (by omega)
  else
    if cut : index < 596864 then
      exact segment_sound _ 596736 128 Restriction1165_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 596864 128 Restriction1165_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
