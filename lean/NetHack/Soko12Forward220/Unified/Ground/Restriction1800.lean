import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1800_0_checked : (List.range' 921600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1800_1_checked : (List.range' 921728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1800_2_checked : (List.range' 921856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1800_3_checked : (List.range' 921984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1800_range (index : Nat) (lower : 921600 ≤ index) (upper : index < 922112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 921856 then
    if cut : index < 921728 then
      exact segment_sound _ 921600 128 Restriction1800_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 921728 128 Restriction1800_1_checked index (by omega) (by omega)
  else
    if cut : index < 921984 then
      exact segment_sound _ 921856 128 Restriction1800_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 921984 128 Restriction1800_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
