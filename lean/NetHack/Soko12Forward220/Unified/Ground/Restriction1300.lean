import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1300_0_checked : (List.range' 665600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1300_1_checked : (List.range' 665728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1300_2_checked : (List.range' 665856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1300_3_checked : (List.range' 665984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1300_range (index : Nat) (lower : 665600 ≤ index) (upper : index < 666112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 665856 then
    if cut : index < 665728 then
      exact segment_sound _ 665600 128 Restriction1300_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 665728 128 Restriction1300_1_checked index (by omega) (by omega)
  else
    if cut : index < 665984 then
      exact segment_sound _ 665856 128 Restriction1300_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 665984 128 Restriction1300_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
