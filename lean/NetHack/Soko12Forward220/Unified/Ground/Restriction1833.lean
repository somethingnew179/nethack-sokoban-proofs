import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1833_0_checked : (List.range' 938496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1833_1_checked : (List.range' 938624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1833_2_checked : (List.range' 938752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1833_3_checked : (List.range' 938880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1833_range (index : Nat) (lower : 938496 ≤ index) (upper : index < 939008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 938752 then
    if cut : index < 938624 then
      exact segment_sound _ 938496 128 Restriction1833_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 938624 128 Restriction1833_1_checked index (by omega) (by omega)
  else
    if cut : index < 938880 then
      exact segment_sound _ 938752 128 Restriction1833_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 938880 128 Restriction1833_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
