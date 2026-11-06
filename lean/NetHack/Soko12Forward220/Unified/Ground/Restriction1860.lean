import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1860_0_checked : (List.range' 952320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1860_1_checked : (List.range' 952448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1860_2_checked : (List.range' 952576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1860_3_checked : (List.range' 952704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1860_range (index : Nat) (lower : 952320 ≤ index) (upper : index < 952832) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 952576 then
    if cut : index < 952448 then
      exact segment_sound _ 952320 128 Restriction1860_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 952448 128 Restriction1860_1_checked index (by omega) (by omega)
  else
    if cut : index < 952704 then
      exact segment_sound _ 952576 128 Restriction1860_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 952704 128 Restriction1860_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
