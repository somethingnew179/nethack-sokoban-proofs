import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1489_0_checked : (List.range' 762368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1489_1_checked : (List.range' 762496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1489_2_checked : (List.range' 762624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1489_3_checked : (List.range' 762752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1489_range (index : Nat) (lower : 762368 ≤ index) (upper : index < 762880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 762624 then
    if cut : index < 762496 then
      exact segment_sound _ 762368 128 Restriction1489_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 762496 128 Restriction1489_1_checked index (by omega) (by omega)
  else
    if cut : index < 762752 then
      exact segment_sound _ 762624 128 Restriction1489_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 762752 128 Restriction1489_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
