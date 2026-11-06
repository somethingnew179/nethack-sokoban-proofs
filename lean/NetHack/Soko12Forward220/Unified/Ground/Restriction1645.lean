import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1645_0_checked : (List.range' 842240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1645_1_checked : (List.range' 842368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1645_2_checked : (List.range' 842496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1645_3_checked : (List.range' 842624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1645_range (index : Nat) (lower : 842240 ≤ index) (upper : index < 842752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 842496 then
    if cut : index < 842368 then
      exact segment_sound _ 842240 128 Restriction1645_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 842368 128 Restriction1645_1_checked index (by omega) (by omega)
  else
    if cut : index < 842624 then
      exact segment_sound _ 842496 128 Restriction1645_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 842624 128 Restriction1645_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
