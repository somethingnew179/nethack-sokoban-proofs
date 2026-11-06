import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1716_0_checked : (List.range' 878592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1716_1_checked : (List.range' 878720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1716_2_checked : (List.range' 878848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1716_3_checked : (List.range' 878976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1716_range (index : Nat) (lower : 878592 ≤ index) (upper : index < 879104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 878848 then
    if cut : index < 878720 then
      exact segment_sound _ 878592 128 Restriction1716_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 878720 128 Restriction1716_1_checked index (by omega) (by omega)
  else
    if cut : index < 878976 then
      exact segment_sound _ 878848 128 Restriction1716_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 878976 128 Restriction1716_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
