import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1302_0_checked : (List.range' 666624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1302_1_checked : (List.range' 666752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1302_2_checked : (List.range' 666880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1302_3_checked : (List.range' 667008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1302_range (index : Nat) (lower : 666624 ≤ index) (upper : index < 667136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 666880 then
    if cut : index < 666752 then
      exact segment_sound _ 666624 128 Restriction1302_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 666752 128 Restriction1302_1_checked index (by omega) (by omega)
  else
    if cut : index < 667008 then
      exact segment_sound _ 666880 128 Restriction1302_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 667008 128 Restriction1302_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
