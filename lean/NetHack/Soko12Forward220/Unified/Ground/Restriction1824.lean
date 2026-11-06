import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1824_0_checked : (List.range' 933888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1824_1_checked : (List.range' 934016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1824_2_checked : (List.range' 934144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1824_3_checked : (List.range' 934272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1824_range (index : Nat) (lower : 933888 ≤ index) (upper : index < 934400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 934144 then
    if cut : index < 934016 then
      exact segment_sound _ 933888 128 Restriction1824_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 934016 128 Restriction1824_1_checked index (by omega) (by omega)
  else
    if cut : index < 934272 then
      exact segment_sound _ 934144 128 Restriction1824_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 934272 128 Restriction1824_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
