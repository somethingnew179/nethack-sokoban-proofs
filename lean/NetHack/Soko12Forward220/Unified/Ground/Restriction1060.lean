import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1060_0_checked : (List.range' 542720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1060_1_checked : (List.range' 542848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1060_2_checked : (List.range' 542976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1060_3_checked : (List.range' 543104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1060_range (index : Nat) (lower : 542720 ≤ index) (upper : index < 543232) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 542976 then
    if cut : index < 542848 then
      exact segment_sound _ 542720 128 Restriction1060_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 542848 128 Restriction1060_1_checked index (by omega) (by omega)
  else
    if cut : index < 543104 then
      exact segment_sound _ 542976 128 Restriction1060_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 543104 128 Restriction1060_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
