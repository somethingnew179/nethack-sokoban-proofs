import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1822_0_checked : (List.range' 932864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1822_1_checked : (List.range' 932992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1822_2_checked : (List.range' 933120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1822_3_checked : (List.range' 933248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1822_range (index : Nat) (lower : 932864 ≤ index) (upper : index < 933376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 933120 then
    if cut : index < 932992 then
      exact segment_sound _ 932864 128 Restriction1822_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 932992 128 Restriction1822_1_checked index (by omega) (by omega)
  else
    if cut : index < 933248 then
      exact segment_sound _ 933120 128 Restriction1822_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 933248 128 Restriction1822_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
