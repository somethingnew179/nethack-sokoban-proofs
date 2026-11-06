import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1829_0_checked : (List.range' 936448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1829_1_checked : (List.range' 936576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1829_2_checked : (List.range' 936704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1829_3_checked : (List.range' 936832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1829_range (index : Nat) (lower : 936448 ≤ index) (upper : index < 936960) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 936704 then
    if cut : index < 936576 then
      exact segment_sound _ 936448 128 Restriction1829_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 936576 128 Restriction1829_1_checked index (by omega) (by omega)
  else
    if cut : index < 936832 then
      exact segment_sound _ 936704 128 Restriction1829_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 936832 128 Restriction1829_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
