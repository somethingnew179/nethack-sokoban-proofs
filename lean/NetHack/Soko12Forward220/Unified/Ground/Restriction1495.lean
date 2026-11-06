import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1495_0_checked : (List.range' 765440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1495_1_checked : (List.range' 765568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1495_2_checked : (List.range' 765696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1495_3_checked : (List.range' 765824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1495_range (index : Nat) (lower : 765440 ≤ index) (upper : index < 765952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 765696 then
    if cut : index < 765568 then
      exact segment_sound _ 765440 128 Restriction1495_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 765568 128 Restriction1495_1_checked index (by omega) (by omega)
  else
    if cut : index < 765824 then
      exact segment_sound _ 765696 128 Restriction1495_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 765824 128 Restriction1495_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
