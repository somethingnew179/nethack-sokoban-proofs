import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1512_0_checked : (List.range' 774144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1512_1_checked : (List.range' 774272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1512_2_checked : (List.range' 774400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1512_3_checked : (List.range' 774528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1512_range (index : Nat) (lower : 774144 ≤ index) (upper : index < 774656) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 774400 then
    if cut : index < 774272 then
      exact segment_sound _ 774144 128 Restriction1512_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 774272 128 Restriction1512_1_checked index (by omega) (by omega)
  else
    if cut : index < 774528 then
      exact segment_sound _ 774400 128 Restriction1512_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 774528 128 Restriction1512_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
