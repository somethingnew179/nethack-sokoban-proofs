import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1675_0_checked : (List.range' 857600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1675_1_checked : (List.range' 857728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1675_2_checked : (List.range' 857856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1675_3_checked : (List.range' 857984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1675_range (index : Nat) (lower : 857600 ≤ index) (upper : index < 858112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 857856 then
    if cut : index < 857728 then
      exact segment_sound _ 857600 128 Restriction1675_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 857728 128 Restriction1675_1_checked index (by omega) (by omega)
  else
    if cut : index < 857984 then
      exact segment_sound _ 857856 128 Restriction1675_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 857984 128 Restriction1675_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
