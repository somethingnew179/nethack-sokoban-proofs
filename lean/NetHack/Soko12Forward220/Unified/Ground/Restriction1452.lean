import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1452_0_checked : (List.range' 743424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1452_1_checked : (List.range' 743552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1452_2_checked : (List.range' 743680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1452_3_checked : (List.range' 743808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1452_range (index : Nat) (lower : 743424 ≤ index) (upper : index < 743936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 743680 then
    if cut : index < 743552 then
      exact segment_sound _ 743424 128 Restriction1452_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 743552 128 Restriction1452_1_checked index (by omega) (by omega)
  else
    if cut : index < 743808 then
      exact segment_sound _ 743680 128 Restriction1452_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 743808 128 Restriction1452_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
