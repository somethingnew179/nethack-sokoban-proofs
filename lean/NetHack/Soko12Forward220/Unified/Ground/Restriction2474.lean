import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2474_0_checked : (List.range' 1266688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2474_1_checked : (List.range' 1266816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2474_2_checked : (List.range' 1266944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2474_3_checked : (List.range' 1267072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2474_range (index : Nat) (lower : 1266688 ≤ index) (upper : index < 1267200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1266944 then
    if cut : index < 1266816 then
      exact segment_sound _ 1266688 128 Restriction2474_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1266816 128 Restriction2474_1_checked index (by omega) (by omega)
  else
    if cut : index < 1267072 then
      exact segment_sound _ 1266944 128 Restriction2474_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1267072 128 Restriction2474_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
