import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2349_0_checked : (List.range' 1202688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2349_1_checked : (List.range' 1202816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2349_2_checked : (List.range' 1202944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2349_3_checked : (List.range' 1203072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2349_range (index : Nat) (lower : 1202688 ≤ index) (upper : index < 1203200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1202944 then
    if cut : index < 1202816 then
      exact segment_sound _ 1202688 128 Restriction2349_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1202816 128 Restriction2349_1_checked index (by omega) (by omega)
  else
    if cut : index < 1203072 then
      exact segment_sound _ 1202944 128 Restriction2349_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1203072 128 Restriction2349_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
