import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0974_0_checked : (List.range' 498688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0974_1_checked : (List.range' 498816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0974_2_checked : (List.range' 498944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0974_3_checked : (List.range' 499072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0974_range (index : Nat) (lower : 498688 ≤ index) (upper : index < 499200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 498944 then
    if cut : index < 498816 then
      exact segment_sound _ 498688 128 Restriction0974_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 498816 128 Restriction0974_1_checked index (by omega) (by omega)
  else
    if cut : index < 499072 then
      exact segment_sound _ 498944 128 Restriction0974_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 499072 128 Restriction0974_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
