import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0023_0_checked : (List.range' 11776 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0023_1_checked : (List.range' 11904 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0023_2_checked : (List.range' 12032 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0023_3_checked : (List.range' 12160 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0023_range (index : Nat) (lower : 11776 ≤ index) (upper : index < 12288) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 12032 then
    if cut : index < 11904 then
      exact segment_sound _ 11776 128 Numeric0023_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 11904 128 Numeric0023_1_checked index (by omega) (by omega)
  else
    if cut : index < 12160 then
      exact segment_sound _ 12032 128 Numeric0023_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 12160 128 Numeric0023_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
