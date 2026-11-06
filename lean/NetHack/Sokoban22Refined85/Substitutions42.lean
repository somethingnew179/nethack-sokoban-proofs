/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions41
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub5040 (p : Pattern) : d874 (change p 161 (some 162)) = d153 p := by
  change d153 (change p 161 (some 162)) = d153 p
  exact sub5039 p
theorem sub5041 (p : Pattern) : d875 (change p 161 (some 162)) = d153 p := by
  change d874 (change p 161 (some 162)) = d153 p
  exact sub5040 p
theorem sub5042 (p : Pattern) : d876 (change p 161 (some 162)) = d4635 p := by
  change (if p 160 then d875 (change p 161 (some 162)) else d872 (change p 161 (some 162))) = d4635 p
  rw [sub5041, sub5038]
  rfl
theorem sub5043 (p : Pattern) : d877 (change p 161 (some 162)) = d4636 p := by
  change (if p 141 then d876 (change p 161 (some 162)) else d871 (change p 161 (some 162))) = d4636 p
  rw [sub5042, sub5037]
  rfl
theorem sub5044 (p : Pattern) : d878 (change p 161 (some 162)) = d4637 p := by
  change (if p 138 then d877 (change p 161 (some 162)) else d867 (change p 161 (some 162))) = d4637 p
  rw [sub5043, sub5033]
  rfl
theorem sub5045 (p : Pattern) : d879 (change p 161 (some 162)) = d110 p := by
  change d111 (change p 161 (some 162)) = d110 p
  exact sub5004 p
theorem sub5046 (p : Pattern) : d880 (change p 161 (some 162)) = d4632 p := by
  change (if p 160 then d870 (change p 161 (some 162)) else d879 (change p 161 (some 162))) = d4632 p
  rw [sub5036, sub5045]
  rfl
theorem sub5047 (p : Pattern) : d881 (change p 161 (some 162)) = d4636 p := by
  change (if p 141 then d876 (change p 161 (some 162)) else d880 (change p 161 (some 162))) = d4636 p
  rw [sub5042, sub5046]
  rfl
theorem sub5048 (p : Pattern) : d159 (change p 161 (some 162)) = d12 p := by
  change d12 (change p 161 (some 162)) = d12 p
  exact sub4890 p
theorem sub5049 (p : Pattern) : d160 (change p 161 (some 162)) = d12 p := by
  change d159 (change p 161 (some 162)) = d12 p
  exact sub5048 p
theorem sub5050 (p : Pattern) : d161 (change p 161 (some 162)) = d12 p := by
  change (if p 160 then d12 (change p 161 (some 162)) else d160 (change p 161 (some 162))) = d12 p
  rw [sub4890, sub5049]
  simp only [ite_self]
theorem sub5051 (p : Pattern) : d162 (change p 161 (some 162)) = d12 p := by
  change (if p 141 then d12 (change p 161 (some 162)) else d161 (change p 161 (some 162))) = d12 p
  rw [sub4890, sub5050]
  simp only [ite_self]
theorem sub5052 (p : Pattern) : d882 (change p 161 (some 162)) = d4638 p := by
  change (if p 138 then d162 (change p 161 (some 162)) else d881 (change p 161 (some 162))) = d4638 p
  rw [sub5051, sub5047]
  rfl
theorem sub5053 (p : Pattern) : d883 (change p 161 (some 162)) = d4639 p := by
  change (if p 116 then d882 (change p 161 (some 162)) else d878 (change p 161 (some 162))) = d4639 p
  rw [sub5052, sub5044]
  rfl
theorem sub5054 (p : Pattern) : d884 (change p 161 (some 162)) = d110 p := by
  change d111 (change p 161 (some 162)) = d110 p
  exact sub5004 p
theorem sub5055 (p : Pattern) : d885 (change p 161 (some 162)) = d4632 p := by
  change (if p 160 then d858 (change p 161 (some 162)) else d884 (change p 161 (some 162))) = d4632 p
  rw [sub5018, sub5054]
  rfl
theorem sub5056 (p : Pattern) : d886 (change p 161 (some 162)) = d134 p := by
  change d135 (change p 161 (some 162)) = d134 p
  exact sub5026 p
theorem sub5057 (p : Pattern) : d887 (change p 161 (some 162)) = d4633 p := by
  change (if p 160 then d865 (change p 161 (some 162)) else d886 (change p 161 (some 162))) = d4633 p
  rw [sub5031, sub5056]
  rfl
theorem sub5058 (p : Pattern) : d888 (change p 161 (some 162)) = d4634 p := by
  change (if p 141 then d887 (change p 161 (some 162)) else d885 (change p 161 (some 162))) = d4634 p
  rw [sub5057, sub5055]
  rfl
theorem sub5059 (p : Pattern) : d889 (change p 161 (some 162)) = d110 p := by
  change d111 (change p 161 (some 162)) = d110 p
  exact sub5004 p
theorem sub5060 (p : Pattern) : d890 (change p 161 (some 162)) = d4632 p := by
  change (if p 160 then d870 (change p 161 (some 162)) else d889 (change p 161 (some 162))) = d4632 p
  rw [sub5036, sub5059]
  rfl
theorem sub5061 (p : Pattern) : d891 (change p 161 (some 162)) = d4636 p := by
  change (if p 141 then d876 (change p 161 (some 162)) else d890 (change p 161 (some 162))) = d4636 p
  rw [sub5042, sub5060]
  rfl
theorem sub5062 (p : Pattern) : d892 (change p 161 (some 162)) = d4637 p := by
  change (if p 138 then d891 (change p 161 (some 162)) else d888 (change p 161 (some 162))) = d4637 p
  rw [sub5061, sub5058]
  rfl
theorem sub5063 (p : Pattern) : d893 (change p 161 (some 162)) = d4638 p := by
  change (if p 138 then d12 (change p 161 (some 162)) else d891 (change p 161 (some 162))) = d4638 p
  rw [sub4890, sub5061]
  rfl
theorem sub5064 (p : Pattern) : d894 (change p 161 (some 162)) = d4639 p := by
  change (if p 116 then d893 (change p 161 (some 162)) else d892 (change p 161 (some 162))) = d4639 p
  rw [sub5063, sub5062]
  rfl
theorem sub5065 (p : Pattern) : d895 (change p 161 (some 162)) = d4639 p := by
  change (if p 115 then d894 (change p 161 (some 162)) else d883 (change p 161 (some 162))) = d4639 p
  rw [sub5064, sub5053]
  simp only [ite_self]
theorem sub5066 (p : Pattern) : d896 (change p 161 (some 162)) = d4640 p := by
  change (if p 71 then d895 (change p 161 (some 162)) else d837 (change p 161 (some 162))) = d4640 p
  rw [sub5065, sub4974]
  rfl
theorem sub5067 (p : Pattern) : d897 (change p 161 (some 162)) = d4641 p := by
  change (if p 49 then d896 (change p 161 (some 162)) else d855 (change p 161 (some 162))) = d4641 p
  rw [sub5066, sub4992]
  rfl
theorem sub5068 (p : Pattern) : d188 (change p 161 (some 162)) = d79 p := by
  change d79 (change p 161 (some 162)) = d79 p
  exact sub4913 p
theorem sub5069 (p : Pattern) : d898 (change p 161 (some 162)) = d79 p := by
  change d188 (change p 161 (some 162)) = d79 p
  exact sub5068 p
theorem sub5070 (p : Pattern) : d8 (change p 161 (some 162)) = d8 p := by
  rfl
theorem sub5071 (p : Pattern) : d190 (change p 161 (some 162)) = d190 p := by
  change (if p 247 then d12 (change p 161 (some 162)) else d8 (change p 161 (some 162))) = d190 p
  rw [sub4890, sub5070]
  rfl
theorem sub5072 (p : Pattern) : d191 (change p 161 (some 162)) = d191 p := by
  change (if p 246 then d190 (change p 161 (some 162)) else d8 (change p 161 (some 162))) = d191 p
  rw [sub5071, sub5070]
  rfl
theorem sub5073 (p : Pattern) : d192 (change p 161 (some 162)) = d192 p := by
  change (if p 204 then d12 (change p 161 (some 162)) else d191 (change p 161 (some 162))) = d192 p
  rw [sub4890, sub5072]
  rfl
theorem sub5074 (p : Pattern) : d193 (change p 161 (some 162)) = d193 p := by
  change (if p 182 then d192 (change p 161 (some 162)) else d191 (change p 161 (some 162))) = d193 p
  rw [sub5073, sub5072]
  rfl
theorem sub5075 (p : Pattern) : d194 (change p 161 (some 162)) = d194 p := by
  change (if p 163 then d193 (change p 161 (some 162)) else d20 (change p 161 (some 162))) = d194 p
  rw [sub5074, sub4899]
  rfl
theorem sub5076 (p : Pattern) : d899 (change p 161 (some 162)) = d194 p := by
  change d194 (change p 161 (some 162)) = d194 p
  exact sub5075 p
theorem sub5077 (p : Pattern) : d900 (change p 161 (some 162)) = d194 p := by
  change d899 (change p 161 (some 162)) = d194 p
  exact sub5076 p
theorem sub5078 (p : Pattern) : d901 (change p 161 (some 162)) = d4642 p := by
  change (if p 160 then d900 (change p 161 (some 162)) else d898 (change p 161 (some 162))) = d4642 p
  rw [sub5077, sub5069]
  rfl
theorem sub5079 (p : Pattern) : d198 (change p 161 (some 162)) = d198 p := by
  change (if p 163 then d62 (change p 161 (some 162)) else d20 (change p 161 (some 162))) = d198 p
  rw [sub4930, sub4899]
  rfl
theorem sub5080 (p : Pattern) : d199 (change p 161 (some 162)) = d198 p := by
  change d198 (change p 161 (some 162)) = d198 p
  exact sub5079 p
theorem sub5081 (p : Pattern) : d902 (change p 161 (some 162)) = d198 p := by
  change d199 (change p 161 (some 162)) = d198 p
  exact sub5080 p
theorem sub5082 (p : Pattern) : d83 (change p 161 (some 162)) = d83 p := by
  change (if p 163 then d12 (change p 161 (some 162)) else d78 (change p 161 (some 162))) = d83 p
  rw [sub4890, sub4912]
  rfl
theorem sub5083 (p : Pattern) : d903 (change p 161 (some 162)) = d83 p := by
  change d83 (change p 161 (some 162)) = d83 p
  exact sub5082 p
theorem sub5084 (p : Pattern) : d904 (change p 161 (some 162)) = d83 p := by
  change d903 (change p 161 (some 162)) = d83 p
  exact sub5083 p
theorem sub5085 (p : Pattern) : d905 (change p 161 (some 162)) = d4643 p := by
  change (if p 160 then d904 (change p 161 (some 162)) else d902 (change p 161 (some 162))) = d4643 p
  rw [sub5084, sub5081]
  rfl
theorem sub5086 (p : Pattern) : d906 (change p 161 (some 162)) = d4644 p := by
  change (if p 141 then d905 (change p 161 (some 162)) else d901 (change p 161 (some 162))) = d4644 p
  rw [sub5085, sub5078]
  rfl
theorem sub5087 (p : Pattern) : d907 (change p 161 (some 162)) = d4645 p := by
  change (if p 138 then d906 (change p 161 (some 162)) else d851 (change p 161 (some 162))) = d4645 p
  rw [sub5086, sub4988]
  rfl
theorem sub5088 (p : Pattern) : d908 (change p 161 (some 162)) = d4646 p := by
  change (if p 138 then d12 (change p 161 (some 162)) else d906 (change p 161 (some 162))) = d4646 p
  rw [sub4890, sub5086]
  rfl
theorem sub5089 (p : Pattern) : d909 (change p 161 (some 162)) = d4647 p := by
  change (if p 116 then d908 (change p 161 (some 162)) else d907 (change p 161 (some 162))) = d4647 p
  rw [sub5088, sub5087]
  rfl
theorem sub5090 (p : Pattern) : d910 (change p 161 (some 162)) = d4648 p := by
  change (if p 115 then d909 (change p 161 (some 162)) else d848 (change p 161 (some 162))) = d4648 p
  rw [sub5089, sub4985]
  rfl
theorem sub5091 (p : Pattern) : d911 (change p 161 (some 162)) = d4649 p := by
  change (if p 71 then d910 (change p 161 (some 162)) else d837 (change p 161 (some 162))) = d4649 p
  rw [sub5090, sub4974]
  rfl
theorem sub5092 (p : Pattern) : d211 (change p 161 (some 162)) = d211 p := by
  change (if p 163 then d12 (change p 161 (some 162)) else d109 (change p 161 (some 162))) = d211 p
  rw [sub4890, sub5002]
  rfl
theorem sub5093 (p : Pattern) : d212 (change p 161 (some 162)) = d211 p := by
  change d211 (change p 161 (some 162)) = d211 p
  exact sub5092 p
theorem sub5094 (p : Pattern) : d912 (change p 161 (some 162)) = d211 p := by
  change d212 (change p 161 (some 162)) = d211 p
  exact sub5093 p
theorem sub5095 (p : Pattern) : d913 (change p 161 (some 162)) = d4650 p := by
  change (if p 160 then d865 (change p 161 (some 162)) else d912 (change p 161 (some 162))) = d4650 p
  rw [sub5031, sub5094]
  rfl
theorem sub5096 (p : Pattern) : d914 (change p 161 (some 162)) = d4651 p := by
  change (if p 141 then d913 (change p 161 (some 162)) else d859 (change p 161 (some 162))) = d4651 p
  rw [sub5095, sub5019]
  rfl
theorem sub5097 (p : Pattern) : d915 (change p 161 (some 162)) = d211 p := by
  change d212 (change p 161 (some 162)) = d211 p
  exact sub5093 p
theorem sub5098 (p : Pattern) : d916 (change p 161 (some 162)) = d4652 p := by
  change (if p 160 then d875 (change p 161 (some 162)) else d915 (change p 161 (some 162))) = d4652 p
  rw [sub5041, sub5097]
  rfl
theorem sub5099 (p : Pattern) : d917 (change p 161 (some 162)) = d4653 p := by
  change (if p 141 then d916 (change p 161 (some 162)) else d871 (change p 161 (some 162))) = d4653 p
  rw [sub5098, sub5037]
  rfl
theorem sub5100 (p : Pattern) : d918 (change p 161 (some 162)) = d4654 p := by
  change (if p 138 then d917 (change p 161 (some 162)) else d914 (change p 161 (some 162))) = d4654 p
  rw [sub5099, sub5096]
  rfl
theorem sub5101 (p : Pattern) : d919 (change p 161 (some 162)) = d4653 p := by
  change (if p 141 then d916 (change p 161 (some 162)) else d880 (change p 161 (some 162))) = d4653 p
  rw [sub5098, sub5046]
  rfl
theorem sub5102 (p : Pattern) : d920 (change p 161 (some 162)) = d4655 p := by
  change (if p 138 then d162 (change p 161 (some 162)) else d919 (change p 161 (some 162))) = d4655 p
  rw [sub5051, sub5101]
  rfl
theorem sub5103 (p : Pattern) : d921 (change p 161 (some 162)) = d4656 p := by
  change (if p 116 then d920 (change p 161 (some 162)) else d918 (change p 161 (some 162))) = d4656 p
  rw [sub5102, sub5100]
  rfl
theorem sub5104 (p : Pattern) : d922 (change p 161 (some 162)) = d149 p := by
  change d149 (change p 161 (some 162)) = d149 p
  exact sub5016 p
theorem sub5105 (p : Pattern) : d923 (change p 161 (some 162)) = d149 p := by
  change d922 (change p 161 (some 162)) = d149 p
  exact sub5104 p
theorem sub5106 (p : Pattern) : d924 (change p 161 (some 162)) = d4632 p := by
  change (if p 160 then d923 (change p 161 (some 162)) else d884 (change p 161 (some 162))) = d4632 p
  rw [sub5105, sub5054]
  rfl
theorem sub5107 (p : Pattern) : d273 (change p 161 (some 162)) = d273 p := by
  change (if p 204 then d120 (change p 161 (some 162)) else d107 (change p 161 (some 162))) = d273 p
  rw [sub5013, sub5000]
  rfl
theorem sub5108 (p : Pattern) : d292 (change p 161 (some 162)) = d292 p := by
  change (if p 182 then d121 (change p 161 (some 162)) else d273 (change p 161 (some 162))) = d292 p
  rw [sub5014, sub5107]
  rfl
theorem sub5109 (p : Pattern) : d300 (change p 161 (some 162)) = d300 p := by
  change (if p 163 then d12 (change p 161 (some 162)) else d292 (change p 161 (some 162))) = d300 p
  rw [sub4890, sub5108]
  rfl
theorem sub5110 (p : Pattern) : d926 (change p 161 (some 162)) = d300 p := by
  change d300 (change p 161 (some 162)) = d300 p
  exact sub5109 p
theorem sub5111 (p : Pattern) : d927 (change p 161 (some 162)) = d300 p := by
  change d926 (change p 161 (some 162)) = d300 p
  exact sub5110 p
theorem sub5112 (p : Pattern) : d928 (change p 161 (some 162)) = d4657 p := by
  change (if p 160 then d927 (change p 161 (some 162)) else d915 (change p 161 (some 162))) = d4657 p
  rw [sub5111, sub5097]
  rfl
theorem sub5113 (p : Pattern) : d929 (change p 161 (some 162)) = d4658 p := by
  change (if p 141 then d928 (change p 161 (some 162)) else d924 (change p 161 (some 162))) = d4658 p
  rw [sub5112, sub5106]
  rfl
theorem sub5114 (p : Pattern) : d241 (change p 161 (some 162)) = d241 p := by
  change (if p 163 then d62 (change p 161 (some 162)) else d132 (change p 161 (some 162))) = d241 p
  rw [sub4930, sub5010]
  rfl
theorem sub5115 (p : Pattern) : d242 (change p 161 (some 162)) = d241 p := by
  change d241 (change p 161 (some 162)) = d241 p
  exact sub5114 p
theorem sub5116 (p : Pattern) : d930 (change p 161 (some 162)) = d241 p := by
  change d242 (change p 161 (some 162)) = d241 p
  exact sub5115 p
theorem sub5117 (p : Pattern) : d245 (change p 161 (some 162)) = d211 p := by
  change d211 (change p 161 (some 162)) = d211 p
  exact sub5092 p
theorem sub5118 (p : Pattern) : d931 (change p 161 (some 162)) = d211 p := by
  change d245 (change p 161 (some 162)) = d211 p
  exact sub5117 p
theorem sub5119 (p : Pattern) : d932 (change p 161 (some 162)) = d4659 p := by
  change (if p 160 then d931 (change p 161 (some 162)) else d930 (change p 161 (some 162))) = d4659 p
  rw [sub5118, sub5116]
  rfl
theorem sub5120 (p : Pattern) : d933 (change p 161 (some 162)) = d153 p := by
  change d153 (change p 161 (some 162)) = d153 p
  exact sub5039 p
theorem sub5121 (p : Pattern) : d934 (change p 161 (some 162)) = d153 p := by
  change d933 (change p 161 (some 162)) = d153 p
  exact sub5120 p
theorem sub5122 (p : Pattern) : d935 (change p 161 (some 162)) = d4652 p := by
  change (if p 160 then d934 (change p 161 (some 162)) else d931 (change p 161 (some 162))) = d4652 p
  rw [sub5121, sub5118]
  rfl
theorem sub5123 (p : Pattern) : d936 (change p 161 (some 162)) = d4660 p := by
  change (if p 141 then d935 (change p 161 (some 162)) else d932 (change p 161 (some 162))) = d4660 p
  rw [sub5122, sub5119]
  rfl
theorem sub5124 (p : Pattern) : d937 (change p 161 (some 162)) = d4661 p := by
  change (if p 138 then d936 (change p 161 (some 162)) else d929 (change p 161 (some 162))) = d4661 p
  rw [sub5123, sub5113]
  rfl
theorem sub5125 (p : Pattern) : d252 (change p 161 (some 162)) = d252 p := by
  change (if p 163 then d26 (change p 161 (some 162)) else d132 (change p 161 (some 162))) = d252 p
  rw [sub4921, sub5010]
  rfl
theorem sub5126 (p : Pattern) : d253 (change p 161 (some 162)) = d252 p := by
  change d252 (change p 161 (some 162)) = d252 p
  exact sub5125 p
theorem sub5127 (p : Pattern) : d938 (change p 161 (some 162)) = d252 p := by
  change d253 (change p 161 (some 162)) = d252 p
  exact sub5126 p
theorem sub5128 (p : Pattern) : d136 (change p 161 (some 162)) = d136 p := by
  change (if p 163 then d62 (change p 161 (some 162)) else d109 (change p 161 (some 162))) = d136 p
  rw [sub4930, sub5002]
  rfl
theorem sub5129 (p : Pattern) : d939 (change p 161 (some 162)) = d136 p := by
  change d136 (change p 161 (some 162)) = d136 p
  exact sub5128 p
theorem sub5130 (p : Pattern) : d940 (change p 161 (some 162)) = d136 p := by
  change d939 (change p 161 (some 162)) = d136 p
  exact sub5129 p
theorem sub5131 (p : Pattern) : d941 (change p 161 (some 162)) = d4662 p := by
  change (if p 160 then d940 (change p 161 (some 162)) else d938 (change p 161 (some 162))) = d4662 p
  rw [sub5130, sub5127]
  rfl
theorem sub5132 (p : Pattern) : d942 (change p 161 (some 162)) = d4663 p := by
  change (if p 141 then d935 (change p 161 (some 162)) else d941 (change p 161 (some 162))) = d4663 p
  rw [sub5122, sub5131]
  rfl
theorem sub5133 (p : Pattern) : d943 (change p 161 (some 162)) = d4664 p := by
  change (if p 138 then d12 (change p 161 (some 162)) else d942 (change p 161 (some 162))) = d4664 p
  rw [sub4890, sub5132]
  rfl
theorem sub5134 (p : Pattern) : d944 (change p 161 (some 162)) = d4665 p := by
  change (if p 116 then d943 (change p 161 (some 162)) else d937 (change p 161 (some 162))) = d4665 p
  rw [sub5133, sub5124]
  rfl
theorem sub5135 (p : Pattern) : d945 (change p 161 (some 162)) = d4666 p := by
  change (if p 115 then d944 (change p 161 (some 162)) else d921 (change p 161 (some 162))) = d4666 p
  rw [sub5134, sub5103]
  rfl
theorem sub5136 (p : Pattern) : d946 (change p 161 (some 162)) = d4667 p := by
  change (if p 71 then d945 (change p 161 (some 162)) else d837 (change p 161 (some 162))) = d4667 p
  rw [sub5135, sub4974]
  rfl
theorem sub5137 (p : Pattern) : d947 (change p 161 (some 162)) = d4668 p := by
  change (if p 49 then d946 (change p 161 (some 162)) else d911 (change p 161 (some 162))) = d4668 p
  rw [sub5136, sub5091]
  rfl
theorem sub5138 (p : Pattern) : d948 (change p 161 (some 162)) = d4669 p := by
  change (if p 48 then d947 (change p 161 (some 162)) else d897 (change p 161 (some 162))) = d4669 p
  rw [sub5137, sub5067]
  rfl
theorem sub5139 (p : Pattern) : d0 (change p 162 (some 163)) = d0 p := by
  rfl
theorem sub5140 (p : Pattern) : d12 (change p 162 (some 163)) = d12 p := by
  rfl
theorem sub5141 (p : Pattern) : d13 (change p 162 (some 163)) = d13 p := by
  change (if p 247 then d12 (change p 162 (some 163)) else d0 (change p 162 (some 163))) = d13 p
  rw [sub5140, sub5139]
  rfl
theorem sub5142 (p : Pattern) : d14 (change p 162 (some 163)) = d14 p := by
  change (if p 246 then d13 (change p 162 (some 163)) else d0 (change p 162 (some 163))) = d14 p
  rw [sub5141, sub5139]
  rfl
theorem sub5143 (p : Pattern) : d15 (change p 162 (some 163)) = d15 p := by
  change (if p 204 then d12 (change p 162 (some 163)) else d14 (change p 162 (some 163))) = d15 p
  rw [sub5140, sub5142]
  rfl
theorem sub5144 (p : Pattern) : d16 (change p 162 (some 163)) = d16 p := by
  change (if p 182 then d15 (change p 162 (some 163)) else d14 (change p 162 (some 163))) = d16 p
  rw [sub5143, sub5142]
  rfl
theorem sub5145 (p : Pattern) : d949 (change p 162 (some 163)) = d16 p := by
  change d16 (change p 162 (some 163)) = d16 p
  exact sub5144 p
theorem sub5146 (p : Pattern) : d2 (change p 162 (some 163)) = d2 p := by
  rfl
theorem sub5147 (p : Pattern) : d30 (change p 162 (some 163)) = d30 p := by
  change (if p 247 then d12 (change p 162 (some 163)) else d2 (change p 162 (some 163))) = d30 p
  rw [sub5140, sub5146]
  rfl
theorem sub5148 (p : Pattern) : d31 (change p 162 (some 163)) = d31 p := by
  change (if p 246 then d30 (change p 162 (some 163)) else d2 (change p 162 (some 163))) = d31 p
  rw [sub5147, sub5146]
  rfl
theorem sub5149 (p : Pattern) : d32 (change p 162 (some 163)) = d32 p := by
  change (if p 204 then d12 (change p 162 (some 163)) else d31 (change p 162 (some 163))) = d32 p
  rw [sub5140, sub5148]
  rfl
theorem sub5150 (p : Pattern) : d33 (change p 162 (some 163)) = d33 p := by
  change (if p 182 then d32 (change p 162 (some 163)) else d14 (change p 162 (some 163))) = d33 p
  rw [sub5149, sub5142]
  rfl
theorem sub5151 (p : Pattern) : d950 (change p 162 (some 163)) = d33 p := by
  change d33 (change p 162 (some 163)) = d33 p
  exact sub5150 p
theorem sub5152 (p : Pattern) : d951 (change p 162 (some 163)) = d33 p := by
  change d950 (change p 162 (some 163)) = d33 p
  exact sub5151 p
theorem sub5153 (p : Pattern) : d952 (change p 162 (some 163)) = d4674 p := by
  change (if p 161 then d951 (change p 162 (some 163)) else d949 (change p 162 (some 163))) = d4674 p
  rw [sub5152, sub5145]
  rfl
theorem sub5154 (p : Pattern) : d953 (change p 162 (some 163)) = d33 p := by
  change d33 (change p 162 (some 163)) = d33 p
  exact sub5150 p
theorem sub5155 (p : Pattern) : d4 (change p 162 (some 163)) = d4 p := by
  rfl
theorem sub5156 (p : Pattern) : d17 (change p 162 (some 163)) = d17 p := by
  change (if p 247 then d12 (change p 162 (some 163)) else d4 (change p 162 (some 163))) = d17 p
  rw [sub5140, sub5155]
  rfl
theorem sub5157 (p : Pattern) : d18 (change p 162 (some 163)) = d18 p := by
  change (if p 246 then d17 (change p 162 (some 163)) else d4 (change p 162 (some 163))) = d18 p
  rw [sub5156, sub5155]
  rfl
theorem sub5158 (p : Pattern) : d43 (change p 162 (some 163)) = d43 p := by
  change (if p 182 then d12 (change p 162 (some 163)) else d18 (change p 162 (some 163))) = d43 p
  rw [sub5140, sub5157]
  rfl
theorem sub5159 (p : Pattern) : d47 (change p 162 (some 163)) = d43 p := by
  change d43 (change p 162 (some 163)) = d43 p
  exact sub5158 p
end NetHack.Sokoban22Refined85
