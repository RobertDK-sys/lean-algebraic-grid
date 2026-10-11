import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace AlgebraicFrequencyGrid

-- 1. Définition de k3 dans ℤ* (t entier strictement positif, k3 = -t)
def k3_of_t (t : ℤ) (_h : t > 0) : ℤ := -t

-- 2. Équation caractéristique de degré 6
-- Correction : exposant réel (2/3 : ℝ) ; `2/3` seul était une division entière (= 0)
noncomputable def equation_deg6 (s2 : ℝ) (k3 : ℝ) : ℝ :=
  let A := 8 * s2 ^ 6 - 24 * s2 ^ 4 + 24 * s2 ^ 2 - 8
  |A| ^ ((2 : ℝ) / 3) * (24 * k3 ^ 2 * s2 ^ 6 - 72 * k3 ^ 2 * s2 ^ 4 - 24 * k3 ^ 2)
    + 4 * s2 ^ 4

-- 3. Pas constant du réseau de Dirac (Δb = -2π / ln 2)
noncomputable def delta_b : ℝ := -2 * Real.pi / Real.log 2

-- 4. Signe dans {-1, 1}
inductive Sign
  | pos
  | neg

noncomputable def Sign.toReal : Sign → ℝ
  | Sign.pos => 1
  | Sign.neg => -1

-- 5. Fréquence b(t, k, signe)  (correction : `Real.arcsin`, et non `Real.asin`)
noncomputable def b_frequency (s2_val : ℝ) (k : ℤ) (signe : Sign) : ℝ :=
  (Real.arcsin (signe.toReal * |s2_val|) - 2 * (k : ℝ) * Real.pi) / Real.log 2

end AlgebraicFrequencyGrid
