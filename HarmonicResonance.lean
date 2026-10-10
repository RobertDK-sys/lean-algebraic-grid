import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

namespace AlgebraicFrequencyGrid

/-- Constante delta_b -/
def delta_b : ℝ := -2 * Real.pi / Real.log 2

/-- Gestion des signes pour les branches de phase -/
inductive Sign
| pos
| neg

def Sign.toReal : Sign → ℝ
| Sign.pos => 1
| Sign.neg => -1

/-- Fréquence de base b(k) indépendante -/
def b_frequency (s2_val : ℝ) (k : ℤ) (signe : Sign) : ℝ :=
  (Real.asin (signe.toReal * abs s2_val) - 2 * (k : ℝ) * Real.pi) / Real.log 2

/-- Fréquence couplée avec un rapport explicite k_a / k_b -/
noncomputable def b_frequency_with_ratio (s2_val : ℝ) (ka : ℤ) (ratio_ka_kb : ℝ) (signe : Sign) : ℝ :=
  let kb_val := (ka : ℝ) / ratio_ka_kb
  (Real.asin (signe.toReal * abs s2_val) - 2 * kb_val * Real.pi) / Real.log 2

/-- Terme individuel de la somme harmonique cosinusoïdale pour une fréquence b et un entier m -/
noncomputable def harmonic_term (b_val : ℝ) (m : ℕ) : ℝ :=
  Real.cos (b_val * Real.log (m : ℝ))

/-- Somme harmonique S_f(n) standard pour deux fréquences b_ka et b_kb -/
noncomputable def harmonic_sum_Sf (n : ℕ) (b_ka b_kb : ℝ) : ℝ :=
  (Finset.range n).sum (fun i => harmonic_term b_ka (i + 1)) +
  (Finset.range n).sum (fun i => harmonic_term b_kb (i + 1))

/-- Somme harmonique S_f(n) utilisant le couplage par rapport k_a / k_b -/
noncomputable def harmonic_sum_Sf_coupled (n : ℕ) (s2_val : ℝ) (ka : ℤ) (ratio_ka_kb : ℝ) (signe : Sign) : ℝ :=
  let b_ka := b_frequency_with_ratio s2_val ka 1 Sign.pos
  let b_kb := b_frequency_with_ratio s2_val ka ratio_ka_kb signe
  (Finset.range n).sum (fun i => harmonic_term b_ka (i + 1)) +
  (Finset.range n).sum (fun i => harmonic_term b_kb (i + 1))

/-- Prédicat de résonance standard basé sur le changement de signe (n-1 et n+1) -/
def is_prime_resonant (n : ℕ) (b_ka b_kb : ℝ) : Prop :=
  let S_prev := harmonic_sum_Sf (n - 1) b_ka b_kb
  let S_next := harmonic_sum_Sf (n + 1) b_ka b_kb
  S_prev * S_next < 0

/-- Prédicat de résonance couplé basé sur le rapport k_a / k_b -/
def is_prime_resonant_coupled (n : ℕ) (s2_val : ℝ) (ka : ℤ) (ratio_ka_kb : ℝ) (signe : Sign) : Prop :=
  let S_prev := harmonic_sum_Sf_coupled (n - 1) s2_val ka ratio_ka_kb signe
  let S_next := harmonic_sum_Sf_coupled (n + 1) s2_val ka ratio_ka_kb signe
  S_prev * S_next < 0

end AlgebraicFrequencyGrid
