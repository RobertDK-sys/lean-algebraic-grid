import AlgebraicGrid
import HarmonicResonance
import PilotDatabase

namespace AlgebraicFrequencyGrid

/-- La résonance couplée est, par définition, un changement de signe de S_f
entre n-1 et n+1. (Remplace l'ancien théorème dont la conclusion était `True`,
qui ne disait rien.) -/
theorem resonance_coupled_iff
    (n : ℕ) (s2_val : ℝ) (ka : ℤ) (ratio_ka_kb : ℝ) (signe : Sign) :
    is_prime_resonant_coupled n s2_val ka ratio_ka_kb signe ↔
      harmonic_sum_Sf_coupled (n - 1) s2_val ka ratio_ka_kb signe *
      harmonic_sum_Sf_coupled (n + 1) s2_val ka ratio_ka_kb signe < 0 :=
  Iff.rfl

/-
Conjecture (non démontrée, donc volontairement hors compilation) :
pour tous n, s2_val, ka, signe, il existe ratio > 0 tel que
`is_prime_resonant_coupled n s2_val ka ratio signe`.
Elle ne peut pas être laissée avec `sorry` dans un build propre ; à énoncer
précisément (pour quels n ?) avant de tenter une preuve.
-/

end AlgebraicFrequencyGrid
