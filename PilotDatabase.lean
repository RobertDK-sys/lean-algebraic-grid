import Mathlib.Data.Real.Basic

namespace AlgebraicFrequencyGrid

/-- Structure représentant un enregistrement pilote pour un entier n -/
structure PilotRecord where
  n : ℕ
  isPrime : Bool
  validPairs : List (ℤ × ℤ)

/-- Base de données empirique des paires (k_a, k_b) validées -/
def pilotDatabase : List PilotRecord := [
  { n := 5,  isPrime := true,  validPairs := [(2, 3), (2, 4)] },
  { n := 7,  isPrime := true,  validPairs := [(2, 3), (2, 4), (2, 5), (2, 6), (3, 5), (3, 6), (5, 6)] },
  { n := 9,  isPrime := false, validPairs := [(2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 5), (3, 6), (3, 7), (5, 6), (5, 7), (6, 7)] },
  { n := 11, isPrime := true,  validPairs := [(2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (7, 9), (7, 10), (9, 10)] },
  { n := 13, isPrime := true,  validPairs := [(2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, 5), (3, 7), (3, 11), (5, 12), (7, 9), (7, 10), (7, 11), (7, 12), (9, 10), (9, 11), (9, 12), (10, 11), (10, 12), (11, 12)] },
  { n := 15, isPrime := false, validPairs := [(2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (5, 8), (6, 8), (7, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14)] },
  { n := 17, isPrime := true,  validPairs := [(2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 16), (5, 8), (5, 16), (6, 8), (6, 16), (7, 8), (7, 16), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 15), (8, 16), (9, 16), (10, 16), (11, 16), (12, 16), (13, 16), (14, 16), (15, 16)] }
]

/-- Fonction de recherche pour vérifier si une paire (ka, kb) est enregistrée comme valide pour un n donné -/
def check_pilot_pair (target_n : ℕ) (ka kb : ℤ) : Bool :=
  match pilotDatabase.find? (fun r => r.n == target_n) with
  | none => false
  | some record => record.validPairs.contains (ka, kb)

#eval check_pilot_pair 7 2 5
#eval check_pilot_pair 9 3 6

end AlgebraicFrequencyGrid
