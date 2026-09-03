import Mathlib
import P2M.Util
import P2M.Sol.S_AdjoinRoot_finite_free_faithfullyFlat_etale_cyclotomic_of_isUnit

set_option autoImplicit false

open Polynomial

universe u

theorem AdjoinRoot.finite_free_faithfullyFlat_etale_cyclotomic_of_isUnit
    (𝒪 : Type u) [CommRing 𝒪] (m : ℕ) (hm : IsUnit ((m : ℕ) : 𝒪)) :
    Module.Finite 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) ∧ Module.Free 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) ∧
      Module.FaithfullyFlat 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) ∧ Algebra.Etale 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) ∧
      (Nontrivial 𝒪 → Module.finrank 𝒪 (AdjoinRoot (cyclotomic m 𝒪)) = Nat.totient m) := by p2m_exact_reverting @_root_.P2MW.S_AdjoinRoot_finite_free_faithfullyFlat_etale_cyclotomic_of_isUnit.solution
