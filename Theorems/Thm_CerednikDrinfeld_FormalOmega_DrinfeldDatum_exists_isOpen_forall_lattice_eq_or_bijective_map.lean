import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isOpen_forall_lattice_eq_or_bijective_map

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isOpen_forall_lattice_eq_or_bijective_map
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      Q.N₀ x ≤ Q.N₀ y ∧ Q.N₁ x ≤ Q.N₁ y ∧
      ((Q.N₀ y = Q.N₀ x ∧ Q.N₁ y = Q.N₁ x) ∨
       (Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl Q.Pi₀) ∧
          Q.N₀ y = Q.N₁ x ∧ Q.N₁ y = Q.N₁ x) ∨
       (Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl Q.Pi₁) ∧
          Q.N₀ y = Q.N₀ x ∧ ∀ v : Fin 2 → K, v ∈ Q.N₁ y ↔ algebraMap 𝒪 K π • v ∈ Q.N₀ x)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isOpen_forall_lattice_eq_or_bijective_map.solution
