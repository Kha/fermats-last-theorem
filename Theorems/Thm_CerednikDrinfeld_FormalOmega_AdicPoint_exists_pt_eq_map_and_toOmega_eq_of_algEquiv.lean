import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_pt_eq_map_and_toOmega_eq_of_algEquiv

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.AdicPoint.exists_pt_eq_map_and_toOmega_eq_of_algEquiv
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    {R : Type} [CommRing R] [Algebra 𝒪 R] (C : Type) [Field C] [Algebra R C]
    (τ : R ≃ₐ[𝒪] R) (s : C ≃+* C) (hτs : ∀ a : R, algebraMap R C (τ a) = s (algebraMap R C a))
    (τn : ∀ k : ℕ, modPow π R k →ₐ[𝒪] modPow π R k)
    (hτn : ∀ (k : ℕ) (a : R), τn k (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) a) =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) (τ a))
    (x : AdicPoint K₀ π R) :
    ∃ x' : AdicPoint K₀ π R, (∀ k : ℕ, x'.pt k = DeligneDatum.map π (τn k) (x.pt k)) ∧
      x'.toOmega C = s (x.toOmega C) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_pt_eq_map_and_toOmega_eq_of_algEquiv.solution
