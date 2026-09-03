import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Span
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two
    (p : ℕ) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K),
        σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k)
    (hK : ¬ Module.Finite ℤ K) :
    p.Prime ∧
      ∃ ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐc[ℤ] K,
      ∀ (R : Type) [CommRing R],
        (∀ f g : K →ₐ[ℤ] R, f.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) =
            g.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) → f = g) ∧
        ∀ g : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] R,
          (∃ f : K →ₐ[ℤ] R, f.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) = g) ↔
            ∃ a : R, a - 1 ∈ Ideal.span {(p : R)} ∧
              ∀ h : MonoidAlgebra ℤ (Multiplicative (ZMod q)),
                a * (g h - algebraMap ℤ R
                  (Bialgebra.counitAlgHom ℤ (MonoidAlgebra ℤ (Multiplicative (ZMod q))) h)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.solution
