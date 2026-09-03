import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_OmegaNr_exists_equiv_of_ringEquiv_frame

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.OmegaNr.exists_equiv_of_ringEquiv_frame
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {𝒪' : Type} [CommRing 𝒪'] {K' : Type} [Field K'] [Algebra 𝒪' K']
    (eb : 𝒪 ≃+* 𝒪') (eK : K ≃+* K') (hcomm : ∀ x : 𝒪, eK (algebraMap 𝒪 K x) = algebraMap 𝒪' K' (eb x))
    {π : 𝒪} {π' : 𝒪'} (hπ : eb π = π')
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K →* Multiplicative ℤ)
    (Onr' : Type) [CommRing Onr'] [Algebra 𝒪' Onr'] (Fr' : Onr' ≃ₐ[𝒪'] Onr')
    (vdet' : Matrix.GeneralLinearGroup (Fin 2) K' →* Multiplicative ℤ)
    (eO : Onr ≃+* Onr') (heO : ∀ x : 𝒪, eO (algebraMap 𝒪 Onr x) = algebraMap 𝒪' Onr' (eb x))
    (hFr : ∀ y, eO (Fr y) = Fr' (eO y))
    (hv : ∀ g, vdet' (Matrix.GeneralLinearGroup.map eK.toRingHom g) = vdet g) :
    ∃ (Ψ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B],
        (∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x)) →
          (OmegaNrObj (K := K) π Onr B ≃ OmegaNrObj (K := K') π' Onr' B)),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
          (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
          (x : OmegaNrObj (K := K) π Onr B) (y : Onr'), (Ψ B hB x).1 y = x.1 (eO.symm y)) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
          (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
          (g : Matrix.GeneralLinearGroup (Fin 2) K) (x x' : OmegaNrObj (K := K) π Onr B),
        OmegaNr.IsTwistedAct π' Onr' Fr' vdet' B (Matrix.GeneralLinearGroup.map eK.toRingHom g) (Ψ B hB x) (Ψ B hB x') ↔
          OmegaNr.IsTwistedAct π Onr Fr vdet B g x x') ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
          (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
          (g : Matrix.GeneralLinearGroup (Fin 2) K) (x x' : OmegaNrObj (K := K) π Onr B),
        DeligneDatum.IsPullback (K := K') (π := π') B (Matrix.GeneralLinearGroup.map eK.toRingHom g) (Ψ B hB x).2 (Ψ B hB x').2 ↔
          DeligneDatum.IsPullback (K := K) (π := π) B g x.2 x'.2) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
          (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
          (B₁ : Type) [CommRing B₁] [Algebra 𝒪 B₁] [Algebra 𝒪' B₁]
          (hB₁ : ∀ x : 𝒪, algebraMap 𝒪 B₁ x = algebraMap 𝒪' B₁ (eb x))
          (f : B →ₐ[𝒪] B₁) (f' : B →ₐ[𝒪'] B₁) (_ : ∀ b, f b = f' b)
          (x : OmegaNrObj (K := K) π Onr B) (x₁ : OmegaNrObj (K := K) π Onr B₁),
        DeligneDatum.IsBaseChange (K := K') (π := π') f' (Ψ B hB x).2 (Ψ B₁ hB₁ x₁).2 ↔
          DeligneDatum.IsBaseChange (K := K) (π := π) f x.2 x₁.2) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_OmegaNr_exists_equiv_of_ringEquiv_frame.solution
