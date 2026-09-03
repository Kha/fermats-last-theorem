import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws

set_option autoImplicit false

open CategoryTheory CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.OmegaNr.isTwistedAct_laws
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ) :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' x'' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      OmegaNr.IsTwistedAct π Onr Fr vdet B g x x' → OmegaNr.IsTwistedAct π Onr Fr vdet B g x x'' → x' = x'') ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      ∃ x', OmegaNr.IsTwistedAct π Onr Fr vdet B g x x') ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), OmegaNr.IsTwistedAct π Onr Fr vdet B 1 x x) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀) (x y z : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      OmegaNr.IsTwistedAct π Onr Fr vdet B g x y → OmegaNr.IsTwistedAct π Onr Fr vdet B g' y z →
      OmegaNr.IsTwistedAct π Onr Fr vdet B (g' * g) x z) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B')
      (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      OmegaNr.IsTwistedAct π Onr Fr vdet B g x x' → OmegaNr.IsTwistedAct π Onr Fr vdet B' g ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x')) ∧

    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀) (ψ : Onr →ₐ[𝒪] B),
      frobTwist Onr Fr (- Multiplicative.toAdd (vdet (g' * g))) ψ =
        frobTwist Onr Fr (- Multiplicative.toAdd (vdet g')) (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g)) ψ)) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (P : (Omega K₀ π).obj B),
      ∃ P', DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P') ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀) (P P' P'' : (Omega K₀ π).obj B),
      DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' → DeligneDatum.IsPullback (K := K₀) (π := π) B g'⁻¹ P' P'' →
      DeligneDatum.IsPullback (K := K₀) (π := π) B (g' * g)⁻¹ P P'') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws.solution
