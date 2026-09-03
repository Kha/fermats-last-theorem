import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Artin_exists_artinFieldCore_nonempty_artinPairCore
attribute [-instance] LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal
attribute [-simp] AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField LanglandsTunnell.P2.Artin

universe u v

theorem LanglandsTunnell.Artin.exists_artinFieldCore_nonempty_artinPairCore
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (ℓ k : ℕ) (hℓ : ℓ.Prime) (hexp : ∀ x : L ≃ₐ[K] L, x ^ (ℓ ^ k) = 1)
    (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣) (σ : L ≃ₐ[K] L) :
    ∃ D : ∀ i : ↥(primeCarriers K 𝔣), ArtinFieldCore.{u, v, v, v, v} K L 𝔣 i,
      ∀ i j : ↥(primeCarriers K 𝔣),
        Nonempty (ArtinPairCore.{u, v, v, v, v, v, v, v, v, v} K L 𝔣 σ (D i) (D j)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Artin_exists_artinFieldCore_nonempty_artinPairCore.solution
