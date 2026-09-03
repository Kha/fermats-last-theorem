import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CerednikDrinfeld_Ribbon
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Finiteness.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_ribbon_kernelEquiv
set_option autoImplicit false
open ModularCurve
universe u_1 u_2 u_3 u_4

theorem CerednikDrinfeld.ribbon_kernelEquiv :
    ∀ {E₁ : Type u_1} {V₁ : Type u_2} {E₂ : Type u_3} {V₂ : Type u_4}
  [inst : Fintype E₁] [inst_1 : Fintype V₁] [inst_2 : DecidableEq V₁] [inst_3 : Fintype E₂] [inst_4 : Fintype V₂]
  [inst_5 : DecidableEq V₂] {D₁ : CerednikDrinfeld.DegeneracyData E₁ V₁} {D₂ : CerednikDrinfeld.DegeneracyData E₂ V₂}
  (H₁ : CerednikDrinfeld.HeckeData D₁) (H₂ : CerednikDrinfeld.HeckeData D₂) (M : CerednikDrinfeld.Matching H₁ H₂),
  ∃ (e : ↥(CerednikDrinfeld.ribbonKernel D₁) ≃ₗ[ℤ] ↥(CerednikDrinfeld.ribbonKernel D₂)),
    (∀ (ℓ : Nat.Primes) (x : ↥(CerednikDrinfeld.ribbonKernel D₁)),
        e ((CerednikDrinfeld.heckeKernelMap H₁ ℓ) x) = (CerednikDrinfeld.heckeKernelMap H₂ ℓ) (e x)) ∧
      ∀ (x y : ↥(CerednikDrinfeld.ribbonKernel D₁)),
        ((CerednikDrinfeld.ribbonGram D₂) (e x)) (e y) = ((CerednikDrinfeld.ribbonGram D₁) x) y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_ribbon_kernelEquiv.solution
