import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion
attribute [-simp] Submodule.finiteAdeleEvalAt_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin
    {a b : ℚ} (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (hR : QuaternionAlgebra.IsOrder R)
    (hRΛ : R ≤ Λ) (q ℓ : ℕ)
    (hq : q ≠ 0) (hℓ : ℓ ≠ 0) (hcop : ℓ.Coprime q) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)))]
    [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)))]
    [DecidableEq (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R))]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (τ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ → (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hmτ : (m = 1 ∧ τ = id) ∨ (m = n ∧ τ = fun h => n⁻¹ * h * n))
    (x : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) → ℤ) (v : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R)) :
    CerednikDrinfeld.pushforward
        (fun e : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) => QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * m))
        ((CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n))
          (CerednikDrinfeld.levelHeckeUSet Λ (CerednikDrinfeld.meetOrder R n) ℓ)).mulVecLin x) v =
      (CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer R) (CerednikDrinfeld.levelHeckeUSet Λ R ℓ)).mulVecLin
        (CerednikDrinfeld.pushforward
          (fun e : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) => QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * m)) x) v := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.solution
