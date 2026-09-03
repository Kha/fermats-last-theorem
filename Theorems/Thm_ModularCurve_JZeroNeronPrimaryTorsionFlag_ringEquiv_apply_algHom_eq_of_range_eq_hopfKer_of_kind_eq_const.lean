import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_ringEquiv_apply_algHom_eq_of_range_eq_hopfKer_of_kind_eq_const
open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.ringEquiv_apply_algHom_eq_of_range_eq_hopfKer_of_kind_eq_const
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin flag.n)
    (hk : flag.kind i = JZeroFlagLayerKind.const)
    (qc : flag.G i.succ →ₐc[ℤ] flag.G i.castSucc)
    (hqc : (qc : flag.G i.succ →ₐ[ℤ] flag.G i.castSucc) = flag.quot i)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K)
    (j : K →ₐc[ℤ] flag.G i.succ) (hinj : Function.Injective j)
    (hrange : (j : K →ₐ[ℤ] flag.G i.succ).range = HopfAlgebra.hopfKer qc)
    (hflat : Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) (flag.G i.succ)) :
    ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ)
      (k : K), σ (ψ k) = ψ k := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_ringEquiv_apply_algHom_eq_of_range_eq_hopfKer_of_kind_eq_const.solution
