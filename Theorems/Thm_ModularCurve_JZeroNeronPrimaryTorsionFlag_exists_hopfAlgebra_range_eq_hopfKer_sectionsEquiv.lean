import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul
open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin flag.n)
    (qc : flag.G i.succ →ₐc[ℤ] flag.G i.castSucc)
    (hqc : (qc : flag.G i.succ →ₐ[ℤ] flag.G i.castSucc) = flag.quot i)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (pr : flag.F i.succ ⟶ L) (hzero : flag.incl i ≫ pr = 0)
    (hses : (ShortComplex.mk (flag.incl i) pr hzero).ShortExact) :
    ∃ (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
      (_ : Module.Flat ℤ K) (j : K →ₐc[ℤ] flag.G i.succ)
      (e : ∀ U : specInt.Fppf,
        L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤)))),
      Function.Injective j ∧
      (j : K →ₐ[ℤ] flag.G i.succ).range = HopfAlgebra.hopfKer qc ∧
      HopfAlgebra.IsHopfGalois qc ∧
      Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) (flag.G i.succ) ∧
      (∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
        (Additive.toMul (e U (L.1.map f.op s))) k
          = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv.solution
