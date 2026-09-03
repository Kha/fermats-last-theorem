import Definitions.Def_CerednikDrinfeld_MumfordUniformization
import Definitions.Def_CerednikDrinfeld_ToricUniformization
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford ModularCurve

theorem CerednikDrinfeld.Mumford.PeriodUniformization.frobenius_toric_and_frobenius_quot_of_torsionEquiv
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} {H : HeckeData D}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    {T : Type} [AddCommGroup T] {hecke : HeckeAlg →+* Module.End ℤ T}
    {gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T}
    (𝒰 : PeriodUniformization r D H A hA T hecke gal)
    (ζ : (A.valuation.Completion)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (χ : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)) ≃+ (↥(ribbonKernel D) →ₗ[ℤ] ZMod p))
    (hχ : ∀ (v : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
      Additive.toMul ((((v : ↥𝒰.P.U) : 𝒰.P.TorusPoints) z)) = ζ ^ (χ v z).val) :
    (∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
      ∀ v : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)), ∃ v' : ↥(Submodule.torsionBy ℤ ↥𝒰.P.U (p : ℤ)),
        gal φ (𝒰.e (v : ↥𝒰.P.U)) = 𝒰.e (v' : ↥𝒰.P.U) ∧
          χ v' = (r : ℤ) • ((χ v) ∘ₗ heckeKernelMap H ⟨r, Fact.out⟩)) ∧
    (∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
      ∀ (u : ↥𝒰.P.U) (x : ↥(ribbonKernel D)), (p : ℤ) • (u : 𝒰.P.TorusPoints) = 𝒰.P.QL x →
        ∀ hu : 𝒰.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩) (u : 𝒰.P.TorusPoints) ∈ 𝒰.P.U,
          ∃ v : ↥𝒰.P.U, (p : ℤ) • v = 0 ∧
            gal φ (𝒰.e u) = 𝒰.e ⟨𝒰.P.precomp (heckeKernelMap H ⟨r, Fact.out⟩) (u : 𝒰.P.TorusPoints), hu⟩ + 𝒰.e v) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_PeriodUniformization_frobenius_toric_and_frobenius_quot_of_torsionEquiv.solution
