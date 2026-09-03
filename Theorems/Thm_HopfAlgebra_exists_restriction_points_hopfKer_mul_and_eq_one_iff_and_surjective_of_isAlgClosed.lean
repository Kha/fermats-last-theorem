import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed

set_option autoImplicit false
theorem HopfAlgebra.exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed
    (R : Type) [CommRing R] [IsDomain R] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (hR : Function.Injective (algebraMap R Ω))
    {H : Type} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
    {B₁ B₀ : Type} [CommRing B₁] [HopfAlgebra R B₁] [Module.Finite R B₁] [Module.Free R B₁] [Coalgebra.IsCocomm R B₁]
    [CommRing B₀] [HopfAlgebra R B₀] [Module.Finite R B₀] [Module.Free R B₀] [Coalgebra.IsCocomm R B₀]
    (π₁ : H →ₐc[R] B₁) (hπ₁ : Function.Surjective π₁) (ρ : B₁ →ₐc[R] B₀) (hρ : Function.Surjective ρ)
    [Module.Finite R ↥(HopfAlgebra.hopfKer ρ)] [Module.Free R ↥(HopfAlgebra.hopfKer ρ)]
    (N N' : Submonoid (WithConv (H →ₐ[R] Ω))) (hNN' : N ≤ N')
    (hpts₁ : ∀ f : H →ₐ[R] Ω,
      (∃ g : B₁ →ₐ[R] Ω, g.comp (π₁ : H →ₐ[R] B₁) = f) ↔ WithConv.toConv f ∈ N')
    (hpts₀ : ∀ f : H →ₐ[R] Ω,
      (∃ g : B₀ →ₐ[R] Ω, g.comp ((ρ.comp π₁ : H →ₐc[R] B₀) : H →ₐ[R] B₀) = f) ↔ WithConv.toConv f ∈ N) :
    ∃ r : WithConv (H →ₐ[R] Ω) → WithConv (↥(HopfAlgebra.hopfKer ρ) →ₐ[R] Ω),
      (∀ f ∈ N', ∀ g : B₁ →ₐ[R] Ω, g.comp (π₁ : H →ₐ[R] B₁) = f.ofConv →
        (r f).ofConv = g.comp (HopfAlgebra.hopfKer ρ).val) ∧
      (∀ f ∈ N', ∀ f' ∈ N', r (f * f') = r f * r f') ∧
      (∀ f ∈ N', (r f = 1 ↔ f ∈ N)) ∧
      (∀ ν : WithConv (↥(HopfAlgebra.hopfKer ρ) →ₐ[R] Ω), ∃ f ∈ N', r f = ν) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed.solution
