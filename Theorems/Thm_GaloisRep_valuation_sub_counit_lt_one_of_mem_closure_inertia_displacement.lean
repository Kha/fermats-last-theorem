import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_valuation_sub_counit_lt_one_of_mem_closure_inertia_displacement

theorem GaloisRep.valuation_sub_counit_lt_one_of_mem_closure_inertia_displacement
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M : AddSubgroup J)
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (m : ↥M)
    (hm : (m : J) ∈ AddSubgroup.closure
      {x : J | ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∃ y ∈ M, x = σ • y - y}) :
    ∀ h : H, A.valuation ((e.symm m) h -
      algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_valuation_sub_counit_lt_one_of_mem_closure_inertia_displacement.solution
