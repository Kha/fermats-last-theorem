import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_LocalInvariant
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_of_assembly
set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_of_assembly
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (θ : ∀ v : extArithIndex S,
      continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) →ₗ[ZMod p]
        Module.Dual (ZMod p)
          (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p)))))
    (hθ : ∀ q : ↥S,
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) (θ (Sum.inr q)))
    (invInf : continuousH2 (extArithLoc S (Sum.inl ()))
        (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inl ())))) →ₗ[ZMod p] ZMod p)
    (hinvInf : Function.Injective invInf)
    (hθinf : IsTheta1 (extArithLoc S (Sum.inl ()))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inl ())) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inl ()))))
        invInf (θ (Sum.inl ())))
    (z : ∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
    (horth : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)),
        ∀ w : ∀ v : extArithIndex S, continuousH1 (extArithLoc S v)
            (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))),
          (∀ v, (w v : H1 _) = (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) v).hom y) →
          ∑ v : extArithIndex S, θ v (z v) (w v) = 0)

    (hloc : ∀ y ∈ continuousH1S S (M.dualTwist (cycloChar p)), ∀ v : extArithIndex S,
      locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) y v ∈
        continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))
    (hlocM : ∀ x ∈ continuousH1S S M, ∀ v : extArithIndex S,
      locTotal (extArithLoc S) M x v ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
    [∀ v : extArithIndex S, FiniteDimensional (ZMod p) (continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))]
    (hREC : ∀ (x : H1 M) (_ : x ∈ continuousH1S S M)
        (y : H1 (M.dualTwist (cycloChar p))) (_ : y ∈ continuousH1S S (M.dualTwist (cycloChar p)))
        (z' : ∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
        (w : ∀ v : extArithIndex S, continuousH1 (extArithLoc S v)
          (Rep.res (extArithLoc S v) (M.dualTwist (cycloChar p))))
        (_ : ∀ v, (z' v : H1 _) = (locRes (extArithLoc S) M v).hom x)
        (_ : ∀ v, (w v : H1 _) = (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) v).hom y),
        ∑ v : extArithIndex S, θ v (z' v) (w v) = 0)

    {G : Type} [Group G] (R J C : Rep ℤ G) (lamJ : J ⟶ C)
    (VB : Type) [AddCommGroup VB]
    (LJ1 : (R ⟶ J) →+ ∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
    (hJ1 : Function.Surjective LJ1)
    (al : (R ⟶ C) →+ VB →+ ZMod p)
    (infl : VB →+ H1 (M.dualTwist (cycloChar p)))
    (hrange : ∀ y : H1 (M.dualTwist (cycloChar p)), y ∈ continuousH1S S (M.dualTwist (cycloChar p)) ↔ ∃ x, infl x = y)
    (u : extArithIndex S → (ZMod p)ˣ)
    (hID : ∀ (s : R ⟶ J) (x : VB) (hx : infl x ∈ continuousH1S S (M.dualTwist (cycloChar p))),
      al (s ≫ lamJ) x = ∑ v : extArithIndex S, (u v : ZMod p) *
        θ v (LJ1 s v) ⟨locTotal (extArithLoc S) (M.dualTwist (cycloChar p)) (infl x) v, hloc _ hx v⟩)

    {G₁ : Type} [Group G₁] (R₁ P₁ : Rep ℤ G₁) (f₁ : R₁ ⟶ P₁) (J₁ C₁ : Rep ℤ G₁) (lamJ₁ : J₁ ⟶ C₁)
    (VB₁ : Type) [AddCommGroup VB₁] (al₁ : (R₁ ⟶ C₁) →+ VB₁ →+ ZMod p)
    (iS₁ : (R ⟶ J) →+ (R₁ ⟶ J₁)) (iC₁ : (R ⟶ C) →+ (R₁ ⟶ C₁)) (iB₁ : VB →+ VB₁) (hiB₁ : Function.Surjective iB₁)
    (hiSlam₁ : ∀ s : R ⟶ J, iC₁ (s ≫ lamJ) = iS₁ s ≫ lamJ₁)
    (hial₁ : ∀ (φ : R ⟶ C) (x : VB), al₁ (iC₁ φ) (iB₁ x) = al φ x)
    (hEXF : ∀ φ : R ⟶ C, (∃ χ : P₁ ⟶ C₁, iC₁ φ = f₁ ≫ χ) ∨ ∃ x : VB₁, al₁ (iC₁ φ) x ≠ 0)
    (LJ1₁ : (R₁ ⟶ J₁) →+ ∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
    (hLJi₁ : ∀ s : R ⟶ J, LJ1₁ (iS₁ s) = LJ1 s)

    {G₂ : Type} [Group G₂] (R₂ P₂ : Rep ℤ G₂) (f₂ : R₂ ⟶ P₂) (E₂ J₂ : Rep ℤ G₂) (iEJ₂ : E₂ ⟶ J₂)
    (iS₂ : (R₁ ⟶ J₁) →+ (R₂ ⟶ J₂))
    (hPIT : ∀ (t : R₁ ⟶ J₁) (χ : P₁ ⟶ C₁), t ≫ lamJ₁ = f₁ ≫ χ →
      ∃ (e : R₂ ⟶ E₂) (χ' : P₂ ⟶ J₂), iS₂ t = e ≫ iEJ₂ + f₂ ≫ χ')
    (LE1₂ : (R₂ ⟶ E₂) →+ H1 M) (hLE1₂ : ∀ e : R₂ ⟶ E₂, LE1₂ e ∈ continuousH1S S M)
    (LJ1₂ : (R₂ ⟶ J₂) →+ ∀ v : extArithIndex S, continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M))
    (hsq₂ : ∀ (e : R₂ ⟶ E₂) (v : extArithIndex S),
      ((LJ1₂ (e ≫ iEJ₂) v : continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M)) : H1 _) =
        (locRes (extArithLoc S) M v).hom (LE1₂ e))
    (hLJf₂ : ∀ χ' : P₂ ⟶ J₂, LJ1₂ (f₂ ≫ χ') = 0)
    (hLJi₂ : ∀ t : R₁ ⟶ J₁, LJ1₂ (iS₂ t) = LJ1₁ t) :
    ∃ x ∈ continuousH1S S M, ∀ v, (locRes (extArithLoc S) M v).hom x = (z v : H1 _) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_of_assembly.solution
