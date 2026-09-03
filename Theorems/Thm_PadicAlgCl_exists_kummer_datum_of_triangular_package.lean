import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_kummer_datum_of_triangular_package
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false
theorem PadicAlgCl.exists_kummer_datum_of_triangular_package
    {B : Type} [CommRing B] [IsLocalRing B] (p : ℕ) [Fact p.Prime]
    (hpB : (p : B) ∈ IsLocalRing.maximalIdeal B)
    (x z : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → Bˣ) (y : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → B)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : FiniteDimensional ℚ F)
    (hxmul : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), x (g * h) = x g * x h)
    (hzmul : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), z (g * h) = z g * z h)
    (hy : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), y (g * h) = (x g : B) * y h + y g * (z h : B))
    (hlev : ∀ s : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), localGaloisToGlobal p s ∈ F.fixingSubgroup → x s = 1 ∧ y s = 0 ∧ z s = 1)
    (hcyc : ∀ (g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (n a : ℕ), (∀ μ : PadicAlgCl p, μ ^ p ^ n = 1 → g μ = μ ^ a) →
      (x g : B) * (z g : B) - (a : B) ∈ Ideal.span {((p ^ n : ℕ) : B)})
    (hzsq : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) - 1 ∈ IsLocalRing.maximalIdeal B)
    (ζ : PadicAlgCl p) (hζ : IsPrimitiveRoot ζ p)
    (Λ : IsLocalRing.ResidueField B →+ ZMod p) (η : B) :
    ∃ (a : ℚ_[p]ˣ) (α : (PadicAlgCl p)ˣ),
      algebraMap ℚ_[p] (PadicAlgCl p) (a : ℚ_[p]) = (α : PadicAlgCl p) ^ p ∧
      ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), g (α : PadicAlgCl p) =
          ζ ^ (Λ (IsLocalRing.residue B (η * (y g * (((z g)⁻¹ : Bˣ) : B))))).val * (α : PadicAlgCl p) := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_kummer_datum_of_triangular_package.solution
