import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor

set_option autoImplicit false

open TensorProduct

universe u

theorem Module.FinitePresentation.exists_notMem_basis_localizedModule_of_basis_residueField_tensor
    {T : Type u} [CommRing T] {M : Type u} [AddCommGroup M] [Module T M] [Module.FinitePresentation T M]
    (p : Ideal T) [hp : p.IsPrime] (hfree : (⟨p, hp⟩ : PrimeSpectrum T) ∈ Module.freeLocus T M)
    {ι : Type} [Finite ι] (m : ι → M)
    (b : Module.Basis ι p.ResidueField (p.ResidueField ⊗[T] M)) (hb : ∀ i, b i = (1 : p.ResidueField) ⊗ₜ[T] m i) :
    ∃ (t : T) (_ : t ∉ p)
      (b' : Module.Basis ι (Localization.Away t) (LocalizedModule (Submonoid.powers t) M)),
      ∀ i, b' i = LocalizedModule.mkLinearMap (Submonoid.powers t) M (m i) := by p2m_exact_reverting @_root_.P2MW.S_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor.solution
