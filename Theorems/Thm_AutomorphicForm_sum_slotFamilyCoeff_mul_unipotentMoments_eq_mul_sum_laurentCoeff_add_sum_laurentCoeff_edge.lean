import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import P2M.Util
import P2M.Sol.S_AutomorphicForm_sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (σr s : HeightOneSpectrum (𝓞 K) → ℂ)
    (hσ : ∀ v ∈ T, σr v ^ 2 = HeckeEigensystem.cNorm v *
      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (hs : ∀ v ∈ T, ((Real.sqrt (Ideal.absNorm (w' v).asIdeal : ℝ) : ℂ) * s v) =
      σr v ^ SatakeCombination.slotDeg K L ws v)
    (hζ : ∀ v ∈ T,
      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          SatakeCombination.slotDeg K L ws v =
        ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (hNws : ∀ v ∈ T, Ideal.absNorm (ws v).1.asIdeal =
      Ideal.absNorm v.asIdeal ^ SatakeCombination.slotDeg K L ws v)
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (Λ κ₀ : ℂ) (c₁ c₂ : HeightOneSpectrum (𝓞 K) → ℂ) (R : ℝ) :
    ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
      SatakeCombination.slotFamilyCoeff K L ws ks js T m *
        (Λ * ((R : ℂ) *
                ∏ i : T,
                  ((1 + (-1 : ℂ) ^ (m i.1 i.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm i.1 *
                      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                          Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m i.1 i.2) 0 / 2) *
                    ((∏ n ∈ Finset.range ((m i.1 i.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                    ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m i.1 i.2) 1) +
                ∑ p : T,
                  (c₁ p.1 *
                      ((1 + (-1 : ℂ) ^ (m p.1 p.2) 0) * (4 * (HeckeEigensystem.cNorm p.1 *
                          ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                              Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m p.1 p.2) 0 / 2) *
                        ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m p.1 p.2) 1) +
                      c₂ p.1 *
                      ((1 + (-1 : ℂ) ^ (m p.1 p.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm p.1 *
                          ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                              Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m p.1 p.2) 0 / 2) *
                        ((∏ n ∈ Finset.range ((m p.1 p.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                        ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m p.1 p.2) 1)) *
                    ∏ i ∈ Finset.univ.erase p,
                      ((1 + (-1 : ℂ) ^ (m i.1 i.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm i.1 *
                          ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                              Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m i.1 i.2) 0 / 2) *
                        ((∏ n ∈ Finset.range ((m i.1 i.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                        ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m i.1 i.2) 1)) +
              κ₀ * ∏ i : T,
                ((1 + (-1 : ℂ) ^ (m i.1 i.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm i.1 *
                    ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m i.1 i.2) 0 / 2) *
                  ((∏ n ∈ Finset.range ((m i.1 i.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                  ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                      Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m i.1 i.2) 1)) =
      (R : ℂ) * (Λ *
          ∑ n ∈ Fintype.piFinset
            (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
          (∏ i : Fin T.card,
            ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
            ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
              LaurentPolynomial ℂ).coeff (n i)) *
          (∏ i : Fin T.card, (if n i = 0 then (1 : ℂ) else 0))) +
        (Λ * ∑ p : T,
            (c₁ p.1 *
              ∑ n ∈ Fintype.piFinset
                (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
              (∏ i : Fin T.card,
                ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                    s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                    Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
                ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
                  LaurentPolynomial ℂ).coeff (n i)) *
              ((∏ i ∈ Finset.univ.erase (T.equivFin p), (if n i = 0 then (1 : ℂ) else 0)) *
                (1 + (-1 : ℂ) ^ (SatakeCombination.slotDeg K L ws p.1 * (n (T.equivFin p)).natAbs))) +
             c₂ p.1 *
              ∑ n ∈ Fintype.piFinset
                (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
              (∏ i : Fin T.card,
                ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                    s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                    Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
                ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
                  LaurentPolynomial ℂ).coeff (n i)) *
              (∏ i : Fin T.card, (if n i = 0 then (1 : ℂ) else 0))) +
          κ₀ *
            ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                  s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                  Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
                LaurentPolynomial ℂ).coeff (n i)) *
            (∏ i : Fin T.card, (if n i = 0 then (1 : ℂ) else 0))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge.solution
