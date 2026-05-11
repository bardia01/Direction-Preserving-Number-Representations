import PaperProofs.Internal.OptimalAlphabets.AsymmetricProduct.Defs

/-!
# OptimalAlphabets.AsymmetricProduct.Bridge

Generic bridge facts connecting the asymmetric product directions to the
unconstrained spherical-code objective.
-/

noncomputable section

namespace OptimalAlphabets
namespace AsymmetricProduct

@[simp] theorem asymProdSphericalCode_card (n : ℕ) (A : Finset ℝ) :
    (asymProdSphericalCode n A).card = (asymProdDirections n A).card := by
  unfold asymProdSphericalCode
  rw [Finset.card_map, Finset.card_attach]

theorem asymProdSphericalCode_mem_sphericalCodesOfCard (n : ℕ) (A : Finset ℝ) :
    asymProdSphericalCode n A ∈ sphericalCodesOfCard n (asymProdDirections n A).card := by
  simp [sphericalCodesOfCard]

/-- Pointwise comparison at the number of induced asymmetric product directions. -/
theorem rho_sph_asymProdDirections_card_le_F_asym (n : ℕ) (A : Finset ℝ) :
    rho_sph n (asymProdDirections n A).card ≤ F_asym n A := by
  unfold rho_sph F_asym
  refine csInf_le ?_ ?_
  · refine ⟨0, ?_⟩
    rintro x ⟨C, hC, rfl⟩
    exact covrad_sph_nonneg C
  · exact ⟨asymProdSphericalCode n A,
      asymProdSphericalCode_mem_sphericalCodesOfCard n A, rfl⟩

end AsymmetricProduct
end OptimalAlphabets

