import Mathlib

open Complex (I exp)
open Real (pi sqrt)

section
variable
  (p : ℕ)
  [p_prime : Fact (Nat.Prime p)]
  (ζ : ℂ)
  [ζ_prim : Fact (IsPrimitiveRoot ζ p)]

def pStar : ℤ :=
  (-1)^((p - 1) / 2) * p

def g : ℂ :=
  ∑ a ∈ Finset.Ico 1 p, legendreSym p a * ζ^a

noncomputable def K : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {ζ}

theorem K_cyclo : IsCyclotomicExtension {p} ℚ (K ζ) := by
  /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
  have hζ : IsPrimitiveRoot ζ p := ζ_prim.out
  have hint : IsIntegral ℚ ζ := (hζ.isIntegral p_prime.out.pos).tower_top
  change IsCyclotomicExtension {p} ℚ (IntermediateField.adjoin ℚ {ζ}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ
  /- ~~~~~~~ END AI ~~~~~~~ -/

include p
theorem K_numField : NumberField (K ζ) := by
  have : IsCyclotomicExtension {p} ℚ (K ζ) := K_cyclo p ζ
  apply IsCyclotomicExtension.numberField {p} ℚ

def squares : Subgroup (ZMod p)ˣ := (powMonoidHom 2).range

theorem squares_index (p_ne_two : p ≠ 2) : Subgroup.index (squares p) = 2 := by
  unfold squares
  rw [IsCyclic.index_powMonoidHom_range]
  rw [Nat.card_eq_fintype_card]
  rw [ZMod.card_units]
  have h_even : Even (p - 1) := Nat.Prime.even_sub_one p_prime.out p_ne_two
  have h_two_dvd : 2 ∣ (p - 1) := Even.two_dvd h_even
  rw [Nat.gcd_eq_right h_two_dvd]

noncomputable def galEquiv : Gal(K ζ / ℚ) ≃* (ZMod p)ˣ :=
  have : NumberField (K ζ) := K_numField p ζ
  have : IsCyclotomicExtension {p} ℚ (K ζ) := K_cyclo p ζ
  IsCyclotomicExtension.Rat.galEquivZMod p (K ζ)

noncomputable def galSquares : Subgroup Gal(K ζ / ℚ) :=
  Subgroup.map ((galEquiv p ζ).symm) (squares p)

theorem galSquares_index (p_ne_two : p ≠ 2) : Subgroup.index (galSquares p ζ) = 2 := by
  unfold galSquares
  rw [Subgroup.index_map_equiv]
  exact (squares_index p p_ne_two)

noncomputable def F : IntermediateField ℚ (K ζ) :=
  IntermediateField.fixedField (galSquares p ζ)

theorem F_degree (p_ne_two : p ≠ 2) : Module.finrank ℚ (F p ζ) = 2 := by
  have : IsCyclotomicExtension {p} ℚ (K ζ) := K_cyclo p ζ
  have : IsGalois ℚ (K ζ) := IsCyclotomicExtension.isGalois {p} ℚ (K ζ)
  have : FiniteDimensional ℚ (K ζ) := (K_numField p ζ).to_finiteDimensional
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  unfold F
  rw [IntermediateField.fixingSubgroup_fixedField]
  exact (galSquares_index p ζ p_ne_two)

theorem F_unique (p_ne_two : p ≠ 2) (E : IntermediateField ℚ (K ζ)) (hE : Module.finrank ℚ E = 2) : E = F p ζ := by
  have : IsCyclotomicExtension {p} ℚ (K ζ) := K_cyclo p ζ
  have : IsGalois ℚ (K ζ) := IsCyclotomicExtension.isGalois {p} ℚ (K ζ)
  have : FiniteDimensional ℚ (K ζ) := (K_numField p ζ).to_finiteDimensional
  have : IsCyclic Gal(K ζ / ℚ) := (MulEquiv.isCyclic (galEquiv p ζ)).mpr inferInstance
  have hGE : E.fixingSubgroup.index = 2 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact hE
  have GE_squares : E.fixingSubgroup = galSquares p ζ := by
    rw [IsCyclic.subgroup_eq_iff_index_eq]
    rw [hGE, galSquares_index p ζ p_ne_two]
  rw [← IsGalois.fixedField_fixingSubgroup E]
  rw [GE_squares]
  rfl

theorem g_pow_two (p_ne_two : p ≠ 2) : (g p ζ)^2 = pStar p := by
  let χ : MulChar (ZMod p) ℂ := MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)
  let ψ : AddChar (ZMod p) ℂ := AddChar.zmodChar p (ζ_prim.out).pow_eq_one
  have lem1 : gaussSum χ ψ ^ 2 = χ (-1) * p := by
    rw [gaussSum_sq]
    . rw [ZMod.card]
    . unfold χ
      rw [MulChar.ringHomComp_ne_one_iff]
      apply quadraticChar_ne_one
      rw [ZMod.ringChar_zmod_n]
      exact p_ne_two
      /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
      rw [Int.coe_castRingHom]
      exact Int.cast_injective
      /- ~~~~~~~ END AI ~~~~~~~ -/
    . apply MulChar.IsQuadratic.comp
      exact quadraticChar_isQuadratic (ZMod p)
    . apply AddChar.zmodChar_primitive_of_primitive_root
      exact ζ_prim.out
  have lem2 : gaussSum χ ψ = g p ζ := by
    unfold gaussSum g
    rw [Finset.sum_eq_add_sum_sdiff_singleton 0]
    rw [MulChar.ringHomComp_apply]
    rw [quadraticChar_zero]
    rw [Int.coe_castRingHom]
    dsimp only
    norm_cast
    rw [zero_mul, zero_add]
    apply Finset.sum_bij (fun x _ => x.val)
    /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
    . -- the map lands in Ico 1 p
      intro a ha
      rw [Finset.mem_sdiff, Finset.mem_singleton] at ha
      rw [Finset.mem_Ico]
      exact ⟨Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).mpr ha.2), ZMod.val_lt a⟩
    . -- injectivity
      intro a₁ _ a₂ _ h
      exact ZMod.val_injective p h
    . -- surjectivity
      intro b hb
      rw [Finset.mem_Ico] at hb
      refine ⟨(b : ZMod p), ?_, ZMod.val_cast_of_lt hb.2⟩
      rw [Finset.mem_sdiff, Finset.mem_singleton]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt hb.1 hb.2
    . -- the summands agree
      intro a _
      simp only [χ, ψ]
      rw [MulChar.ringHomComp_apply, Int.coe_castRingHom, AddChar.zmodChar_apply]
      simp [legendreSym]
    . -- side goal from pulling out the 0 term
      intro h
      exact absurd (Finset.mem_univ 0) h
    /- ~~~~~~~ END AI ~~~~~~~ -/
  have p_odd : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two (p_prime.out) p_ne_two)
  have p_div : p / 2 = (p - 1) / 2 := by omega
  rw [← lem2, lem1]
  unfold pStar
  rw [MulChar.ringHomComp_apply]
  rw [quadraticChar_neg_one, ZMod.χ₄_eq_neg_one_pow]
  . rw [ZMod.card]
    rw [p_div]
    rw [Int.coe_castRingHom]
    simp
  . rw [ZMod.card]
    exact p_odd
  . rw [ZMod.ringChar_zmod_n]
    exact p_ne_two

noncomputable def cycloSqrt : ℂ :=
  match p % 4 with
  | 0 | 2 => sqrt 2
  | 1 => g p ζ
  | 3 => I * g p ζ
  | _ + 4 => by omega

theorem p_notMulOf_4 : p % 4 ≠ 0 := by
  intro h
  absurd p_prime.out
  if hp : p = 4 then
    rw [hp]
    norm_num
  else
    apply Nat.not_prime_of_dvd_of_ne (m := 4)
    . omega
    . norm_num
    . symm; exact hp

theorem cycloSqrt_sqrt : (cycloSqrt p ζ)^2 = p := by
  unfold cycloSqrt
  match h : (p % 4) with
  | 2 =>
    dsimp
    have p_eq_two : p = 2 := by
      match Nat.Prime.eq_two_or_odd p_prime.out with
      | .inl hp => exact hp
      | .inr hp => omega
    rw [p_eq_two]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    rfl
  | 1 =>
    dsimp
    /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
    have p_ne_two : p ≠ 2 := by omega
    have heven : Even ((p - 1) / 2) := by
      rw [Nat.even_iff]
      omega
    rw [g_pow_two p ζ p_ne_two]
    unfold pStar
    rw [heven.neg_one_pow]
    push_cast
    ring
    /- ~~~~~~~ END AI ~~~~~~~ -/
  | 3 =>
    dsimp
    /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
    have p_ne_two : p ≠ 2 := by omega
    have hodd : Odd ((p - 1) / 2) := by
      rw [Nat.odd_iff]
      omega
    rw [mul_pow, Complex.I_sq, g_pow_two p ζ p_ne_two]
    unfold pStar
    rw [hodd.neg_one_pow]
    push_cast
    ring
    /- ~~~~~~~ END AI ~~~~~~~ -/
  | 0 =>
    exfalso
    exact p_notMulOf_4 p h
  | _ + 4 => omega

omit ζ_prim
theorem cycloSqrt_cyclo : cycloSqrt p ζ ∈ IntermediateField.adjoin ℚ {ζ, I, (sqrt 2 / 2) + I * (sqrt 2 / 2)} := by
  /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
  have hI : I ∈ IntermediateField.adjoin ℚ {ζ, I, (sqrt 2 / 2) + I * (sqrt 2 / 2)} :=
    IntermediateField.subset_adjoin _ _ (by simp)
  /- ~~~~~~~ END AI ~~~~~~~ -/
  have hζ : ζ ∈ IntermediateField.adjoin ℚ {ζ, I, (sqrt 2 / 2) + I * (sqrt 2 / 2)} :=
    IntermediateField.subset_adjoin _ _ (by simp)
  have hg : g p ζ ∈ IntermediateField.adjoin ℚ {ζ, I, (sqrt 2 / 2) + I * (sqrt 2 / 2)} := by
    unfold g
    apply sum_mem
    intro a ha
    apply mul_mem
    . apply IntermediateField.intCast_mem
    . apply pow_mem
      exact hζ
  unfold cycloSqrt
  match h : (p % 4) with
  | 2 =>
    dsimp
    /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
    have hw : (sqrt 2 / 2) + I * (sqrt 2 / 2) ∈
        IntermediateField.adjoin ℚ {ζ, I, (sqrt 2 / 2) + I * (sqrt 2 / 2)} :=
      IntermediateField.subset_adjoin _ _ (by simp)
    have h_eq : (sqrt 2 : ℂ) = (1 - I) * ((sqrt 2 / 2) + I * (sqrt 2 / 2)) := by
      linear_combination ((sqrt 2 : ℂ) / 2) * Complex.I_sq
    have h := mul_mem (sub_mem (one_mem _) hI) hw
    rwa [← h_eq] at h
    /- ~~~~~~~ END AI ~~~~~~~ -/
  | 1 =>
    dsimp
    exact hg
  | 3 =>
    dsimp
    exact mul_mem hI hg
  | 0 =>
    exfalso
    exact p_notMulOf_4 p h
  | _ + 4 => omega

end
