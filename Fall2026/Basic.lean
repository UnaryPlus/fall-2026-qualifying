-- Owen Bechtel
-- Proof of fall 2026 algebra qualifying exam, problem 7
-- About 25%-30% is AI generated (Claude Code, Opus 5.5)
import Mathlib

open Complex (I exp)
open Real (pi sqrt)

section
variable
  (p : ℕ)
  [p_prime : Fact (Nat.Prime p)]

noncomputable def ζ : ℂ :=
  exp (2 * pi * I / p)

def pStar : ℤ :=
  (-1)^((p - 1) / 2) * p

noncomputable def g : ℂ :=
  ∑ a ∈ Finset.Ico 1 p, legendreSym p a * (ζ p)^a

noncomputable def K : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {ζ p}

theorem ζ_prim : IsPrimitiveRoot (ζ p) p := by
  apply Complex.isPrimitiveRoot_exp
  exact Nat.Prime.ne_zero p_prime.out

theorem K_cyclo : IsCyclotomicExtension {p} ℚ (K p) := by
  /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
  have hint : IsIntegral ℚ (ζ p) := ((ζ_prim p).isIntegral p_prime.out.pos).tower_top
  change IsCyclotomicExtension {p} ℚ (IntermediateField.adjoin ℚ {ζ p}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
  exact (ζ_prim p).adjoin_isCyclotomicExtension ℚ
  /- ~~~~~~~ END AI ~~~~~~~ -/

theorem K_numField : NumberField (K p) := by
  have : IsCyclotomicExtension {p} ℚ (K p) := K_cyclo p
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

noncomputable def galEquiv : Gal(K p / ℚ) ≃* (ZMod p)ˣ :=
  have : NumberField (K p) := K_numField p
  have : IsCyclotomicExtension {p} ℚ (K p) := K_cyclo p
  IsCyclotomicExtension.Rat.galEquivZMod p (K p)

noncomputable def galSquares : Subgroup Gal(K p / ℚ) :=
  Subgroup.map ((galEquiv p).symm) (squares p)

theorem galSquares_index (p_ne_two : p ≠ 2) : Subgroup.index (galSquares p) = 2 := by
  unfold galSquares
  rw [Subgroup.index_map_equiv]
  exact (squares_index p p_ne_two)

noncomputable def F : IntermediateField ℚ (K p) :=
  IntermediateField.fixedField (galSquares p)

theorem F_degree (p_ne_two : p ≠ 2) : Module.finrank ℚ (F p) = 2 := by
  have : IsCyclotomicExtension {p} ℚ (K p) := K_cyclo p
  have : IsGalois ℚ (K p) := IsCyclotomicExtension.isGalois {p} ℚ (K p)
  have : FiniteDimensional ℚ (K p) := (K_numField p).to_finiteDimensional
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  unfold F
  rw [IntermediateField.fixingSubgroup_fixedField]
  exact (galSquares_index p p_ne_two)

theorem F_unique (p_ne_two : p ≠ 2) (E : IntermediateField ℚ (K p)) (hE : Module.finrank ℚ E = 2) : E = F p := by
  have : IsCyclotomicExtension {p} ℚ (K p) := K_cyclo p
  have : IsGalois ℚ (K p) := IsCyclotomicExtension.isGalois {p} ℚ (K p)
  have : FiniteDimensional ℚ (K p) := (K_numField p).to_finiteDimensional
  have : IsCyclic Gal(K p / ℚ) := (MulEquiv.isCyclic (galEquiv p)).mpr inferInstance
  have hGE : E.fixingSubgroup.index = 2 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact hE
  have GE_squares : E.fixingSubgroup = galSquares p := by
    rw [IsCyclic.subgroup_eq_iff_index_eq]
    rw [hGE, galSquares_index p p_ne_two]
  rw [← IsGalois.fixedField_fixingSubgroup E]
  rw [GE_squares]
  rfl

theorem g_pow_two (p_ne_two : p ≠ 2) : (g p)^2 = pStar p := by
  let χ : MulChar (ZMod p) ℂ := MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)
  let ψ : AddChar (ZMod p) ℂ := AddChar.zmodChar p (ζ_prim p).pow_eq_one
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
      exact ζ_prim p
  have lem2 : gaussSum χ ψ = g p := by
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
  | 2 => sqrt 2
  | 1 => g p
  | 3 => I * g p
  | _ => 0

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

theorem cycloSqrt_sqrt : (cycloSqrt p)^2 = p := by
  unfold cycloSqrt
  match h : p % 4 with
  | 2 =>
    simp
    have p_eq_two : p = 2 := by
      match Nat.Prime.eq_two_or_odd p_prime.out with
      | .inl hp => exact hp
      | .inr hp => omega
    rw [p_eq_two]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    rfl
  | 1 =>
    simp
    /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
    have p_ne_two : p ≠ 2 := by omega
    have heven : Even ((p - 1) / 2) := by
      rw [Nat.even_iff]
      omega
    rw [g_pow_two p p_ne_two]
    unfold pStar
    rw [heven.neg_one_pow]
    push_cast
    ring
    /- ~~~~~~~ END AI ~~~~~~~ -/
  | 3 =>
    simp
    /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
    have p_ne_two : p ≠ 2 := by omega
    have hodd : Odd ((p - 1) / 2) := by
      rw [Nat.odd_iff]
      omega
    rw [mul_pow, Complex.I_sq, g_pow_two p p_ne_two]
    unfold pStar
    rw [hodd.neg_one_pow]
    push_cast
    ring
    /- ~~~~~~~ END AI ~~~~~~~ -/
  | 0 =>
    exfalso
    exact p_notMulOf_4 p h
  | _ + 4 => omega

theorem cycloSqrt_genBy : cycloSqrt p ∈ IntermediateField.adjoin ℚ {ζ p, I, (sqrt 2 / 2) + I * (sqrt 2 / 2)} := by
  /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
  have hI : I ∈ IntermediateField.adjoin ℚ {ζ p, I, (sqrt 2 / 2) + I * (sqrt 2 / 2)} :=
    IntermediateField.subset_adjoin _ _ (by simp)
  /- ~~~~~~~ END AI ~~~~~~~ -/
  have hζ : ζ p ∈ IntermediateField.adjoin ℚ {ζ p, I, (sqrt 2 / 2) + I * (sqrt 2 / 2)} :=
    IntermediateField.subset_adjoin _ _ (by simp)
  have hg : g p ∈ IntermediateField.adjoin ℚ {ζ p, I, (sqrt 2 / 2) + I * (sqrt 2 / 2)} := by
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
    simp
    /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
    have hw : (sqrt 2 / 2) + I * (sqrt 2 / 2) ∈
        IntermediateField.adjoin ℚ {ζ p, I, (sqrt 2 / 2) + I * (sqrt 2 / 2)} :=
      IntermediateField.subset_adjoin _ _ (by simp)
    have h_eq : (sqrt 2 : ℂ) = (1 - I) * ((sqrt 2 / 2) + I * (sqrt 2 / 2)) := by
      linear_combination ((sqrt 2 : ℂ) / 2) * Complex.I_sq
    have h := mul_mem (sub_mem (one_mem _) hI) hw
    rwa [← h_eq] at h
    /- ~~~~~~~ END AI ~~~~~~~ -/
  | 1 =>
    simp
    exact hg
  | 3 =>
    simp
    exact mul_mem hI hg
  | 0 =>
    exfalso
    exact p_notMulOf_4 p h
  | _ + 4 => omega

end

noncomputable def cycloSqrtNat (n : ℕ) : ℂ :=
  if n = 0 then 0
  else List.prod (List.pmap
    (P := Nat.Prime)
    (fun p hp => cycloSqrt p (p_prime := ⟨hp⟩))
    (Nat.primeFactorsList n)
    (fun _ => Nat.prime_of_mem_primeFactorsList))

noncomputable def cycloSqrtInt (n : ℤ) : ℂ :=
  (if n < 0 then I else 1) * cycloSqrtNat (Int.natAbs n)

theorem cycloSqrtNat_sqrt (n : ℕ) : (cycloSqrtNat n)^2 = n := by
  if h : n = 0 then
    rw [h]
    unfold cycloSqrtNat
    rw [ite_eq_left rfl]
    norm_num
  else
    unfold cycloSqrtNat
    rw [ite_eq_right h]
    rw [← powMonoidHom_apply, ← List.prod_hom, List.map_pmap]
    simp_rw [powMonoidHom_apply, cycloSqrt_sqrt]
    have lem (x : ℕ) : ↑x = Nat.castRingHom ℂ x := by dsimp
    conv in (fun _ _ => _) => ext _ _; rw [lem]
    rw [List.pmap_eq_map, List.prod_hom]
    rw [Nat.prod_primeFactorsList h]
    dsimp

theorem cycloSqrtInt_sqrt (n : ℤ) : (cycloSqrtInt n)^2 = n := by
  unfold cycloSqrtInt
  rw [mul_pow]
  rw [cycloSqrtNat_sqrt]
  norm_num
  if h : n < 0 then
    rw [ite_eq_left h]
    rw [abs_eq_neg_self.mpr (le_of_lt h)]
    norm_num
  else
    rw [ite_eq_right h]
    rw [abs_eq_self.mpr (le_of_not_gt h)]

noncomputable def cycloSqrtInt_gens (n : ℤ) : Set ℂ :=
  {I, (sqrt 2 / 2) + I * (sqrt 2 / 2)} ∪
  {ζ x | x ∈ Nat.primeFactorsList (Int.natAbs n)}

theorem cycloSqrtInt_genBy (n : ℤ) : cycloSqrtInt n ∈ IntermediateField.adjoin ℚ (cycloSqrtInt_gens n) := by
  unfold cycloSqrtInt
  unfold cycloSqrtInt_gens
  apply mul_mem
  . if h : n < 0 then
      rw [ite_eq_left h]
      apply IntermediateField.mem_adjoin_of_mem
      simp
    else
      rw [ite_eq_right h]
      apply one_mem
  . unfold cycloSqrtNat
    if h : n.natAbs = 0 then
      rw [ite_eq_left h]
      apply zero_mem
    else
      rw [ite_eq_right h]
      apply list_prod_mem
      intro x hx
      have ⟨p, hp1, hp2⟩ := List.mem_pmap.mp hx
      have p_prime := Nat.prime_of_mem_primeFactorsList hp1
      rw [← hp2]
      apply (IsConcreteLE.le_iff (S := IntermediateField.adjoin ℚ {ζ p, I, sqrt 2 / 2 + I * (sqrt 2 / 2)})).mp
      . apply IntermediateField.adjoin.mono
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with ha | ha | ha
        . apply Set.mem_union_right
          use p
          exact ⟨hp1, symm ha⟩
        . simp; tauto
        . simp; tauto
      . exact cycloSqrt_genBy p (p_prime := ⟨p_prime⟩)

theorem cycloSqrtInt_eq_pm_sqrt (n : ℤ) : cycloSqrtInt n = Complex.sqrt n ∨ cycloSqrtInt n = -Complex.sqrt n := by
  apply eq_or_eq_neg_of_sq_eq_sq
  rw [cycloSqrtInt_sqrt]
  unfold Complex.sqrt
  simp

theorem quadratic_in_cyclo (n : ℤ) : IntermediateField.adjoin ℚ {Complex.sqrt n} ≤ IntermediateField.adjoin ℚ (cycloSqrtInt_gens n) := by
  rw [IntermediateField.adjoin_simple_le_iff]
  match cycloSqrtInt_eq_pm_sqrt n with
  | .inl h =>
    rw [← h]
    exact cycloSqrtInt_genBy n
  | .inr h =>
    rw [← neg_mem_iff]
    rw [← h]
    exact cycloSqrtInt_genBy n

theorem actuallyCyclo (n : ℤ) :
  IsCyclotomicExtension
  ({4, 8} ∪ {x | x ∈ Nat.primeFactorsList (Int.natAbs n)})
  ℚ (IntermediateField.adjoin ℚ (cycloSqrtInt_gens n)) := by
  /- ~~~~~~~ BEGIN AI ~~~~~~~ -/
  set S : Set ℕ := {4, 8} ∪ {x | x ∈ Nat.primeFactorsList (Int.natAbs n)} with hS
  -- (√2/2) + I(√2/2) = exp(2πi/8) is a primitive 8th root of unity
  have w_prim : IsPrimitiveRoot ((sqrt 2 / 2 : ℂ) + I * (sqrt 2 / 2)) 8 := by
    have h := Complex.isPrimitiveRoot_exp 8 (by norm_num)
    have : exp (2 * ↑pi * I / ↑(8 : ℕ)) = (sqrt 2 / 2 : ℂ) + I * (sqrt 2 / 2) := by
      rw [show 2 * (pi : ℂ) * I / ((8 : ℕ) : ℂ) = ((pi / 4 : ℝ) : ℂ) * I by push_cast; ring]
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_pi_div_four, Real.sin_pi_div_four]
      push_cast
      ring
    rwa [this] at h
  -- every order in S has a primitive root among the generators
  have hprim : ∀ m ∈ S, m ≠ 0 →
      ∃ r ∈ IntermediateField.adjoin ℚ (cycloSqrtInt_gens n), IsPrimitiveRoot r m := by
    intro m hm _
    simp only [hS, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_ofPred_eq] at hm
    rcases hm with (rfl | rfl) | hm
    · exact ⟨I, IntermediateField.subset_adjoin _ _ (by simp [cycloSqrtInt_gens]),
        Complex.isPrimitiveRoot_I⟩
    · exact ⟨_, IntermediateField.subset_adjoin _ _ (by simp [cycloSqrtInt_gens]), w_prim⟩
    · exact ⟨ζ m, IntermediateField.subset_adjoin _ _ (Set.mem_union_right _ ⟨m, hm, rfl⟩),
        Complex.isPrimitiveRoot_exp m (Nat.prime_of_mem_primeFactorsList hm).ne_zero⟩
  -- the generators generate the same field as all m-th roots of unity, m ∈ S
  have heq : IntermediateField.adjoin ℚ (cycloSqrtInt_gens n) =
      IntermediateField.adjoin ℚ {b : ℂ | ∃ m ∈ S, m ≠ 0 ∧ b ^ m = 1} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro b hb
      apply IntermediateField.subset_adjoin
      simp only [cycloSqrtInt_gens, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_ofPred_eq] at hb
      rcases hb with (rfl | rfl) | ⟨p, hp, rfl⟩
      · exact ⟨4, by simp [hS], by norm_num, Complex.isPrimitiveRoot_I.pow_eq_one⟩
      · exact ⟨8, by simp [hS], by norm_num, w_prim.pow_eq_one⟩
      · have hp0 := (Nat.prime_of_mem_primeFactorsList hp).ne_zero
        exact ⟨p, Set.mem_union_right _ hp, hp0, (Complex.isPrimitiveRoot_exp p hp0).pow_eq_one⟩
    · rw [IntermediateField.adjoin_le_iff]
      rintro b ⟨m, hm, hm0, hb⟩
      obtain ⟨r, hr, hrm⟩ := hprim m hm hm0
      have : NeZero m := ⟨hm0⟩
      obtain ⟨k, _, rfl⟩ := hrm.eq_pow_of_pow_eq_one hb
      exact pow_mem hr k
  rw [heq]
  exact IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot S ℚ ℂ
    (fun m hm hm0 => (hprim m hm hm0).imp fun _ h => h.2)
  /- ~~~~~~~ END AI ~~~~~~~ -/
