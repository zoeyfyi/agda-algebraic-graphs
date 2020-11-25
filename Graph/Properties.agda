open import Graph.Base
open import Graph.Reasoning

module Graph.Properties where
 
+-sym : ∀ { A : Set } { G H : Graph A } → G + H ≡ H + G
+-sym = record
  { vₗ = λ { (+ₗ x) → +ᵣ x ; (+ᵣ x) → +ₗ x }
  ; vᵣ = λ { (+ₗ x) → +ᵣ x ; (+ᵣ x) → +ₗ x }
  ; eₗ = λ { (+ₗ x) → +ᵣ x ; (+ᵣ x) → +ₗ x }
  ; eᵣ = λ { (+ₗ x) → +ᵣ x ; (+ᵣ x) → +ₗ x }
  }

+-assoc : ∀ { A : Set } { G H I : Graph A } → G + (H + I) ≡ (G + H) + I
+-assoc = record
  { vₗ = λ { (+ₗ x) → +ₗ (+ₗ x) ; (+ᵣ (+ₗ x)) → +ₗ (+ᵣ x) ; (+ᵣ (+ᵣ x)) → +ᵣ x }
  ; vᵣ = λ { (+ₗ (+ₗ x)) → +ₗ x ; (+ₗ (+ᵣ x)) → +ᵣ (+ₗ x) ; (+ᵣ x) → +ᵣ (+ᵣ x) }
  ; eₗ = λ { (+ₗ x) → +ₗ (+ₗ x) ; (+ᵣ (+ₗ x)) → +ₗ (+ᵣ x) ; (+ᵣ (+ᵣ x)) → +ᵣ x }
  ; eᵣ = λ { (+ₗ (+ₗ x)) → +ₗ x ; (+ₗ (+ᵣ x)) → +ᵣ (+ₗ x) ; (+ᵣ x) → +ᵣ (+ᵣ x) }
  }
  
+-identityʳ : ∀ { A : Set } { G : Graph A } → G + ε ≡ G
+-identityʳ = record
  { vₗ = λ { (+ₗ x) → x }
  ; vᵣ = λ x → +ₗ x
  ; eₗ = λ { (+ₗ x) → x }
  ; eᵣ = +ₗ 
  }

+-identityˡ : ∀ { A : Set } { G : Graph A } → ε + G ≡ G
+-identityˡ = record
  { vₗ = λ { (+ᵣ x) → x }
  ; vᵣ = +ᵣ
  ; eₗ = λ { (+ᵣ x) → x }
  ; eᵣ = +ᵣ
  }

+-congˡ : ∀ { A : Set } { G H I : Graph A } → G ≡ H → G + I ≡ H + I
+-congˡ G≈H = record
               { vₗ = λ { (+ₗ x) → +ₗ (_≡_.vₗ G≈H x) ; (+ᵣ x) → +ᵣ x }
               ; vᵣ = λ { (+ₗ x) → +ₗ (_≡_.vᵣ G≈H x) ; (+ᵣ x) → +ᵣ x }
               ; eₗ = λ { (+ₗ x) → +ₗ (_≡_.eₗ G≈H x) ; (+ᵣ x) → +ᵣ x }
               ; eᵣ = λ { (+ₗ x) → +ₗ (_≡_.eᵣ G≈H x) ; (+ᵣ x) → +ᵣ x }
               }

+-congʳ : ∀ { A : Set } { G H I : Graph A } → H ≡ I → G + H ≡ G + I
+-congʳ {_} {G} {H} {I} H≡I = begin
  G + H ≡⟨ +-sym ⟩
  H + G ≡⟨ +-congˡ H≡I ⟩
  I + G ≡⟨ +-sym ⟩
  G + I ∎
  where open ≡-Reasoning


⇀-assoc : ∀ { A : Set } { G H I : Graph A } → G ⇀ (H ⇀ I) ≡ (G ⇀ H) ⇀ I
⇀-assoc = record
  { vₗ = λ { (⇀ₗ x) → ⇀ₗ (⇀ₗ x) ; (⇀ᵣ (⇀ₗ x)) → ⇀ₗ (⇀ᵣ x) ; (⇀ᵣ (⇀ᵣ x)) → ⇀ᵣ x }
  ; vᵣ = λ { (⇀ₗ (⇀ₗ x)) → ⇀ₗ x ; (⇀ₗ (⇀ᵣ x)) → ⇀ᵣ (⇀ₗ x) ; (⇀ᵣ x) → ⇀ᵣ (⇀ᵣ x) }
  ; eₗ = λ { (⇀ₗ x) → ⇀ₗ (⇀ₗ x) ; (⇀ᵣ (⇀ₗ x)) → ⇀ₗ (⇀ᵣ x) ; (⇀ᵣ (⇀ᵣ x)) → ⇀ᵣ x ; (⇀ᵣ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ (⇀ᵣ x) x₁ ; (⇀ₗᵣ x (⇀ₗ x₁)) → ⇀ₗ (⇀ₗᵣ x x₁) ; (⇀ₗᵣ x (⇀ᵣ x₁)) → ⇀ₗᵣ (⇀ₗ x) x₁ }
  ; eᵣ = λ { (⇀ₗ (⇀ₗ x)) → ⇀ₗ x ; (⇀ₗ (⇀ᵣ x)) → ⇀ᵣ (⇀ₗ x) ; (⇀ₗ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ x (⇀ₗ x₁) ; (⇀ᵣ x) → ⇀ᵣ (⇀ᵣ x) ; (⇀ₗᵣ (⇀ₗ x) x₁) → ⇀ₗᵣ x (⇀ᵣ x₁) ; (⇀ₗᵣ (⇀ᵣ x) x₁) → ⇀ᵣ (⇀ₗᵣ x x₁) }
  }
 
⇀-identˡ : ∀ { A : Set } { G : Graph A } → G ⇀ ε ≡ G
⇀-identˡ = record
  { vₗ = λ { (⇀ₗ x) → x }
  ; vᵣ = ⇀ₗ
  ; eₗ = λ { (⇀ₗ x) → x }
  ; eᵣ = ⇀ₗ
  }

⇀-identʳ : ∀ { A : Set } { G : Graph A } → ε ⇀ G ≡ G
⇀-identʳ = record
  { vₗ = λ { (⇀ᵣ x) → x }
  ; vᵣ = ⇀ᵣ
  ; eₗ = λ { (⇀ᵣ x) → x }
  ; eᵣ = ⇀ᵣ
  }

⇀-congˡ : ∀ { A : Set } { G H I : Graph A } → G ≡ H → G ⇀ I ≡ H ⇀ I
⇀-congˡ G≈H = record
               { vₗ = λ { (⇀ₗ x) → ⇀ₗ (_≡_.vₗ G≈H x) ; (⇀ᵣ x) → ⇀ᵣ x }
               ; vᵣ = λ { (⇀ₗ x) → ⇀ₗ (_≡_.vᵣ G≈H x) ; (⇀ᵣ x) → ⇀ᵣ x }
               ; eₗ = λ { (⇀ₗ x) → ⇀ₗ (_≡_.eₗ G≈H x) ; (⇀ᵣ x) → ⇀ᵣ x ; (⇀ₗᵣ x x₁) → ⇀ₗᵣ (_≡_.vₗ G≈H x) x₁ }
               ; eᵣ = λ { (⇀ₗ x) → ⇀ₗ (_≡_.eᵣ G≈H x) ; (⇀ᵣ x) → ⇀ᵣ x ; (⇀ₗᵣ x x₁) → ⇀ₗᵣ (_≡_.vᵣ G≈H x) x₁ }
               }

⇀-congʳ : ∀ { A : Set } { G H I : Graph A } → H ≡ I → G ⇀ H ≡ G ⇀ I
⇀-congʳ G≈H = record
               { vₗ = λ { (⇀ₗ x) → ⇀ₗ x ; (⇀ᵣ x) → ⇀ᵣ (_≡_.vₗ G≈H x) }
               ; vᵣ = λ { (⇀ₗ x) → ⇀ₗ x ; (⇀ᵣ x) → ⇀ᵣ (_≡_.vᵣ G≈H x) }
               ; eₗ = λ { (⇀ₗ x) → ⇀ₗ x ; (⇀ᵣ x) → ⇀ᵣ (_≡_.eₗ G≈H x) ; (⇀ₗᵣ x x₁) → ⇀ₗᵣ x (_≡_.vₗ G≈H x₁) }
               ; eᵣ = λ { (⇀ₗ x) → ⇀ₗ x ; (⇀ᵣ x) → ⇀ᵣ (_≡_.eᵣ G≈H x) ; (⇀ₗᵣ x x₁) → ⇀ₗᵣ x (_≡_.vᵣ G≈H x₁) }
               }

⇀-congʳ-≤ : ∀ { A : Set } { G H I : Graph A } → H ≤ I → G ⇀ H ≤ G ⇀ I
⇀-congʳ-≤ H≤I = record
                  { def = record
                            { vₗ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ x ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ (_≡_.vₗ (_≤_.def H≤I) (+ₗ x)) ; (+ᵣ x) → x }
                            ; vᵣ = +ᵣ
                            ; eₗ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ x ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ (_≡_.eₗ (_≤_.def H≤I) (+ₗ x)) ; (+ₗ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ x (_≡_.vₗ (_≤_.def H≤I) (+ₗ x₁)) ; (+ᵣ x) → x }
                            ; eᵣ = +ᵣ
                            }
                  }

⇀-distrib-+ : ∀ { A : Set } { G H I : Graph A } → G ⇀ (H + I) ≡ G ⇀ H + G ⇀ I
⇀-distrib-+ = record
                { vₗ = λ { (⇀ₗ x) → +ₗ (⇀ₗ x) ; (⇀ᵣ (+ₗ x)) → +ₗ (⇀ᵣ x) ; (⇀ᵣ (+ᵣ x)) → +ᵣ (⇀ᵣ x) }
                ; vᵣ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ x ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ (+ₗ x) ; (+ᵣ (⇀ₗ x)) → ⇀ₗ x ; (+ᵣ (⇀ᵣ x)) → ⇀ᵣ (+ᵣ x) }
                ; eₗ = λ { (⇀ₗ x) → +ₗ (⇀ₗ x) ; (⇀ᵣ (+ₗ x)) → +ₗ (⇀ᵣ x) ; (⇀ᵣ (+ᵣ x)) → +ᵣ (⇀ᵣ x) ; (⇀ₗᵣ x (+ₗ x₁)) → +ₗ (⇀ₗᵣ x x₁) ; (⇀ₗᵣ x (+ᵣ x₁)) → +ᵣ (⇀ₗᵣ x x₁) }
                ; eᵣ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ x ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ (+ₗ x) ; (+ₗ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ x (+ₗ x₁) ; (+ᵣ (⇀ₗ x)) → ⇀ₗ x ; (+ᵣ (⇀ᵣ x)) → ⇀ᵣ (+ᵣ x) ; (+ᵣ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ x (+ᵣ x₁) }
                }

+-distrib-⇀ : ∀ { A : Set } { G H I : Graph A } → (G + H) ⇀ I ≡ G ⇀ I + H ⇀ I
+-distrib-⇀ = record
                { vₗ = λ { (⇀ₗ (+ₗ x)) → +ₗ (⇀ₗ x) ; (⇀ₗ (+ᵣ x)) → +ᵣ (⇀ₗ x) ; (⇀ᵣ x) → +ₗ (⇀ᵣ x) }
                ; vᵣ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ (+ₗ x) ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ x ; (+ᵣ (⇀ₗ x)) → ⇀ₗ (+ᵣ x) ; (+ᵣ (⇀ᵣ x)) → ⇀ᵣ x }
                ; eₗ = λ { (⇀ₗ (+ₗ x)) → +ₗ (⇀ₗ x) ; (⇀ₗ (+ᵣ x)) → +ᵣ (⇀ₗ x) ; (⇀ᵣ x) → +ₗ (⇀ᵣ x) ; (⇀ₗᵣ (+ₗ x) x₁) → +ₗ (⇀ₗᵣ x x₁) ; (⇀ₗᵣ (+ᵣ x) x₁) → +ᵣ (⇀ₗᵣ x x₁) }
                ; eᵣ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ (+ₗ x) ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ x ; (+ₗ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ (+ₗ x) x₁ ; (+ᵣ (⇀ₗ x)) → ⇀ₗ (+ᵣ x) ; (+ᵣ (⇀ᵣ x)) → ⇀ᵣ x ; (+ᵣ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ (+ᵣ x) x₁ }
                }

⇀-decomp : ∀ { A : Set } { G H I : Graph A } → G ⇀ (H ⇀ I) ≡ G ⇀ H + (G ⇀ I + H ⇀ I)
⇀-decomp = record
             { vₗ = λ { (⇀ₗ x) → +ₗ (⇀ₗ x) ; (⇀ᵣ x) → +ᵣ (+ᵣ x) }
             ; vᵣ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ x ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ (⇀ₗ x) ; (+ᵣ (+ₗ (⇀ₗ x))) → ⇀ₗ x ; (+ᵣ (+ₗ (⇀ᵣ x))) → ⇀ᵣ (⇀ᵣ x) ; (+ᵣ (+ᵣ x)) → ⇀ᵣ x }
             ; eₗ = λ { (⇀ₗ x) → +ₗ (⇀ₗ x) ; (⇀ᵣ x) → +ᵣ (+ᵣ x) ; (⇀ₗᵣ x (⇀ₗ x₁)) → +ₗ (⇀ₗᵣ x x₁) ; (⇀ₗᵣ x (⇀ᵣ x₁)) → +ᵣ (+ₗ (⇀ₗᵣ x x₁)) }
             ; eᵣ = λ { (+ₗ (⇀ₗ x)) → ⇀ₗ x ; (+ₗ (⇀ᵣ x)) → ⇀ᵣ (⇀ₗ x) ; (+ₗ (⇀ₗᵣ x x₁)) → ⇀ₗᵣ x (⇀ₗ x₁) ; (+ᵣ (+ₗ (⇀ₗ x))) → ⇀ₗ x ; (+ᵣ (+ₗ (⇀ᵣ x))) → ⇀ᵣ (⇀ᵣ x) ; (+ᵣ (+ₗ (⇀ₗᵣ x x₁))) → ⇀ₗᵣ x (⇀ᵣ x₁) ; (+ᵣ (+ᵣ x)) → ⇀ᵣ x }
             }

+-idem : ∀ { A : Set } { G : Graph A } → G + G ≡ G
+-idem {_} {G} = begin
  G + G                          ≡⟨ sym ⇀-identˡ ⟩
  (G + G) ⇀ ε                    ≡⟨ +-distrib-⇀ ⟩
  (G ⇀ ε) + (G ⇀ ε)              ≡⟨ sym +-identityʳ ⟩
  ((G ⇀ ε) + (G ⇀ ε)) + ε        ≡⟨ sym (+-congʳ ⇀-identˡ) ⟩
  ((G ⇀ ε) + (G ⇀ ε)) + (ε ⇀ ε)  ≡⟨ sym +-assoc ⟩
  (G ⇀ ε) + ((G ⇀ ε) + (ε ⇀ ε))  ≡⟨ sym ⇀-decomp ⟩
  G ⇀ (ε ⇀ ε)                    ≡⟨ ⇀-assoc ⟩
  (G ⇀ ε) ⇀ ε                    ≡⟨ ⇀-identˡ ⟩
  G ⇀ ε                          ≡⟨ ⇀-identˡ ⟩
  G                              ∎
  where open ≡-Reasoning
  
+-absorp : ∀ { A : Set } { G H : Graph A } → G ⇀ H + G + H ≡ G ⇀ H
+-absorp {_} {G} {H} = begin
  G ⇀ H + G + H             ≡⟨ +-congˡ (+-congʳ (sym ⇀-identˡ)) ⟩
  G ⇀ H + G ⇀ ε + H         ≡⟨ +-congʳ (sym ⇀-identˡ) ⟩
  G ⇀ H + G ⇀ ε + H ⇀ ε     ≡⟨ sym +-assoc ⟩
  G ⇀ H + (G ⇀ ε + H ⇀ ε)   ≡⟨ sym ⇀-decomp ⟩
  G ⇀ (H ⇀ ε)               ≡⟨ ⇀-congʳ ⇀-identˡ ⟩
  G ⇀ H                     ∎
  where open ≡-Reasoning
  
⇀-sat : ∀ { A : Set } { G : Graph A } → G ⇀ G ⇀ G ≡ G ⇀ G
⇀-sat {_} {G} = begin
  G ⇀ G ⇀ G                ≡⟨ sym ⇀-assoc ⟩
  G ⇀ (G ⇀ G)              ≡⟨ ⇀-decomp ⟩
  G ⇀ G + (G ⇀ G + G ⇀ G)  ≡⟨ +-congʳ +-idem ⟩
  G ⇀ G + G ⇀ G            ≡⟨ +-idem ⟩
  G ⇀ G                    ∎
  where open ≡-Reasoning
  
≡→≤ : ∀ { A : Set } { G H : Graph A } → G ≡ H → G ≤ H
≡→≤ {_} {G} {H} G≡H = begin
  G  ≡⟨ G≡H ⟩
  H  ∎
  where open ≤-Reasoning

≲-least : ∀ { A : Set } { G : Graph A } → ε ≤ G
≲-least {_} {G} = record { def = begin
  ε + G ≡⟨ +-identityˡ ⟩
  G ∎}
  where open ≡-Reasoning

+-order : ∀ { A : Set } { G H : Graph A } → G ≤ G + H
+-order {_} {G} {H} = record { def = begin
  G + (G + H) ≡⟨ +-assoc ⟩
  G + G + H ≡⟨ +-congˡ +-idem ⟩
  G + H ∎}
  where open ≡-Reasoning

+⇀-order : ∀ { A : Set } { G H : Graph A } → G + H ≤ G ⇀ H
+⇀-order {_} {G} {H} = record { def = begin
  G + H + G ⇀ H ≡⟨ +-congˡ +-sym ⟩
  H + G + G ⇀ H ≡⟨ +-sym ⟩
  G ⇀ H + (H + G) ≡⟨ +-congʳ +-sym ⟩
  G ⇀ H + (G + H) ≡⟨ +-assoc ⟩
  G ⇀ H + G + H ≡⟨ +-absorp ⟩
  G ⇀ H ∎}
  where open ≡-Reasoning

+-mono : ∀ { A : Set } { G H I : Graph A } → G ≤ H → G + I ≤ H + I
+-mono {_} {G} {H} {I} G≤H = record { def = begin
  G + I + (H + I) ≡⟨ +-congˡ +-sym ⟩
  I + G + (H + I) ≡⟨ +-assoc ⟩
  I + G + H + I ≡⟨ +-congˡ (sym +-assoc) ⟩
  I + (G + H) + I ≡⟨ +-congˡ (+-congʳ (_≤_.def G≤H)) ⟩
  I + H + I ≡⟨ +-congˡ +-sym ⟩
  H + I + I ≡⟨ sym +-assoc ⟩
  H + (I + I) ≡⟨ +-congʳ +-idem ⟩
  H + I ∎}
  where open ≡-Reasoning

⇀-monoˡ : ∀ { A : Set } { G H I : Graph A } → G ≤ H → G ⇀ I ≤ H ⇀ I
⇀-monoˡ {_} {G} {H} {I} G≤H = record { def = begin
  G ⇀ I + H ⇀ I ≡⟨ sym +-distrib-⇀ ⟩
  (G + H) ⇀ I ≡⟨ ⇀-congˡ (_≤_.def G≤H) ⟩
  H ⇀ I ∎}
  where open ≡-Reasoning

⇀-monoʳ : ∀ { A : Set } { G H I : Graph A } → G ≤ H → I ⇀ G ≤ I ⇀ H
⇀-monoʳ {_} {G} {H} {I} G≤H = record { def = begin
  I ⇀ G + I ⇀ H ≡⟨ sym ⇀-distrib-+ ⟩
  I ⇀ (G + H) ≡⟨ ⇀-congʳ (_≤_.def G≤H) ⟩
  I ⇀ H ∎}
  where open ≡-Reasoning
