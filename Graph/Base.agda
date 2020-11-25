module Graph.Base where

infixl 4 _≡_
infixl 4 _≤_
infixl 8 _+_
infixl 9 _⇀_

data Graph (A : Set) : Set where
  ε : Graph A
  Vertex : A → Graph A
  _+_ : Graph A → Graph A → Graph A
  _⇀_ : Graph A → Graph A → Graph A

-- vertex axioms
data _∈ᵥ_ { A : Set } : A → Graph A → Set where
  x∈Vx : ∀ { x : A } → x ∈ᵥ Vertex x
  +ₗ : ∀ { x : A } { G H : Graph A } → x ∈ᵥ G → x ∈ᵥ (G + H)
  +ᵣ : ∀ { x : A } { G H : Graph A } → x ∈ᵥ H → x ∈ᵥ (G + H)
  ⇀ₗ : ∀ { x : A } { G H : Graph A } → x ∈ᵥ G → x ∈ᵥ (G ⇀ H)
  ⇀ᵣ : ∀ { x : A } { G H : Graph A } → x ∈ᵥ H → x ∈ᵥ (G ⇀ H)

-- edge axioms
data ⟦_,_⟧∈ₑ_ { A : Set } : A → A → Graph A → Set where
  +ₗ : ∀ { x y : A } { G H : Graph A } → ⟦ x , y ⟧∈ₑ G → ⟦ x , y ⟧∈ₑ (G + H)
  +ᵣ : ∀ { x y : A } { G H : Graph A } → ⟦ x , y ⟧∈ₑ H → ⟦ x , y ⟧∈ₑ (G + H)
  ⇀ₗ : ∀ { x y : A } { G H : Graph A } → ⟦ x , y ⟧∈ₑ G → ⟦ x , y ⟧∈ₑ (G ⇀ H)
  ⇀ᵣ : ∀ { x y : A } { G H : Graph A } → ⟦ x , y ⟧∈ₑ H → ⟦ x , y ⟧∈ₑ (G ⇀ H)
  ⇀ₗᵣ : ∀ { x y : A } { G H : Graph A } → x ∈ᵥ G → y ∈ᵥ H → ⟦ x , y ⟧∈ₑ (G ⇀ H)

-- equality axioms
record _≡_ { A : Set } ( G H : Graph A ) : Set where
  field
    vₗ : ∀ { x : A } → x ∈ᵥ G → x ∈ᵥ H
    vᵣ : ∀ { x : A } → x ∈ᵥ H → x ∈ᵥ G
    eₗ : ∀ { x y : A } → ⟦ x , y ⟧∈ₑ G → ⟦ x , y ⟧∈ₑ H
    eᵣ : ∀ { x y : A } → ⟦ x , y ⟧∈ₑ H → ⟦ x , y ⟧∈ₑ G

record _≤_ { A : Set} ( G H : Graph A ) : Set where
  field
    def : G + H ≡ H

refl : ∀ { A : Set } { G : Graph A } → G ≡ G
refl = record
         { vₗ = λ z → z ; vᵣ = λ z → z ; eₗ = λ z → z ; eᵣ = λ z → z }

sym : ∀ { A : Set } { G H : Graph A } → G ≡ H → H ≡ G
sym G≡H = record
            { vₗ = _≡_.vᵣ G≡H
            ; vᵣ = _≡_.vₗ G≡H
            ; eₗ = _≡_.eᵣ G≡H
            ; eᵣ = _≡_.eₗ G≡H
            }

trans : ∀ { A : Set } { G H I : Graph A } → G ≡ H → H ≡ I → G ≡ I
trans G≡H H≡I = record
                  { vₗ = λ z → _≡_.vₗ H≡I (_≡_.vₗ G≡H z)
                  ; vᵣ = λ z → _≡_.vᵣ G≡H (_≡_.vᵣ H≡I z)
                  ; eₗ = λ z → _≡_.eₗ H≡I (_≡_.eₗ G≡H z)
                  ; eᵣ = λ z → _≡_.eᵣ G≡H (_≡_.eᵣ H≡I z)
                  }

≡-to-≤ : ∀ { A : Set } { G H : Graph A } → G ≡ H → G ≤ H
≡-to-≤ G≡H = record
               { def = record
                         { vₗ = λ { (+ₗ x) → _≡_.vₗ G≡H x ; (+ᵣ x) → x }
                         ; vᵣ = λ z → +ₗ (_≡_.vᵣ G≡H z)
                         ; eₗ = λ { (+ₗ x) → _≡_.eₗ G≡H x ; (+ᵣ x) → x }
                         ; eᵣ = λ z → +ₗ (_≡_.eᵣ G≡H z)
                         }
               }

≤-refl : ∀ { A : Set } { G : Graph A } → G ≤ G
≤-refl = record
           { def = record
                     { vₗ = λ { (+ₗ x) → x ; (+ᵣ x) → x }
                     ; vᵣ = +ₗ
                     ; eₗ = λ { (+ₗ x) → x ; (+ᵣ x) → x }
                     ; eᵣ = +ₗ
                     }
           }

≤-trans : ∀ { A : Set } { G H I : Graph A } → G ≤ H → H ≤ I → G ≤ I
≤-trans G≤H H≤I = record
                    { def = record
                              { vₗ = λ { (+ₗ x) → _≡_.vₗ (_≤_.def H≤I) (+ₗ (_≡_.vₗ (_≤_.def G≤H) (+ₗ x))) ; (+ᵣ x) → x }
                              ; vᵣ = +ᵣ
                              ; eₗ = λ { (+ₗ x) → _≡_.eₗ (_≤_.def H≤I) (+ₗ (_≡_.eₗ (_≤_.def G≤H) (+ₗ x))) ; (+ᵣ x) → x }
                              ; eᵣ = +ᵣ
                              }
                    }
