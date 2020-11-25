open import Graph.Base

module Graph.Reasoning where


  module ≡-Reasoning where

    infix 1 begin_
    infixr 2 _≡⟨⟩_ _≡⟨_⟩_
    infix 3 _∎

    begin_ : ∀ { A : Set } { G H : Graph A } → G ≡ H → G ≡ H
    begin G≡H = G≡H

    _≡⟨⟩_ : ∀ { A : Set } (G : Graph A) { H : Graph A } → G ≡ H → G ≡ H
    G ≡⟨⟩ G≡H = G≡H

    _≡⟨_⟩_ : ∀ { A : Set } (G : Graph A) { H I : Graph A } → G ≡ H → H ≡ I → G ≡ I
    G ≡⟨ G≡H ⟩ H≡I = trans G≡H H≡I

    _∎ : ∀ { A : Set } (G : Graph A) → G ≡ G
    G ∎ = refl


  module ≤-Reasoning where

    infix 1 begin_
    infixr 2 _≡⟨⟩_ _≡⟨_⟩_ _≤⟨⟩_ _≤⟨_⟩_
    infix 3 _∎

    begin_ : ∀ { A : Set } { G H : Graph A } → G ≤ H → G ≤ H
    begin G≤H = G≤H

    _≡⟨⟩_ : ∀ { A : Set } (G : Graph A) { H : Graph A } → G ≤ H → G ≤ H
    G ≡⟨⟩ G≤H = G≤H
  
    _≡⟨_⟩_ : ∀ { A : Set } (G : Graph A) { H I : Graph A } → G ≡ H → H ≤ I → G ≤ I
    G ≡⟨ G≡H ⟩ H≤I = ≤-trans (≡-to-≤ G≡H) H≤I

    _≤⟨⟩_ : ∀ { A : Set } (G : Graph A) { H : Graph A } → G ≤ H → G ≤ H
    G ≤⟨⟩ G≤H = G≤H

    _≤⟨_⟩_ : ∀ { A : Set } (G : Graph A) { H I : Graph A } → G ≤ H → H ≤ I → G ≤ I
    G ≤⟨ G≤H ⟩ H≤I = ≤-trans G≤H H≤I

    _∎ : ∀ { A : Set } (G : Graph A) → G ≤ G
    G ∎ = ≤-refl
