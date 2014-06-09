#lang racket

(require redex)

(define-language λv
  (lam (λ (x ...) e))
  (ae lam x boolean number (o ae ...))
  (o + - * =)
  (ce (ae ae ...) (if ae e e) (call/cc ae) (set! v ae) (letrec ((x ae) ...) e))
  (e ae ce (let ((x e)) e))
  (x variable-not-otherwise-mentioned))

(define-extended-language CESK λv
  (v void number boolean closure (cont κ))
  (e .... v)
  (closure (clo lam ρ))
  (addr v x)
  (state (ς e ρ σ κ))
  (ρ ((x addr) ...))
  (σ ((addr v) ...))
  (κ (letk x e ρ κ)
      halt))

(define red
  (reduction-relation
   CESK
   (--> e
        (ς e () () halt)
        "inject"
        (side-condition (not ((redex-match CESK v) (term e)))))
   (--> (ς v ρ σ halt)
        v
        "exit")
   (--> (ς (ae_1 ae_2 ...) ρ σ κ)
        (applyproc closure v_1 ... σ κ)
        "applyproc"
        (where closure   (A ae_1 ρ σ))
        (where (v_1 ...) (A-n ae_2 ... ρ σ)))
   (--> (ς ae ρ σ κ)
        (applykont κ (A ae ρ σ) σ)
        "applykont"
        (side-condition (not ((redex-match CESK v) (term e)))))
   (--> (ς (if ae e_1 e_2) ρ σ)
        (ς e_1 ρ σ κ)
        "ift"
        (side-condition (term (A ae ρ σ))))
   (--> (ς (if ae e_1 e_2) ρ σ)
        (ς e_1 ρ σ κ)
        "iff"
        (side-condition (not (term (A ae ρ σ)))))
   (--> (ς (let ((x e_1)) e_2) ρ σ κ_1)
        (ς e_1 ρ σ κ_2)
        "let"
        (where κ_2 (letk x e_2 ρ κ)))
   (--> (ς (set! x ae) ρ σ_1 κ)
        (applykont κ void σ_2)
        "set!"
        (where σ_2 (σ-exntend σ ((ρ-lookup ρ x) (A ae ρ σ)))))
   (--> (ς (letrec ((x ae) ...) e) ρ_1 σ_1 κ)
        (ς e ρ_2 σ_2 κ)
        "letrec"
        (where (addr ...) (alloc-n x ...))
        (where ρ_2 (ρ-extend ρ_1 (x addr) ...))
        (where (v ...) (A-n ae ... ρ_2 σ))
        (where σ_2 (σ-extend σ_1 (addr v) ...)))
   (--> (ς (call/cc ae) ρ σ κ)
        (applyproc (A ae ρ σ) (cont κ) σ κ)
        "call/cc")))

(define-metafunction CESK
  A : ae ρ σ -> v
  [(A number ρ σ)     number]
  [(A boolean ρ σ)    boolean]
  [(A lam ρ σ)        (clo lam ρ)]
  [(A x ρ σ)          (ρσ-lookup ρ σ x)]
  [(A (o ae ...) ρ σ) (Oo o (A ae ρ σ) ...)])

(define-metafunction CESK
  A-n : ae ... ρ σ -> (v ...)
  [(A-n ρ σ) ()]
  [(A-n ae_1 ae_2 ... ρ σ)  ((A ae_1 ρ σ) ,@(term (A-n ae_2 ... ρ σ)))])

(define-metafunction CESK
  Oo : o v ... -> v
  [(Oo + number ...) ,(apply + (term (number ...)))]
  [(Oo - number ...) ,(apply - (term (number ...)))]
  [(Oo * number ...) ,(apply * (term (number ...)))]
  [(Oo = number ...) ,(apply = (term (number ...)))])

(define-metafunction CESK
  applyproc : closure v ... σ κ -> state
  [(applyproc (clo (λ (x ..._1) e) ρ_1) v ..._1 σ_1 κ) (ς e ρ_2 σ_2 κ)
   (where (addr ...) (alloc-n x ...))
   (where ρ_2  (ρ-extend ρ_1 (x addr) ...))
   (where σ_2  (σ-extend σ_1 (addr v) ...))])

(define-metafunction CESK
  applykont : κ v σ -> state
  [(applykont (letk x e ρ_1 κ) v σ_1) (ς e ρ_2 σ_2 κ)
   (where addr (alloc x))
   (where ρ_2  (ρ-extend ρ_1 (x addr)))
   (where σ_2  (σ-extend σ_1 (addr v)))]
  [(applykont halt v σ) (ς v () () halt)])

(define-metafunction CESK
  [(in-ρ ρ x) ,(not (equal? #f (assq (term x) (term ρ))))])

(define-metafunction CESK
  ρ-lookup : ρ x -> addr
  [(ρ-lookup ρ x) ,(second (assq (term x) (term ρ)))])

(define-metafunction CESK
  ρ-extend : ρ (x addr) ... -> ρ
  [(ρ-extend ρ) ρ]
  [(ρ-extend ρ (x addr)) ,(cons (term (x addr)) (term ρ))]
  [(ρ-extend ρ (x_1 addr_1) (x_2 addr_2) ...)
   (ρ-extend (ρ-extend ρ (x_1 addr_1)) (x_2 addr_2) ...)])

(define-metafunction CESK
  σ-lookup : σ addr -> v
  [(σ-lookup σ addr) ,(second (assq (term addr) (term σ)))])

(define-metafunction CESK
  σ-extend : σ (addr v) ... -> σ
  [(σ-extend σ) σ]
  [(σ-extend σ (addr v)) ,(cons (term (addr v)) (term σ))]
  [(σ-extend σ (addr_1 v_1) (addr_2 v_2) ...)
   (σ-extend (σ-extend σ (addr_1 v_1)) (addr_2 v_2) ...)])

(define-metafunction CESK
  ρσ-lookup : ρ σ x -> v
  [(ρσ-lookup ρ σ x) (σ-lookup σ (ρ-lookup ρ x))])

(define-metafunction CESK
  alloc : x -> addr
  [(alloc x) x])

(define-metafunction CESK
  alloc-n : x ... -> (addr ...)
  [(alloc-n) ()]
  [(alloc-n x_1 x_2 ...) ,(cons (term (alloc x_1)) (term (alloc-n x_2 ...)))])
