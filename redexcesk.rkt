#lang racket

(require redex
         pict)

; Ignore for the moment
(provide red^
         red^-pic
         red~-pic
         red~
         (rename-out [red red**]))

(define-language λv
  (lam (λ (x ...) e))
  (ae lam x boolean number (o ae ...))
  (o + - * =)
  (ce (ae ae ...) (if ae e e) (call/cc ae) (set! x ae) (letrec ((x ae) ...) e))
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

(define-extended-language CESK^ CESK
  (e .... v^)
  (closure^ (clo^ lam ρ^))
  (tmp (proc^ (closure^ v^ ... σ^ κ^) ...)
       (state^ ...))
  (v^ v (cont κ^) closure^)
  (addr^ addr)
  (state^ (ς^ e ρ^ σ^ κ^))
  (ρ^ ((x addr^) ...))
  (σ^ ((addr^ (v^ ...)) ...))
  (κ^ (letk x e ρ^ addr^)
      halt))

(define-extended-language CESK~ CESK^
  (e .... v~)
  (closure~ (clo~ lam ρ~))
  (tmp .... (proc~ (closure v~ ... σ~ κ~) ...)
       (state~ ...))
  (v~ v^ (cont κ~) closure~)
  (addr~ addr^)
  (state~ (ς~ e ρ~ σ~ κ~))
  (ρ~ ((x addr~) ...))
  (σ~ ((addr~ (v~ ...)) ...))
  (κ~ (letk x e ρ~ addr~)
      halt))

(define red
  (reduction-relation
   CESK
   (--> e
        (ς e () () halt)
        "inject"
        (side-condition/hidden (not ((redex-match CESK v) (term e)))))
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
        (side-condition/hidden (or (not ((redex-match CESK v) (term ae)))
                                   (not (equal? (term κ) (term halt))))))
   (--> (ς (if ae e_1 e_2) ρ σ κ)
        (ς e_1 ρ σ κ)
        "ift"
        (side-condition (term (A ae ρ σ))))
   (--> (ς (if ae e_1 e_2) ρ σ κ)
        (ς e_2 ρ σ κ)
        "iff"
        (side-condition (term (negate (A ae ρ σ)))))
   (--> (ς (let ((x  e_1)) e_2) ρ σ κ_1)
        (ς e_1 ρ σ κ_2)
        "let"
        (where κ_2 (letk x e_2 ρ κ_1)))
   (--> (ς (set! x ae) ρ σ_1 κ)
        (applykont κ void σ_2)
        "set!"
        (where σ_2 (σ-extend σ_1 ((ρ-lookup ρ x) (A ae ρ σ_1)))))
   (--> (ς (letrec ((x ae) ...) e) ρ_1 σ_1 κ)
        (ς e ρ_2 σ_2 κ)
        "letrec"
        (where (addr ...) (alloc-n σ_1 x ...))
        (where ρ_2 (ρ-extend ρ_1 (x addr) ...))
        (where (v ...) (A-n ae ... ρ_2 σ_1))
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
   (where (addr ...) (alloc-n σ_1 x ...))
   (where ρ_2  (ρ-extend ρ_1 (x addr) ...))
   (where σ_2  (σ-extend σ_1 (addr v) ...))])

(define-metafunction CESK
  applykont : κ v σ -> state
  [(applykont (letk x e ρ_1 κ) v σ_1) (ς e ρ_2 σ_2 κ)
   (where addr (alloc σ_1 x))
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
  [(ρ-extend ((x_1 addr_1) ... (x_3 addr_3) (x_2 addr_2) ...) (x_3 addr_4))
   ((x_1 addr_1) ... (x_3 addr_4) (x_2 addr_2) ...)]
  [(ρ-extend ρ (x addr)) ,(cons (term (x addr)) (term ρ))]
  [(ρ-extend ρ (x_1 addr_1) (x_2 addr_2) ...)
   (ρ-extend (ρ-extend ρ (x_1 addr_1)) (x_2 addr_2) ...)])

(define-metafunction CESK
  σ-lookup : σ addr -> v
  [(σ-lookup σ addr) ,(second (assq (term addr) (term σ)))])

(define-metafunction CESK
  σ-extend : σ (addr v) ... -> σ
  [(σ-extend σ) σ]
  [(σ-extend ((addr_1 v_1) ... (addr_3 v_3) (addr_2 v_2) ...) (addr_3 v_4))
   ((addr_1 v_1) ... (addr_3 v_4) (addr_2 v_2) ...)]
  [(σ-extend σ (addr v)) ,(cons (term (addr v)) (term σ))]
  [(σ-extend σ (addr_1 v_1) (addr_2 v_2) ...)
   (σ-extend (σ-extend σ (addr_1 v_1)) (addr_2 v_2) ...)])

(define-metafunction CESK
  ρσ-lookup : ρ σ x -> v
  [(ρσ-lookup ρ σ x) (σ-lookup σ (ρ-lookup ρ x))])

(define-metafunction CESK
  alloc : σ x -> addr
  [(alloc σ x) ,(variable-not-in (term σ) (term x))])

(define-metafunction CESK
  alloc-n : σ x ... -> (addr ...)
  [(alloc-n σ) ()]
  [(alloc-n σ x_1 x_2 ...) ,(cons (term (alloc σ x_1)) (term (alloc-n σ x_2 ...)))])

(define-metafunction CESK
  [(negate #f) #t]
  [(negate v) #f])

;; CESK^

(define red^
  (reduction-relation
   CESK^
   (--> e
        (ς^ e () () halt)
        "inject"
        (side-condition/hidden (not ((redex-match CESK^ v^) (term e)))))
   (--> (ς^ v^ ρ^ σ^ halt)
        v^
        "exit")
   (--> (ς^ (ae_1 ae_2 ...) ρ^ σ^ κ^)
        (proc^ (v^_2 ... σ^ κ^) ...)
        "applyproc"
        (where (v^_3 ...)       (A^ ae_1 ρ^ σ^))
        (where (closure^ ...)   (closure^-filter v^_3 ...))
        (where ((v^_1 ...) ...) (A^-n ae_2 ... ρ^ σ^))
        (where ((v^_2 ...) ...) (cv-match (closure^ ...) (v^_1 ...) ...)))
   (--> (proc^ (closure^_1 v^_1 ... σ^_1 κ^_1) ...
               (closure^_2 v^_2 ... σ^_2 κ^_2)
               (closure^_3 v^_3 ... σ^_3 κ^_3) ...)
        (applyproc^ closure^_2 v^_2 ... σ^_2 κ^_2)
        "applyproc*")
   (--> (ς^ ae ρ^ σ^ κ^_1)
        (applykont^ κ^_1 (A^ ae ρ^ σ^) σ^)
        "applykont"
        (side-condition/hidden (or (not ((redex-match CESK^ v^) (term ae)))
                                   (not (equal? (term κ^_1) (term halt))))))
   (--> (state^_1 ... state^_2 state^_3 ...)
        state^_2
        "applykont*")
   (--> (ς^ (if ae e_1 e_2) ρ^ σ^ κ^)
        (ς^ e_1 ρ^ σ^ κ^)
        "ift"
        (side-condition (term (has-t (A^ ae ρ^ σ^)))))
   (--> (ς^ (if ae e_1 e_2) ρ^ σ^ κ^)
        (ς^ e_2 ρ^ σ^ κ^)
        "iff"
        (side-condition (term (has-f (A^ ae ρ^ σ^)))))
   (--> (ς^ (let ((x  e_1)) e_2) ρ^ σ^_1 κ^_1)
        (ς^ e_1 ρ^ σ^_2 κ^_2)
        "let"
        (where addr^ (alloc^ σ^_1 x))
        (where σ^_2  (σ^-extend σ^_1 (addr^ (cont κ^_1))))
        (where κ^_2  (letk x e_2 ρ^ addr^)))
   (--> (ς^ (set! x ae) ρ^ σ^_1 κ^)
        (applykont^ κ^ (void) σ^_2)
        "set!"
        (where (v^ ...) (A^ ae ρ^ σ^_1))
        (where σ^_2 (σ^-extend σ^_1 ((ρ^-lookup ρ^ x) v^) ...)))
   (--> (ς^ (letrec ((x ae) ...) e) ρ^_1 σ^_1 κ^)
        (ς^ e ρ^_2 σ^_2 κ^)
        "letrec"
        (where (addr^ ...) (alloc^-n σ^_1 x ...))
        (where ρ^_2 (ρ-extend ρ^_1 (x addr^) ...))
        (where ((v^ ...) ...) (A^-n ae ... ρ^_2 σ^_1))
        (where σ^_2 (σ^-extend σ^_1 (addr^ v^) ... ...)))
   (--> (ς^ (call/cc ae) ρ^ σ^ κ^)
        (applyproc^ (A^ ae ρ^ σ^) (cont κ^) σ^ κ^)
        "call/cc")))

(define-metafunction CESK^
  cv-match : (closure^ ...) (v^ ...) ... -> ((v^ ...) ...)
  [(cv-match () (v^ ...) ...) ()]
  {(cv-match (closure^ ...) (v^_1 ...) ... () (v^_2 ...) ...) ()}
  [(cv-match (closure^) (v^) ...) ((closure^ ,@(term (v^ ...))))]
  [(cv-match (closure^) (v^_1) ... (v^_2 v^_3 v^_4 ...) (v^_5 ...) ...)
   (,@(term (cv-match (closure^) (v^_1) ... (v^_2) (v^_5 ...) ...))
    ,@(term (cv-match (closure^) (v^_1) ... (v^_3 v^_4 ...) (v^_5 ...) ...)))]
  [(cv-match (closure^_1 closure^_2 closure^_3 ...) (v^ ...) ...)
   (,@(term (cv-match (closure^_1) (v^ ...) ...))
    ,@(term (cv-match (closure^_2 closure^_3 ...) (v^ ...) ...)))])

(define-metafunction CESK^
  A^ : ae ρ^ σ^ -> (v^ ...)
  [(A^ ρ^ σ^)               ()]
  [(A^ number ρ^ σ^)        (number)]
  [(A^ boolean ρ^ σ^)       (boolean)]
  [(A^ lam ρ^ σ^)           ((clo^ lam ρ^))]
  [(A^ x ρ^ σ^)             (ρσ^-lookup ρ^ σ^ x)]
  [(A^ (o ae ...) ρ^ σ^)    (Oo^ o (A^ ae ρ^ σ^) ...)])

(define-metafunction CESK^
  A^-n : ae ... ρ^ σ^ -> ((v^ ...) ...)
  [(A^-n ρ^ σ^)                ()]
  [(A^-n ae_1 ae_2 ... ρ^ σ^) ((A^ ae_1 ρ^ σ^) ,@(term (A^-n ae_2 ... ρ^ σ^)))])

(define-metafunction CESK^
  Oo^ : o (v^ ...) ... -> (v^ ...)
  [(Oo^ o (number) ... () (v^_3 ...) ...) ()]
  [(Oo^ o (number) ... (v^_1 v^_2 v^_3 ...) (v^_4 ...) ...)
   (,@(term (Oo^ o (number) ... (v^_1) (v^_4 ...) ...))
    ,@(term (Oo^ o (number) ... (v^_2 v^_3 ...) (v^_4 ...) ...)))]
  [(Oo^ + (number) ...) (,(apply + (term (number ...))))]
  [(Oo^ - (number) ...) (,(apply - (term (number ...))))]
  [(Oo^ * (number) ...) (,(apply * (term (number ...))))]
  [(Oo^ = (number) ...) (,(apply = (term (number ...))))]
  [(Oo^ o (v^ ...) ...) ()])

(define-metafunction CESK^
  [(has-t ()) #f]
  [(has-t (v^_1 v^_2 ...)) ,(or (term v^_1) (term (has-t (v^_2 ...))))])

(define-metafunction CESK^
  [(has-f ()) #f]
  [(has-f (v^_1 v^_2 ...)) ,(or (not (term v^_1)) (term (has-f (v^_2 ...))))])

(define-metafunction CESK^
  applyproc^ : closure^ v^ ... σ^ κ^ -> state^
  [(applyproc^ (clo^ (λ (x ..._1) e) ρ^_1) v^ ..._1 σ^_1 κ^) (ς^ e ρ^_2 σ^_2 κ^)
   (where (addr^ ...) (alloc^-n σ^_1 x ...))
   (where ρ^_2        (ρ^-extend ρ^_1 (x addr^) ...))
   (where σ^_2        (σ^-extend σ^_1 (addr^ v^) ...))])

(define-metafunction CESK^
  applykont^ : κ^ (v^ ...) σ^ -> (state^ ...)
  [(applykont^ κ^ () σ^) ()]
  [(applykont^ κ^ (v^_1 v^_2 v^_3 ...) σ^)
   (,@(term (applykont^ κ^ (v^_1) σ^))
    ,@(term (applykont^ κ^ (v^_2 v^_3 ...) σ^)))]
  [(applykont^ (letk x e ρ^_1 addr) (v^) σ^_1) ((ς^ e ρ^_2 σ^_2 κ^) ...)
   (where (v^_4 ...) (σ^-lookup σ^_1 addr))
   (where (κ^ ...)   (κ^-filter v^_4 ...))
   (where addr^      (alloc^ σ^_1 x))
   (where ρ^_2       (ρ^-extend ρ^_1 (x addr^)))
   (where σ^_2       (σ^-extend σ^_1 (addr^ v^)))]
  [(applykont^ halt (v^) σ^) ((ς^ v^ () () halt))])

(define-metafunction CESK^
  κ^-unfilter : v^ ... -> (v^ ...)
  [(κ^-unfilter)                  ()]
  [(κ^-unfilter (cont κ^) v^ ...) (κ^-unfilter v^ ...)]
  [(κ^-unfilter v^_1 v^_2 ...)    (v^_1 ,@(term (κ^-unfilter v^_2 ...)))])

(define-metafunction CESK^
  κ^-filter : v^ ... -> (κ^ ...)
  [(κ^-filter)                  ()]
  [(κ^-filter (cont κ^) v^ ...) (κ^ ,@(term (κ^-filter v^ ...)))]
  [(κ^-filter v^_1 v^_2 ...)    (κ^-filter v^_2 ...)])

(define-metafunction CESK^
  closure^-filter : v^ ... -> (closure^ ...)
  [(closure^-filter)                 ()]
  [(closure^-filter closure^ v^ ...) (closure^ ,@(term (closure^-filter v^ ...)))]
  [(closure^-filter v^_1 v^_2 ...)   (closure^-filter v^_2 ...)])

(define-metafunction CESK^
  ρ^-lookup : ρ^ x -> addr^
  [(ρ^-lookup ρ^ x) ,(second (assq (term x) (term ρ^)))])

(define-metafunction CESK^
  ρ^-extend : ρ^ (x addr^) ... -> ρ^
  [(ρ^-extend ρ^) ρ^]
  [(ρ^-extend ((x_1 addr^_1) ... (x_3 addr^_3) (x_2 addr^_2) ...) (x_3 addr^_4))
   ((x_1 addr^_1) ... (x_3 addr^_4) (x_2 addr^_2) ...)]
  [(ρ^-extend ρ^ (x addr^)) ,(cons (term (x addr^)) (term ρ^))]
  [(ρ^-extend ρ^ (x_1 addr^_1) (x_2 addr^_2) ...)
   (ρ^-extend (ρ^-extend ρ^ (x_1 addr^_1)) (x_2 addr^_2) ...)])

(define-metafunction CESK^
  σ^-lookup : σ^ addr^ -> (v^ ...)
  [(σ^-lookup σ^ addr^) ,(second (assq (term addr^) (term σ^)))])

(define-metafunction CESK^
  σ^-extend : σ^ (addr^ v^) ... -> σ^
  [(σ^-extend σ^) σ^]
  [(σ^-extend ((addr^_1 (v^_1 ...)) ... (addr^_3 (v^_3 ... v^_4 v^_5 ...)) (addr^_2 (v^_2 ...)) ...)
              (addr^_3 v^_4))
   ((addr^_1 (v^_1 ...)) ... (addr^_3 (v^_3 ... v^_4 v^_5 ...)) (addr^_2 (v^_2 ...)) ...)]
  [(σ^-extend ((addr^_1 (v^_1 ...)) ... (addr^_3 (v^_3 ...)) (addr^_2 (v^_2 ...)) ...) (addr^_3 v^_4))
   ((addr^_1 (v^_1 ...)) ... (addr^_3 ,(cons (term v^_4) (term (v^_3 ...)))) (addr^_2 (v^_2 ...)) ...)]
  [(σ^-extend σ^ (addr^ v^)) ,(cons (term (addr^ (v^))) (term σ^))]
  [(σ^-extend σ^ (addr^_1 v_1) (addr^_2 v_2) ...)
   (σ^-extend (σ^-extend σ^ (addr^_1 v_1)) (addr^_2 v_2) ...)])

(define-metafunction CESK^
  ρσ^-lookup : ρ^ σ^ x -> (v^ ...)
  [(ρσ^-lookup ρ^ σ^ x) (σ^-lookup σ^ (ρ^-lookup ρ^ x))])

(define-metafunction CESK^
  alloc^ : σ^ x -> addr^
  [(alloc^ σ^ x) x])
  ;[(alloc^ σ^ x) 0])

(define-metafunction CESK^
  alloc^-n : σ^ x ... -> (addr^ ...)
  [(alloc^-n σ^) ()]
  [(alloc^-n σ^ x_1 x_2 ...) ,(cons (term (alloc^ σ^ x_1)) (term (alloc^-n σ^ x_2 ...)))])

;; CESK~

(define red~
  (reduction-relation
   CESK~
   (--> e
        (ς~ e () () halt)
        "inject"
        (side-condition/hidden (not ((redex-match CESK~ v~) (term e)))))
   (--> (ς~ v~ ρ~ σ~ halt)
        v~
        "exit")
   (--> (ς~ (ae_1 ae_2 ...) ρ~ σ~ κ~)
        (proc~ (v~_2 ... σ~ κ~) ...)
        "applyproc"
        (where (v~_3 ...)       (A~ ae_1 ρ~ σ~))
        (where (closure~ ...)   (closure~-filter v~_3 ...))
        (where ((v~_1 ...) ...) (A~-n ae_2 ... ρ~ σ~))
        (where ((v~_2 ...) ...) (cv-match~ (closure~ ...) (v~_1 ...) ...)))
   (--> (proc~ (closure~_1 v~_1 ... σ~_1 κ~_1) ...
               (closure~_2 v~_2 ... σ~_2 κ~_2)
               (closure~_3 v~_3 ... σ~_3 κ~_3) ...)
        (applyproc~ closure~_2 v~_2 ... σ~_2 κ~_2)
        "applyproc*")
   (--> (ς~ ae ρ~ σ~ κ~_1)
        (applykont~ κ~_1 (A~ ae ρ~ σ~) σ~)
        "applykont"
        (side-condition/hidden (or (not ((redex-match CESK~ v~) (term ae)))
                                   (not (equal? (term κ~_1) (term halt))))))
   (--> (state~_1 ... state~_2 state~_3 ...)
        state~_2
        "applykont*")
   (--> (ς~ (if ae e_1 e_2) ρ~ σ~ κ~)
        (ς~ e_1 ρ~ σ~ κ~)
        "ift"
        (side-condition (term (has-t (A~ ae ρ~ σ~)))))
   (--> (ς~ (if ae e_1 e_2) ρ~ σ~ κ~)
        (ς~ e_2 ρ~ σ~ κ~)
        "iff"
        (side-condition (term (has-f (A~ ae ρ~ σ~)))))
   (--> (ς~ (let ((x  e_1)) e_2) ρ~ σ~_1 κ~_1)
        (ς~ e_1 ρ~ σ~_2 κ~_2)
        "let"
        (where addr~ (alloc~ σ~_1 x))
        (where σ~_2  (σ~-extend σ~_1 (addr~ (cont κ~_1))))
        (where κ~_2  (letk x e_2 ρ~ addr~)))
   (--> (ς~ (set! x ae) ρ~ σ~_1 κ~)
        (applykont~ κ~ (void) σ~_2)
        "set!"
        (where (v~ ...) (A~ ae ρ~ σ~_1))
        (where σ~_2 (σ~-extend σ~_1 ((ρ~-lookup ρ~ x) v~) ...)))
   (--> (ς~ (letrec ((x ae) ...) e) ρ~_1 σ~_1 κ~)
        (ς~ e ρ~_2 σ~_2 κ~)
        "letrec"
        (where (addr~ ...) (alloc~-n σ~_1 x ...))
        (where ρ~_2 (ρ-extend ρ~_1 (x addr~) ...))
        (where ((v~ ...) ...) (A~-n ae ... ρ~_2 σ~_1))
        (where σ~_2 (σ~-extend σ~_1 (addr~ v~) ... ...)))
   (--> (ς~ (call/cc ae) ρ~ σ~ κ~)
        (applyproc~ (A~ ae ρ~ σ~) (cont κ~) σ~ κ~)
        "call/cc")))

(define-metafunction CESK~
  cv-match~ : (closure~ ...) (v~ ...) ... -> ((v~ ...) ...)
  [(cv-match~ () (v~ ...) ...) ()]
  {(cv-match~ (closure~ ...) (v~_1 ...) ... () (v~_2 ...) ...) ()}
  [(cv-match~ (closure~) (v~) ...) ((closure~ ,@(term (v~ ...))))]
  [(cv-match~ (closure~) (v~_1) ... (v~_2 v~_3 v~_4 ...) (v~_5 ...) ...)
   (,@(term (cv-match~ (closure~) (v~_1) ... (v~_2) (v~_5 ...) ...))
    ,@(term (cv-match~ (closure~) (v~_1) ... (v~_3 v~_4 ...) (v~_5 ...) ...)))]
  [(cv-match~ (closure~_1 closure~_2 closure~_3 ...) (v~ ...) ...)
   (,@(term (cv-match~ (closure~_1) (v~ ...) ...))
    ,@(term (cv-match~ (closure~_2 closure~_3 ...) (v~ ...) ...)))])

(define-metafunction CESK~
  A~ : ae ρ~ σ~ -> (v~ ...)
  [(A~ ρ~ σ~)               ()]
  [(A~ number ρ~ σ~)        (number)]
  [(A~ boolean ρ~ σ~)       (boolean)]
  [(A~ lam ρ~ σ~)           ((clo~ lam ρ~))]
  [(A~ x ρ~ σ~)             (ρσ~-lookup ρ~ σ~ x)]
  [(A~ (o ae ...) ρ~ σ~)    (Oo~ o (A~ ae ρ~ σ~) ...)])

(define-metafunction CESK~
  A~-n : ae ... ρ~ σ~ -> ((v~ ...) ...)
  [(A~-n ρ~ σ~)                ()]
  [(A~-n ae_1 ae_2 ... ρ~ σ~) ((A~ ae_1 ρ~ σ~) ,@(term (A~-n ae_2 ... ρ~ σ~)))])

(define-metafunction CESK~
  Oo~ : o (v~ ...) ... -> (v~ ...)
  [(Oo~ o (number) ... () (v~_3 ...) ...) ()]
  [(Oo~ o (number) ... (v~_1 v~_2 v~_3 ...) (v~_4 ...) ...)
   (,@(term (Oo~ o (number) ... (v~_1) (v~_4 ...) ...))
    ,@(term (Oo~ o (number) ... (v~_2 v~_3 ...) (v~_4 ...) ...)))]
  [(Oo~ + (number) ...) (,(apply + (term (number ...))))]
  [(Oo~ - (number) ...) (,(apply - (term (number ...))))]
  [(Oo~ * (number) ...) (,(apply * (term (number ...))))]
  [(Oo~ = (number) ...) (,(apply = (term (number ...))))]
  [(Oo~ o (v~ ...) ...) ()])

(define-metafunction CESK~
  [(has-t~ ()) #f]
  [(has-t~ (v~_1 v~_2 ...)) ,(or (term v~_1) (term (has-t (v~_2 ...))))])

(define-metafunction CESK~
  [(has-f~ ()) #f]
  [(has-f~ (v~_1 v~_2 ...)) ,(or (not (term v~_1)) (term (has-f (v~_2 ...))))])

(define-metafunction CESK~
  applyproc~ : closure~ v~ ... σ~ κ~ -> state~
  [(applyproc~ (clo~ (λ (x ..._1) e) ρ~_1) v~ ..._1 σ~_1 κ~) (ς~ e ρ~_2 σ~_2 κ~)
   (where (addr~ ...) (alloc~-n σ~_1 x ...))
   (where ρ~_2        (ρ~-extend ρ~_1 (x addr~) ...))
   (where σ~_2        (σ~-extend σ~_1 (addr~ v~) ...))])

(define-metafunction CESK~
  applykont~ : κ~ (v~ ...) σ~ -> (state~ ...)
  [(applykont~ κ~ () σ~) ()]
  [(applykont~ κ~ (v~_1 v~_2 v~_3 ...) σ~)
   (,@(term (applykont~ κ~ (v~_1) σ~))
    ,@(term (applykont~ κ~ (v~_2 v~_3 ...) σ~)))]
  [(applykont~ (letk x e ρ~_1 addr) (v~) σ~_1) ((ς~ e ρ~_2 σ~_2 κ~) ...)
   (where (v~_4 ...) (σ~-lookup σ~_1 addr))
   (where (κ~ ...)   (κ~-filter v~_4 ...))
   (where addr~      (alloc~ σ~_1 x))
   (where ρ~_2       (ρ~-extend ρ~_1 (x addr~)))
   (where σ~_2       (σ~-extend σ~_1 (addr~ v~)))]
  [(applykont~ halt (v~) σ~) ((ς~ v~ () () halt))])

(define-metafunction CESK~
  κ~-unfilter : v~ ... -> (v~ ...)
  [(κ~-unfilter)                  ()]
  [(κ~-unfilter (cont κ~) v~ ...) (κ~-unfilter v~ ...)]
  [(κ~-unfilter v~_1 v~_2 ...)    (v~_1 ,@(term (κ~-unfilter v~_2 ...)))])

(define-metafunction CESK~
  κ~-filter : v~ ... -> (κ~ ...)
  [(κ~-filter)                  ()]
  [(κ~-filter (cont κ~) v~ ...) (κ~ ,@(term (κ~-filter v~ ...)))]
  [(κ~-filter v~_1 v~_2 ...)    (κ~-filter v~_2 ...)])

(define-metafunction CESK~
  closure~-filter : v~ ... -> (closure~ ...)
  [(closure~-filter)                 ()]
  [(closure~-filter closure~ v~ ...) (closure~ ,@(term (closure~-filter v~ ...)))]
  [(closure~-filter v~_1 v~_2 ...)   (closure~-filter v~_2 ...)])

(define-metafunction CESK~
  ρ~-lookup : ρ~ x -> addr~
  [(ρ~-lookup ρ~ x) ,(second (assq (term x) (term ρ~)))])

(define-metafunction CESK~
  ρ~-extend : ρ~ (x addr~) ... -> ρ~
  [(ρ~-extend ρ~) ρ~]
  [(ρ~-extend ((x_1 addr~_1) ... (x_3 addr~_3) (x_2 addr~_2) ...) (x_3 addr~_4))
   ((x_1 addr~_1) ... (x_3 addr~_4) (x_2 addr~_2) ...)]
  [(ρ~-extend ρ~ (x addr~)) ,(cons (term (x addr~)) (term ρ~))]
  [(ρ~-extend ρ~ (x_1 addr~_1) (x_2 addr~_2) ...)
   (ρ~-extend (ρ~-extend ρ~ (x_1 addr~_1)) (x_2 addr~_2) ...)])

(define-metafunction CESK~
  σ~-lookup : σ~ addr~ -> (v~ ...)
  [(σ~-lookup σ~ addr~) ,(second (assq (term addr~) (term σ~)))])

(define-metafunction CESK~
  σ~-extend : σ~ (addr~ v~) ... -> σ~
  [(σ~-extend σ~) σ~]
  [(σ~-extend ((addr~_1 (v~_1 ...)) ... (addr~_3 (v~_3 ... v~_4 v~_5 ...)) (addr~_2 (v~_2 ...)) ...)
              (addr~_3 v~_4))
   ((addr~_1 (v~_1 ...)) ... (addr~_3 (v~_3 ... v~_4 v~_5 ...)) (addr~_2 (v~_2 ...)) ...)]
  [(σ~-extend ((addr~_1 (v~_1 ...)) ... (addr~_3 (v~_3 ...)) (addr~_2 (v~_2 ...)) ...) (addr~_3 v~_4))
   ((addr~_1 (v~_1 ...)) ... (addr~_3 ,(cons (term v~_4) (term (v~_3 ...)))) (addr~_2 (v~_2 ...)) ...)]
  [(σ~-extend σ~ (addr~ v~)) ,(cons (term (addr~ (v~))) (term σ~))]
  [(σ~-extend σ~ (addr~_1 v_1) (addr~_2 v_2) ...)
   (σ~-extend (σ~-extend σ~ (addr~_1 v_1)) (addr~_2 v_2) ...)])

(define-metafunction CESK~
  ρσ~-lookup : ρ~ σ~ x -> (v~ ...)
  [(ρσ~-lookup ρ~ σ~ x) (σ~-lookup σ~ (ρ~-lookup ρ~ x))])

(define-metafunction CESK~
  alloc~ : σ~ x -> addr~
  [(alloc~ σ~ x)
   ,(if ((length (flatten (term σ~))) . < . 100)
        (variable-not-in (term σ~) (term x))
        (term x))])

(define-metafunction CESK~
  alloc~-n : σ~ x ... -> (addr~ ...)
  [(alloc~-n σ~) ()]
  [(alloc~-n σ~ x_1 x_2 ...) ,(cons (term (alloc~ σ~ x_1)) (term (alloc~-n σ~ x_2 ...)))])

;; Tests

(define (test-suite)
  (test-->> red
            (term (+ 3 2 1))
            (term 6))
  (test-->> red
            (term ((λ (x) (+ x 4)) 3))
            (term 7))
  (test-->> red
            (term (let ((x 5))
                    x))
            (term 5))
  (test-->> red
            (term (let ((x 5))
                    (let ((y 6))
                      (+ x y))))
            (term 11))
  (test-->> red
            (term (let ((x (+ 3 2)))
                    (+ x 5)))
            (term 10))
  (test-->> red
            (term (let ((x 5))
                    (let ((x 6))
                      x)))
            (term 6))
  (test-->> red
            (term (let ((x 5))
                    (let ((y (set! x 6)))
                      x)))
            (term 6))
  (test-results))

(test-suite)

(define (test-suite^)
  (test-->> red^
            (term 5)
            (term 5))
  (test-->> red^
            (term (+ 3 2))
            (term 5))
  (test-->> red^
            (term ((λ (x) (+ x 1)) 5))
            (term 6))
  (test-->> red^
            (term (if #f 5 0))
            (term 0))
  (test-->> red^
            (term (if #t 8 9))
            (term 8))
  (test-->> red^
            (term ((λ (x) (if x 3 2)) (= 0 (- 2 2))))
            (term 3))
  (test-->> red^
            (term ((λ (x y) (+ x y)) 3 2))
            (term 4)
            (term 5)
            (term 6))
  (test-results))
(test-suite^)

(define (test-suite~)
  (test-->> red~
            (term 5)
            (term 5))
  (test-->> red~
            (term (+ 3 2))
            (term 5))
  (test-->> red~
            (term ((λ (x) (+ x 1)) 5))
            (term 6))
  (test-->> red~
            (term (if #f 5 0))
            (term 0))
  (test-->> red~
            (term (if #t 8 9))
            (term 8))
  (test-->> red~
            (term ((λ (x) (if x 3 2)) (= 0 (- 2 2))))
            (term 3))
  (test-->> red~
            (term ((λ (x y) (+ x y)) 3 2))
            (term 5))
  (test-results))
(test-suite~)

;; Pictures

(define red-pic
  (with-compound-rewriters
   (['ρ-extend
     (λ (lws)
       (list "" (list-ref lws 2) "[" (list-ref lws 3) "]" ""))]
    ['σ-extend
     (λ (lws)
       (list "" (list-ref lws 2) "[" (list-ref lws 3) "]" ""))]
    ['ρ-lookup
     (λ (lws)
       (list "" (list-ref lws 2) "(" (list-ref lws 3) ")" ""))])
   (render-reduction-relation red)))

(define red^-pic
  (with-compound-rewriters
   (['ρ-extend
     (λ (lws)
       (list "" (list-ref lws 2) "[" (list-ref lws 3) "]" ""))]
    ['σ^-extend
     (λ (lws)
       (list "" (list-ref lws 2) "⊔[" (list-ref lws 3) "]" ""))]
    ['ρ^-lookup
     (λ (lws)
       (list "" (list-ref lws 2) "(" (list-ref lws 3) ")" ""))])
   (render-reduction-relation red^)))

(define red~-pic
  (with-compound-rewriters
   (['ρ-extend
     (λ (lws)
       (list "" (list-ref lws 2) "[" (list-ref lws 3) "]" ""))]
    ['σ~-extend
     (λ (lws)
       (list "" (list-ref lws 2) "⊔[" (list-ref lws 3) "]" ""))]
    ['ρ~-lookup
     (λ (lws)
       (list "" (list-ref lws 2) "(" (list-ref lws 3) ")" ""))])
   (render-reduction-relation red~)))
