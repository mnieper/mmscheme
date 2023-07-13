#!r6rs

(library (mmtools)
  (export
    current-database
    parameterize
    declare-constant!
    declare-variable!
    declare-axiom!
    declare-proposition!
    token
    expression
    proof)
  (import
    (rnrs)
    (mm3)
    (mmtokens))

  (define-syntax token
    (lambda (stx)
      (syntax-case stx ()
        [(_ tok)
         (parse-token #'tok)])))

  (define current-database
    (let ([db (make-database)])
      (case-lambda
        [() db]
        [(new-db)
         (assert (database? new-db))
         (set! db new-db)])))

  (define-syntax parameterize
    (lambda (x)
      (syntax-case x ()
        [(_ () b1 ... b2) #'(begin b1 ... b2)]
        [(_ ([x e] ...) b1 ... b2)
         (with-syntax ([(p ...) (generate-temporaries #'(x ...))]
                       [(y ...) (generate-temporaries #'(x ...))])
           #'(let ([p x] ... [y e] ...)
               (let ([swap (lambda ()
                             (let ([t (p)]) (p y) (set! y t))
                             ...)])
                 (dynamic-wind swap (lambda () b1 ... b2) swap))))])))

  (define-syntax expression
    (lambda (stx)
      (syntax-case stx ()
        [(_ type tokens)
         (let ([tok* (parse-tokens #'tokens)])
           (when (null? tok*)
             (syntax-violation #f "untyped expression" #'tokens))
           #`(make-expression (token type)
                              #,(car tok*)
                              (list #,@(cdr tok*))))])))

  (define-syntax proof
    (lambda (stx)
      (syntax-case stx ()
        [(_ prf)
         (parse-proof #'prf)])))

  (define-syntax declare-constant!
    (lambda (stx)
      (syntax-case stx ()
        [(_ tok)
         #'(database-declare-constant! (current-database) (token tok))])))

  (define-syntax declare-variable!
    (lambda (stx)
      (syntax-case stx ()
        [(_ lbl exp)
         (let ([tok* (parse-tokens #'exp)])
           (unless (fx=? (length tok*) 2)
             (syntax-violation #f "invalid floating hypothesis" #'exp))
           #`(database-declare-variable! (current-database)
                                         (token lbl)
                                         #,(car tok*)
                                         #,(cadr tok*)))])))

  (define-syntax declare-axiom!
    (lambda (stx)
      (syntax-case stx ()
        [(_ (elbl eexp) ... lbl exp)
         #'(database-declare-axiom! (current-database)
                                    (list (expression elbl eexp) ...)
                                    (expression lbl exp))])))

  (define-syntax declare-proposition!
    (lambda (stx)
      (syntax-case stx ()
        [(_ (elbl eexp) ... lbl exp prf)
         #'(database-declare-proposition! (current-database)
                                          (list (expression elbl eexp) ...)
                                          (expression lbl exp)
                                          (proof prf))]))))
