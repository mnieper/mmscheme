#!r6rs

(library (mm3)
  (export
    token?
    token-list?
    database
    make-database
    database?
    database-declare-constant!
    database-constant?
    database-declare-variable!
    database-variable?
    database-declare-axiom!
    database-declare-proposition!
    make-expression
    expression?
    proof?
    proper-proof?
    make-unknown-proof
    unknown-proof?
    make-shift-step
    shift-step?
    make-reduce-step
    reduce-step?
    put-database)
  (import (rnrs))

  ;; Tokens

  (define token?
    (lambda (obj)
      (symbol? obj)))

  (define token-list?
    (lambda (obj)
      (and (list? obj)
           (for-all token? obj))))

  (define token=?
    (lambda (tok1 tok2)
      (symbol=? tok1 tok2)))

  (define token-list=?
    (lambda (ls1 ls2)
      (and (fx=? (length ls1) (length ls2))
           (for-all token=? ls1 ls2))))

  (define make-token-hashtable
    (lambda ()
      (make-eq-hashtable)))

  ;; Databases

  (define-record-type database
    (opaque #t)
    (fields token-table (mutable tokens))
    (protocol
      (lambda (new)
        (lambda ()
          (new (make-token-hashtable) '())))))

  (define declare-token!
    (lambda (db tok val)
      (define token-table (database-token-table db))
      (assert (not (hashtable-contains? token-table tok)))
      (hashtable-set! token-table tok val)
      (database-tokens-set! db (cons tok (database-tokens db)))))

  (define token-type
    (lambda (db tok)
      (hashtable-ref (database-token-table db) tok #f)))

  ;; Math symbols

  (define-record-type math-symbol)

  ;; Constants

  (define-record-type constant
    (sealed #t)
    (parent math-symbol))

  (define database-declare-constant!
    (lambda (db tok)
      (assert (database? db))
      (assert (token? tok))
      (declare-token! db tok (make-constant))))

  (define database-constant?
    (lambda (db tok)
      (assert (database? db))
      (assert (token? tok))
      (constant? (hashtable-ref (database-token-table db) tok #f))))

  ;; Variables

  (define-record-type variable
    (sealed #t)
    (parent math-symbol)
    (fields type))

  (define-record-type floating-hypothesis
    (sealed #t)
    (fields type variable))

  (define database-declare-variable!
    (lambda (db lbl type tok)
      (assert (database? db))
      (assert (token? lbl))
      (assert (database-constant? db type))
      (assert (token? tok))
      (declare-token! db tok (make-variable type))
      (declare-token! db lbl (make-floating-hypothesis type tok))))

  (define database-variable?
    (lambda (db tok)
      (assert (database? db))
      (assert (token? tok))
      (variable? (hashtable-ref (database-token-table db) tok #f))))

  ;; Expressions

  (define-record-type expression
    (sealed #t)
    (fields label type symbols)
    (protocol
      (lambda (new)
        (lambda (lbl type sym*)
          (assert (token? lbl))
          (assert (token? type))
          (assert (token-list? sym*))
          (new lbl type sym*)))))

  (define expression-list?
    (lambda (obj)
      (and (list? obj)
           (for-all expression? obj))))

  (define database-expression?
    (lambda (db obj)
      (and (expression? obj)
           (constant? (token-type db (expression-type obj)))
           (for-all (lambda (tok)
                      (math-symbol? (token-type db tok)))
                    (expression-symbols obj)))))

  (define database-expression-list?
    (lambda (db obj)
      (and (list? obj)
           (for-all (lambda (obj) (database-expression? db obj)) obj))))

  (define expression->math-symbol-list
    (lambda (exp)
      (cons (expression-type exp)
            (expression-symbols exp))))

  ;; Assertions

  (define-record-type assertion
    (fields hypotheses expression variables))

  ;; Axioms

  (define-record-type axiom
    (parent assertion))

  (define-record-type essential-hypothesis
    (fields assertion expression))

  (define database-declare-axiom!
    (lambda (db hyp* ass)
      (assert (database? db))
      (assert (database-expression-list? db hyp*))
      (assert (database-expression? db ass))
      (let ([lbl* (map expression-label hyp*)]
            [albl (expression-label ass)])
        (for-each
          (lambda (lbl hyp)
            (declare-token! db lbl (make-essential-hypothesis
                                    albl (expression->math-symbol-list hyp))))
          lbl* hyp*)
        (declare-token! db albl (make-axiom lbl*
                                            (expression->math-symbol-list ass)
                                            (collect-variables db hyp* ass))))))

  (define collect-variables
    (lambda (db hyp* exp)
      (let ([var-table (make-token-hashtable)])
        (define f!
          (lambda (var* exp)
            (fold-left
              (lambda (var* sym)
                (cond
                 [(and (variable? (token-type db sym))
                       (not (hashtable-contains? var-table sym)))
                  (hashtable-set! var-table sym #t)
                  (cons sym var*)]
                 [else var*]))
              var*
              (expression-symbols exp))))
        (reverse (f! (fold-left f! '() hyp*) exp)))))

  ;; Propositions

  (define-record-type proposition
    (parent assertion)
    (fields proof))

  (define database-declare-proposition!
    (lambda (db hyp* ass prf)
      (assert (database? db))
      (assert (database-expression-list? db hyp*))
      (assert (database-expression? db ass))
      (assert (proof? prf))
      (let ([lbl* (map expression-label hyp*)]
            [albl (expression-label ass)])
        (for-each
          (lambda (lbl hyp)
            (declare-token! db lbl (make-essential-hypothesis
                                    albl (expression->math-symbol-list hyp))))
          lbl* hyp*)
        (declare-token! db albl (make-proposition lbl*
                                                  (expression->math-symbol-list ass)
                                                  (collect-variables db hyp* ass)
                                                  prf)))
      (assert (proves? db hyp* ass prf))))

  ;; Proofs

  (define-record-type proof)

  (define-record-type unknown-proof
    (sealed #t)
    (parent proof))

  (define-record-type proper-proof
    (parent proof))

  (define-record-type shift-step
    (sealed #t)
    (parent proper-proof)
    (fields label)
    (protocol
      (lambda (pargs->new)
        (lambda (lbl)
          (assert (token? lbl))
          ((pargs->new) lbl)))))

  (define-record-type reduce-step
    (sealed #t)
    (parent proper-proof)
    (fields label floating-hypotheses essential-hypotheses)
    (protocol
      (lambda (pargs->new)
        (lambda (lbl fhyp* ehyp*)
          (assert (token? lbl))
          (assert (and (list? fhyp*)
                       (for-all proper-proof? fhyp*)))
          (assert (and (list? ehyp*)
                       (for-all proof? ehyp*)))
          ((pargs->new) lbl fhyp* ehyp*)))))

  (define proves?
    (lambda (db hyp* ass prf)
      (define g?
        (lambda (goal res)
          (or (not res)
              (token-list=? goal res))))
      (call/cc
       (lambda (k)
         (define check
           (lambda (x)
             (or x (k #f))))
         (define f
           (lambda (prf)
             (cond
              [(shift-step? prf)
               (let ([hyp (token-type db (shift-step-label prf))])
                 (cond
                  [(floating-hypothesis? hyp)
                   (list (floating-hypothesis-type hyp)
                         (floating-hypothesis-variable hyp))]
                  [(essential-hypothesis? hyp)
                   (check (token=? (essential-hypothesis-assertion hyp)
                                   (expression-label ass)))
                   (essential-hypothesis-expression hyp)]
                  [else
                   (check #f)]))]
              [(reduce-step? prf)
               (let ([thm (token-type db (reduce-step-label prf))]
                     [fhyp* (reduce-step-floating-hypotheses prf)]
                     [ehyp* (reduce-step-essential-hypotheses prf)])
                 (assert (assertion? thm))
                 (let ([var* (assertion-variables thm)]
                       [hyp* (assertion-hypotheses thm)])
                   (define subst (make-token-hashtable))
                   (assert (fx=? (length var*) (length fhyp*)))
                   (assert (fx=? (length hyp*) (length ehyp*)))
                   (for-each
                     (lambda (var fhyp)
                       (let ([res (f fhyp)])
                         (check (token=? (car res)
                                         (variable-type (token-type db var))))
                         (hashtable-set! subst var (cdr res))))
                     var* fhyp*)
                   (for-each
                     (lambda (hyp ehyp)
                       (let ([res (f ehyp)]
                             [goal (substitute db
                                               subst
                                               (essential-hypothesis-expression
                                                (token-type db hyp)))])
                         (check (g? goal res))))
                     hyp* ehyp*)
                   (substitute db subst (assertion-expression thm))))]
              [(unknown-proof? prf) #f]
              [else (assert #f)])))
         (g? (expression->math-symbol-list ass)
             (f prf))))))

  (define substitute
    (lambda (db subst exp)
      (fold-right
        (lambda (sym sym*)
          (define type (token-type db sym))
          (cond
           [(variable? type)
            (append (assert (hashtable-ref subst sym #f))
                    sym*)]
           [(constant? type)
            (cons sym sym*)]
           [else (assert #f)]))
        '()
        exp)))

  ;; Output

  (define put-database
    (lambda (p db)
      (assert (textual-output-port? p))
      (assert (database? db))
      (for-each
        (lambda (tok)
          (put-object p db tok (token-type db tok)))
        (reverse (database-tokens db)))))

  (define textual-output-port?
    (lambda (obj)
      (and (output-port? obj)
           (textual-port? obj))))

  (define put-object
    (lambda (p db tok type)
      (cond
       [(constant? type)
        (put-constant p tok)]
       [(variable? type)
        (put-variable p tok)]
       [(floating-hypothesis? type)
        (put-floating-hypothesis p
                                 tok
                                 (floating-hypothesis-type type)
                                 (floating-hypothesis-variable type))]
       [(axiom? type)
        (put-axiom p
                   db
                   tok
                   (assertion-hypotheses type)
                   (assertion-expression type))]
       [(proposition? type)
        (put-proposition p
                         db
                         tok
                         (assertion-hypotheses type)
                         (assertion-expression type)
                         (proposition-proof type))]

       [(essential-hypothesis? type) (values)]
       [else (assert #f)])))

  (define put-constant
    (lambda (p tok)
      (put-string p "$c ")
      (put-token p tok)
      (put-string p " $.\n")))

  (define put-variable
    (lambda (p tok)
      (put-string p "$v ")
      (put-token p tok)
      (put-string p " $.\n")))

  (define put-floating-hypothesis
    (lambda (p lbl type var)
      (put-token p lbl)
      (put-string p " $f ")
      (put-token p type)
      (put-string p " ")
      (put-token p var)
      (put-string p " $.\n")))

  (define put-axiom
    (lambda (p db lbl hyp* ass)
      (put-string p "${\n")
      (for-each
        (lambda (hyp)
          (let ([type (token-type db hyp)])
            (put-essential-hypothesis p hyp
                                      (essential-hypothesis-expression type))))
        hyp*)
      (put-string p "  ")
      (put-token p lbl)
      (put-string p " $a ")
      (put-math-symbols p ass)
      (put-string p "$.\n")
      (put-string p "$}\n")))

  (define put-proposition
    (lambda (p db lbl hyp* ass prf)
      (put-string p "${\n")
      (for-each
        (lambda (hyp)
          (let ([type (token-type db hyp)])
            (put-essential-hypothesis p hyp
                                      (essential-hypothesis-expression type))))
        hyp*)
      (put-string p "  ")
      (put-token p lbl)
      (put-string p " $p ")
      (put-math-symbols p ass)
      (put-string p "$= ")
      (put-proof p prf)
      (put-string p "$.\n")
      (put-string p "$}\n")))

  (define put-essential-hypothesis
    (lambda (p lbl exp)
      (put-string p "  ")
      (put-token p lbl)
      (put-string p " $e ")
      (put-math-symbols p exp)
      (put-string p "$.\n")))

  (define put-math-symbols
    (lambda (p sym*)
      (for-each
        (lambda (sym)
          (put-token p sym)
          (put-string p " "))
        sym*)))

  (define put-proof
    (lambda (p prf)
      (let f ([prf prf])
        (cond
         [(unknown-proof? prf)
          (put-token p '?)]
         [(shift-step? prf)
          (put-token p (shift-step-label prf))]
         [(reduce-step? prf)
          (for-each f
            (append (reduce-step-floating-hypotheses prf)
                    (reduce-step-essential-hypotheses prf)))
          (put-token p (reduce-step-label prf))]
         [else (assert #f)])
        (put-string p " "))))

  (define put-token
    (lambda (p tok)
      (put-string p (symbol->string tok))))

  )
