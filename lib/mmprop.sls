#!r6rs

(library (mmprop)
  (export wff
          wff?
          wff-quote
          wff->proof
          make-prop-database
          prop-database?
          prop-database-declare-wff-variable!
          make-wff-variable
          wff-variable?
          make-conditional
          conditional?
          conditional-antecedent
          conditional-consequent)
  (import (rnrs)
          (string-split)
          (mm3)
          (mmtools))

  ;; Databases

  (define-record-type prop-database
    (parent database)
    (opaque #t)
    (fields)
    (protocol
      (lambda (pargs->new)
        (lambda ()
          (parameterize ([current-database ((pargs->new))])
            (declare-constant! wff)
            (declare-constant! "|-")
            (declare-constant! "->")
            (declare-constant! "(")
            (declare-constant! ")")
            (declare-wff-variable! ph)
            (declare-wff-variable! ps)
            (declare-wff-variable! ch)
            (declare-wff-variable! th)
            (declare-wff-variable! ta)
            (declare-axiom! wi "wff ( ph -> ps )")
            (declare-axiom! (min "|- ph")
                            (maj "|- ( ph -> ps )")
                            mp   "|- ps")
            (declare-axiom! simp "|- ( ph -> ( ps -> ph ) )")
            (declare-axiom!
             frege
             "|- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ")
            (declare-axiom!
             peirce
             "|- ( ( ( ph -> ps ) -> ph ) -> ph )")
            (current-database))))))

  (define prop-database-declare-wff-variable!
    (lambda (db tok)
      (assert (prop-database? db))
      (assert (token? tok))
      (database-declare-variable! db
                                  (wff->label tok)
                                  (token wff)
                                  tok)))

  (define-syntax declare-wff-variable!
    (lambda (stx)
      (syntax-case stx ()
        [(_ tok)
         #'(prop-database-declare-wff-variable! (current-database) (token tok))])))

  (define wff->label
    (lambda (tok)
      (symbol-append 'w tok)))

  ;; Wffs

  ;; TODO: Parser for wffs!

  (define-record-type wff
    (opaque #t))

  (define wff->proof
    (lambda (wff)
      (assert (wff? wff))
      (cond
       [(wff-variable? wff)
        (make-shift-step (wff->label (wff-variable-token wff)))]
       [(conditional? wff)
        (make-reduce-step (token wi)
                          (list (wff->proof (conditional-antecedent wff))
                                (wff->proof (conditional-consequent wff)))
                          (list))]
       [else (assert #f)])))

  (define-syntax wff-quote
    (lambda (stx)
      (syntax-case stx ()
        [(_ s)
         (string? (syntax->datum #'s))
         (let-values ([(x tok*)])
           (let f ([tok* (map string->symbol (string-split (syntax->datum #'s)))]
                   [stack '()])
             (if (null? tok*)
                 (syntax-violation #f "invalid syntax" stx)
                 (let ([tok (car tok*)] [tok* (cdr tok*)])
                   (cond
                    [(eq? tok (token "("))
                     (let-values ([(x tok*) (f tok* (cons stack 'token))])
                       (when (null? tok*)
                         ...)
                       ;; get symbol
                       ;; load again
                       ;; get right )
                       )]
                    [(memq tok '(ph ps ch th ta))
                     (values #`(make-wff-variable '#,(datum->syntax #'* tok))
                             tok*)]
                    [else
                     (syntax-violation #f "invalid syntax" stx)]))))
           (unless (null? tok*)
             (syntax-violation #f "invalid syntax" stx))
           x)])))

  ;; Variables

  (define-record-type wff-variable
    (opaque #t)
    (parent wff)
    (sealed #t)
    (fields token)
    (protocol
      (lambda (pargs->new)
        (lambda (tok)
          (assert (token? tok))
          ((pargs->new) tok)))))

  ;; Conditionals

  (define-record-type conditional
    (fields antecedent consequent)
    (parent wff)
    (opaque #t)
    (protocol
      (lambda (pargs->new)
        (lambda (a c)
          (assert (wff? a))
          (assert (wff? c))
          ((pargs->new) a c)))))

  ;; Utilities

  (define symbol-append
    (lambda sym*
      (string->symbol (apply string-append (map symbol->string sym*)))))

  ;; Completeness of implicational propositional logic

  )
