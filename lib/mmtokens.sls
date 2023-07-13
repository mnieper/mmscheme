#!r6rs

(library (mmtokens)
  (export
    parse-token
    parse-tokens
    parse-proof)
  (import (rnrs)
          (string-split)
          (mm3))

  ;; Tokens

  (define parse-token
    (lambda (stx)
      (syntax-case stx ()
        [sym
         (identifier? #'sym)
         #''sym]
        [str
         (string? (syntax->datum #'str))
         #`'#,(datum->syntax #'* (string->symbol (syntax->datum #'str)))])))

  (define parse-tokens
    (lambda (stx)
      (syntax-case stx ()
        [(tok ...)
         (map parse-token #'(tok ...))]
        [str
         (string? (syntax->datum #'str))
         (let ([str* (string-split (syntax->datum #'str))])
           (map (lambda (str)
                  #`'#,(datum->syntax #'* (string->symbol str)))
                str*))])))

  ;; Proofs

  (define parse-proof
    (lambda (stx)
      (syntax-case stx (unquote)
        [#f #'(make-unknown-proof)]
        [,x
         #'x]
        [((lbl fhyp ...) ehyp ...)
         #`(make-reduce-step #,(parse-token #'lbl)
                             (list #,@(map parse-proof #'(fhyp ...)))
                             (list #,@(map parse-proof #'(ehyp ...))))]

        [lbl
         #`(make-shift-step #,(parse-token #'lbl))])))




  )
