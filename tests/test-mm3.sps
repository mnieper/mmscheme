#!r6rs

(import (rnrs)
        (mm3)
        (mmtools))

(declare-constant! "(")
(declare-constant! ")")
(declare-constant! "+")
(declare-constant! "|-")
(declare-constant! "->")
(declare-constant! "0")
(declare-constant! term)
(declare-constant! wff)

(declare-variable! tt (term t))
(declare-variable! tr (term r))
(declare-variable! ts (term s))
(declare-variable! wp (wff P))
(declare-variable! wq (wff Q))

(declare-axiom! tze "term 0")
(declare-axiom! tpl "term ( t + r )")

(declare-axiom!
 (min "|- P")
 (maj "|- P -> Q")
 mp   "|- Q")

(declare-proposition!
 p.1 "term ( t + 0 )"
 ((tpl tt ((tze)))))

(put-database (current-output-port)
              (current-database))
