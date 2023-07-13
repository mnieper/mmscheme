#!r6rs

(import (rnrs)
        (mm3)
        (mmtools)
        (mmprop))

(current-database (make-prop-database))

(declare-proposition!
 (mp2.1 "|- ph")
 (mp2.2 "|- ps")
 (mp2.3 "|- ( ph -> ( ps -> ch ) )")
 mp2 "|- ch"
 ((mp ,(wff->proof (make-wff-variable (token ps)))
      ,(wff->proof (make-wff-variable (token ch))))
  mp2.2
  ((mp ,(wff->proof (make-wff-variable (token ph)))
       ,(wff->proof (make-conditional
                     (make-wff-variable (token ps))
                     (make-wff-variable (token ch)))))
   mp2.1 mp2.3)))

(put-database (current-output-port)
              (current-database))
