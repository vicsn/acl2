; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-SOUND and R1CS-COMPLETE of Signature::verify; the circuit and the
; stage lemmas are in sig-verify-parts.lisp.

(in-package "ALEOVM")

(include-book "sig-verify-parts")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (in-theory (disable hpos-lc-eval-decomp)))

(set-ignore-ok t)

(defruled sig-stage-nonce
  (sig-b* ((mv out cs & &) (sig-c-verify pk pr ad msg sr rb rrs rsts sc cb crs steps
                                      ox oy sk kb krs ksts m r mx rx my ry gout z
                                      u vs asg0))
    (implies (and (sig-verify-hyps)
                  (r1cs::r1cs-constraints-holdp cs asg (base-prime)))
             (and (scalarp (lookup-equal sc asg)) (scalarp (lookup-equal sr asg))
                  (hpos-pt-boundp gn asg)
                  (ecurve::edwards-bls12-pointp (hpos-pt-eval gn asg))
                  (equal (hpos-pt-eval gn asg)
                         (group-add-funspec
                          (aleo-g-scalar-multiply-funspec (lookup-equal sr asg))
                          (group-mul-funspec (hpos-pt-eval pk asg) (lookup-equal sc asg)))))))
  :do-not-induct t
  :use (sig-c-verify-split
        (:instance sig-nonce-sound
                   (s sr) (rbits rb) (rs rrs) (sts rsts) (schal sc) (cbits cb)
                   (p (base-prime))))
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append))

(defruled sig-psd8-cong
  (implies (equal g1 g2)
           (equal (aleo-hash-to-scalar-psd8-funspec (cons (ecurve::point-finite->x g1) rest))
                  (aleo-hash-to-scalar-psd8-funspec (cons (ecurve::point-finite->x g2) rest)))))


(defruled sig-stage-hash0
  (sig-b* ((mv out cs & &) (sig-c-verify pk pr ad msg sr rb rrs rsts sc cb crs steps
                                      ox oy sk kb krs ksts m r mx rx my ry gout z
                                      u vs asg0))
    (implies (and (sig-verify-hyps)
                  (r1cs::r1cs-constraints-holdp cs asg (base-prime)))
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asg))
                  (equal (lebits=>nat (take 250 (lookup-equal-list bs asg)))
                         (aleo-hash-to-scalar-psd8-funspec
                          (list* (ecurve::point-finite->x (hpos-pt-eval gn asg))
                                 (ecurve::point-finite->x (hpos-pt-eval pk asg))
                                 (ecurve::point-finite->x (hpos-pt-eval pr asg))
                                 (ecurve::point-finite->x (hpos-pt-eval ad asg))
                                 (lookup-equal-list msg asg)))))))
  :do-not-induct t
  :use (sig-c-verify-split sig-stage-nonce
        (:instance sig-xs-eval
                   (gx (nth 4 vs)) (pkx (car pk)) (prx (car pr)) (adx (car ad)))
        (:instance key-h2s-psd8-sound
                   (xs (sig-xs (nth 4 vs) (car pk) (car pr) (car ad) msg))
                   (vs (nthcdr 6 vs))
                   (asg (mv-nth 3 (hpos-c-gadd (sig-mul-out cb ox oy steps)
                                               (key-gmul-wires rsts) vs asg0)))
                   (asgx asg)))
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append hpos-pt-eval hpos-pt-boundp
               ecurve::point-finite->x-of-point-finite car-cons cdr-cons nfix
               (:t r1cs::natp-of-lookup-equal-when-r1cs-valuationp-type)))

(defruled sig-stage-hash
  (sig-b* ((mv out cs & &) (sig-c-verify pk pr ad msg sr rb rrs rsts sc cb crs steps
                                      ox oy sk kb krs ksts m r mx rx my ry gout z
                                      u vs asg0))
    (implies (and (sig-verify-hyps)
                  (r1cs::r1cs-constraints-holdp cs asg (base-prime)))
             (and (equal bits (take 250 bs))
                  (bit-listp (lookup-equal-list bs asg))
                  (equal (lebits=>nat (take 250 (lookup-equal-list bs asg)))
                         (aleo-hash-to-scalar-psd8-funspec
                          (list* (ecurve::point-finite->x
                                  (group-add-funspec
                                   (aleo-g-scalar-multiply-funspec (lookup-equal sr asg))
                                   (group-mul-funspec (hpos-pt-eval pk asg)
                                                      (lookup-equal sc asg))))
                                 (ecurve::point-finite->x (hpos-pt-eval pk asg))
                                 (ecurve::point-finite->x (hpos-pt-eval pr asg))
                                 (ecurve::point-finite->x (hpos-pt-eval ad asg))
                                 (lookup-equal-list msg asg)))))))
  :do-not-induct t
  :use (sig-stage-hash0 sig-stage-nonce
        (:instance sig-psd8-cong
                   (g1 (hpos-pt-eval (cons (nth 4 vs) (nth 5 vs)) asg))
                   (g2 (group-add-funspec
                        (aleo-g-scalar-multiply-funspec (lookup-equal sr asg))
                        (group-mul-funspec (hpos-pt-eval pk asg) (lookup-equal sc asg))))
                   (rest (list* (ecurve::point-finite->x (hpos-pt-eval pk asg))
                               (ecurve::point-finite->x (hpos-pt-eval pr asg))
                               (ecurve::point-finite->x (hpos-pt-eval ad asg))
                               (lookup-equal-list msg asg)))))
  :in-theory nil)

(defruled sig-stage-addr
  (sig-b* ((mv out cs & &) (sig-c-verify pk pr ad msg sr rb rrs rsts sc cb crs steps
                                      ox oy sk kb krs ksts m r mx rx my ry gout z
                                      u vs asg0))
    (implies (and (sig-verify-hyps)
                  (r1cs::r1cs-constraints-holdp cs asg (base-prime)))
             (and (scalarp (lookup-equal sk asg))
                  (hpos-pt-boundp ca asg)
                  (equal (hpos-pt-eval ca asg)
                         (compute-key-to-address-funspec
                          (list (hpos-pt-eval pk asg) (hpos-pt-eval pr asg)
                                (lookup-equal sk asg)))))))
  :do-not-induct t
  :use (sig-c-verify-split
        (:instance key-compute-key-to-address-sound
                   (s sk) (rbits kb) (rs krs) (sts ksts) (p (base-prime))
                   (vs (cdr (mv-nth 2 (hpos-c-hash-to-scalar
                                  8 (sig-xs (nth 4 vs) (car pk) (car pr) (car ad) msg)
                                  u (nthcdr 6 vs)
                                  (mv-nth 3 (hpos-c-gadd (sig-mul-out cb ox oy steps)
                                                         (key-gmul-wires rsts) vs asg0))))))
                   (asg0 (mv-nth 3 (hpos-c-hash-to-scalar
                                    8 (sig-xs (nth 4 vs) (car pk) (car pr) (car ad) msg)
                                    u (nthcdr 6 vs)
                                    (mv-nth 3 (hpos-c-gadd (sig-mul-out cb ox oy steps)
                                                           (key-gmul-wires rsts) vs asg0))))))
        (:instance key-take-6-pt-boundp
                   (vs (nthcdr 6 (cdr (mv-nth 2 (hpos-c-hash-to-scalar
                                  8 (sig-xs (nth 4 vs) (car pk) (car pr) (car ad) msg)
                                  u (nthcdr 6 vs)
                                  (mv-nth 3 (hpos-c-gadd (sig-mul-out cb ox oy steps)
                                                         (key-gmul-wires rsts) vs asg0)))))))))
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append key-ck-out
               acl2::len-of-nthcdr nfix natp (:e nfix) (:t len) (:e base-prime) (:e <) (:e binary-+) (:e unary--)
               fix))

(defrule sig-final-logic
  (implies (and (equal zv (if (and (equal c (lebits=>nat l1)) (equal a ca)) 1 0))
                (equal l1 (take 250 l))
                (equal (lebits=>nat (take 250 l)) cand)
                (equal ca caspec))
           (equal zv (if (and (equal c cand) (equal a caspec)) 1 0)))
  :rule-classes nil)


(defruled sig-out-abstract2
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (symbolp schal) (r1cs::valuation-bindsp asg schal)
                (hpos-pt-boundp ad asg) (hpos-pt-boundp ca asg)
                (ecurve::edwards-bls12-pointp (hpos-pt-eval ad asg))
                (symbolp m) (symbolp r) (symbolp mx) (symbolp rx) (symbolp my)
                (symbolp ry) (symbolp gout) (symbolp z)
                (r1cs::valuation-bindsp asg m) (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg mx) (r1cs::valuation-bindsp asg rx)
                (r1cs::valuation-bindsp asg my) (r1cs::valuation-bindsp asg ry)
                (r1cs::valuation-bindsp asg gout) (r1cs::valuation-bindsp asg z)
                (r1cs::r1cs-constraints-holdp
                 (sig-eq-gadget schal bits ad ca m r mx rx my ry gout z)
                 asg (base-prime))
                (equal bits (take 250 bs))
                (symbol-listp bs) (equal (len bs) 253)
                (r1cs::valuation-binds-allp asg bs)
                (bit-listp (lookup-equal-list bs asg))
                (equal (lebits=>nat (take 250 (lookup-equal-list bs asg))) cand)
                (equal (hpos-pt-eval ca asg) (compute-key-to-address-funspec ck)))
           (equal (lookup-equal z asg)
                  (if (and (equal (lookup-equal schal asg) cand)
                           (equal (hpos-pt-eval ad asg) (compute-key-to-address-funspec ck)))
                      1 0)))
  :do-not-induct t
  :use (sig-take-250-facts sig-eq-sound
        (:instance edwards-bls12-pointp-of-compute-key-to-address-funspec))
  :in-theory nil)

(defruled sig-out-value
  (sig-b* ((mv out cs & &) (sig-c-verify pk pr ad msg sr rb rrs rsts sc cb crs steps
                                      ox oy sk kb krs ksts m r mx rx my ry gout z
                                      u vs asg0))
    (implies (and (sig-verify-hyps)
                  (r1cs::r1cs-constraints-holdp cs asg (base-prime)))
             (equal (lookup-equal out asg)
                    (if (and (equal (lookup-equal sc asg)
                                    (aleo-hash-to-scalar-psd8-funspec
                                     (list* (ecurve::point-finite->x
                                             (group-add-funspec
                                              (aleo-g-scalar-multiply-funspec (lookup-equal sr asg))
                                              (group-mul-funspec (hpos-pt-eval pk asg)
                                                                 (lookup-equal sc asg))))
                                            (ecurve::point-finite->x (hpos-pt-eval pk asg))
                                            (ecurve::point-finite->x (hpos-pt-eval pr asg))
                                            (ecurve::point-finite->x (hpos-pt-eval ad asg))
                                            (lookup-equal-list msg asg))))
                             (equal (hpos-pt-eval ad asg)
                                    (compute-key-to-address-funspec
                                     (list (hpos-pt-eval pk asg) (hpos-pt-eval pr asg)
                                           (lookup-equal sk asg)))))
                        1 0))))
  :do-not-induct t
  :use (sig-c-verify-split sig-stage-hash sig-stage-addr
        (:instance sig-out-abstract2
                   (schal sc)
                   (bits (mv-nth 0 (hpos-c-hash-to-scalar
                                  8 (sig-xs (nth 4 vs) (car pk) (car pr) (car ad) msg)
                                  u (nthcdr 6 vs)
                                  (mv-nth 3 (hpos-c-gadd (sig-mul-out cb ox oy steps)
                                                         (key-gmul-wires rsts) vs asg0)))))
                   (bs (mv-nth 0 (hpos-h2s-wires
                                  (mv-nth 2 (hpos-c-poseidon-hash-many
                                             8 (sig-xs (nth 4 vs) (car pk) (car pr) (car ad) msg)
                                             1 (nthcdr 6 vs)
                                             (mv-nth 3 (hpos-c-gadd (sig-mul-out cb ox oy steps)
                                                                    (key-gmul-wires rsts) vs asg0)))))))
                   (ca (cons (nth 4 (nthcdr 6 (cdr (mv-nth 2 (hpos-c-hash-to-scalar
                                  8 (sig-xs (nth 4 vs) (car pk) (car pr) (car ad) msg)
                                  u (nthcdr 6 vs)
                                  (mv-nth 3 (hpos-c-gadd (sig-mul-out cb ox oy steps)
                                                         (key-gmul-wires rsts) vs asg0))))))) (nth 5 (nthcdr 6 (cdr (mv-nth 2 (hpos-c-hash-to-scalar
                                  8 (sig-xs (nth 4 vs) (car pk) (car pr) (car ad) msg)
                                  u (nthcdr 6 vs)
                                  (mv-nth 3 (hpos-c-gadd (sig-mul-out cb ox oy steps)
                                                         (key-gmul-wires rsts) vs asg0)))))))))
                   (ck (list (hpos-pt-eval pk asg) (hpos-pt-eval pr asg)
                             (lookup-equal sk asg)))
                   (cand (aleo-hash-to-scalar-psd8-funspec
                          (list* (ecurve::point-finite->x
                                  (group-add-funspec
                                   (aleo-g-scalar-multiply-funspec (lookup-equal sr asg))
                                   (group-mul-funspec (hpos-pt-eval pk asg)
                                                      (lookup-equal sc asg))))
                                 (ecurve::point-finite->x (hpos-pt-eval pk asg))
                                 (ecurve::point-finite->x (hpos-pt-eval pr asg))
                                 (ecurve::point-finite->x (hpos-pt-eval ad asg))
                                 (lookup-equal-list msg asg))))))
  :in-theory '(r1cs::r1cs-constraints-holdp-of-append (:e base-prime) (:e integer-length)))

(defruled signature-verify-sound
  :short "R1CS-SOUND of Signature::verify, given Group::new on pk_sig, pr_sig
          and the address (points on the curve), and the bound allocated
          wires: the output wire is signature-verify-funspec of the wire
          signature (challenge, response, compute key), address and message."
  (sig-b* ((mv out cs & &) (sig-c-verify pk pr ad msg sr rb rrs rsts sc cb crs steps
                                      ox oy sk kb krs ksts m r mx rx my ry gout z
                                      u vs asg0))
    (implies (and (sig-verify-hyps)
                  (r1cs::r1cs-constraints-holdp cs asg (base-prime)))
             (equal (lookup-equal out asg)
                    (signature-verify-funspec
                     (list (lookup-equal sc asg) (lookup-equal sr asg)
                           (list (hpos-pt-eval pk asg) (hpos-pt-eval pr asg)
                                 (lookup-equal sk asg)))
                     (hpos-pt-eval ad asg)
                     (lookup-equal-list msg asg)))))
  :do-not-induct t
  :use (sig-out-value sig-stage-nonce sig-stage-addr)
  :in-theory '(signature-verify-funspec curve-signaturep-of-list curve-compute-keyp
               address-to-field-funspec group-to-x-coordinate-funspec
               len true-listp car-cons cdr-cons (:e natp) (:e <) (:e len)
               (:t ecurve::edwards-bls12-pointp) (:t scalarp)
               edwards-bls12-pointp-of-compute-key-to-address-funspec))
