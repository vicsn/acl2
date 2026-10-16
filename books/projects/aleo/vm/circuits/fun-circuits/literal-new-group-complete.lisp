; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-COMPLETE of the group, address and signature arms of Literal::new,
; with the cofactor witness of group-enforce-in-group-complete.lisp in
; place of the witness assumption of literal-group-new-complete-when-witness
; and literal-signature-new-complete-when-witness.
;
; The signature arm still uses the abstract hash_to_scalar_psd4 for sk_prf;
; literal-signature-new-gadget does not contain the Poseidon constraints.

(in-package "ALEOVM")

(include-book "literal-new-r1cs")
(include-book "group-enforce-in-group-complete")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled literal-group-new-complete
  :short "R1CS-COMPLETE for the group arm of @('Literal::new'): the
          coordinates of the literal's point and the cofactor witness
          satisfy @('enforce_in_group')."
  (implies (and (literalp x)
                (literal-case x :group)
                (symbolp xcoord) (symbolp ycoord)
                (symbolp qx) (symbolp qy)
                (symbolp cx2) (symbolp cy2)
                (symbolp dxy) (symbolp dx2) (symbolp dy2)
                (symbolp x3) (symbolp y3)
                (symbolp exy) (symbolp ex2) (symbolp ey2)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xcoord)
                (r1cs::valuation-bindsp asg ycoord)
                (r1cs::valuation-bindsp asg qx)
                (r1cs::valuation-bindsp asg qy)
                (r1cs::valuation-bindsp asg cx2)
                (r1cs::valuation-bindsp asg cy2)
                (r1cs::valuation-bindsp asg dxy)
                (r1cs::valuation-bindsp asg dx2)
                (r1cs::valuation-bindsp asg dy2)
                (r1cs::valuation-bindsp asg x3)
                (r1cs::valuation-bindsp asg y3)
                (r1cs::valuation-bindsp asg exy)
                (r1cs::valuation-bindsp asg ex2)
                (r1cs::valuation-bindsp asg ey2)
                (group-enforce-in-group-witness-lookupsp
                 xcoord ycoord qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                 (literal-group->get x) asg p))
           (and (r1cs::r1cs-constraints-holdp
                 (literal-group-new-gadget
                  xcoord ycoord qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                 asg p)
                (equal (literal-new x) (literal-fix x))))
  :use ((:instance literal-group-new-complete-when-witness)
        (:instance group-enforce-in-group-equations-when-witness-lookupsp
                   (x xcoord) (y ycoord) (pt (literal-group->get x))))
  :enable literal-new-when-not-recomputed)

(defruled literal-address-new-complete
  :short "R1CS-COMPLETE for the address arm of @('Literal::new'), which
          is @('Group::new') of the address point."
  (implies (and (literalp x)
                (literal-case x :address)
                (symbolp xcoord) (symbolp ycoord)
                (symbolp qx) (symbolp qy)
                (symbolp cx2) (symbolp cy2)
                (symbolp dxy) (symbolp dx2) (symbolp dy2)
                (symbolp x3) (symbolp y3)
                (symbolp exy) (symbolp ex2) (symbolp ey2)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg xcoord)
                (r1cs::valuation-bindsp asg ycoord)
                (r1cs::valuation-bindsp asg qx)
                (r1cs::valuation-bindsp asg qy)
                (r1cs::valuation-bindsp asg cx2)
                (r1cs::valuation-bindsp asg cy2)
                (r1cs::valuation-bindsp asg dxy)
                (r1cs::valuation-bindsp asg dx2)
                (r1cs::valuation-bindsp asg dy2)
                (r1cs::valuation-bindsp asg x3)
                (r1cs::valuation-bindsp asg y3)
                (r1cs::valuation-bindsp asg exy)
                (r1cs::valuation-bindsp asg ex2)
                (r1cs::valuation-bindsp asg ey2)
                (group-enforce-in-group-witness-lookupsp
                 xcoord ycoord qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2
                 (literal-address->get x) asg p))
           (and (r1cs::r1cs-constraints-holdp
                 (literal-group-new-gadget
                  xcoord ycoord qx qy cx2 cy2 dxy dx2 dy2 x3 y3 exy ex2 ey2 p)
                 asg p)
                (equal (literal-new x) (literal-fix x))))
  :use ((:instance literal-group-new-complete-when-witness)
        (:instance group-enforce-in-group-equations-when-witness-lookupsp
                   (x xcoord) (y ycoord) (pt (literal-address->get x))))
  :enable literal-new-when-not-recomputed)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled literal-signature-new-complete
  :short "R1CS-COMPLETE for the signature arm of @('Literal::new'): the
          canonical scalar witnesses of @(tsee literal-scalar-new-complete)
          and the cofactor witnesses of @('pk_sig') and @('pr_sig') satisfy
          @(tsee literal-signature-new-gadget).  The Poseidon constraints of
          @('hash_to_scalar_psd4') are not part of that gadget."
  (implies (and (literalp x)
                (literal-case x :signature)
                (symbolp c) (symbol-listp cxs) (symbol-listp crs)
                (symbolp r) (symbol-listp rxs) (symbol-listp rrs)
                (equal (len cxs) 251) (equal (len crs) 250)
                (equal (len rxs) 251) (equal (len rrs) 250)
                (symbolp pkx) (symbolp pky)
                (symbolp pk-qx) (symbolp pk-qy)
                (symbolp pk-cx2) (symbolp pk-cy2)
                (symbolp pk-dxy) (symbolp pk-dx2) (symbolp pk-dy2)
                (symbolp pk-x3) (symbolp pk-y3)
                (symbolp pk-exy) (symbolp pk-ex2) (symbolp pk-ey2)
                (symbolp prx) (symbolp pry)
                (symbolp pr-qx) (symbolp pr-qy)
                (symbolp pr-cx2) (symbolp pr-cy2)
                (symbolp pr-dxy) (symbolp pr-dx2) (symbolp pr-dy2)
                (symbolp pr-x3) (symbolp pr-y3)
                (symbolp pr-exy) (symbolp pr-ex2) (symbolp pr-ey2)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c)
                (r1cs::valuation-binds-allp asg cxs)
                (r1cs::valuation-binds-allp asg crs)
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-binds-allp asg rxs)
                (r1cs::valuation-binds-allp asg rrs)
                (r1cs::valuation-bindsp asg pkx)
                (r1cs::valuation-bindsp asg pky)
                (r1cs::valuation-bindsp asg pk-qx)
                (r1cs::valuation-bindsp asg pk-qy)
                (r1cs::valuation-bindsp asg pk-cx2)
                (r1cs::valuation-bindsp asg pk-cy2)
                (r1cs::valuation-bindsp asg pk-dxy)
                (r1cs::valuation-bindsp asg pk-dx2)
                (r1cs::valuation-bindsp asg pk-dy2)
                (r1cs::valuation-bindsp asg pk-x3)
                (r1cs::valuation-bindsp asg pk-y3)
                (r1cs::valuation-bindsp asg pk-exy)
                (r1cs::valuation-bindsp asg pk-ex2)
                (r1cs::valuation-bindsp asg pk-ey2)
                (r1cs::valuation-bindsp asg prx)
                (r1cs::valuation-bindsp asg pry)
                (r1cs::valuation-bindsp asg pr-qx)
                (r1cs::valuation-bindsp asg pr-qy)
                (r1cs::valuation-bindsp asg pr-cx2)
                (r1cs::valuation-bindsp asg pr-cy2)
                (r1cs::valuation-bindsp asg pr-dxy)
                (r1cs::valuation-bindsp asg pr-dx2)
                (r1cs::valuation-bindsp asg pr-dy2)
                (r1cs::valuation-bindsp asg pr-x3)
                (r1cs::valuation-bindsp asg pr-y3)
                (r1cs::valuation-bindsp asg pr-exy)
                (r1cs::valuation-bindsp asg pr-ex2)
                (r1cs::valuation-bindsp asg pr-ey2)
                (equal (lookup-equal c asg)
                       (signature->challenge (literal-signature->get x)))
                (equal (lookup-equal-list cxs asg)
                       (scalar-bits-le (lookup-equal c asg)))
                (equal (lookup-equal-list crs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list cxs asg)
                        (scalar-modulus-minus-one-bits)))
                (equal (lookup-equal r asg)
                       (signature->response (literal-signature->get x)))
                (equal (lookup-equal-list rxs asg)
                       (scalar-bits-le (lookup-equal r asg)))
                (equal (lookup-equal-list rrs asg)
                       (crv-bits-lte-const-witness
                        (lookup-equal-list rxs asg)
                        (scalar-modulus-minus-one-bits)))
                (group-enforce-in-group-witness-lookupsp
                 pkx pky pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2
                 pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2
                 (compute-key->pk-sig
                  (signature->compute-key (literal-signature->get x)))
                 asg p)
                (group-enforce-in-group-witness-lookupsp
                 prx pry pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2
                 pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2
                 (compute-key->pr-sig
                  (signature->compute-key (literal-signature->get x)))
                 asg p))
           (r1cs::r1cs-constraints-holdp
            (literal-signature-new-gadget
             c cxs crs r rxs rrs
             pkx pky pk-qx pk-qy pk-cx2 pk-cy2 pk-dxy pk-dx2 pk-dy2
             pk-x3 pk-y3 pk-exy pk-ex2 pk-ey2
             prx pry pr-qx pr-qy pr-cx2 pr-cy2 pr-dxy pr-dx2 pr-dy2
             pr-x3 pr-y3 pr-exy pr-ex2 pr-ey2 p)
            asg p))
  :do-not-induct t
  :use ((:instance literal-signature-new-complete-when-witness)
        (:instance group-enforce-in-group-equations-when-witness-lookupsp
                   (x pkx) (y pky)
                   (qx pk-qx) (qy pk-qy) (cx2 pk-cx2) (cy2 pk-cy2)
                   (dxy pk-dxy) (dx2 pk-dx2) (dy2 pk-dy2)
                   (x3 pk-x3) (y3 pk-y3)
                   (exy pk-exy) (ex2 pk-ex2) (ey2 pk-ey2)
                   (pt (compute-key->pk-sig
                        (signature->compute-key (literal-signature->get x)))))
        (:instance group-enforce-in-group-equations-when-witness-lookupsp
                   (x prx) (y pry)
                   (qx pr-qx) (qy pr-qy) (cx2 pr-cx2) (cy2 pr-cy2)
                   (dxy pr-dxy) (dx2 pr-dx2) (dy2 pr-dy2)
                   (x3 pr-x3) (y3 pr-y3)
                   (exy pr-exy) (ex2 pr-ex2) (ey2 pr-ey2)
                   (pt (compute-key->pr-sig
                        (signature->compute-key (literal-signature->get x))))))
  :in-theory '(groupp-of-compute-key->pk-sig
               groupp-of-compute-key->pr-sig))
