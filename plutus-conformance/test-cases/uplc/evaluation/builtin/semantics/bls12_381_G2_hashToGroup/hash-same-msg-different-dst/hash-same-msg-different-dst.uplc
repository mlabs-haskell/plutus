-- Check that hashing the same message with different DSTs gives different
-- results: this should return False.
(program 1.0.0
 [
  [
   (builtin bls12_381_G2_equal)
   [
    [
     (builtin bls12_381_G2_hashToGroup)
     (con bytestring #8e)
    ]
    (con bytestring #0a)
   ]
  ]
  [
   [
    (builtin bls12_381_G2_hashToGroup)
    (con bytestring #8e)
   ]
   (con bytestring #01)
  ]
 ]
)